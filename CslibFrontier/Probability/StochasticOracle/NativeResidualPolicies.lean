/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualOracle
import CslibFrontier.Probability.PMF.Disintegration.Support
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic

/-!
# Source behavioral tables derived from actual native epochs

[Wang2027], Theorem 6, PDF p. 13. Genuine next-source-query/halting epochs
retain arbitrary native hidden state and response-dependent local execution.
The concrete residual oracle supplies its finite residual law after selection;
posterior disintegration constructs the behavioral tables. No finite bound on
local instructions or hidden tape metadata is imposed. The latent residual is
instrumentation, including on wrong-query cancellations; it is not assumed to
have been revealed to the native code. The posterior construction still retains
the code’s actual raw queries and responses.

Native token minima are not yet proved: successful-only provenance must show
that output completion preserves native success, and actual accrued bills must
be identified with the source batch-cost score. General compiled upper-selector
admission/attainment also remains separate.

## Main definitions

* `Outcome`, `joint`: source actions/responses and the actual hidden native trace.
* `policy`, `selectionPolicy`: source behavioral tables and explicit output completion.

## Main results

* `joint_hidden`: the instrumented experiment has the actual native trace law.
* `policy_law`: the constructed tables preserve the instrumented source/native joint law.
* `terminal_law`: output readback is the original unbounded stopped native output.
* `policy_nonreuse`, `selection_admissible`: source no-reuse and behavioral admission are derived.
* `selection_cost`: output completion preserves the source batch-cost score.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualPolicies
open Finset NativeRetention ResidualCover NativeResidualEncoding ConcurrentBatch
open Turing NativeOpenExecution NativeInterface NativeBatch
open Cslib.Optimization.OneConstraint
variable {z n m tapes : ℕ} {Control : Type} {input : List Bool}
variable (T : Fin z → Block) (points : Fin n ≃ Point T) (candidates : Fin m ≃ Candidate T)
variable (P : Parameters z) (limits : Limits (z + 1)) (invoice : Fin (z + 1) → ℕ)
variable (machine : MultiTapePTM tapes Bool Control Unit)

private abbrev NativeState := Trace.State (z + 1) tapes Unit Control input
private abbrev Pick := Quantitative.Selected (z + 1) tapes Unit Control input

/-- Actual native epochs with their finite source observations. The hidden
trace retains divergence, all earlier invoices and arbitrary native metadata. -/
structure Outcome (z tapes : ℕ) (Control : Type) (input : List Bool) where
  /-- Selected first call set. -/
  first : ResidualCover.Batch z
  /-- First near-cover residual, or no near call. -/
  firstReply : Option (Fin z)
  /-- Selected response-dependent second call set. -/
  second : ResidualCover.Batch z
  /-- Second near-cover residual, or no near call. -/
  secondReply : Option (Fin z)
  /-- The real hidden native trace after the final local-computation epoch. -/
  hidden : Trace.State (z + 1) tapes Unit Control input

private def choose (state : NativeState (z := z) (tapes := tapes) (Control := Control)
    (input := input)) :
    PMF (Pick (z := z) (tapes := tapes) (Control := Control) (input := input)) :=
  (seekSourceFrom limits (NativeResidualOracle.sample T points candidates P invoice)
    machine state.hidden).map fun hit => ⟨state, hit⟩

private def action (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input)) :
    ResidualCover.Batch z := NativeResidualOracle.selectedCalls limits picked.checkpoint

private def respond (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (r : Option (Fin z)) : PMF (NativeState (z := z) (tapes := tapes) (Control := Control)
      (input := input)) :=
  NativeResidualOracle.response T points candidates limits invoice machine
    picked.before picked.checkpoint r

/-- Instrument actual native source epochs with the freshly sampled finite
source residuals. Their raw words, hidden native states and receipts are computed
by the concrete oracle; they are not supplied as a representation contract. -/
def joint (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    PMF (Outcome z tapes Control input) := do
  let first ← choose T points candidates P limits invoice machine (Trace.initial world)
  let r ← (reply P (action limits first)).toPMF
  let afterFirst ← respond T points candidates limits invoice machine first r
  let second ← choose T points candidates P limits invoice machine afterFirst
  let s ← (reply P (action limits second)).toPMF
  let afterSecond ← respond T points candidates limits invoice machine second s
  let final ← Trace.step limits (NativeResidualOracle.sample T points candidates P invoice)
    machine afterSecond
  pure ⟨action limits first, r, action limits second, s, final⟩

private theorem choose_respond (state : NativeState (z := z) (tapes := tapes)
    (Control := Control) (input := input)) :
    (choose T points candidates P limits invoice machine state).bind (fun picked =>
      (reply P (action limits picked)).toPMF.bind
        (respond T points candidates limits invoice machine picked)) =
      Trace.step limits (NativeResidualOracle.sample T points candidates P invoice)
        machine state := by
  change (choose T points candidates P limits invoice machine state).bind (fun picked =>
    (reply P (NativeResidualOracle.selectedCalls limits picked.checkpoint)).toPMF.bind
      (NativeResidualOracle.response T points candidates limits invoice machine
        picked.before picked.checkpoint)) = _
  simp only [choose, PMF.bind_map, ← NativeResidualOracle.response_factor,
    Trace.step, Function.comp_def]

/-- Forgetting the source observation instrumentation recovers the original
three-epoch native law, with no halting or representation premise. At a two-turn
limit its last epoch consists solely of post-response local execution. -/
theorem joint_hidden (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    (joint T points candidates P limits invoice machine world).map Outcome.hidden =
      Trace.law limits (NativeResidualOracle.sample T points candidates P invoice)
        machine 3 world := by
  simp only [joint, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind,
    PMF.pure_map, PMF.bind_pure, ← PMF.bind_bind]
  rw [choose_respond]
  rw [PMF.bind_bind
    (Trace.step limits (NativeResidualOracle.sample T points candidates P invoice)
      machine (Trace.initial world)) (choose T points candidates P limits invoice machine)]
  simp only [choose_respond, Trace.law, ObservedProcess.stateLaw, PMF.pure_bind, PMF.bind_bind]

/-- Decode the actual halted native mask under the original candidate labels.
Divergence, malformed masks and nonhalting states give the empty failure family. -/
@[expose] def readOutput (state : Trace.State (z + 1) tapes Unit Control input) :
    Finset (Candidate T) :=
  match state.hidden with
  | some (.ready world) =>
    ((NativeOpenSelection.result (decodeFamily m) world).map
      (fun C => C.map candidates.toEmbedding)).getD ∅
  | _ => ∅

private def firstPrior (world : World tapes Control Unit (ServerState (z + 1) Unit) input)
    (A : ResidualCover.Batch z) :
    PMF (Pick (z := z) (tapes := tapes) (Control := Control) (input := input)) :=
  PMF.posterior (choose T points candidates P limits invoice machine (Trace.initial world))
    (action limits) A

private def secondPrior (world : World tapes Control Unit (ServerState (z + 1) Unit) input)
    (A : ResidualCover.Batch z) (r : Option (Fin z)) :
    PMF (Pick (z := z) (tapes := tapes) (Control := Control) (input := input)) := do
  let first ← firstPrior T points candidates P limits invoice machine world A
  let next ← respond T points candidates limits invoice machine first r
  choose T points candidates P limits invoice machine next

private def finish (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (r : Option (Fin z)) : PMF (Finset (Candidate T)) := do
  let next ← respond T points candidates limits invoice machine picked r
  let final ← Trace.step limits (NativeResidualOracle.sample T points candidates P invoice)
    machine next
  pure (readOutput T candidates final)

/-- Behavioral tables derived from the actual machine's source-epoch hidden
posteriors. Only the finite source observations and output family are tabulated;
work tapes, private bits and unbounded local computation remain in the PMFs. -/
def policy (world : World tapes Control Unit (ServerState (z + 1) Unit) input) : TwoPolicy T where
  first := Distribution.ofPMF
    ((choose T points candidates P limits invoice machine
      (Trace.initial world)).map (action limits))
  second A r := Distribution.ofPMF
    ((secondPrior T points candidates P limits invoice machine world A r).map (action limits))
  output A r B s := Distribution.ofPMF
    ((PMF.posterior (secondPrior T points candidates P limits invoice machine world A r)
      (action limits) B).bind fun second =>
        finish T points candidates P limits invoice machine second s)

private theorem select_response {S A R O : Type} (prior : PMF S) (observe : S → A)
    (respond : A → PMF R) (next : S → R → PMF O) :
    (prior.map observe).bind (fun a => (respond a).bind fun r =>
      ((PMF.posterior prior observe a).bind fun s => next s r).map
        (fun o => (a, r, o))) =
      prior.bind (fun s => (respond (observe s)).bind fun r =>
        (next s r).map fun o => (observe s, r, o)) := by
  simp only [PMF.map_bind]
  have h := PMF.posterior_bind prior observe (fun s a =>
    (respond a).bind fun r => (next s r).map fun o => (a, r, o))
  rw [← h]
  apply congrArg ((prior.map observe).bind)
  funext a
  exact PMF.bind_comm _ _ _

/-- The finite behavioral policy has the complete native action/response/output
joint law. The representation is constructed for every actual native machine,
not supplied as an admission premise, and preserves hidden-state correlations. -/
theorem policy_law (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    ((policy T points candidates P limits invoice machine world).run P).toPMF =
      (joint T points candidates P limits invoice machine world).map (fun outcome =>
        (outcome.first, outcome.firstReply, outcome.second, outcome.secondReply,
          readOutput T candidates outcome.hidden)) := by
  simp only [policy, TwoPolicy.run, Distribution.toPMF_bind, Distribution.toPMF_map,
    Distribution.toPMF_ofPMF, PMF.map_bind]
  have hsecond (A : ResidualCover.Batch z) (r : Option (Fin z)) :=
    congrArg (PMF.map (fun (B, s, C) => (A, r, B, s, C)))
      (select_response (secondPrior T points candidates P limits invoice machine world A r)
        (action limits) (fun B => (reply P B).toPMF)
        (finish T points candidates P limits invoice machine))
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hsecond
  simp_rw [hsecond]
  have hfirst := select_response
    (choose T points candidates P limits invoice machine (Trace.initial world))
    (action limits) (fun A => (reply P A).toPMF) (fun first r => do
      let afterFirst ← respond T points candidates limits invoice machine first r
      let second ← choose T points candidates P limits invoice machine afterFirst
      let s ← (reply P (action limits second)).toPMF
      let C ← finish T points candidates P limits invoice machine second s
      pure (action limits second, s, C))
  simpa only [firstPrior, secondPrior, finish, joint,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.map_comp,
    Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.pure_map] using hfirst

private def usedCalls (records : List (Trace.Record (z + 1))) : ResidualCover.Batch z :=
  (usedHistory (records.filterMap id)).map (finSuccEquiv z).toEmbedding

private theorem choose_safe
    (state : NativeState (z := z) (tapes := tapes) (Control := Control) (input := input))
    (hv : Trace.Valid limits [] state)
    (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (hp : picked ∈ (choose T points candidates P limits invoice machine state).support) :
    Disjoint (action limits picked) (usedCalls state.records) := by
  simp only [choose, PMF.mem_support_map_iff] at hp
  obtain ⟨hit, hh, rfl⟩ := hp
  cases hs : state.hidden with
  | none =>
    simp only [hs, seekSourceFrom, PMF.mem_support_pure_iff] at hh
    subst hit
    simp [action, NativeResidualOracle.selectedCalls, sourceSignal]
  | some phase =>
    cases phase with
    | pending chosen => simp [Trace.Valid, hs] at hv
    | ready world =>
      simp only [Trace.Valid, hs] at hv
      obtain ⟨hinv, hhistory⟩ := hv
      cases hit with
      | none => simp [action, NativeResidualOracle.selectedCalls, sourceSignal]
      | some phase =>
        have hstate := Trace.seek_state limits
          (NativeResidualOracle.sample T points candidates P invoice) machine
          (.ready world) phase (by simpa only [hs] using hh)
        cases phase with
        | ready next => simp [action, NativeResidualOracle.selectedCalls, sourceSignal]
        | pending chosen =>
          cases chosen with
          | halted next => simp [action, NativeResidualOracle.selectedCalls, sourceSignal]
          | «local» next => simp [action, NativeResidualOracle.selectedCalls, sourceSignal]
          | query next op control =>
            cases op
            cases ha : admit limits next.memory.privateState
                (next.config.channels ()).queryBuffer with
            | none => simp [action, NativeResidualOracle.selectedCalls, sourceSignal, ha]
            | some batch =>
              obtain ⟨_, _, _, _, hd⟩ := admit_sound limits next.memory.privateState _ batch ha
              have hu : next.memory.privateState.used =
                  usedHistory (state.records.filterMap id) := by
                change (Trace.server (Phase.pending (.query next () control))).used = _
                rw [hstate]
                change world.memory.privateState.used = _
                rw [hinv.1.1, hhistory, List.append_nil]
              rw [hu] at hd
              simpa only [action, NativeResidualOracle.selectedCalls, sourceSignal, ha,
                Option.map_some, Option.bind_some, Option.elim_some, NativeResidualOracle.calls,
                usedCalls, Finset.disjoint_map] using hd

private theorem choose_before
    (state : NativeState (z := z) (tapes := tapes) (Control := Control) (input := input))
    (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (hp : picked ∈ (choose T points candidates P limits invoice machine state).support) :
    picked.before = state := by
  obtain ⟨hit, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  rfl

private theorem choose_boundary
    (state : NativeState (z := z) (tapes := tapes) (Control := Control) (input := input))
    (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (hp : picked ∈ (choose T points candidates P limits invoice machine state).support)
    (phase : Phase tapes Control Unit (ServerState (z + 1) Unit) input)
    (he : picked.checkpoint = some phase) : sourceBoundary limits phase := by
  apply Quantitative.selected_boundary limits
    (NativeResidualOracle.sample T points candidates P invoice)
    machine (PMF.pure state) picked _ phase he
  simpa only [choose, Quantitative.select, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind, PMF.map, Function.comp_def] using hp

private theorem supported_step
    (state next : NativeState (z := z) (tapes := tapes) (Control := Control) (input := input))
    (picked : Pick (z := z) (tapes := tapes) (Control := Control) (input := input))
    (hp : picked ∈ (choose T points candidates P limits invoice machine state).support)
    (r : Option (Fin z)) (hr : r ∈ (reply P (action limits picked)).toPMF.support)
    (hn : next ∈ (respond T points candidates limits invoice machine picked r).support) :
    next ∈ (Trace.step limits (NativeResidualOracle.sample T points candidates P invoice)
      machine state).support := by
  obtain ⟨hit, hh, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨hit, hh, ?_⟩
  exact NativeResidualOracle.response_support T points candidates P limits invoice machine
    state next hit r hr hn

/-- Actual source nonreuse survives the native posterior construction. Null
histories do not impose constraints; every reached first/second action pair is
disjoint, without assuming behavioral admission or a representation law. -/
theorem policy_nonreuse (world : World tapes Control Unit (ServerState (z + 1) Unit) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = [])
    (A : ResidualCover.Batch z) (r : Option (Fin z)) (B : ResidualCover.Batch z)
    (hA : 0 < (policy T points candidates P limits invoice machine world).first.weight A)
    (hr : 0 < (reply P A).weight r)
    (hB : 0 < ((policy T points candidates P limits invoice machine world).second A r).weight B) :
    Disjoint A B := by
  have hA' : A ∈ ((choose T points candidates P limits invoice machine
      (Trace.initial world)).map (action limits)).support := by
    intro h
    change 0 < (((choose T points candidates P limits invoice machine
      (Trace.initial world)).map (action limits)) A).toReal at hA
    rw [h, ENNReal.toReal_zero] at hA
    exact (lt_irrefl _ hA)
  have hr' : r ∈ (reply P A).toPMF.support := by
    intro h
    have he := (reply P A).toPMF_real r
    rw [h, ENNReal.toReal_zero] at he
    linarith
  have hB' : B ∈ ((secondPrior T points candidates P limits invoice machine world A r).map
      (action limits)).support := by
    intro h
    change 0 < (((secondPrior T points candidates P limits invoice machine world A r).map
      (action limits)) B).toReal at hB
    rw [h, ENNReal.toReal_zero] at hB
    exact (lt_irrefl _ hB)
  obtain ⟨second, hs, hsecond⟩ := (PMF.mem_support_map_iff _ _ _).mp hB'
  simp only [secondPrior, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨first, hf, next, hn, hs⟩ := hs
  obtain ⟨hf, hfirst⟩ := PMF.mem_support_of_posterior _ _ _ hA' first hf
  rw [← hfirst] at hr'
  have hstep := supported_step T points candidates P limits invoice machine
    (Trace.initial world) next first hf r hr' hn
  have hv : Trace.Valid limits [] next := by
    have hinit := Trace.initial_valid limits world hi
    rw [hzero] at hinit
    exact Trace.step_valid limits (NativeResidualOracle.sample T points candidates P invoice)
      machine [] _ next hinit hstep
  have hd := choose_safe T points candidates P limits invoice machine next hv second hs
  obtain ⟨record, hrecords, hrecord⟩ := NativeResidualOracle.response_record
    T points candidates limits invoice machine first.before next first.checkpoint
      (choose_boundary T points candidates P limits invoice machine _ first hf) r hn
  have hb := choose_before T points candidates P limits invoice machine _ first hf
  rw [hb] at hrecords
  change next.records = record :: [] at hrecords
  have hu : usedCalls next.records = A := by
    rw [hrecords, ← hfirst, action, hrecord]
    cases record <;> simp [usedCalls, usedHistory, NativeResidualOracle.calls]
  rw [hu, hsecond] at hd
  exact hd.symm

/-- Original-label output read directly from the actual optional native terminal
world. Missing terminal mass and malformed/nonhalting output remain failures. -/
@[expose] def terminalOutput
    (result : Option (World tapes Control Unit (ServerState (z + 1) Unit) input)) :
    Finset (Candidate T) :=
  ((result.bind fun world => NativeOpenSelection.result (decodeFamily m) world).map
    (fun C => C.map candidates.toEmbedding)).getD ∅

/-- With two permitted source turns, the constructed policy reads precisely the
original stopped native output, including divergent mass. Local computation is
not assigned a fixed clock and no termination or desired-output law is assumed. -/
theorem terminal_law (world : World tapes Control Unit (ServerState (z + 1) Unit) input)
    (hi : Invariant limits world.memory) (ht : limits.turns = 2) :
    ((policy T points candidates P limits invoice machine world).run P).toPMF.map
        (fun (_, _, _, _, C) => C) =
      (NativeUnboundedExecution.terminal machine
        (environment limits (NativeResidualOracle.sample T points candidates P invoice)) world).map
          (terminalOutput T candidates) := by
  rw [policy_law, PMF.map_comp]
  change (joint T points candidates P limits invoice machine world).map
    ((readOutput T candidates) ∘ Outcome.hidden) = _
  rw [← PMF.map_comp, joint_hidden]
  have h := Trace.law_native_terminal limits
    (NativeResidualOracle.sample T points candidates P invoice)
    machine world hi
  rw [ht] at h
  rw [← h, PMF.map_comp]
  apply PMF.bind_congr_on_support
  intro state hs
  have hd := Trace.law_done limits (NativeResidualOracle.sample T points candidates P invoice)
    machine world hi state (by simpa only [ht] using hs)
  rcases hd with hd | ⟨next, he, _⟩
  · simp [readOutput, terminalOutput, hd, Function.comp_def]
  · simp [readOutput, terminalOutput, he, Function.comp_def, worldOf]

open scoped Classical in
/-- Harmless selection-only completion of the observed output table. Intersection
can delete unproposed candidates but never add candidates to the native output.
Its agreement on admitted successful outputs is a separate obligation. -/
def selectionPolicy
    (world : World tapes Control Unit (ServerState (z + 1) Unit) input) : TwoPolicy T :=
  { policy T points candidates P limits invoice machine world with
    output := fun A r B s =>
      ((policy T points candidates P limits invoice machine world).output A r B s).map
        (fun C => C ∩ payload T (received A r ∪ received B s)) }

/-- Actual no-reuse plus the explicit output completion derive full source
behavioral admission, rather than placing it in a machine representation contract. -/
theorem selection_admissible
    (world : World tapes Control Unit (ServerState (z + 1) Unit) input)
    (hi : Invariant limits world.memory) (hzero : world.memory.privateState.history = []) :
    (selectionPolicy T points candidates P limits invoice machine world).Admissible P := by
  classical
  intro A r B hA hr hB
  refine ⟨policy_nonreuse T points candidates P limits invoice machine world hi hzero A r B
    hA hr hB, ?_⟩
  intro s C _ hC
  obtain ⟨D, _, rfl⟩ := (Distribution.mem_support_map
    ((policy T points candidates P limits invoice machine world).output A r B s)
      (fun C => C ∩ payload T (received A r ∪ received B s)) C).mp
        (mem_filter.mpr ⟨mem_univ _, hC⟩)
  exact inter_subset_right

/-- Output completion preserves the derived policy's expected issued batch cost
exactly. It neither assumes nor asserts a native optimum or success lower bound. -/
theorem selection_cost
    (world : World tapes Control Unit (ServerState (z + 1) Unit) input) :
    (selectionPolicy T points candidates P limits invoice machine world).cost P =
      (policy T points candidates P limits invoice machine world).cost P := by
  rw [TwoPolicy.cost_eq, TwoPolicy.cost_eq]
  rfl

end Cslib.Probability.StochasticOracle.NativeResidualPolicies
