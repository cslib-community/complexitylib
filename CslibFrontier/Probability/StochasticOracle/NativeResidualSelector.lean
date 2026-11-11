/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.SourceEncoding
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.Feedback
public import CslibFrontier.Probability.StochasticOracle.ResidualCover
public import CslibFrontier.Computability.Probabilistic.NativeBatch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Mathlib.Tactic

/-!
# Native residual-directed source requests

[Wang2027], setup (1)--(3) and Theorem 6, PDF pp. 12--13. The original
binary-rational WSC input contains no hidden exact cover. Runtime incidence scans
recover one-hop components; for the source construction these are exactly the
connected components because each block has a whole-block fallback candidate.
Components are ordered by their least original element. Specialist opportunity
`j+1` denotes component `j` in this order, and opportunity zero is the near cover.
A subinstance query keeps original candidate labels and weights, rather than
renumbering a residual and losing output provenance.

The concrete two-turn scheduler asks the near cover, then selects a specialist
from the least actually uncovered element after parsing and certifying the first
raw report. It uses the existing same-code guarded feedback implementation.
No separately compiled continuation, hidden cover, scheduler-realization witness
or desired success law is supplied. Local work is response dependent and excluded
from the oracle deadline, as in the source model, PDF p. 5.

This module supplies runtime codecs, component/residual computation and the
compiled joint execution law. The general source-family specialization, universal
native optimum and uniform optimal-output theorem are not yet proved here.

## Main definitions

* `Query`, `queryEncoding`: original WSC data paired with the subinstance universe.
* `region`, `representatives`: component recovery using only original incidence.
* `residual`, `selected`, `request`: actual retained-history adaptive scheduling.
* `controller`: one implementation for all runtime role counts.

## Main results

* `region_eq`: incidence scans recover blocks whenever common incidence identifies them.
* `computable_request`: uniform native compilation of residual-directed source packets.
* `controller_law`: original-input same-code execution with arbitrary correlated environments.
* `controller_protocol`: termination and exact accepted-source resource/provenance meters.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualSelector
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ConcurrentBatch
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Original WSC data and the selected original-element universe. Candidate labels
are positions in the original system, including in specialist responses. -/
structure Query where
  /-- Original rational incidence and certification data. -/
  system : NativeRetention.Input
  /-- The full source universe or a computed residual subuniverse. -/
  points : List ℕ
  deriving DecidableEq

/-- Framed original WSC input followed by a framed list of unary original element labels. -/
enc_structure queryEncoding : Query where system : encInput, points : (encList encUnary)

/-- Candidate labels of the actual subinstance, without changing their original IDs.
Candidates must lie wholly inside the requested universe. -/
@[expose] def Query.candidates (q : Query) : List ℕ :=
  (population q.system).filter fun j =>
    (q.system.rows.getD j []).all fun e => decide (e ∈ q.points)

/-- One-hop incidence region, scanned in original element order. The source's
whole-block candidates make one hop sufficient; this is not a generic BFS claim. -/
@[expose] def region (x : NativeRetention.Input) (seed : ℕ) : List ℕ :=
  (ground x).filter fun e => x.rows.any fun row =>
    decide (seed ∈ row) && decide (e ∈ row)

/-- Each recovered region contributes exactly its least original point. -/
@[expose] def representatives (x : NativeRetention.Input) : List ℕ :=
  (ground x).filter fun e => decide ((region x e).headD 0 = e)

/-- The incidence scan agrees with any source block partition whose blocks are
characterized by shared candidates. This hypothesis is a source incidence fact,
not a supplied runtime component certificate or success conclusion. -/
theorem region_eq (x : NativeRetention.Input) (block : ℕ → ℕ) (seed : ℕ)
    (h : ∀ e ∈ ground x, (∃ row ∈ x.rows, seed ∈ row ∧ e ∈ row) ↔ block e = block seed) :
    region x seed = (ground x).filter (fun e => decide (block e = block seed)) := by
  apply List.filter_congr
  intro e he
  apply Bool.eq_iff_iff.mpr
  simpa only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using h e he

/-- Actual uncovered original points after full packet parsing and local retention. -/
@[expose] def residual (state : RuntimeControl.State) : List ℕ :=
  let data := Packets.assemble state.work
  (ground data).filter fun e => !(decide (e ∈ covered data (retain data)))

/-- The next target is derived from actual retained coverage, never an oracle label. -/
@[expose] def target (state : RuntimeControl.State) : ℕ :=
  (residual state).headD 0

/-- First issue the near cover. The only possible second-turn opportunity is a
specialist whose recovered representative is the first uncovered point. -/
@[expose] def selected (state : RuntimeControl.State) (i : ℕ) : Bool :=
  if state.turns = 2 then decide (i = 0) else
    decide (state.turns = 1) && decide (0 < i) &&
      decide ((representatives state.work.system).getD (i - 1) 0 = target state)

/-- A near-cover query contains the whole instance; the follow-up contains the
actual uncovered universe. The original rows, weights and global labels survive. -/
@[expose] def query (state : RuntimeControl.State) : Query :=
  ⟨state.work.system, if state.turns = 2 then ground state.work.system else residual state⟩

/-- All requests in a turn are computed from the old runtime context. The role
interface size is runtime data, not a compilation parameter. -/
@[expose] def slots (state : RuntimeControl.State) : Fin state.work.opportunities → Option Word :=
  fun i => if selected state i.val then some (queryEncoding (query state)) else none

/-- Actual concurrent source packet, with runtime opportunity count and no hidden witnesses. -/
@[expose] def request (state : RuntimeControl.State) : Word :=
  (List.range state.work.opportunities).flatMap fun i =>
    if selected state i then
      true :: Kolmogorov.selfDelimitingCode (queryEncoding (query state)) else [false]

private def slotWord : Option Word → Word
  | none => [false]
  | some word => true :: Kolmogorov.selfDelimitingCode word

private theorem encode_flatMap (n : ℕ) (f : Fin n → Option Word) :
    encodeSlots n f = (List.ofFn f).flatMap slotWord := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ, List.flatMap_cons, encodeSlots, ih]
    cases f 0 <;> rfl

/-- The runtime-list implementation is precisely the original concurrent codec. -/
theorem request_eq (state : RuntimeControl.State) :
    request state = encodeSlots state.work.opportunities (slots state) := by
  rw [encode_flatMap, List.ofFn_eq_map, List.flatMap_map]
  unfold request
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  simp only [slots]
  split_ifs <;> rfl

/-- The near-cover opportunity cannot be reused in the follow-up batch. -/
theorem near_not_reused (state : RuntimeControl.State) (ht : state.turns = 1)
    (i : Fin state.work.opportunities) (hi : i.val = 0) : slots state i = none := by
  simp [slots, selected, ht, hi]

/-- With two turns remaining the preformed request contains only the near cover. -/
theorem first_slots (state : RuntimeControl.State) (ht : state.turns = 2) :
    slots state = fun i => if i.val = 0 then some (queryEncoding (query state)) else none := by
  funext i
  simp [slots, selected, ht]

attribute [local fun_prop] NativeRetention.computable_rows NativeRetention.computable_dual

private theorem region_computable : ComputableInPolyTime
    (fun p : NativeRetention.Input × ℕ => region p.1 p.2)
    (encPair encInput encUnary) (encList encUnary) := by
  unfold region
  apply filterWithInput (NativeRetention.computable_ground.comp (by fun_prop))
  apply anyWithInput (by fun_prop)
  fun_prop

private theorem representatives_computable : ComputableInPolyTime representatives
    encInput (encList encUnary) := by
  unfold representatives
  apply filterWithInput NativeRetention.computable_ground
  have hr := region_computable
  fun_prop

private theorem runtime_fields : ComputableInPolyTime
    (fun s : RuntimeControl.State => (s.work, s.requests, s.privateWord,
      s.turns, s.opportunities, s.allotments)) RuntimeControl.encoding
    (encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))) := .of_eq fun _ => rfl
private theorem work_computable : ComputableInPolyTime RuntimeControl.State.work
    RuntimeControl.encoding Packets.encWork := runtime_fields.fst'
private theorem turns_computable : ComputableInPolyTime RuntimeControl.State.turns
    RuntimeControl.encoding encUnary := runtime_fields.snd'.snd'.snd'.fst'
private theorem system_computable : ComputableInPolyTime Packets.Work.system
    Packets.encWork encInput := Packets.work_fields.fst'
attribute [local fun_prop] work_computable turns_computable system_computable

private theorem retained_coverage_computable : ComputableInPolyTime
    (fun state : RuntimeControl.State =>
      covered (Packets.assemble state.work) (retain (Packets.assemble state.work)))
    RuntimeControl.encoding (encList encUnary) := by
  have ha : ComputableInPolyTime (fun state : RuntimeControl.State => Packets.assemble state.work)
      RuntimeControl.encoding encInput := Packets.computable_assemble.comp work_computable
  exact NativeRetention.computable_covered.comp (ha.prod (computable_retain.comp ha))

private theorem residual_computable : ComputableInPolyTime residual RuntimeControl.encoding
    (encList encUnary) := by
  have ha : ComputableInPolyTime (fun state : RuntimeControl.State => Packets.assemble state.work)
      RuntimeControl.encoding encInput := Packets.computable_assemble.comp work_computable
  have hc := retained_coverage_computable.comp
    (ComputableInPolyTime.fst RuntimeControl.encoding encUnary)
  have hm := ComputableInPolyTime.decide_mem hc
    (ComputableInPolyTime.snd RuntimeControl.encoding encUnary)
  exact filterWithInput (NativeRetention.computable_ground.comp ha)
    (ComputableInPolyTime.decide_not hm)

private theorem selected_computable : ComputableInPolyTime
    (fun p : RuntimeControl.State × ℕ => selected p.1 p.2)
    (encPair RuntimeControl.encoding encUnary) encBool := by
  have hr := representatives_computable
  have ht := residual_computable
  unfold selected target
  fun_prop

private theorem query_computable : ComputableInPolyTime query RuntimeControl.encoding
    queryEncoding := by
  have hs : ComputableInPolyTime (fun state : RuntimeControl.State => state.work.system)
      RuntimeControl.encoding encInput := system_computable.comp work_computable
  have he := decide_eq' turns_computable
    (ComputableInPolyTime.const (2 : ℕ) (encIn := RuntimeControl.encoding) (encOut := encUnary))
  have hp : ComputableInPolyTime
      (fun state : RuntimeControl.State =>
        if state.turns = 2 then ground state.work.system else residual state)
      RuntimeControl.encoding (encList encUnary) :=
    ComputableInPolyTime.ite_decide he (NativeRetention.computable_ground.comp hs)
      residual_computable
  exact (hs.prod hp).of_enc_eq fun _ => rfl

private theorem word_computable : ComputableInPolyTime
    (fun s => queryEncoding (query s)) RuntimeControl.encoding encBits :=
  (ComputableInPolyTime.of_eq (f := fun q => queryEncoding q) (fun _ => rfl)).comp
    query_computable

/-- Constructed native compilation, with runtime role count, history and arbitrary replies. -/
theorem computable_request : ComputableInPolyTime request
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits := by
  have hc : ComputableInPolyTime
      (fun state : RuntimeControl.State => state.work.opportunities)
      RuntimeControl.encoding encUnary := Packets.work_fields.snd'.fst'.comp work_computable
  have hw := word_computable.comp (ComputableInPolyTime.fst RuntimeControl.encoding encUnary)
  have hyes := bitsCons (const true) (selfDelimitingCode.comp hw)
  have hout : ComputableInPolyTime request RuntimeControl.encoding encBits :=
    flatMapToBitsWithInput (ComputableInPolyTime.range.comp hc)
      (selected_computable.ite hyes (const [false]))
  exact hout.comp RuntimeControl.computable_unframe

/-- Original binary WSC input, framed first, followed by a unary number of specialist roles.
The role count and instance are runtime data of one fixed native program. -/
abbrev startupEncoding := encPair SourceEncoding.encoding encUnary

/-- Compute fresh runtime control from original binary incidence data; hidden exact
covers, prepared contexts and prior proposal histories are absent from this input. -/
@[expose] def initial (z : ℕ) (x : SourceEncoding.Input) : RuntimeControl.State :=
  ⟨⟨SourceEncoding.toNative x, z + 1, []⟩, [], [], 2, z + 1, 2⟩

private theorem initial_computable : ComputableInPolyTime
    (fun p : SourceEncoding.Input × ℕ => initial p.2 p.1)
    startupEncoding RuntimeControl.encoding := by
  have hs := SourceEncoding.computable_toNative.comp
    (ComputableInPolyTime.fst SourceEncoding.encoding encUnary)
  have hn := ComputableInPolyTime.unary_succ.comp
    (ComputableInPolyTime.snd SourceEncoding.encoding encUnary)
  have hw : ComputableInPolyTime
      (fun p : SourceEncoding.Input × ℕ => (SourceEncoding.toNative p.1, p.2 + 1, ([] : List Word)))
      startupEncoding (encPair encInput (encPair encUnary (encList encBits))) :=
    hs.prod (hn.prod (const []))
  have hr : ComputableInPolyTime
      (fun p : SourceEncoding.Input × ℕ =>
        (([] : List Word), ([] : Word), (2 : ℕ), p.2 + 1, (2 : ℕ)))
      startupEncoding (encPair (encList encBits)
        (encPair encBits (encPair encUnary (encPair encUnary encUnary)))) :=
    (const []).prod ((const []).prod ((const 2).prod (hn.prod (const 2))))
  exact (hw.prod hr).of_enc_eq fun _ => rfl

/-- A native implementation together with the derived full joint law. -/
structure Controller where
  /-- Native tape count. -/
  tapes : ℕ
  /-- Finite native control type. -/
  Controls : Type
  /-- Finiteness of that control. -/
  finite : Finite Controls
  /-- One actual program, independent of instance and oracle. -/
  program : MultiTapePTM tapes Bool Controls Unit
  /-- Reserved runtime context tape. -/
  context : Fin tapes
  /-- Execution from original input, preserving the actual output and complete source memory. -/
  law : ∀ (P : Type) (env : Environment Unit P) (x : SourceEncoding.Input) (z : ℕ)
    (memory : Memory Unit P),
    (NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (startupEncoding (x, z)), memory⟩).map
        (Option.map (NativeReplyContext.observe context)) =
      (Feedback.run env 2 (initial z x) (fun _ => ⟨[], [], 0⟩) memory request).map
        fun outcome => some (⟨tapeOfList (RuntimeControl.packet outcome.state),
          RuntimeControl.result outcome.state, outcome.memory⟩ : NativeReplyContext.Observation P)

private theorem controller_nonempty : Nonempty Controller := by
  obtain ⟨time, space, _, _, hp⟩ := initial_computable
  obtain ⟨tapes, R, hR, code, context, hlaw⟩ :=
    Feedback.exists_native_controller_from_state startupEncoding (fun p => initial p.2 p.1)
      (fun p => time (startupEncoding p).length)
      (fun p => space (startupEncoding p).length) hp request computable_request
  exact ⟨⟨tapes, R, hR, code, context, fun P env x z => hlaw P env (x, z)⟩⟩

/-- One fixed implementation for all runtime role counts, chosen independently of
source probabilities, hidden covers and quantitative conclusions. -/
def controller : Controller := Classical.choice controller_nonempty

/-- The constructed controller has the same actual retained-history joint law,
including source memory, response-dependent local work, stopping and decoded output. -/
theorem controller_law (z : ℕ) (P : Type) (env : Environment Unit P)
    (x : SourceEncoding.Input) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal controller.program env
      ⟨controller.program.initialConfig (startupEncoding (x, z)), memory⟩).map
        (Option.map (NativeReplyContext.observe controller.context)) =
      (Feedback.run env 2 (initial z x) (fun _ => ⟨[], [], 0⟩) memory request).map
        fun outcome => some (⟨tapeOfList (RuntimeControl.packet outcome.state),
          RuntimeControl.result outcome.state, outcome.memory⟩ :
            NativeReplyContext.Observation P) :=
  controller.law P env x z memory

/-- On the actual guarded source protocol, the same controller terminates with
an authenticated source ledger and exact accrued-cost/time/provenance meters.
The protocol enforces deadline, turn budget and global nonreuse for accepted
batches. This does not assert that malformed or unsupported queries are accepted. -/
theorem controller_protocol {Private : Type} (z : ℕ) (x : SourceEncoding.Input)
    (limits : Limits (z + 1)) (sample : Sampler (z + 1) Private) (seed : Private)
    (outcome : Option (NativeReplyContext.Observation (ServerState (z + 1) Private)))
    (ho : outcome ∈ ((NativeUnboundedExecution.terminal controller.program
      (environment limits sample)
        ⟨controller.program.initialConfig (startupEncoding (x, z)),
          ⟨ConcurrentBatch.initial seed, []⟩⟩).map
            (Option.map (NativeReplyContext.observe controller.context))).support) :
    ∃ final, outcome = some final ∧ NativeBatch.Invariant limits final.memory := by
  have hlaw := ho
  rw [controller_law] at hlaw
  obtain ⟨_, _, hsome⟩ := (PMF.mem_support_map_iff _ _ _).mp hlaw
  have hn : outcome ≠ none := by rw [← hsome]; exact Option.some_ne_none _
  obtain ⟨raw, hr, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  cases raw with
  | none => exact False.elim (hn he.symm)
  | some world =>
    have hinv := NativeBatch.terminal_invariant limits sample controller.program
      ⟨controller.program.initialConfig (startupEncoding (x, z)),
        ⟨ConcurrentBatch.initial seed, []⟩⟩ world
      (NativeBatch.initial_invariant limits seed) hr
    exact ⟨NativeReplyContext.observe controller.context world, he.symm, hinv⟩

end Cslib.Probability.StochasticOracle.NativeResidualSelector
