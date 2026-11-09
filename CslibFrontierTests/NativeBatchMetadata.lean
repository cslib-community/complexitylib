/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontierTests.NativeBatchPolicy
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Unbounded actual invoice metadata and retained charges after silent divergence

A geometric latent natural number supplies all first-batch invoices and is kept
in oracle memory for later calls. Every natural value has positive probability;
there is no lossless finite invoice alphabet. The actual native whole-policy
transfer and selected-epoch accounting use the full discrete metadata directly.
A silent native loop after a real charged prefix keeps that prefix's invoices.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution NativeInterface
open Cslib.Probability.StochasticOracle.ConcurrentBatch
open Cslib.Probability.NativeBatch
open scoped NNReal ENNReal
namespace CslibFrontierTests.NativeBatchMetadata
open CslibFrontierTests.NativeBatchPolicy (machine first firstReceipt firstMemory)
open CslibFrontierTests.ConcurrentBatch (limits)

/-- An actual countably supported latent law, with no maximum possible invoice. -/
def metadata : PMF ℕ :=
  (ProbabilityTheory.geometricMeasure ⟨1 / 2, by constructor <;> norm_num⟩).toPMF

/-- Every latent metadata value really has positive mass. -/
theorem metadata_support (n : ℕ) : n ∈ metadata.support := by
  change (ProbabilityTheory.geometricMeasure _).toPMF n ≠ 0
  rw [MeasureTheory.Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton
    (by norm_num [Subtype.ext_iff])]
  apply ne_of_gt
  apply ENNReal.ofReal_pos.mpr
  change 0 < (1 - (1 / 2 : ℝ)) ^ n * (1 / 2)
  positivity

/-- All simultaneously issued calls retain the same unbounded invoice variable. -/
def metadataPaths (value : ℕ) (_ : Fin 3) : CallTrace :=
  ⟨some (1, [true]), fun _ => value + 1, by intro _ _ _; exact le_rfl⟩

/-- One fixed hidden-state oracle for every native competitor and every history. -/
def sample : Sampler 3 ℕ := fun state _ =>
  if state.history = [] then metadata.map fun value => (metadataPaths value, value)
  else PMF.pure (metadataPaths state.privateState, state.privateState)

/-- Actual ordinary native start for the same finite-control two-packet code. -/
def start : World 0 (Fin 12) Unit (ServerState 3 ℕ) [] :=
  ⟨machine.initialConfig [], ⟨StochasticOracle.ConcurrentBatch.initial 0, []⟩⟩

/-- Actual complete native law is represented without bounding private metadata,
invoice sizes, output strings or the silent instruction count. -/
example : (Trace.law limits sample machine 3 start).map
      (fun state => state.hidden.map worldOf) =
    NativeUnboundedExecution.terminal machine (environment limits sample) start :=
  Trace.law_native_terminal limits sample machine start (NativeBatch.initial_invariant limits 0)

/-- Every natural invoice scale occurs in the concrete guarded concurrent handler. -/
theorem unbounded_invoices (value : ℕ) :
    ∃ out ∈ (serve limits sample (encodeBatch first) start.memory.privateState).support,
      out.1.tokens = (2 * (value + 1) : ℕ) := by
  have ha : admit limits start.memory.privateState (encodeBatch first) = some first := by
    simp [admit, decodeBatch_encode, start, StochasticOracle.ConcurrentBatch.initial, limits]
  rw [serve_accepted _ _ _ _ _ ha]
  simp only [sample, start, StochasticOracle.ConcurrentBatch.initial, ite_true, PMF.map_comp]
  refine ⟨_, (PMF.mem_support_map_iff _ _ _).mpr ⟨value, metadata_support value, rfl⟩, ?_⟩
  have hactive : active first.slots = {0, 1} := by decide
  change ((observe limits _ first (metadataPaths value)).tokens : ℝ≥0) = _
  rw [observe_tokens]
  simp [hactive, metadataPaths, CallTrace.stop, limits]

/-- No finite response alphabet can preserve these actual invoice observations.
This is not a claim that every task-specific statistical abstraction is impossible. -/
example {R : Type} [Finite R] (encode : ℕ → R) (recover : R → ℕ)
    (h : ∀ value, recover (encode value) = 2 * (value + 1)) : False := by
  apply not_injective_infinite_finite encode
  intro a b hab
  have he := congrArg recover hab
  rw [h a, h b] at he
  omega

/-- The entire actual metadata-sensitive policy satisfies the derived conditional
resource tower; no finite sufficient abstraction or integrability is assumed. -/
example : Quantitative.expected limits sample machine Trace.charge 3 start =
    ∑ turn ∈ Finset.range 3,
      Quantitative.marginal limits sample machine Trace.charge turn start :=
  Quantitative.expected_accrued limits sample machine Trace.charge 3 start

private theorem sample_paths (state : ServerState 3 ℕ) (batch : Batch 3)
    (paths : Fin 3 → CallTrace) (value : ℕ)
    (hs : (paths, value) ∈ (sample state batch).support) : paths = metadataPaths value := by
  simp only [sample] at hs
  split at hs
  · rw [PMF.mem_support_map_iff] at hs
    obtain ⟨n, _, he⟩ := hs
    cases he
    rfl
  · rw [PMF.mem_support_pure_iff] at hs
    cases hs
    rfl

private theorem response_minimum {Controls : Type} {tapes : ℕ} {x : List Bool}
    (competitor : MultiTapePTM tapes Bool Controls Unit)
    (prior : PMF (Trace.State 3 tapes ℕ Controls x))
    (picked : Quantitative.Selected 3 tapes ℕ Controls x)
    (hp : picked ∈ (Quantitative.select limits sample competitor prior).support)
    (next : Trace.State 3 tapes ℕ Controls x)
    (hn : next ∈ (Trace.respond limits sample competitor picked.before picked.checkpoint).support) :
    (1 : ℝ≥0∞) * Quantitative.newest Trace.issued next ≤
      1 * Quantitative.newest Trace.charge next := by
  simp only [Trace.respond, PMF.mem_support_map_iff] at hn
  obtain ⟨nextPhase, hn, rfl⟩ := hn
  cases he : picked.checkpoint with
  | none =>
    simp only [he, respondSource, PMF.mem_support_pure_iff] at hn
    subst nextPhase
    simp [Quantitative.newest, Trace.receipt, Trace.issued, Trace.charge]
  | some phase =>
    have hb := Quantitative.selected_boundary limits sample competitor prior picked hp phase he
    rw [he] at hn
    cases phase with
    | ready world =>
      change world.config.tapes.state = none at hb
      simp only [respondSource, phaseStep, hb, Option.isNone_none, ite_true,
        PMF.pure_map, PMF.mem_support_pure_iff] at hn
      subst nextPhase
      simp [Quantitative.newest, Trace.receipt, Trace.issued, Trace.charge]
    | pending chosen =>
      cases chosen with
      | halted world => exact hb.elim
      | «local» world => exact hb.elim
      | query world op state =>
        cases op
        change (admit limits world.memory.privateState
          (world.config.channels ()).queryBuffer).isSome = true at hb
        cases ha : admit limits world.memory.privateState
            (world.config.channels ()).queryBuffer with
        | none => simp [ha] at hb
        | some batch =>
          simp only [respondSource, phaseStep, dispatch, environment, serve, ha,
            PMF.map_comp, PMF.mem_support_map_iff] at hn
          obtain ⟨⟨paths, value⟩, hs, hr⟩ := hn
          have hs := sample_paths _ batch paths value hs
          subst paths
          cases hr
          simp only [Function.comp_def, Quantitative.newest, List.headD_cons, Trace.receipt,
            Memory.record, commit, List.head?_cons, Trace.issued, Option.isSome_some,
            ite_true, Trace.charge, Option.elim_some, one_mul]
          rw [observe_tokens]
          have hpos : 0 < ∑ i ∈ active batch.slots,
              (metadataPaths value i).accrued
                ((metadataPaths value i).stop (min (limits.cutoff i) (limits.deadline -
                  world.memory.privateState.elapsed))) := by
            obtain ⟨i, hi⟩ := batch.nonempty
            apply Finset.sum_pos'
            · intro _ _
              exact Nat.zero_le _
            · exact ⟨i, hi, Nat.succ_pos value⟩
          exact_mod_cast hpos

/-- A nonvacuous universal conditional cost envelope: this one fixed geometric
oracle charges at least one token for every selected nonempty batch, for every
actual native competitor, despite unbounded invoices and hidden correlation. -/
theorem all_competitors : ∀ (tapes : ℕ) (Controls : Type) (x : List Bool)
    (competitor : MultiTapePTM tapes Bool Controls Unit),
    NativeUnboundedExecution.SelectionOnly competitor (environment limits sample)
      (candidateParser (n := 3) 1) (decodeFamily 1) (fun _ => true)
        (Trace.startWorld (n := 3) (input := x) competitor 0) →
    Quantitative.expected limits sample competitor Trace.issued 3
        (Trace.startWorld (n := 3) (input := x) competitor 0) ≤
      Quantitative.expected limits sample competitor Trace.charge 3
        (Trace.startWorld (n := 3) (input := x) competitor 0) := by
  intro tapes Controls x competitor ha
  have he := Quantitative.universal_cost_lower limits sample 1 (fun _ => true) 1 0
    tapes Controls x competitor ha
  simp only [one_mul] at he
  apply he
  intro turn _ o ho hi
  have hb := Quantitative.conditional_of_response_bound limits sample competitor _ o ho
    Trace.issued Trace.charge 1 1 (response_minimum competitor _)
  simpa only [one_mul, Quantitative.conditional_issued limits sample competitor _ o ho,
    hi, ite_true] using hb

/-! ### A genuinely silent native suffix after an accrued batch -/

/-- A real native machine which stays at the same local configuration forever. -/
def spin : MultiTapePTM 0 Bool Unit Unit where
  initial := ()
  tr _ _ _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }
    (fun _ => none) (fun _ => 0)

/-- Resume with the actually constructed first receipt and its private oracle memory. -/
def spinning (u : Bool) : World 0 Unit Unit (ServerState 3 Bool) [] :=
  ⟨spin.initialConfig [], firstMemory u⟩

private theorem spin_instruction (u bit : Bool) : instruction spin (spinning u) bit =
    .local (spinning u) := by
  simp only [instruction, spinning, spin, MultiTapeMachine.initialConfig, Cfg.init,
    MultiTapeMachine.Config.step, Action.apply, Fin.isValue, moveInputPos_zero,
    zero_add, Option.toList_none, List.append_nil]
  congr 4 <;> funext i <;> exact Fin.elim0 i

private theorem spin_ready (u : Bool) : sourceSilent limits
      CslibFrontierTests.ConcurrentBatch.sample spin (.ready (spinning u)) =
    PMF.pure (.pending (.local (spinning u))) := by
  have hstate : (spinning u).config.tapes.state = some () := rfl
  simp only [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary,
    NativeUnboundedExecution.halted, hstate, reduceCtorEq, ite_false, phaseStep,
    Option.isNone_some, Bool.false_eq_true, prepare, PMF.map_comp, Function.comp_def,
    spin_instruction]
  exact PMF.map_const _ _

private theorem spin_local (u : Bool) : sourceSilent limits
      CslibFrontierTests.ConcurrentBatch.sample spin (.pending (.local (spinning u))) =
    PMF.pure (.ready (spinning u)) := by
  simp [sourceSilent, StoppedProcess.beforeBoundary, sourceBoundary, phaseStep, dispatch]

/-- Actual infinite silent computation has zero next-boundary mass. -/
theorem spin_diverges (u : Bool) : seekSourceFrom limits CslibFrontierTests.ConcurrentBatch.sample
    spin (some (.ready (spinning u))) = PMF.pure none := by
  have hs (fuel : ℕ) (phase : Phase 0 Unit Unit (ServerState 3 Bool) [])
      (hp : phase ∈ (ObservedProcess.stateLaw
        (sourceSilent limits CslibFrontierTests.ConcurrentBatch.sample spin) fuel
          (.ready (spinning u))).support) :
      phase = .ready (spinning u) ∨ phase = .pending (.local (spinning u)) := by
    induction fuel generalizing phase with
    | zero =>
      simp only [ObservedProcess.stateLaw, PMF.mem_support_pure_iff] at hp
      exact Or.inl hp
    | succ fuel ih =>
      simp only [ObservedProcess.stateLaw, PMF.mem_support_bind_iff] at hp
      obtain ⟨mid, hm, hp⟩ := hp
      rcases ih mid hm with rfl | rfl
      · rw [spin_ready, PMF.mem_support_pure_iff] at hp
        exact Or.inr hp
      · rw [spin_local, PMF.mem_support_pure_iff] at hp
        exact Or.inl hp
  apply StoppedProcess.option_ext
  intro phase
  simp only [PMF.pure_apply, reduceCtorEq, ite_false]
  apply (PMF.apply_eq_zero_iff _ _).mpr
  intro hp
  simp only [seekSourceFrom] at hp
  obtain ⟨hb, fuel, hf⟩ := (StoppedProcess.terminal_support _ _ _ _ _).mp hp
  rcases hs fuel phase hf with rfl | rfl
  · simp [sourceBoundary, NativeUnboundedExecution.halted, spinning,
      MultiTapeMachine.initialConfig, Cfg.init, spin] at hb
  · exact hb.elim

/-- This charged prefix is a real first-batch receipt, not a fake terminal bill. -/
def chargedPrefix (u : Bool) : Trace.State 3 0 Bool Unit [] :=
  ⟨some (.ready (spinning u)), [some (firstReceipt u)]⟩

/-- A later silent divergence preserves all previously accrued invoice data. -/
example (u : Bool) :
    Trace.step limits CslibFrontierTests.ConcurrentBatch.sample spin (chargedPrefix u) =
    PMF.pure ⟨none, [none, some (firstReceipt u)]⟩ := by
  simp [Trace.step, chargedPrefix, spin_diverges, Trace.respond, respondSource, Trace.receipt]

end CslibFrontierTests.NativeBatchMetadata
