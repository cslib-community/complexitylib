/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative
public import CslibFrontier.Probability.PMF.ObservedProcess.Trajectory
import CslibFrontier.Probability.PMF.SupportTsum
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Actual native infinite-path bills, including silent divergence

[Wang2027], model pp. 4--6, Theorem 5/App. A.5 pp. 12,16. The actual native
source-epoch transition constructs an infinite trajectory of complete retained
states. Its total nonnegative bill is the series of actual newly accrued receipts.
Previously billed tokens persist when local computation diverges. No finite
response alphabet or local instruction clock bound is imposed.

Open the `NativeBatch.PathCost` scope for the discrete state sigma algebra.
This matches PMF semantics; it does not represent arbitrary nonatomic oracle laws.

## Main definitions

* `pathMeasureFrom`, `pathMeasure`, `partialBill`, `totalBill`: actual paths and retained costs.

## Main results

* `partialBill_eq_accrued`: actual accrued bills are the path series' partial sums.
* `lintegral_totalBill`: total expected bill is the supremum of finite native expectations.
* `lintegral_totalBill_complete`: the actual source budget identifies the complete expectation.
* `totalBill_integrable_budget`: real integrability derived from local source cost envelopes.
-/

public section
noncomputable section
namespace Cslib.Probability.NativeBatch.PathCost
open MeasureTheory NativeOpenExecution StochasticOracle.ConcurrentBatch Turing Trace
open scoped ENNReal NNReal
variable {n k : ℕ} {Private Control : Type} {input : List Bool}

/-- Discrete native hidden states, with product sigma algebra on infinite paths.
Even continuous-valued metadata is viewed through its actual PMF law here. -/
scoped instance stateMeasurableSpace : MeasurableSpace (State n k Private Control input) := ⊤
attribute [local instance] stateMeasurableSpace

variable (limits : Limits n) (sample : Sampler n Private)
variable (machine : MultiTapePTM k Bool Control Unit)

/-- Continue the actual native epoch transition from a retained trace prefix. -/
@[expose] def pathMeasureFrom (state : State n k Private Control input) :
    Measure (ℕ → State n k Private Control input) :=
  ObservedProcess.trajectory (Trace.step limits sample machine) state

/-- Execute the original native epoch transition forever, preserving its entire
hidden state and accrued receipts after halt or divergence. -/
@[expose] def pathMeasure (world : World k Control Unit (ServerState n Private) input) :
    Measure (ℕ → State n k Private Control input) :=
  pathMeasureFrom limits sample machine (Trace.initial world)

instance pathMeasure_isProbabilityMeasure
    (world : World k Control Unit (ServerState n Private) input) :
    IsProbabilityMeasure (pathMeasure limits sample machine world) := by
  unfold pathMeasure pathMeasureFrom
  infer_instance

/-- Actual newly appended nonnegative receipt scores through the given epoch. -/
@[expose] def partialBill (score : Record n → ℝ≥0∞) (turns : ℕ)
    (ω : ℕ → State n k Private Control input) : ℝ≥0∞ :=
  accrued score (ω 0) + ∑ t ∈ Finset.range turns, Quantitative.newest score (ω (t + 1))

/-- Actual total nonnegative path bill. Divergence cannot erase an earlier receipt. -/
@[expose] def totalBill (score : Record n → ℝ≥0∞)
    (ω : ℕ → State n k Private Control input) : ℝ≥0∞ :=
  accrued score (ω 0) + ∑' t, Quantitative.newest score (ω (t + 1))

/-- Nonnegative receipt scores give measurable actual partial bills. -/
theorem measurable_partialBill (score : Record n → ℝ≥0∞) (turns : ℕ) :
    Measurable (partialBill (k := k) (Private := Private) (Control := Control)
      (input := input) score turns) := by
  unfold partialBill
  apply ((Measurable.of_discrete : Measurable (accrued (k := k) (Private := Private)
    (Control := Control) (input := input) score)).comp (measurable_pi_apply 0)).add
  apply Finset.measurable_sum
  intro t ht
  exact (Measurable.of_discrete : Measurable (Quantitative.newest score)).comp
    (measurable_pi_apply (t + 1))

/-- The total nonnegative actual bill is measurable, without an integrability premise. -/
theorem measurable_totalBill (score : Record n → ℝ≥0∞) :
    Measurable (totalBill (k := k) (Private := Private) (Control := Control)
      (input := input) score) := by
  unfold totalBill
  apply ((Measurable.of_discrete : Measurable (accrued (k := k) (Private := Private)
    (Control := Control) (input := input) score)).comp (measurable_pi_apply 0)).add
  apply Measurable.tsum
  intro t
  exact (Measurable.of_discrete : Measurable (Quantitative.newest score)).comp
    (measurable_pi_apply (t + 1))

/-- Actual accrued ledgers equal the series' partial sums on almost every path.
The equality follows from native receipt appending, including zero-call decisions. -/
theorem partialBill_eq_accrued_from (score : Record n → ℝ≥0∞)
    (state : State n k Private Control input) :
    ∀ᵐ ω ∂pathMeasureFrom limits sample machine state,
      ∀ turns, partialBill score turns ω = accrued score (ω turns) := by
  let S := State n k Private Control input
  have hrelation : MeasurableSet {p : S × S |
      accrued score p.2 = accrued score p.1 + Quantitative.newest score p.2} := by
    have ha : Measurable (accrued (k := k) (Private := Private) (Control := Control)
      (input := input) score) := Measurable.of_discrete
    have hn : Measurable (Quantitative.newest (k := k) (Private := Private) (Control := Control)
      (input := input) score) := Measurable.of_discrete
    exact measurableSet_eq_fun (ha.comp measurable_snd)
      ((ha.comp measurable_fst).add (hn.comp measurable_snd))
  have hsteps : ∀ t, ∀ᵐ ω ∂pathMeasureFrom limits sample machine state,
      accrued score (ω (t + 1)) = accrued score (ω t) +
        Quantitative.newest score (ω (t + 1)) := by
    intro t
    apply ObservedProcess.ae_step (Trace.step limits sample machine) state t
      (fun a b => accrued score b = accrued score a + Quantitative.newest score b) hrelation
    intro state next hn
    simp only [Trace.step, PMF.mem_support_bind_iff, Trace.respond, PMF.mem_support_map_iff] at hn
    obtain ⟨hit, _, after, _, rfl⟩ := hn
    simp only [accrued, Quantitative.newest, List.map_cons, List.sum_cons, List.headD_cons]
    exact add_comm _ _
  filter_upwards [ae_all_iff.mpr hsteps] with ω hsteps
  intro turns
  induction turns with
  | zero => simp [partialBill]
  | succ t ih =>
    rw [partialBill, Finset.sum_range_succ, ← add_assoc]
    change partialBill score t ω + Quantitative.newest score (ω (t + 1)) = _
    rw [ih, hsteps t]

/-- Fresh execution is the zero-retained-prefix case of actual continuation. -/
theorem partialBill_eq_accrued (score : Record n → ℝ≥0∞)
    (world : World k Control Unit (ServerState n Private) input) :
    ∀ᵐ ω ∂pathMeasure limits sample machine world,
      ∀ turns, partialBill score turns ω = accrued score (ω turns) :=
  partialBill_eq_accrued_from limits sample machine score (Trace.initial world)

/-- Finite partial bills continue from the actual retained prefix, without
resetting any earlier charges. -/
theorem lintegral_partialBill_from (score : Record n → ℝ≥0∞) (turns : ℕ)
    (state : State n k Private Control input) :
    (∫⁻ ω, partialBill score turns ω ∂pathMeasureFrom limits sample machine state) =
      ∑' next, ObservedProcess.stateLaw (Trace.step limits sample machine) turns state next *
        accrued score next := by
  rw [lintegral_congr_ae ((partialBill_eq_accrued_from limits sample machine score state).mono
    (fun ω h => h turns))]
  exact ObservedProcess.lintegral_coordinate _ _ _ _

/-- Expected actual partial bill is exactly the original finite native expectation. -/
theorem lintegral_partialBill (score : Record n → ℝ≥0∞) (turns : ℕ)
    (world : World k Control Unit (ServerState n Private) input) :
    (∫⁻ ω, partialBill score turns ω ∂pathMeasure limits sample machine world) =
      Quantitative.expected limits sample machine score turns world := by
  rw [lintegral_congr_ae ((partialBill_eq_accrued limits sample machine score world).mono
    (fun ω h => h turns))]
  exact ObservedProcess.lintegral_coordinate _ _ _ _

/-- Monotone convergence for the actual native bill. No finite total-cost bound,
integrability or almost-sure termination is supplied as a hypothesis. -/
theorem lintegral_totalBill_from (score : Record n → ℝ≥0∞)
    (state : State n k Private Control input) :
    (∫⁻ ω, totalBill score ω ∂pathMeasureFrom limits sample machine state) =
      ⨆ turns, ∑' next,
        ObservedProcess.stateLaw (Trace.step limits sample machine) turns state next *
          accrued score next := by
  change (∫⁻ ω, accrued score (ω 0) + ∑' t, Quantitative.newest score (ω (t + 1))
    ∂pathMeasureFrom limits sample machine state) = _
  simp only [ENNReal.tsum_eq_iSup_nat, ENNReal.add_iSup]
  change (∫⁻ ω, ⨆ turns, partialBill score turns ω
    ∂pathMeasureFrom limits sample machine state) = _
  rw [lintegral_iSup (fun t => measurable_partialBill score t)]
  · simp only [lintegral_partialBill_from]
  · intro a b hab ω
    exact add_le_add le_rfl (Finset.sum_le_sum_of_subset
      (f := fun t => Quantitative.newest score (ω (t + 1))) (Finset.range_mono hab))

/-- Infinite actual bills from a fresh native start have exactly the supremum
of the original finite native expectations. -/
theorem lintegral_totalBill (score : Record n → ℝ≥0∞)
    (world : World k Control Unit (ServerState n Private) input) :
    (∫⁻ ω, totalBill score ω ∂pathMeasure limits sample machine world) =
      ⨆ turns, Quantitative.expected limits sample machine score turns world :=
  lintegral_totalBill_from limits sample machine score (Trace.initial world)

private theorem expected_after_budget (score : Record n → ℝ≥0∞) (hz : score none = 0)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) (extra : ℕ) :
    Quantitative.expected limits sample machine score (limits.turns + 1 + extra) world =
      Quantitative.expected limits sample machine score (limits.turns + 1) world := by
  let Done (state : State n k Private Control input) : Prop :=
    state.hidden = none ∨ ∃ next, state.hidden = some (.ready next) ∧
      NativeUnboundedExecution.halted next
  have hd : ∀ extra state, state ∈
      (law limits sample machine (limits.turns + 1 + extra) world).support → Done state := by
    intro extra
    induction extra with
    | zero => exact law_done limits sample machine world hi
    | succ extra ih =>
      intro state hs
      change state ∈ ((law limits sample machine (limits.turns + 1 + extra) world).bind
        (Trace.step limits sample machine)).support at hs
      obtain ⟨previous, hp, hs⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have hp := ih previous hp
      rw [step_done limits sample machine previous hp, PMF.mem_support_pure_iff] at hs
      subst state
      exact hp
  induction extra with
  | zero => rfl
  | succ extra ih =>
    change Quantitative.mean ((law limits sample machine (limits.turns + 1 + extra) world).bind
      (Trace.step limits sample machine)) (accrued score) = _
    unfold Quantitative.mean
    rw [PMF.tsum_bind_mul]
    rw [PMF.tsum_mul_congr_support _ (fun state hs => show
      (∑' next, Trace.step limits sample machine state next * accrued score next) =
        accrued score state from by
      rw [step_done limits sample machine state (hd extra state hs)]
      simp [accrued, hz])]
    exact ih

/-- The actual infinite-path expectation equals the complete finite native trace
expectation. The finite source budget is enforced by dispatch; halt or silent
divergence contributes no future charges but retains its earlier bill. -/
theorem lintegral_totalBill_complete (score : Record n → ℝ≥0∞) (hz : score none = 0)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory) :
    (∫⁻ ω, totalBill score ω ∂pathMeasure limits sample machine world) =
      Quantitative.expected limits sample machine score (limits.turns + 1) world := by
  have hm : Monotone (fun t => Quantitative.expected limits sample machine score t world) := by
    apply monotone_nat_of_le_succ
    intro t
    change Quantitative.mean (law limits sample machine t world) (accrued score) ≤
      Quantitative.mean ((law limits sample machine t world).bind
        (Trace.step limits sample machine)) (accrued score)
    rw [Quantitative.step_accrued]
    exact le_self_add
  rw [lintegral_totalBill]
  apply le_antisymm (iSup_le (fun turns => ?_)) (le_iSup _ (limits.turns + 1))
  by_cases ht : turns ≤ limits.turns + 1
  · exact hm ht
  · have he : limits.turns + 1 + (turns - (limits.turns + 1)) = turns :=
      Nat.add_sub_cancel' (le_of_not_ge ht)
    rw [← he, expected_after_budget limits sample machine score hz world hi]

/-- Finite source conditional invoice envelopes imply almost-sure finite actual
path bills and real integrability, with the source turn-budget expectation bound.
Unbounded realized reports and later silent divergence are allowed. -/
theorem totalBill_integrable_budget (c : ℝ≥0)
    (world : World k Control Unit (ServerState n Private) input)
    (hi : Invariant limits world.memory)
    (H : ∀ turn, ∀ o ∈
      ((Quantitative.select limits sample machine (law limits sample machine turn world)).map
        (Quantitative.observe limits)).support, o.issued = true →
      Quantitative.conditionalMean limits sample machine (law limits sample machine turn world)
        o charge ≤ c) :
    (∀ᵐ ω ∂pathMeasure limits sample machine world, totalBill charge ω < ⊤) ∧
    Integrable (fun ω => (totalBill charge ω).toReal)
      (pathMeasure limits sample machine world) ∧
    (∫ ω, (totalBill charge ω).toReal ∂pathMeasure limits sample machine world) ≤
      (c : ℝ) * limits.turns := by
  have hb : (∫⁻ ω, totalBill charge ω ∂pathMeasure limits sample machine world) ≤
      (c : ℝ≥0∞) * limits.turns := by
    rw [lintegral_totalBill]
    apply iSup_le
    intro turns
    exact (Quantitative.cost_upper_budget limits sample machine c turns world hi
      (fun turn _ => H turn)).1
  have hfinite := ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hb
  have hm := measurable_totalBill (n := n) (k := k) (Private := Private) (Control := Control)
    (input := input) charge
  have hae := ae_lt_top hm hfinite
  refine ⟨hae, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfinite, ?_⟩
  rw [integral_toReal hm.aemeasurable hae]
  simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) hb

end Cslib.Probability.NativeBatch.PathCost
