/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.FullCover
public import CslibFrontier.Probability.FiniteTable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Random billed costs for full-cover policies

[Wang2027], Section 3 and Theorem 1, PDF pp. 5–7, allow random billed costs
correlated with success of the same call. The finite stopped-trace experiment
charges conditional expected costs, not deterministic realized bills. Here the
ambient probability space is arbitrary, and the bills need not be bounded,
discrete or independent of success. `billed_cost_eq` transfers the stopped-trace
formula to these bills using exactly the conditional expected batch-cost part of
the failure-invariant call assumption. It does not assume the expected total cost.

## Main results

* `billed_cost_eq`: the stopped-policy LP cost for integrable random bills.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset MeasureTheory Cslib.Optimization.OneConstraint
variable {ι : Type} [Fintype ι]

/-- The batch occupying a slot in a padded execution trace. -/
@[expose] def Plan.batchAt : {n : ℕ} → Plan ι n → Fin n → Finset ι
  | _+1, (A,B), i => Fin.cases A (fun j => B.batchAt j) i

omit [Fintype ι] in
/-- Trace cost is the sum of the expected batch costs in its occupied slots. -/
theorem Plan.traceCost_eq_sum (I : FullCoverInstance ι ℝ) {n : ℕ} (B : Plan ι n) :
    B.traceCost I = ∑ t, I.batchCost (B.batchAt t) := by
  induction n with
  | zero => simp [Plan.traceCost]
  | succ n ih =>
    rcases B with ⟨A,B⟩
    simp [Plan.traceCost, Fin.sum_univ_succ, Plan.batchAt, ih]

private theorem finite_partition_integral {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (μ : Measure Ω) (X : Ω → α)
    (hm : ∀ a, MeasurableSet {ω | X ω = a}) (f : Ω → ℝ) (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∑ a, ∫ ω in {ω | X ω = a}, f ω ∂μ := by
  classical
  have heq : f = fun ω => ∑ a, Set.indicator {ω | X ω = a} f ω := by
    funext ω
    simp [Set.indicator, eq_comm]
  conv_lhs => rw [heq]
  rw [integral_finsetSum _ (fun a _ => hf.indicator (hm a))]
  apply sum_congr rfl
  intro a _
  exact integral_indicator (hm a)

/-- Expected realized charges equal expected conditional batch charges. The
conditional-cost identities are per slot and selected batch, permitting arbitrary
correlation with that batch's success and random unbounded integrable bills. -/
theorem expected_bills_eq_batch_costs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (I : FullCoverInstance ι ℝ) (n : ℕ)
    (selected : Fin n → Ω → Finset ι)
    (hm : ∀ t A, MeasurableSet {ω | selected t ω = A})
    (bill : Fin n → Ω → ℝ) (hint : ∀ t, Integrable (bill t) μ)
    (hcost : ∀ t A, ∫ ω in {ω | selected t ω = A}, bill t ω ∂μ =
      μ.real {ω | selected t ω = A} * I.batchCost A) :
    ∫ ω, ∑ t, bill t ω ∂μ =
      ∑ t, ∑ A, μ.real {ω | selected t ω = A} * I.batchCost A := by
  rw [integral_finsetSum _ (fun t _ => hint t)]
  apply sum_congr rfl
  intro t _
  rw [finite_partition_integral μ (selected t) (hm t) (bill t) (hint t)]
  exact sum_congr rfl fun A _ => hcost t A

private theorem finite_observable_integral {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X) (f : α → ℝ) :
    ∫ ω, f (X ω) ∂μ = ∑ a, μ.real {ω | X ω = a} * f a := by
  rw [← integral_map hX.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  apply sum_congr rfl
  intro a _
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hX (measurableSet_singleton a)]
  rfl

/-- The original random billing model has exactly the LP cost. The ambient law
realizes the stopped execution's finite trace law; only per-slot, per-selected-batch
conditional means are prescribed for the actual bills. -/
theorem billed_cost_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : FullCoverInstance ι ℝ)
    {n : ℕ} (π : Policy ι ℝ n)
    [MeasurableSpace (Bool × Plan ι n)] [MeasurableSingletonClass (Bool × Plan ι n)]
    (trace : Ω → Bool × Plan ι n) (htrace : Measurable trace)
    (hlaw : ∀ e, μ.real {ω | trace ω = e} = (π.execution I).weight e)
    (bill : Fin n → Ω → ℝ) (hint : ∀ t, Integrable (bill t) μ)
    (hcost : ∀ t A, ∫ ω in {ω | (trace ω).2.batchAt t = A}, bill t ω ∂μ =
      μ.real {ω | (trace ω).2.batchAt t = A} * I.batchCost A) :
    ∫ ω, ∑ t, bill t ω ∂μ = π.scheduleLaw.mean (Plan.expectedCost I) := by
  classical
  let : MeasurableSpace (Finset ι) := ⊤
  have hs : ∀ t, Measurable (fun ω => (trace ω).2.batchAt t) := fun t =>
    (measurable_of_finite (fun e : Bool × Plan ι n => e.2.batchAt t)).comp htrace
  have hmeas : ∀ t A, MeasurableSet {ω | (trace ω).2.batchAt t = A} :=
    fun t A => (hs t) (measurableSet_singleton A)
  rw [expected_bills_eq_batch_costs μ I n (fun t ω => (trace ω).2.batchAt t)
    hmeas bill hint hcost]
  have hsum : (∑ t, ∑ A, μ.real {ω | (trace ω).2.batchAt t = A} * I.batchCost A) =
      ∫ ω, (trace ω).2.traceCost I ∂μ := by
    simp_rw [Plan.traceCost_eq_sum]
    rw [integral_finsetSum _ (fun t _ => ?_)]
    · apply sum_congr rfl
      intro t _
      exact (finite_observable_integral μ _ (hs t) (I.batchCost)).symm
    · exact ((Integrable.of_finite (f := I.batchCost)).comp_measurable (hs t))
  rw [hsum]
  change (∫ ω, executionCost I (trace ω) ∂μ) = _
  rw [finite_observable_integral μ trace htrace (executionCost I)]
  simp only [hlaw]
  exact (execution_equivalence I π).2

end Cslib.Probability.StochasticOracle
