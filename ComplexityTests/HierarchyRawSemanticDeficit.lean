/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of genuine RAW semantic omissions)
import Complexity.Foundations.Probability.HierarchyRawSemanticDeficit
import all ComplexityTests.HierarchyProductAllocation
import all ComplexityTests.HierarchyJointSignedMean

/-!
A growing field/horizon family has positive parent precision and a retained positive
bin with final budget zero and nonzero genuine canonical mean. The charge and budget
are fixed before the field or horizon. Thus parent activity cannot justify dropping
the canonical omission or replacing the existing all-final-budgets-positive guard.
No successful joint recursive history or child accuracy is constructed here.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
namespace RawSemanticDeficitRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private def budget (A : ℕ) : ℕ :=
  32 * (A * (HierarchyTask.residual (k := HP.k) 0).rank + 1)

private def data (P A h n : ℕ) : BudgetData HP P :=
  {ProductAllocationRegression.data HP P A h with
    base := rate n • (1 : Matrix (ZMod P) (ZMod P) ℝ)}

private lemma base_nonneg (P A h n : ℕ) (x y : ZMod P) :
    0 ≤ (data HP P A h n).base x y := by
  change 0 ≤ rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y
  exact mul_nonneg (rate_pos n).le (by by_cases hh : x = y <;> simp [Matrix.one_apply, hh])

private lemma base_mass (P : ℕ) [Fact P.Prime] (A h n : ℕ) :
    (data HP P A h n).base *ᵥ 1 ≤ 1 := by
  intro x
  simp only [data, smul_mulVec, one_mulVec, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
  exact (rate_antitone (Nat.zero_le n)).trans_eq (by norm_num [rate])

private lemma fine_numerator (P A h n : ℕ) :
    (data HP P A h (n + 1)).cutoff (n + 1) 1 = 1 := by
  change boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 1 (n + 1)
    (fun _ => 1) 1 = 1
  have hh : rate (n + 1) / rate n = (1 / 16 : ℝ) := by
    rw [BudgetData.rate_succ_sixteen n]
    field_simp [(rate_pos (n + 1)).ne']
  simp only [boundedRoutedBinCutoff, Nat.succ_ne_zero, ↓reduceIte,
    show ¬(1 : ℝ) < 0 by norm_num, routedBinCutoff, mul_one, binWeight,
    div_self (rate_pos (n + 1)).ne', hh]
  rw [polynomialSwitch4_of_ge (by norm_num) le_rfl,
    polynomialSwitch4_of_le (by norm_num) (by norm_num)]
  norm_num

-- All positive bins through the full horizon are retained, including the exhausted
-- nonzero fine ray. There is no hypothesis asserting canonical agreement at budget zero.
example (A : ℕ) (hA : 1 ≤ A) :
    ∀ depth : ℕ, ∃ (P : ℕ) (hP : P.Prime), let : Fact P.Prime := ⟨hP⟩
      ∃ (H : Horizon P) (D : BudgetData HP P)
        (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (n : ℕ),
        depth ≤ H.maxExponent ∧ n ≤ H.maxExponent ∧
        D.rankCharge = A ∧ D.bins = range (H.maxExponent + 1) ∧
        0 < D.requestPrecision (budget HP A) r ∧
        D.binBudget (budget HP A) n r = 0 ∧
        0 < LogSpaceEstimation.lastBudget (budget HP A) 1 D.slack (D.sampleScale r none) ∧
        ∀ x : ZMod P, 0 < rowSliceMean
          (fun σ x => r.source.retains (channels D.padding) σ x)
          (fun σ y => r.terminal.retains (channels D.padding) σ y)
          (D.residualCanonicalRay r (some n)) x x := by
  intro depth
  let M := budget HP A
  let n := M + 1
  obtain ⟨P, hP, _, _, H, hH, _⟩ :=
    exists_bounded_depth_prime (max depth n + 1) 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  let D := data HP P A H.maxExponent n
  let r := ProductAllocationRegression.request HP P
  have hn : n ≤ H.maxExponent := by rw [hH]; omega
  have hp : 0 < D.requestPrecision M r := by
    rw [D.requestPrecision_grid M 0 0 r rfl rfl]
    dsimp only [D, data, ProductAllocationRegression.data, r,
      ProductAllocationRegression.request]
    norm_num only [Nat.cast_zero, add_zero, mul_zero, sub_zero, Nat.cast_one, mul_one]
    dsimp only [M, budget]
    push_cast
    ring_nf
    positivity
  have hz : D.binBudget M n r = 0 := by
    change LogSpaceEstimation.lastBudget M 1 D.slack (D.sampleScale r (some n)) = 0
    rw [D.sampleScale_grid r 0 n rfl rfl]
    change LogSpaceEstimation.lastBudget M 1 1 (4 * ((0 : ℤ) - n)) = 0
    rw [zero_sub]
    simp only [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_neg, Int.natAbs_mul, Int.natAbs_natCast, Nat.one_mul]
    norm_num only
    dsimp only [n]
    omega
  have hCf (x y : ZMod P) : D.base x y ≤ rate 0 := by
    change rate n * (1 : Matrix (ZMod P) (ZMod P) ℝ) x y ≤ rate 0
    by_cases he : x = y
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_one]
      exact rate_antitone (Nat.zero_le n)
    · simp only [Matrix.one_apply, he, ↓reduceIte, mul_zero]
      exact (rate_pos 0).le
  have hrank : 1 ≤ r.task.rank := by
    simp only [r, ProductAllocationRegression.request, HierarchyTask.rank]
    omega
  have hcharge : (1 : ℝ) ≤ D.rankCharge := by
    change (1 : ℝ) ≤ A
    exact_mod_cast hA
  refine ⟨P, hP, H, D, r, n, ?_, hn, rfl, rfl, hp, hz,
    D.raw_negative_budget_pos_of_precision hcharge M 0 0 r
      hrank rfl rfl hp, ?_⟩
  · rw [hH]; omega
  · intro x
    rw [D.residualCanonicalRay_positive_mean rfl rfl rfl
      (by norm_num [D, data, ProductAllocationRegression.data]) H r 0 2 (by decide)
      0 0 [1] [2, 3] rfl rfl (by omega) (by omega)
      (base_nonneg HP P A H.maxExponent n) (base_mass HP P A H.maxExponent n)
      hCf n hn x x]
    have hnume : D.cutoff n (D.base x x / D.binRate n) = 1 := by
      change (data HP P A H.maxExponent (M + 1)).cutoff (M + 1)
        ((rate (M + 1) * (1 : Matrix (ZMod P) (ZMod P) ℝ) x x) / rate (M + 1)) = 1
      simp only [Matrix.one_apply_eq, mul_one, div_self (rate_pos (M + 1)).ne']
      exact fine_numerator HP P A H.maxExponent M
    rw [hnume, mul_one]
    apply add_pos_of_pos_of_nonneg (rate_pos n)
    apply sum_nonneg
    intro z _
    apply mul_nonneg
    · exact (HP.toHierarchyParams.isCorrectionSeq_correctionIter
        (rate_pos 0) (base_nonneg HP P A H.maxExponent n)).nonneg HP.k x z
    · exact mul_nonneg (rate_pos n).le (D.cutoff_bounds n _).1

section Nonunit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open JointSignedRegression

-- The non-unit fixture has a positive true correction and product. Even completely
-- exhausted positive mass is paid together against genuine C+EC-E, including zero entries.
example (A : ℕ) (x y : ZMod 5) :
    (B HP A).residualOmittedPositive 0 0 1 (r HP) x y ≤
      max 1 (((HP.k : ℝ) + 1) / HP.θ) *
        HP.toHierarchyParams.residual (canonicalChannel id (rate 1))
          (canonicalChannel id (rate 1)) (rate 1) (B HP A).base x y := by
  exact (B HP A).residualOmittedPositive_le_residual 2 rfl rfl rfl 0 (r HP) 1
    (TerminalMeanRegression.small_nonneg HP) (TerminalMeanRegression.small_mass HP)
    (TerminalMeanRegression.small_stage HP) 0 x y

-- Both genuine dense tables vanish at the strictly coarse bin, not just their
-- deterministic mean. This places no support requirement on an approximate table.
example (A : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
      (r HP).source (BudgetData.midpoint (r HP)) (r HP).terminal ((B HP A).binRate 0)
    (B HP A).residualCanonicalChild 0 Q.direct σ x y = 0 ∧
      (B HP A).residualCanonicalChild 0 Q.right σ x y = 0 := by
  exact ⟨(B HP A).residualCanonicalDirect_zero_of_lt rfl rfl 0 1 (r HP)
    (TerminalMeanRegression.small_stage HP) (by decide) σ x y,
    (B HP A).residualCanonicalRight_zero_of_lt rfl rfl 0 1 (r HP)
    (TerminalMeanRegression.small_stage HP) (by decide) σ x y⟩
end Nonunit

end RawSemanticDeficitRegression
