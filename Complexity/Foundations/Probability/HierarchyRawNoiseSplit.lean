/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyRawNoise

/-!
# Semantic and transported parts of residual RAW noise

The reference at a positive endpoint is the genuine signed canonical ray; at zero
it is the literal zero approximation. The transported part retains BOTH endpoint
errors on the same environment, including the once-negative correction.
Only the semantic part cancels when both endpoint budgets are positive.

These original identities do not pay the transported input moment from own-request
IH. In particular neither accurate conditional means nor endpoint availability
supply that moment. The production walk, masks and denominator are unchanged.

## Main results

* `decodedGroupInput_residual_split`: literal two-endpoint error decomposition.
* `residualSemanticGroupInput_eq_zero_of_two_mul_lt`: semantic cancellation only.
* `decodedGroupInput_eq_zero_of_le`: unconditional exhausted input.
* `rawRelativeNoiseBudget_residual_split_le`: correlated, denominator-preserving payment split.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Budget-independent canonical sampling at positive endpoints, with the genuine
zero boundary. The ray list includes the negative correction exactly once. -/
@[expose] def residualSemanticGroupInput (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ((B.rays .residual).map fun bin =>
    (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0
      then 0 else B.residualCanonicalRay r bin σ x y) -
    (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
      then 0 else B.residualCanonicalRay r bin σ x y)).sum

/-- The actual transported fine error minus the actual transported coarse error.
No canonical support or equality between different positive endpoint calls is assumed. -/
@[expose] def residualTransportedGroupInput
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ((B.rays .residual).map fun bin =>
    (((B.sample history (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))
        .residual r bin).getD 0 σ x y) -
      (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0
        then 0 else B.residualCanonicalRay r bin σ x y)) -
    (((B.sample history (LogSpaceEstimation.lastBudget M (2 * d) B.slack
        (B.sampleScale r bin)) .residual r bin).getD 0 σ x y) -
      (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
        then 0 else B.residualCanonicalRay r bin σ x y))).sum

/-- The signed reference and the two transported endpoint perturbations reconstruct
exactly the executed input. This identity does not require successful calls. -/
theorem decodedGroupInput_residual_split
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.decodedGroupInput history M d .residual r =
      B.residualSemanticGroupInput M d r + B.residualTransportedGroupInput history M d r := by
  funext σ x y
  simp only [decodedGroupInput, residualSemanticGroupInput, residualTransportedGroupInput,
    Pi.add_apply, Matrix.add_apply, ← List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro bin _
  ring

/-- Semantic cancellation concerns zero versus positive status, not equality of
actual samples at different positive budgets. Fine bins exhausted at both ends cancel too. -/
theorem residualSemanticGroupInput_eq_zero_of_two_mul_lt (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : 2 * d < M) :
    B.residualSemanticGroupInput M d r = 0 := by
  funext σ x y
  unfold residualSemanticGroupInput
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨bin, _, rfl⟩ := List.mem_map.mp ha
  have hz : (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0) ↔
      (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  simp only [hz, sub_self]

/-- Before the semantic boundary, the ACTUAL input is precisely its transported
perturbation. It need not vanish, even if both endpoint calls succeed. -/
theorem decodedGroupInput_eq_transported_of_two_mul_lt
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : 2 * d < M) :
    B.decodedGroupInput history M d .residual r =
      B.residualTransportedGroupInput history M d r := by
  rw [B.decodedGroupInput_residual_split,
    B.residualSemanticGroupInput_eq_zero_of_two_mul_lt M d r hd, zero_add]

/-- Beyond the parent boundary all actual endpoints are zero, without a positive
history call or any accuracy assertion at budget zero. -/
theorem decodedGroupInput_eq_zero_of_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hd : M ≤ d) :
    B.decodedGroupInput history M d .residual r = 0 := by
  have hf (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hc (bin : Option ℕ) :
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0 := by
    unfold LogSpaceEstimation.lastBudget
    omega
  funext σ x y
  simp [decodedGroupInput, hf, hc, B.sample_zero]

/-- The actual conditional budget separates semantic sampling from transported
endpoint perturbations, with the fixed factor eight for arbitrary correlation.
All pair densities, denominators and actual spectral factors remain inside both
budgets. Paying the transported term from own-request IH is still required. -/
theorem rawRelativeNoiseBudget_residual_split_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (j : ℕ) :
    B.rawRelativeNoiseBudget M r s t hst ks ku ss su
      (fun i => B.decodedGroupInput history M (dyadicSlack (Nat.log2 M + 1) i)
        .residual r) G j ≤
      8 * (B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i => B.residualSemanticGroupInput M (dyadicSlack (Nat.log2 M + 1) i) r) G j +
      B.rawRelativeNoiseBudget M r s t hst ks ku ss su
        (fun i => B.residualTransportedGroupInput history M
          (dyadicSlack (Nat.log2 M + 1) i) r) G j) := by
  let Xs := retainedMask s (side P ks) B.padding ss
  let Yu := retainedMask t (side P ku) B.padding su
  let graphs := graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
  let S := fun i => B.residualSemanticGroupInput M (dyadicSlack (Nat.log2 M + 1) i) r
  let E := fun i => B.residualTransportedGroupInput history M
    (dyadicSlack (Nat.log2 M + 1) i) r
  let q := fun (A : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) i x y =>
    (({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)).dens : ℝ) *
      (2 * (graphs x y).spectralExpansion ^
        (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i)) *
        𝔼 σ ∈ ({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)),
          |(A i σ x y - rowSliceMean Xs Yu (A i) x y) / (rate ku + G x y)| ^ 4)
  have hq (i : ℕ) (x y : ZMod P) :
      q (fun i => S i + E i) i x y ≤ 8 * (q S i x y + q E i x y) := by
    have hp (σ : Environment P 3) :
        |((S i + E i) σ x y - rowSliceMean Xs Yu (S i + E i) x y) /
            (rate ku + G x y)| ^ 4 ≤
          8 * (|(S i σ x y - rowSliceMean Xs Yu (S i) x y) /
            (rate ku + G x y)| ^ 4 +
          |(E i σ x y - rowSliceMean Xs Yu (E i) x y) /
            (rate ku + G x y)| ^ 4) := by
      simp only [rowSliceMean, Pi.add_apply, Matrix.add_apply, expect_add_distrib]
      rw [show (S i σ x y + E i σ x y -
          ((𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, S i τ x y) +
            𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, E i τ x y)) / (rate ku + G x y) =
          (S i σ x y - 𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, S i τ x y) /
            (rate ku + G x y) +
          (E i σ x y - 𝔼 τ ∈ {τ | Xs τ x ∧ Yu τ y}, E i τ x y) /
            (rate ku + G x y) by ring]
      have ht := add_pow_le
        (abs_nonneg ((S i σ x y - rowSliceMean Xs Yu (S i) x y) / (rate ku + G x y)))
        (abs_nonneg ((E i σ x y - rowSliceMean Xs Yu (E i) x y) / (rate ku + G x y))) 4
      norm_num only [Nat.reduceSub, Nat.reducePow] at ht
      exact (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) 4).trans ht
    have he := expect_le_expect (s := {σ | Xs σ x ∧ Yu σ y}) (fun σ _ => hp σ)
    simp only [expect_add_distrib, ← mul_expect] at he
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤
        (({σ | Xs σ x ∧ Yu σ y} : Finset (Environment P 3)).dens : ℝ) *
          (2 * (graphs x y).spectralExpansion ^
            (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) i))) by
      exact mul_nonneg (by positivity) (mul_nonneg (by norm_num)
        (pow_nonneg (RotationMap.spectralExpansion_nonneg _) _)))
    dsimp only [q]
    nlinarith only [hh]
  have hNu : 0 ≤ ((P : ℝ) * r.source.rate)⁻¹ := by
    rw [hs]
    exact inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg _) (rate_pos ks).le)
  simp_rw [B.decodedGroupInput_residual_split]
  change (j : ℝ) ^ 3 * ∑ i ∈ range j,
    ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y, q (fun i => S i + E i) i x y ≤ _
  calc
    _ ≤ (j : ℝ) ^ 3 * ∑ i ∈ range j,
        ((P : ℝ) * r.source.rate)⁻¹ * ∑ x, ∑ y, 8 * (q S i x y + q E i x y) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ hNu
      apply sum_le_sum; intro x _
      apply sum_le_sum; intro y _
      exact hq i x y
    _ = _ := by
      simp only [mul_add, sum_add_distrib, ← mul_sum, rawRelativeNoiseBudget]
      dsimp only [q, S, E, Xs, Yu, graphs]
      ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
