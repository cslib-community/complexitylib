/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of the budget evaluator's two-payment estimates)
import Complexity.Foundations.Probability.HierarchyInitialPerturbation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility

/-! Clipping follows the joint mean; ordinary progress keeps its own charge. These finite
fixtures test local estimates, not successful recursive availability or uniform absorption. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib
open scoped BigOperators

-- The approximate value is positive while the dominated canonical target is zero.
example : min 1 (|(0 : ℝ) - (1 / 2) ^ 4| / (1 + 0)) ≤
    32 * 1 * |(0 : ℝ) ^ (4⁻¹ : ℝ) - ((1 / 2) ^ 4) ^ (4⁻¹ : ℝ)| :=
  min_relative_sub_le_root_four (by norm_num) (by positivity) (by norm_num)
    (by norm_num) (by norm_num)

-- The approximate value has no canonical domination requirement, even when it is large.
example : min 1 (|(0 : ℝ) - 65536| / (1 + 0)) ≤
    32 * 1 * |(0 : ℝ) ^ (4⁻¹ : ℝ) - 65536 ^ (4⁻¹ : ℝ)| :=
  min_relative_sub_le_root_four (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

private def child (σ : Fin 2) : ℝ := if σ = 0 then 1 / 16 else 0

private lemma child_root_four (σ : Fin 2) :
    |child σ ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4 = child σ := by
  have h : 0 ≤ child σ := by unfold child; positivity
  rw [Real.zero_rpow (by norm_num : (4⁻¹ : ℝ) ≠ 0), sub_zero,
    abs_of_nonneg (Real.rpow_nonneg h _)]
  simpa only [Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) h (by decide)

-- Both draws use the same child and conditioning slice. With physical scale 32 the
-- centered noise is ±1, while the own-slice rooted fourth moment is only 1/32.
example :
    (𝔼 σ : Fin 2, |child σ ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4) = 1 / 32 ∧
    (𝔼 σ : Fin 2, min 1 |32 * child σ - 1| ^ 4) = 1 := by
  constructor
  · simp_rw [child_root_four]
    norm_num [expect_eq_sum_div_card, Fin.sum_univ_two, child]
  · norm_num [expect_eq_sum_div_card, Fin.sum_univ_two, child]

-- The clipped mean payment retains the physical scale; clipping each atom first
-- would give 1/2, whereas clipping after the actual mean gives 1.
example :
    min 1 (|32 * (𝔼 σ : Fin 2, (child σ - 0))| / (1 + 0)) ^ 4 ≤
      (512 * (3 * (1 : ℝ) + 3) ^ 3) * 32 *
        𝔼 σ : Fin 2, |child σ ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4 := by
  exact min_relative_expect_sub_four_le univ (by norm_num) (by norm_num) (by norm_num)
    (fun _ _ => le_rfl) (fun σ _ => by unfold child; positivity) (by simp)

example : min 1 (|32 * (𝔼 σ : Fin 2, child σ)| / (1 + 0)) = (1 : ℝ) ∧
    (𝔼 σ : Fin 2, min 1 |32 * child σ|) = 1 / 2 := by
  norm_num [expect_eq_sum_div_card, Fin.sum_univ_two, child]

-- Empty conditional slices use the actual zero-mean convention.
example : min 1 (|(7 : ℝ) * (𝔼 σ ∈ (∅ : Finset (Fin 2)), (child σ - 0))| /
    (1 + 0)) ^ 4 ≤ (512 * (3 * (1 : ℝ) + 3) ^ 3) * 7 *
      𝔼 σ ∈ (∅ : Finset (Fin 2)),
        |child σ ^ (4⁻¹ : ℝ) - (0 : ℝ) ^ (4⁻¹ : ℝ)| ^ 4 := by
  exact min_relative_expect_sub_four_le ∅ (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp) (by simp)

open Matrix Matrix.HierarchyParams Matrix.HierarchyParams.H4RankEnvironment
attribute [local implicit_reducible] Matrix

-- Fix the structural charge first, then vary source, terminal and bin exponents together.
-- The actual scheduled call covers fine, coarse and equal bins without identifying rates
-- with rounded masses. This does not assert that these finite costs fit a parent reserve.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hrate : B.binRate = rate) (M d ks ka bin : ℕ) (hM : 0 < M) :
    let B' := { B with rankCharge := 7 }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    let cost := max d (LogSpaceEstimation.scaleCutoff B'.slack (B'.sampleScale r (some bin)))
    let m := LogSpaceEstimation.lastBudget M d B'.slack (B'.sampleScale r (some bin))
    let w := (cost : ℝ) + |(bin : ℝ) - ka| + 1
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
    m < M ∧
    (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|) * (2 : ℝ) ^ (-B'.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B'.requestPrecision M r) * (2 : ℝ) ^ (-7 : ℝ) *
        (2 : ℝ) ^ (8 * w) * (2 : ℝ) ^ (-|(bin : ℝ) - ka| / 2) := by
  dsimp only
  exact BudgetData.requestPrecision_initial_scheduled_raw_pay
    { B with rankCharge := 7 } (by norm_num) hrate
    M d ks ka bin hM _ rfl rfl rfl

-- Fine/coarse signed errors are combined only after the positive comparisons. Exact
-- equal-budget cancellation has zero clipped loss, even when each summand is large.
example : min 1 (|∑ i ∈ (univ : Finset (Fin 2)),
    (if i = 0 then (17 : ℝ) else -17)| / 1) = 0 := by
  norm_num [Fin.sum_univ_two]

example (a : ℝ) (ha : 0 < a) (fine coarse : ℝ) :
    min 1 (|fine - coarse| / a) ≤ min 1 (|fine| / a) + min 1 (|coarse| / a) := by
  simpa only [sub_eq_add_neg, abs_neg] using min_abs_add_div_le ha fine (-coarse)

-- This signed-sum consumer retains correlated terms on their common denominator.
example (a : ℝ) (ha : 0 < a) (e : Fin 3 → ℝ) :
    min 1 (|∑ i, e i| / a) ≤ ∑ i, min 1 (|e i| / a) :=
  min_abs_sum_div_le univ ha e

-- Perfectly correlated source/terminal/usage masks integrate the rooted error without
-- an inverse atom-density penalty. The approximate child is one at zero target.
example :
    rowNormPow 4 1 1 (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
      (fun _ _ _ => (1 : ℝ)) ≤
    1 * rootDistPow 4 1 1 (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
      (fun σ _ _ => if σ = 0 then (1 : ℝ) else 0) (fun _ _ _ => 0) := by
  apply rowNormPow_le_rootDistPow_of_conditional (by norm_num)
    (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0) (fun σ _ => σ = 0)
    (fun σ _ _ => if σ = 0 then (1 : ℝ) else 0) (fun _ _ _ => 0)
    (fun _ _ => 1) 1 (by norm_num)
  · intro σ _ _ hσ
    simp only [hσ, ↓reduceIte]
  · intro _ _
    have hs : ({σ : Fin 2 | σ = 0} : Finset _) = {0} := by ext σ; simp
    norm_num [hs]

example :
    rowNormPow 4 1 1 (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
      (fun _ _ _ => (1 : ℝ)) = 1 / 2 := by
  norm_num [rowNormPow, expect_eq_sum_div_card, Fin.sum_univ_two]

-- Rounded mass is retained in fine bins; coarse and equal bins cancel the same mass.
example :
    rate 0 * (gridMass 5 1 / gridMass 5 (max 1 0)) / rate 1 = 16 ∧
    rate 1 * (gridMass 5 0 / gridMass 5 (max 0 1)) / rate 0 = 625 / 1296 ∧
    rate 1 * (gridMass 5 1 / gridMass 5 (max 1 1)) / rate 1 = 1 ∧
    gridMass 5 1 ≠ rate 1 := by
  norm_num [rate, gridMass, show side 5 0 = 5 from rfl,
    show side 5 1 = 3 from rfl]

-- The signed-prefix estimate applies with identical correlated masks, including exact
-- cancellation although both individual clipped payments are positive.
example :
    rowNormPow 4 1 1 (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
      (fun _ _ _ => min 1 (|∑ i : Fin 2, if i = 0 then (17 : ℝ) else -17| / 1)) ≤
      (2 : ℝ) ^ 3 * ∑ i : Fin 2,
        rowNormPow 4 1 1 (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
          (fun _ _ _ => min 1 (|if i = 0 then (17 : ℝ) else -17| / 1)) := by
  simpa only [card_univ, Fintype.card_fin, Nat.cast_ofNat] using
    rowNormPow_clipped_sum_le (univ : Finset (Fin 2)) (by norm_num : (0 : ℝ) ≤ 1 * 1)
      (fun (σ : Fin 2) (_ : Unit) => σ = 0) (fun σ _ => σ = 0)
      (fun i _ _ => if i = 0 then (17 : ℝ) else -17) (fun _ _ => 1) (by norm_num)

-- The same fixed structural charge works for exhausted groups at every terminal exponent.
-- This exact-zero test asserts no positive-budget uniform reserve absorption.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (M d ka : ℕ) (hd : M ≤ d)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    let B' := {B with rankCharge := 7}
    B'.initialClippedRootGroupCharge M d r ka 3 = 0 :=
  BudgetData.initialClippedRootGroupCharge_eq_zero_of_le _ M d r ka 3 hd

-- A supported, nonconstant error is averaged on the broad slice before the fourth
-- power. Its exact fourth moment is 1/16, against own-usage moment 1/2: density^3.
example :
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun _ => rowSliceMean (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
        (fun σ _ _ => if σ = 0 then (1 : ℝ) else 0)) = 1 / 16 ∧
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun σ _ => σ = 0)
      (fun σ _ _ => if σ = 0 then (1 : ℝ) else 0) = 1 / 2 := by
  norm_num [rowNormPow, rowSliceMean, expect_eq_sum_div_card, Fin.sum_univ_two]

-- The new sharp coefficient keeps the actual rounded masses. P=5 has mass(1)=81/625,
-- so the fine coefficient is neither its old linear value nor an exact nominal identity.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} [Fact (Nat.Prime 5)]
    (B : BudgetData HP 5) (hcap : B.binCap = 16) :
    B.initialClippedRootCoefficient 1 0 = 512 * (99 : ℝ) ^ 3 * 16 ∧
    B.initialClippedRootCoefficient 0 1 = 80000 / 81 ∧
    B.initialClippedRootCoefficient 1 1 = 512 * (99 : ℝ) ^ 3 ∧
    B.initialClippedRootCoefficient 0 1 <
      512 * (99 : ℝ) ^ 3 * (625 / 1296) := by
  norm_num [BudgetData.initialClippedRootCoefficient, hcap, rate, gridMass,
    show side 5 0 = 5 from rfl, show side 5 1 = 3 from rfl]

-- Fix charge 7 BEFORE arbitrary exponents and budgets. Both nonzero endpoint slacks
-- use their own actual scheduled request precision; the final window is retained.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hrate : B.binRate = rate) (M d ks ka bin : ℕ) :
    let B' := {B with rankCharge := 7}
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    ∀ δ ∈ ({d, 2 * d} : Finset ℕ),
    let m := LogSpaceEstimation.lastBudget M δ B'.slack (B'.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
    (2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) *
        (2 : ℝ) ^ (-B'.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B'.requestPrecision M r) * (2 : ℝ) ^ (-7 : ℝ) *
        (2 : ℝ) ^ ((δ : ℝ) / (16 * B'.slack) + 1 / 16 -
          3 * |(bin : ℝ) - ka| / 4) := by
  dsimp only
  intro δ _
  exact BudgetData.requestPrecision_initial_clipped_adjust {B with rankCharge := 7}
    (by norm_num) hrate M δ ks ka bin _ rfl rfl rfl

-- The actual coefficient-times-own-precision endpoint payment, with a single fixed
-- structural charge and no parent accuracy hypothesis. Zero endpoints remain allowed.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hrate : B.binRate = rate) (H : Horizon P)
    (M d ks ka bin : ℕ) (ha : ka ≤ H.maxExponent) (hi : bin ≤ H.maxExponent) :
    let B' := {B with rankCharge := 7}
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    let m := LogSpaceEstimation.lastBudget M d B'.slack (B'.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
    B'.initialClippedRootCoefficient ka bin * B'.initialEndpointCharge m Q.direct 3 ≤
      max (512 * (6 * B'.binCap + 3) ^ 3) (32768 * B'.binCap ^ 3) * (3 : ℝ) ^ 4 *
        ((2 : ℝ) ^ (-B'.requestPrecision M r) * (2 : ℝ) ^ (-7 : ℝ) *
          (2 : ℝ) ^ ((d : ℝ) / (16 * B'.slack) + 1 / 16 -
            3 * |(bin : ℝ) - ka| / 4)) ^ 4 := by
  dsimp only
  exact BudgetData.initialClippedRootEndpoint_le {B with rankCharge := 7}
    (by norm_num) hrate H M d ks ka bin ha hi _ rfl rfl rfl 3
