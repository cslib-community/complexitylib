/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of the budget evaluator's two-payment estimates)
import Complexity.Foundations.Probability.HierarchyInitialPerturbation
import Complexity.Foundations.Probability.HierarchyInitialFeasibility
import Complexity.Foundations.Probability.HierarchyTransportedPreparation

/-! Clipping follows the joint mean; ordinary progress keeps its own charge. These finite
fixtures test local estimates, not successful recursive availability or uniform absorption. -/
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Finset Cslib Cslib.Probability
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable

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

-- Arbitrarily many zero budgets do not multiply a single correlated nonzero error.
-- The old cardinality cube would cost 125 on these five terms; Minkowski costs 1.
example :
    rowNormPow 4 1 1 (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ _ => min 1 (|∑ i : Fin 5, if i = 0 then (1 : ℝ) else 0| / 1)) ≤ 1 := by
  have h := rowNormPow_clipped_sum_le_pow_sum (univ : Finset (Fin 5))
    (by norm_num : (0 : ℝ) ≤ 1 * 1)
    (fun (_ : Fin 2) (_ : Unit) => True) (fun _ _ => True)
    (fun i _ _ => if i = 0 then (1 : ℝ) else 0) (fun _ _ => 1) (by norm_num)
    (fun i => if i = 0 then (1 : ℝ) else 0) (by
      intro i _
      by_cases hi : i = 0 <;>
        norm_num [hi, rowNormPow, expect_eq_sum_div_card, Fin.sum_univ_two])
  norm_num [Fin.sum_univ_succ] at h ⊢
  exact h

-- A single charge is fixed before source/terminal exponents and field width.
-- The budget is positive, but bounded: this is not a uniform-in-M theorem.
private lemma finite_window {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hbins : B.bins = range 3) (hcap : B.binCap = 16)
    (hslack : B.slack = 1) (ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    2 * (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      (∑ j ∈ range 3, B.initialClippedRootWindow 4
        (Cslib.RowCompression.dyadicSlack (Nat.log2 4 + 1) j) ka r) ≤ (2 : ℝ) ^ (64 : ℝ) := by
  have hc : (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) ≤ 1024 := by
    have hh := Real.rpow_le_rpow (by rw [hcap]; norm_num :
      0 ≤ max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3))
      (show max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) ≤
        (1024 : ℝ) ^ 4 by rw [hcap]; norm_num) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have he : ((1024 : ℝ) ^ 4) ^ (4⁻¹ : ℝ) = 1024 := by
      convert Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ) ≤ 1024)
        (by decide : (4 : ℕ) ≠ 0) using 1
    rwa [he] at hh
  have hw (d : ℕ) (hd : d ≤ 4) : B.initialClippedRootWindow 4 d ka r ≤ 24 := by
    have he (δ bin : ℕ) (hδ : δ ≤ 8) :
        (2 : ℝ) ^ ((δ : ℝ) / (16 * B.slack) + 1 / 16 -
          3 * |(bin : ℝ) - ka| / 4) ≤ 4 := by
      have hδ' : (δ : ℝ) ≤ 8 := by exact_mod_cast hδ
      have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (δ : ℝ) / (16 * B.slack) + 1 / 16 -
          3 * |(bin : ℝ) - ka| / 4 ≤ 2 by rw [hslack]; linarith [abs_nonneg ((bin : ℝ) - ka)])
      norm_num at hh
      exact hh
    unfold BudgetData.initialClippedRootWindow
    rw [hbins]
    calc
      _ ≤ ∑ _bin ∈ range 3, (8 : ℝ) := by
        apply sum_le_sum
        intro bin _
        have hf := he d bin (by omega)
        have hc := he (2 * d) bin (by omega)
        split_ifs <;> linarith
      _ = 24 := by norm_num
  have hs : (∑ j ∈ range 3, B.initialClippedRootWindow 4
      (Cslib.RowCompression.dyadicSlack (Nat.log2 4 + 1) j) ka r) ≤ 72 := by
    calc
      _ ≤ ∑ _j ∈ range 3, (24 : ℝ) := by
        apply sum_le_sum
        intro j hj
        apply hw
        have hj' := mem_range.mp hj
        interval_cases j <;> norm_num [Cslib.RowCompression.dyadicSlack]
      _ = 72 := by norm_num
  have hn : 0 ≤ (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) := by rw [hcap]; positivity
  calc
    _ ≤ 2 * 1024 * (72 : ℝ) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hs (by
        apply sum_nonneg
        intro j _
        unfold BudgetData.initialClippedRootWindow
        apply sum_nonneg
        intro bin _
        split_ifs <;> positivity) (by positivity)
    _ ≤ _ := by norm_num

example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hbins : B.bins = range 3) (hcap : B.binCap = 16)
    (hslack : B.slack = 1) (hrate : B.binRate = rate) (H : Horizon P)
    (hH : 2 ≤ H.maxExponent) (ks ka : ℕ) (ha : ka ≤ 2) :
    let B' := {B with rankCharge := 64}
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    (∑ j ∈ range 3, (B'.initialClippedRootGroupCharge 4
      (Cslib.RowCompression.dyadicSlack (Nat.log2 4 + 1) j) r ka 3) ^ (4⁻¹ : ℝ)) ^ 4 ≤
      (3 : ℝ) ^ 4 * ((2 : ℝ) ^ (-B'.requestPrecision 4 r)) ^ 4 := by
  dsimp only
  exact BudgetData.initialClippedRootPrefix_paid { B with rankCharge := 64 }
    (by norm_num) hrate H 4 3 ks ka (ha.trans hH)
    (fun bin hb => by rw [hbins] at hb; have hh := mem_range.mp hb; omega)
    _ rfl rfl rfl (finite_window { B with rankCharge := 64 } hbins hcap hslack ka _) 3

-- The same finite allocation reaches the existing first-mean minimum, which the
-- actualFourMax and hb/hraw reserve proofs consume. The other statistics stay unpaid.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hbins : B.bins = range 3) (hcap : B.binCap = 16)
    (hslack : B.slack = 1) (hrate : B.binRate = rate) (H : Horizon P)
    (hH : 2 ≤ H.maxExponent) (ks ka : ℕ) (ha : ka ≤ 2)
    (R : RoleProfile 3) (ζ Lh Lρ : ℝ) :
    let B' : BudgetData HP P := { B with rankCharge := 64 }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    B'.initialComputedPrecisionMoment 4 2 r R ks ka [] [] 3 ζ Lh Lρ 2 false 0 ≤
      8 * ((3 : ℝ) ^ 4 * ((2 : ℝ) ^ (-B'.requestPrecision 4 r)) ^ 4 +
        rowNormPow 4 P r.source.rate
          (NormalizedMoments.retainedMask R.source (side P ks) B'.padding [])
          (NormalizedMoments.retainedMask R.terminal (side P ka) B'.padding [])
          (fun _ x y => min 1 (|B'.initialPolynomialLoss 4 2 2 r x y| /
            (rate ka + B'.base x y)))) := by
  dsimp only
  exact BudgetData.initialComputedPrecisionMoment_first_paid { B with rankCharge := 64 }
    (by norm_num) hrate H 4 2 2 ks ka (ha.trans hH)
    (fun bin hb => by rw [hbins] at hb; have hh := mem_range.mp hb; omega)
    (⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
      gridChannel 2 ka [], gridChannel 2 ka []⟩) rfl rfl rfl R [] [] 3 ζ Lh Lρ
    (finite_window { B with rankCharge := 64 } hbins hcap hslack ka _)

-- At positive parent budget 4, every terminal exponent has a matching active bin
-- with two positive, unequal endpoint budgets. An offset bin instead hits the exact
-- zero/equal guard. This tests the literal allocator, not assumed child availability.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hslack : B.slack = 1) (hrate : B.binRate = rate)
    (ks ka : ℕ) :
    let B' : BudgetData HP P := { B with rankCharge := 64 }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    LogSpaceEstimation.lastBudget 4 1 B'.slack (B'.sampleScale r (some ka)) = 3 ∧
    LogSpaceEstimation.lastBudget 4 2 B'.slack (B'.sampleScale r (some ka)) = 2 ∧
    LogSpaceEstimation.lastBudget 4 1 B'.slack (B'.sampleScale r (some (ka + 1))) = 0 ∧
    LogSpaceEstimation.lastBudget 4 2 B'.slack (B'.sampleScale r (some (ka + 1))) = 0 := by
  dsimp only
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
      gridChannel 2 ka [], gridChannel 2 ka []⟩
  change LogSpaceEstimation.lastBudget 4 1 B.slack
      (({ B with rankCharge := 64 } : BudgetData HP P).sampleScale r (some ka)) = 3 ∧
    LogSpaceEstimation.lastBudget 4 2 B.slack
      (({ B with rankCharge := 64 } : BudgetData HP P).sampleScale r (some ka)) = 2 ∧
    LogSpaceEstimation.lastBudget 4 1 B.slack
      (({ B with rankCharge := 64 } : BudgetData HP P).sampleScale r (some (ka + 1))) = 0 ∧
    LogSpaceEstimation.lastBudget 4 2 B.slack
      (({ B with rankCharge := 64 } : BudgetData HP P).sampleScale r (some (ka + 1))) = 0
  rw [BudgetData.sampleScale_grid { B with rankCharge := 64 } r ka ka hrate rfl,
    BudgetData.sampleScale_grid { B with rankCharge := 64 } r ka (ka + 1) hrate rfl]
  norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, hslack]

-- The endpoint window is independent of the parent budget at the final slack. Charge 64
-- is fixed before M, both request exponents and the field width; there are three bins.
private lemma endpoint_window {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hbins : B.bins = range 3) (hcap : B.binCap = 16)
    (hslack : B.slack = 1) (M j ka : ℕ)
    (hd : Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j ≤ 16)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
      B.initialClippedEndpointWindow M j ka r ≤ (2 : ℝ) ^ (64 : ℝ) := by
  have hc : (max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
      (4⁻¹ : ℝ) ≤ 1024 := by
    have hh := Real.rpow_le_rpow (by rw [hcap]; norm_num :
      0 ≤ max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3))
      (show max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3) ≤
        (1024 : ℝ) ^ 4 by rw [hcap]; norm_num) (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    have he : ((1024 : ℝ) ^ 4) ^ (4⁻¹ : ℝ) = 1024 :=
      Real.pow_rpow_inv_natCast (by norm_num) (by decide : (4 : ℕ) ≠ 0)
    rwa [he] at hh
  have hw : B.initialClippedEndpointWindow M j ka r ≤ 12 := by
    unfold BudgetData.initialClippedEndpointWindow
    rw [hbins]
    calc
      _ ≤ ∑ _bin ∈ range 3, (4 : ℝ) := by
        apply sum_le_sum
        intro bin _
        split_ifs
        · norm_num
        · apply (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (show _ ≤ (2 : ℝ) by
              rw [hslack]
              have hd' : (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j : ℝ) ≤ 16 := by
                exact_mod_cast hd
              linarith [abs_nonneg ((bin : ℝ) - ka)])).trans_eq
          norm_num
      _ = 12 := by norm_num
  have hw0 : 0 ≤ B.initialClippedEndpointWindow M j ka r := by
    unfold BudgetData.initialClippedEndpointWindow
    exact sum_nonneg fun _ _ => by split_ifs <;> positivity
  exact (mul_le_mul hc hw hw0 (by norm_num)).trans (by norm_num)

-- Every positive parent precision, at any surviving slack at most 16. In particular
-- precisions 4, 8 and 16 and slacks 1, 2, 4 and 16 share the structural charge 64.
-- The structural charge is 64 before choosing the parent budget. This is an allocation
-- and actual-minimum client, conditional on the separate child IH, not a full reserve.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hbins : B.bins = range 3) (hcap : B.binCap = 16)
    (hslack : B.slack = 1) (hrate : B.binRate = rate) (H : Horizon P)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent) (ζ Lh Lρ : ℝ)
    (p j : ℕ) (hp0 : 0 < p) :
    let B' : BudgetData HP P := { B with rankCharge := 64 }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [],
        gridChannel 2 0 [], gridChannel 2 0 []⟩
    let M := 16 * (64 * r.task.rank + p)
    Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j ≤ 16 →
    0 < B'.requestPrecision M r ∧ B'.requestPrecision M r = p ∧
      B'.initialClippedEndpointPrefixCharge M j r 0 1 ≤ (2 : ℝ) ^ (-4 * (p : ℝ)) ∧
      B'.initialComputedPrecisionMoment M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
        0 0 [] [] 1 ζ Lh Lρ j false 0 ≤
        8 * ((2 : ℝ) ^ (-4 * (p : ℝ)) + rowNormPow 4 P r.source.rate
          (retainedMask (0 : Fin 3) (side P 0) B'.padding [])
          (retainedMask (2 : Fin 3) (side P 0) B'.padding [])
          (fun _ x y => min 1 (|B'.initialPolynomialLoss M 2 j r x y| /
            (rate 0 + B'.base x y)))) := by
  dsimp only
  intro hd
  let B' : BudgetData HP P := { B with rankCharge := 64 }
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [],
      gridChannel 2 0 [], gridChannel 2 0 []⟩
  let M := 16 * (64 * r.task.rank + p)
  have hp : B'.requestPrecision M r = p := by
    change (M : ℝ) / (16 * B.slack) +
      (Real.logb 2 (rate 0) + Real.logb 2 (rate 0)) / 2 - 64 * r.task.rank = p
    rw [hslack]
    norm_num [rate, M]
  have hw := endpoint_window B' hbins hcap hslack M j 0 hd r
  have he := B'.initialClippedEndpointPrefixCharge_paid (by norm_num) hrate H M
    j 0 0 (Nat.zero_le _) hi r rfl rfl rfl hw 1
  have hm := B'.initialComputedPrecisionMoment_first_endpoint_paid (by norm_num) hrate H
    M 2 j 0 0 (Nat.zero_le _) hi r rfl rfl rfl
    ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ hw
  have hpow : ((2 : ℝ) ^ (-(p : ℝ))) ^ 4 = (2 : ℝ) ^ (-4 * (p : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp only [hp, one_pow, one_mul, hpow] at he hm
  exact ⟨by rw [hp]; exact_mod_cast hp0, hp, he, hm⟩

-- Unavailable positive endpoints are not invented by the telescope. The zero boundary
-- remains available, and exhausted equal pairs make no lower call at all.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hslack : B.slack = 1)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : B.sampleScale r (some 0) = 0) :
    B.sample (fun _ _ => none) 0 (.pilotInput ⟨0, HP.k_pos⟩) r (some 0) = some 0 ∧
      B.pairedSample (fun _ _ => none) 4 4 (.pilotInput ⟨0, HP.k_pos⟩) r (some 0) = some 0 ∧
      B.pairedSample (fun _ _ => none) 4 2 (.pilotInput ⟨0, HP.k_pos⟩) r (some 0) = none := by
  simp [BudgetData.sample, BudgetData.pairedSample, hs, hslack,
    LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff,
    BudgetData.positiveSample, BudgetData.row]


-- An actual live scheduled endpoint invalidates the charge-64 uniform window inference.
-- The unconditional first-overflow tail multiplies this window by a weight >= 1.
-- This is an envelope counterexample, not a claim about the actual estimator error.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hslack : B.slack = 1) (hbin : 0 ∈ B.bins)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : B.sampleScale r (some 0) = 0) (w : ℝ) (hw : 1 ≤ w) :
    ¬ w * B.initialClippedEndpointWindow 8192 1 0 r ≤ (2 : ℝ) ^ (64 : ℝ) := by
  intro h
  have hlive : LogSpaceEstimation.lastBudget 8192
      (Cslib.RowCompression.dyadicSlack (Nat.log2 8192 + 1) 1) B.slack
      (B.sampleScale r (some 0)) ≠ 0 := by
    norm_num [Cslib.RowCompression.dyadicSlack, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, hslack, hs]
  have hg := B.initialClippedEndpointWindow_growth 8192 1 0 0 r hbin hlive w 64 hw h
  norm_num [Cslib.RowCompression.dyadicSlack, hslack] at hg


-- Zero and exhausted endpoints have no transport charge, before any precision estimate.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (j ka : ℕ) (coefficient : ℝ) :
    B.initialClippedEndpointWindow 0 j ka r = 0 ∧
      B.initialClippedEndpointPrefixCharge 0 j r ka coefficient = 0 := by
  simp [BudgetData.initialClippedEndpointWindow, BudgetData.initialClippedEndpointPrefixCharge,
    BudgetData.initialEndpointCharge, LogSpaceEstimation.lastBudget]


-- The same obstruction occurs in the exact tail sum of the numerical reserve.
open Cslib.RowCompression in
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hslack : B.slack = 1) (hbin : 0 ∈ B.bins)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : B.sampleScale r (some 0) = 0) :
    ¬ (∑ i ∈ Ico 1 (Nat.log2 8192 + 1), (28 : ℝ) ^ (Nat.log2 8192 + 1 - i) *
      B.initialClippedEndpointWindow 8192 i 0 r) ≤ (2 : ℝ) ^ (64 : ℝ) := by
  intro h
  have hlive : LogSpaceEstimation.lastBudget 8192
      (dyadicSlack (Nat.log2 8192 + 1) 1) B.slack (B.sampleScale r (some 0)) ≠ 0 := by
    norm_num [dyadicSlack, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, hslack, hs]
  have hg := B.initialClippedEndpointWindow_tail_growth 8192 1 1 0 0 r
    (by decide) hbin hlive 64 h
  norm_num [dyadicSlack, hslack] at hg


-- Positive parent precision does not imply a positive scheduled endpoint budget.
-- At M=1 even the final endpoint is exhausted; its transport window is exactly zero.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hslack : B.slack = 1) (hcharge : B.rankCharge = 0)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = 1) (ht : r.terminal.rate = 1) (ka : ℕ) :
    0 < B.requestPrecision 1 r ∧ B.initialClippedEndpointWindow 1 (Nat.log2 1) ka r = 0 := by
  constructor
  · norm_num [BudgetData.requestPrecision, LogSpaceEstimation.precision,
      hslack, hcharge, hs, ht]
  · simp [BudgetData.initialClippedEndpointWindow, Cslib.RowCompression.dyadicSlack,
      LogSpaceEstimation.lastBudget]

-- The large-slack obstruction above coexists with a valid deterministic rarity payment.
-- This is the same literal window and propagation, with its actual outer event weight.
open Cslib.RowCompression in
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    (∑ j ∈ range (Nat.log2 8192 + 1),
      (((2 + 256 / dyadicFloor 1 (Nat.log2 8192 + 1) j) /
        (compatibleCapacity HP.K (Nat.log2 8192 + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
      ∑ i ∈ Ico j (Nat.log2 8192 + 1), (28 : ℝ) ^ (Nat.log2 8192 + 1 - i) *
        B.initialClippedEndpointWindow 8192 i 0 r) ≤
      (2 + 256 / (1 : ℝ)) ^ (4⁻¹ : ℝ) *
        (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) / 63 :=
  compatible_growing_mean_tail_le (by norm_num)
    (mul_nonneg (by norm_num) (tsum_nonneg fun _ => LogSpaceEstimation.scaleMajorant_nonneg _))
    HP.K _ _ (fun i _ => B.initialClippedEndpointWindow_growing 8192 i 0 r)

-- Charge 64 is fixed first. Vary both exponents and every positive integer precision;
-- the actual first-mean minimum now receives a whole-tail payment with no slack cutoff.
open Cslib.RowCompression in
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hslack : B.slack = 1) (hrate : B.binRate = rate) (H : Horizon P)
    (hi : ∀ bin ∈ B.bins, bin ≤ H.maxExponent) (ks ka : ℕ) (ha : ka ≤ H.maxExponent)
    (p : ℕ) (hp : 0 < p) (ζ Lh Lρ : ℝ) :
    let B' : BudgetData HP P := { B with rankCharge := 64 }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
        gridChannel 2 ka [], gridChannel 2 ka []⟩
    let M := 16 * (64 * r.task.rank + p + 2 * (ks + ka))
    0 < B'.requestPrecision M r ∧
      (∑ j ∈ range (Nat.log2 M + 1),
        (((2 + 256 / dyadicFloor 1 (Nat.log2 M + 1) j) /
          (compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ)) ^ (4⁻¹ : ℝ)) *
        ∑ i ∈ Ico j (Nat.log2 M + 1), (28 : ℝ) ^ (Nat.log2 M + 1 - i) *
          B'.initialComputedPrecisionMoment M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
            ks ka [] [] 1 ζ Lh Lρ i false 0 ^ (4⁻¹ : ℝ)) ≤
        B'.initialComputedFirstTailBudget M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 1 ∧
      (∑ j ∈ range (Nat.log2 M + 1), dyadicFloor 1 (Nat.log2 M + 1) j *
        B'.initialComputedPrecisionMoment M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 ζ Lh Lρ j false 0 ^ (4⁻¹ : ℝ)) ≤
        B'.initialComputedFirstPreBudget M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 1 ∧
      B'.initialComputedPrecisionMoment M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 ζ Lh Lρ (Nat.log2 M) false 0 ^ (4⁻¹ : ℝ) ≤
        B'.initialComputedFirstFinalBudget M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 ∧
      (∑ j ∈ range (Nat.log2 M + 1), (64 * (HP.K : ℝ) * (2 : ℝ) ^ 4 /
        ((compatibleCapacity HP.K (Nat.log2 M + 1) j : ℝ) *
          dyadicFloor 1 (Nat.log2 M + 1) j ^ 4)) *
        B'.initialComputedPrecisionMoment M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 ζ Lh Lρ j false 0) ≤
        B'.initialComputedFirstRawBudget M 2 r ⟨0, 1, 2, by decide, by decide, by decide⟩
          ks ka [] [] 1 1 2 := by
  dsimp only
  let B' : BudgetData HP P := { B with rankCharge := 64 }
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 ks [],
      gridChannel 2 ka [], gridChannel 2 ka []⟩
  let M := 16 * (64 * r.task.rank + p + 2 * (ks + ka))
  have hprec := B'.requestPrecision_grid M ks ka r rfl rfl
  have hpeq : B'.requestPrecision M r = p := by
    rw [hprec]
    dsimp only [B']
    rw [hslack]
    dsimp only [M]
    push_cast
    ring
  constructor
  · rw [hpeq]
    exact_mod_cast hp
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact B'.initialComputedPrecisionMoment_first_tail_le (by norm_num) hrate H M 2 ks ka
        ha hi r (rate_pos ks).le rfl rfl rfl
        ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ 1 (by norm_num)
    · exact B'.initialComputedPrecisionMoment_first_pre_le (by norm_num) hrate H M 2 ks ka
        ha hi r (rate_pos ks).le rfl rfl rfl
        ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ 1 (by norm_num)
    · exact B'.initialComputedPrecisionMoment_first_final_le (by norm_num) hrate H M 2 ks ka
        ha hi r (rate_pos ks).le rfl rfl rfl
        ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ
    · exact B'.initialComputedPrecisionMoment_first_raw_le (by norm_num) hrate H M 2 ks ka
        ha hi r rfl rfl rfl
        ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ 1 2 (by norm_num)

-- All four transport components share a charge selected before arbitrary precision.
-- This numerical allocation excludes the separate semantic deficit and noise budgets.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (floor cap C Cpre L : ℝ) :
    ∃ A : ℕ, ∀ p : ℝ,
      BudgetData.initialFirstTransportPayment HP floor cap C Cpre
        (L * (2 : ℝ) ^ (-(A : ℝ)) * (2 : ℝ) ^ (-p)) ≤
          (2 : ℝ) ^ (-4 * p) := by
  obtain ⟨A, hA⟩ := BudgetData.initialFirstTransportPayment_exists_charge HP floor cap C Cpre L
  refine ⟨A, fun p => ?_⟩
  convert hA ((2 : ℝ) ^ (-p)) using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

-- The exact raw coefficient keeps K+1 and exponent -24d at the literal unit floor.
open Cslib.RowCompression in
example (K m j : ℕ) :
    64 * (K : ℝ) * (2 : ℝ) ^ 4 /
      ((compatibleCapacity K m j : ℝ) * dyadicFloor 1 m j ^ 4) =
      (1024 * (K : ℝ) / (K + 1)) * (1 / 16777216 : ℝ) ^ dyadicSlack m j := by
  convert compatible_false_weight_eq 1 K m j 2 using 1
  norm_num
  ring

-- One evaluator per retained depth, with a bounded family of budgets. The charge is fixed
-- first; positive precision grows with depth and actual nonzero omitted mass persists.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (hrate : B.binRate = rate) (hslack : B.slack = 1)
    (n : ℕ) :
    let B' : BudgetData HP P := {B with rankCharge := 1}
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [],
        gridChannel 2 0 [], gridChannel 2 0 []⟩
    r.task.rank < n →
      0 < B'.requestPrecision (16 * n) r ∧
      (∀ bin ≤ n, LogSpaceEstimation.scaleCutoff B'.slack
        (B'.sampleScale r (some bin)) < 16 * n) ∧
      rate n / rate 0 ≤ (2 : ℝ) ^ (-B'.requestPrecision (16 * n) r) ∧
      0 < rate n / 4 ∧
      (rate n / 4) * (1 - polynomialSwitch4 (1 / 2) 1 ((rate n / 4) / rate n)) =
        rate n / 4 := by
  dsimp only
  intro hn
  let B' : BudgetData HP P := {B with rankCharge := 1}
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 0 [],
      gridChannel 2 0 [], gridChannel 2 0 []⟩
  have hn0 : 0 < n := by omega
  have hp : B'.requestPrecision (16 * n) r = (n : ℝ) - r.task.rank := by
    rw [B'.requestPrecision_grid (16 * n) 0 0 r rfl rfl]
    dsimp only [B']
    rw [hslack]
    push_cast
    ring
  have hg := B'.bounded_family_depth_guards (by norm_num [B']) n (16 * n) 0 0
    (by change B.slack * (1 + 4 * (n + 0)) < _; rw [hslack]; omega)
    (by change _ ≤ 32 * B.slack * n; rw [hslack]; omega)
    (by omega) r hrate rfl rfl
  refine ⟨?_, hg.1, hg.2.2, div_pos (rate_pos n) (by norm_num), ?_⟩
  · rw [hp]
    exact sub_pos.mpr (by exact_mod_cast hn)
  · have he : (rate n / 4) / rate n = (1 / 4 : ℝ) := by
      field_simp [(rate_pos n).ne']
    rw [he, polynomialSwitch4_of_le (by norm_num) (by norm_num)]
    ring

-- A fixed-depth semantic obstruction, not an executed full-estimator counterexample:
-- at depth zero true mass 1/4 is omitted, so its normalized error is 1/5, above 2^-8.
example :
    (1 / 4 : ℝ) * (1 - polynomialSwitch4 (1 / 2) 1 ((1 / 4) / rate 0)) /
      (rate 0 + 1 / 4) > (2 : ℝ) ^ (-8 : ℝ) := by
  have hz : polynomialSwitch4 (1 / 2) 1 ((1 / 4 : ℝ) / rate 0) = 0 :=
    polynomialSwitch4_of_le (by norm_num) (by norm_num [rate])
  rw [hz]
  norm_num [rate]

-- The literal initial group can omit every bin even when its cutoff fits. Its actual
-- charge must remain in stationary/raw/tail analysis, rather than being set to zero.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ}
    (B : BudgetData HP P) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.initialInactiveCharge 16 0 r = B.binCap * ∑ bin ∈ B.bins, B.binRate bin := by
  unfold BudgetData.initialInactiveCharge
  norm_num [Cslib.RowCompression.dyadicSlack]

-- This consumes the existing computed first-mean minimum and the very final budget
-- appearing in initial_compressed_precision_reserve. It remains conditional on child IH;
-- neither the other three reserve statistics nor the exceptional group is certified.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hcharge : 0 ≤ B.rankCharge)
    (M n ks ka : ℕ) (hM : 1 < M)
    (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n) (hP : P ≤ 2 ^ (n + 1))
    (H : Horizon P) (hn : n ≤ H.maxExponent) (hks : ks ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hC : ∀ x y, 0 ≤ B.base x y) (R : RoleProfile 3) (ss st : List (ZMod P))
    (coefficient ζ Lh Lρ : ℝ) :
    B.initialComputedPrecisionMoment M n r R ks ka ss st coefficient ζ Lh Lρ
      (Nat.log2 M) false 0 ^ (4⁻¹ : ℝ) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (((max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^
          (4⁻¹ : ℝ) * |coefficient| * (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (-B.rankCharge)) * (4 * ∑' h, LogSpaceEstimation.scaleMajorant h) +
        (32 : ℝ) ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r)) := by
  have hka : ka ≤ H.maxExponent := (by omega : ka ≤ n).trans hn
  exact (B.initialComputedPrecisionMoment_first_final_le hcharge hrate H M n ks ka hka
    (fun bin hb => by rw [hbins, mem_range] at hb; omega) r
    (by rw [hs]; exact (rate_pos ks).le) hs ht htask R ss st coefficient ζ Lh Lρ).trans
    (B.initialComputedFirstFinalBudget_bounded_family hcharge M n ks ka hM hbins hrate
      hlo hhi ha hP H hks r hs ht hC R ss st coefficient)

-- Each larger retained depth admits its own bounded prime and common field horizon.
-- This changes the evaluator family, never the bin set during one recursive execution.
example (n : ℕ) :
    ∃ P, P.Prime ∧ 2 ^ n < P ∧ P ≤ 2 ^ (n + 1) ∧
      ∃ H : Horizon P, H.maxExponent = n ∧ H.maxIdentifier = 0 :=
  exists_bounded_depth_prime n 0 (by positivity)

-- Unbounded source/terminal/bin exponents under ONE charge. The full finite bin
-- horizon grows with n, and an admissible prime exists for every such horizon below.
-- Actual positive parent precision and both unequal endpoint budgets are checked.
-- This tests joint scalar cancellation, not a successful recursive family.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hrate : B.binRate = rate) (hslack : B.slack = 1)
    (n p : ℕ) (H : Horizon P) (hn : n + 2 ≤ H.maxExponent) :
    let B' : BudgetData HP P := { B with rankCharge := 7, bins := range (n + 3) }
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [],
        gridChannel 2 (n + 1) [], gridChannel 2 (n + 1) []⟩
    let M := 16 * (7 * r.task.rank + p + 4 * n + 4)
    B'.requestPrecision M r = p + 2 ∧ 0 < B'.requestPrecision M r ∧
      ∀ bin ∈ ({n, n + 1, n + 2} : Finset ℕ), ∀ e ∈ ({8, 16} : Finset ℕ),
      let m := LogSpaceEstimation.lastBudget M e B'.slack (B'.sampleScale r (some bin))
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
      ∀ y,
      (B'.binRate bin * HierarchyTask.usageRatio (channels B'.padding)
        r.terminal Q.direct y / rate (n + 1)) * (2 : ℝ) ^ (-B'.requestPrecision m Q.direct) ≤
        16 * ((2 : ℝ) ^ (-((p : ℝ) + 2)) * (2 : ℝ) ^ (-7 : ℝ) *
          (2 : ℝ) ^ (16 - |(bin : ℝ) - (n + 1)|)) := by
  dsimp only
  let B' : BudgetData HP P := { B with rankCharge := 7, bins := range (n + 3) }
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [],
      gridChannel 2 (n + 1) [], gridChannel 2 (n + 1) []⟩
  let M := 16 * (7 * r.task.rank + p + 4 * n + 4)
  have hp : B'.requestPrecision M r = p + 2 := by
    rw [B'.requestPrecision_grid M n (n + 1) r rfl rfl]
    dsimp only [B']
    rw [hslack]
    dsimp only [M]
    push_cast
    ring
  refine ⟨hp, by rw [hp]; positivity, ?_⟩
  intro bin hbin e he y
  have hbin' : bin = n ∨ bin = n + 1 ∨ bin = n + 2 := by simpa using hbin
  have hcut : LogSpaceEstimation.scaleCutoff B'.slack (B'.sampleScale r (some bin)) ≤ 5 := by
    rw [B'.sampleScale_grid r (n + 1) bin hrate rfl]
    change LogSpaceEstimation.scaleCutoff B.slack _ ≤ _
    rw [hslack]
    rcases hbin' with hb | hb | hb <;> rw [hb] <;>
      norm_num [LogSpaceEstimation.scaleCutoff, Int.natAbs_of_nonneg,
        show (n : ℤ) + 1 - n = 1 by omega,
        show (n : ℤ) + 1 - (n + 1) = 0 by omega,
        show (n : ℤ) + 1 - (n + 2) = -1 by omega]
  have hne : LogSpaceEstimation.lastBudget M 8 B'.slack (B'.sampleScale r (some bin)) ≠
      LogSpaceEstimation.lastBudget M (2 * 8) B'.slack (B'.sampleScale r (some bin)) := by
    unfold LogSpaceEstimation.lastBudget
    dsimp only [M]
    omega
  have h := B'.initial_normalized_active_precision_le (by norm_num [B']) hrate H
    M 8 n (n + 1) bin e (by omega) (by rcases hbin' with rfl | rfl | rfl <;> omega)
    r rfl rfl rfl hne (by simpa only [show 2 * 8 = 16 by decide] using he) y
  rw [hp] at h
  simpa only [B', r, M, hslack, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, div_one,
    show (2 : ℝ) * 8 = 16 by norm_num]
    using h

example (n : ℕ) :
    ∃ P, P.Prime ∧ 2 ^ (n + 2) < P ∧ P ≤ 2 ^ (n + 3) ∧
      ∃ H : Horizon P, H.maxExponent = n + 2 ∧ H.maxIdentifier = 0 := by
  simpa only [Nat.add_assoc] using exists_bounded_depth_prime (n + 2) 0 (by positivity)

-- A fixed charge is chosen before unbounded depth/precision and full bin horizons.
-- The conditional client below consumes actual computed centered noise, rather than
-- just testing the scalar exponent. Production leaves and recursive availability stay open.
private def unboundedNoiseRequest {P : ℕ} (HP : FourthRootHierarchyParams 16 1 16 32 8) (n : ℕ) :
    HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.row 0 (.pilotInput ⟨0, HP.k_pos⟩), gridChannel 0 n [],
    gridChannel 2 (n + 1) [], gridChannel 2 (n + 1) []⟩

example {HP : FourthRootHierarchyParams 16 1 16 32 8} (binCap coefficient : ℝ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = binCap → B.rankCharge = A → B.binRate = rate → B.slack = 1 →
      ∀ n p, B.bins = range (n + 3) → ∀ H : Horizon P, n + 2 ≤ H.maxExponent →
      let r := unboundedNoiseRequest HP n (P := P)
      let M := 16 * (A * r.task.rank + p + 4 * n + 4)
      0 < B.requestPrecision M r ∧
      ∀ j (R : RoleProfile 3) (ζ Lh Lρ : ℝ),
      B.initialComputedPrecisionMoment M (n + 2) r R n (n + 1) [] [] coefficient ζ Lh Lρ
          j true 0 ≤
        8 * (((2 : ℝ) ^ (-B.requestPrecision M r) *
          (1 / 16 : ℝ) ^ Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) ^ 4 +
          B.initialRelativeNoiseBudget M r R.source R.terminal R.source_terminal
            n (n + 1) [] [] B.base (j + 1)) := by
  obtain ⟨A, hA⟩ := BudgetData.initialComputedPrecisionMoment_firstNoise_uniform_charge
    (HP := HP) binCap coefficient
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate hslack n p hbins H hn
  dsimp only
  let r := unboundedNoiseRequest HP n (P := P)
  let M := 16 * (A * r.task.rank + p + 4 * n + 4)
  have hp : B.requestPrecision M r = p + 2 := by
    rw [B.requestPrecision_grid M n (n + 1) r rfl rfl, hslack, hcharge]
    dsimp only [M]
    push_cast
    ring
  have hq : { r with usage := r.terminal } = r := rfl
  refine ⟨by rw [hp]; positivity, ?_⟩
  intro j R ζ Lh Lρ
  have h := hA B hcap hcharge hrate H M j n (n + 1) (by omega)
    (fun bin hb => by rw [hbins, mem_range] at hb; omega) r rfl
    (by rw [hq, hp]; positivity) R [] [] (n + 2) ζ Lh Lρ
  simpa only [hq] using h

-- The actual computed first-noise minimum pays its unconditional propagated tail
-- on the same unbounded full-horizon family. The supported semantic tail stays literal.
open Cslib.RowCompression in
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (A n p : ℕ) (hcharge : B.rankCharge = A)
    (hrate : B.binRate = rate) (hslack : B.slack = 1)
    (hbins : B.bins = range (n + 3)) (H : Horizon P) (hn : n + 2 ≤ H.maxExponent)
    (coefficient : ℝ) :
    let r := unboundedNoiseRequest HP n (P := P)
    let M := 16 * (A * r.task.rank + p + 4 * n + 4)
    let m := Nat.log2 M + 1
    0 < B.requestPrecision M r ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) *
      B.initialComputedPrecisionMoment M (n + 2) r threeRoles n (n + 1) [] []
        coefficient 0 0 0 j true 0 ^ (4⁻¹ : ℝ)) ≤
      (8 : ℝ) ^ (4⁻¹ : ℝ) *
        (BudgetData.initialNormalizedNoiseConstant B.binCap coefficient *
          (2 : ℝ) ^ (-((p : ℝ) + 2)) * (2 : ℝ) ^ (-(A : ℝ)) * (1792 / 57) +
        ∑ j ∈ range m, (28 : ℝ) ^ (m - j) *
          B.initialRelativeNoiseBudget M r threeRoles.source threeRoles.terminal
            threeRoles.source_terminal n (n + 1) [] [] B.base (j + 1) ^ (4⁻¹ : ℝ)) := by
  dsimp only
  let r := unboundedNoiseRequest HP n (P := P)
  let M := 16 * (A * r.task.rank + p + 4 * n + 4)
  have hp : B.requestPrecision M r = p + 2 := by
    rw [B.requestPrecision_grid M n (n + 1) r rfl rfl, hslack, hcharge]
    dsimp only [M]
    push_cast
    ring
  have hq : { r with usage := r.terminal } = r := rfl
  have hadm : B.initialNormalizedNoiseAdmissible M r (n + 1) :=
    ⟨by rw [hcharge]; positivity, hrate, rfl, by rw [hq, hp]; positivity,
      H, by omega, fun bin hb => by rw [hbins, mem_range] at hb; omega⟩
  have ht := (B.initialComputedPrecisionMoment_firstNoise_schedule_le M (n + 2) n (n + 1)
    r (by change 0 ≤ rate n; exact (rate_pos n).le) hadm threeRoles [] [] coefficient
      0 0 0 1 1 (by norm_num)).2.2.1
  refine ⟨by rw [hp]; positivity, ?_⟩
  simpa only [hq, hp, hcharge] using ht

-- Concrete unbounded source n / terminal n+1, full bins and positive actual precision.
-- Actual own-request/reset execution remains an explicit conditional IH, restricted
-- to unequal positive endpoints. No execution is requested for equal/unused bins.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (A n p : ℕ) (hcharge : B.rankCharge = A)
    (hrate : B.binRate = rate) (hslack : B.slack = 1)
    (hbins : B.bins = range (n + 3)) (H : Horizon P) (hn : n + 2 ≤ H.maxExponent)
    (exponent : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ) (ζ floor coefficient : ℝ)
    (D : ℕ → ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hzero : ∀ bin, D bin 0 = 0)
    (ih :
      let r := unboundedNoiseRequest HP n (P := P)
      let M := 16 * (A * r.task.rank + p + 4 * n + 4)
      ∀ i bin, bin ∈ B.bins →
      let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i
      let q := { r with usage := r.terminal }
      let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale q (some bin))
      let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale q (some bin))
      fine ≠ coarse → ∀ m ∈ ({fine, coarse} : Finset ℕ), m < M → 0 < m →
      let q := { r with usage := r.terminal }
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        q.source (BudgetData.midpoint q) q.terminal (B.binRate bin)
      B.compressedBin m bin (exponent Q.direct) ζ floor Q.direct = some (D bin m) ∧
      rootDistPow 4 P Q.direct.source.rate
        (fun σ x => Q.direct.source.retains (channels B.padding) σ x)
        (fun σ y => Q.direct.usage.retains (channels B.padding) σ y) (D bin m)
        (denseChild B.padding id Q.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base) ≤
        coefficient ^ 4 * ((2 : ℝ) ^ (-B.requestPrecision m Q.direct)) ^ 4 ∧
      ∃ R, B.compressedBin m bin (exponent Q.right) ζ floor Q.right = some R)
    (hbase : ∀ x y, 0 ≤ B.base x y) :
    let r := unboundedNoiseRequest HP n (P := P)
    let M := 16 * (A * r.task.rank + p + 4 * n + 4)
    ∃ groups,
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.completedGroup (fun m q => if m < M then B.compressedHistory exponent ζ floor m q
          else none) M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) i)
          (.pilotInput ⟨0, HP.k_pos⟩) r) = some groups ∧
      ∀ (Lt : ℕ) (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
        (j : ℕ), j < Nat.log2 M + 1 →
      rowNormPow 4 P r.source.rate (retainedMask (0 : Fin 3) (side P n) B.padding [])
        (retainedMask 2 (side P (n + 1)) B.padding [])
        (actualNoiseEntry threeRoles.source threeRoles.terminal (side P n) (side P (n + 1))
          Lt B.padding [] [] (n + 1) B.base (firstSignalIncrement (fun m σ x y =>
            ((groups.take m).map (fun T => T σ x y)).sum) (n + 1) second) 0 0 j) ≤
        B.initialComputedNormalizedNoise M r threeRoles n (n + 1) [] [] coefficient j := by
  dsimp only
  let r := unboundedNoiseRequest HP n (P := P)
  let M := 16 * (A * r.task.rank + p + 4 * n + 4)
  have hp : B.requestPrecision M r = p + 2 := by
    rw [B.requestPrecision_grid M n (n + 1) r rfl rfl, hslack, hcharge]
    dsimp only [M]
    push_cast
    ring
  exact B.initial_compressed_normalized_noise_consumer (by rw [hcharge]; positivity)
    hrate H exponent ζ floor M (by dsimp only [M]; omega)
    (by rw [hbins]; exact ⟨0, mem_range.mpr (by omega)⟩) r threeRoles n (n + 1) [] []
    rfl rfl rfl (by omega) (fun bin hb => by rw [hbins, mem_range] at hb; omega)
    (by change 0 ≤ B.requestPrecision M r; rw [hp]; positivity) D hzero coefficient ih hbase

-- Actual direct-source inheritance, rank decrease and strictly positive own precision
-- at both unequal endpoints, for coarse/equal-scale/fine bins under fixed charge seven.
example {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
    (B : BudgetData HP P) (hrate : B.binRate = rate) (hslack : B.slack = 1)
    (n p : ℕ) :
    let B' : BudgetData HP P := { B with rankCharge := 7 }
    let r := unboundedNoiseRequest HP n (P := P)
    let M := 16 * (7 * r.task.rank + p + 4 * n + 4)
    ∀ bin ∈ ({n, n + 1, n + 2} : Finset ℕ), ∀ e ∈ ({8, 16} : Finset ℕ),
      let m := LogSpaceEstimation.lastBudget M e B'.slack (B'.sampleScale r (some bin))
      let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
        r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
      0 < m ∧ m < M ∧ Q.direct.source = r.source ∧
        Q.right.source = BudgetData.midpoint r ∧ Q.direct.task.rank < r.task.rank ∧
        0 < B'.requestPrecision m Q.direct := by
  dsimp only
  let B' : BudgetData HP P := { B with rankCharge := 7 }
  let r := unboundedNoiseRequest HP n (P := P)
  let M := 16 * (7 * r.task.rank + p + 4 * n + 4)
  have hrank : r.task.rank = 36 := by
    norm_num [r, unboundedNoiseRequest, HierarchyTask.rank, BoundedRowTask.localTask,
      CorrectionRowTask.rank, PilotRowTask.rank, PilotTask.rank]
  intro bin hb e he
  have hb' : bin = n ∨ bin = n + 1 ∨ bin = n + 2 := by simpa using hb
  have he' : e = 8 ∨ e = 16 := by simpa using he
  have hcut : LogSpaceEstimation.scaleCutoff B'.slack (B'.sampleScale r (some bin)) ≤ 5 := by
    rw [B'.sampleScale_grid r (n + 1) bin hrate rfl]
    change LogSpaceEstimation.scaleCutoff B.slack _ ≤ _
    rw [hslack]
    rcases hb' with h | h | h <;> rw [h] <;>
      norm_num [LogSpaceEstimation.scaleCutoff, Int.natAbs_of_nonneg,
        show (n : ℤ) + 1 - n = 1 by omega,
        show (n : ℤ) + 1 - (n + 1) = 0 by omega,
        show (n : ℤ) + 1 - (n + 2) = -1 by omega]
  have hm : LogSpaceEstimation.lastBudget M e B'.slack (B'.sampleScale r (some bin)) = M - e := by
    unfold LogSpaceEstimation.lastBudget
    rw [max_eq_left (by omega)]
  rw [hm]
  refine ⟨by dsimp only [M]; rw [hrank]; omega,
    by dsimp only [M]; rw [hrank]; omega, rfl, rfl, ?_, ?_⟩
  · change 14 < r.task.rank
    rw [hrank]
    decide
  · let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (BudgetData.midpoint r) r.terminal (B'.binRate bin)
    rw [B'.requestPrecision_grid (M - e) n bin Q.direct rfl (congrFun hrate bin)]
    change 0 < (M - e : ℕ) / (16 * (B.slack : ℝ)) - 2 * ((bin : ℝ) + n) - 7 * 14
    rw [hslack, Nat.cast_sub (by dsimp only [M]; rw [hrank]; omega)]
    dsimp only [M]
    rw [hrank]
    push_cast
    rcases he' with rfl | rfl <;> rcases hb' with rfl | rfl | rfl <;>
      norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] <;>
      linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
