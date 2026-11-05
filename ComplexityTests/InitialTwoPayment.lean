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
          ks ka [] [] 1 1 := by
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
  · exact B'.initialComputedPrecisionMoment_first_tail_le (by norm_num) hrate H M 2 ks ka
      ha hi r (rate_pos ks).le rfl rfl rfl
      ⟨0, 1, 2, by decide, by decide, by decide⟩ [] [] 1 ζ Lh Lρ 1 (by norm_num)
