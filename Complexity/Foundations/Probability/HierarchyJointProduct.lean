/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyFineDirect
import Complexity.Foundations.Probability.GridRowMoment.Rate
import all Complexity.Foundations.Probability.HierarchyInitialPerturbation
import all Complexity.Foundations.Probability.HierarchyFixedCharge

/-!
# Joint signed residual mean allocation

The active product minimum and the once-negative correction are paid at literal
own-request precision and actual truncated budgets. Constants are chosen after
fixed hierarchy primitives and the bin cap, before fields and finite horizons.
These are original consequences of the existing bounded comparison and precision
APIs, rather than a new cited endpoint. Successful child execution and own-mask IH
are still hypotheses; this does not
construct joint recursive availability, paired noise, completion or the full IH.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

variable [Fact P.Prime] (B : BudgetData HP P)

/-- Literal product minimum envelope. The coarse left coefficient is zero, the
boundary left cost remains, and the fine ordinary coefficient is cubic. The
rounded midpoint density is retained in the compared expressions. -/
theorem residualProduct_min_envelope (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent)
    (u eL eR : ℝ) (hu : 0 < u) :
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let T := HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)
    let E := (if ka ≤ i then 2 * B.binCap else 0) * HP.K * eL ^ 4 +
      (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
        (rate ka / u) * eR ^ 4
    let c := rate i * (rate ka / gridMass P ka)
    min ((F / rate ka) * (c * (gridMass P ka / gridMass P (max ka i)) * 33554432 * E))
      ((1 / rate ka) ^ 4 * (4 * (c * T) ^ ((3 : ℝ) / 4)) ^ 4 *
        (c * (gridMass P ka / gridMass P (max ka i)) * 33554432 * E)) ≤
      (max F (256 * T ^ 3) * 33554432) *
        (if i < ka then rate i / rate ka else (rate i / rate ka) ^ 3) * E := by
  dsimp only
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let T := HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)
  let E := (if ka ≤ i then 2 * B.binCap else 0) * HP.K * eL ^ 4 +
    (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
      (rate ka / u) * eR ^ 4
  have hK : (0 : ℝ) ≤ HP.K := Nat.cast_nonneg _
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hf := rate_pos ka
  have hE : 0 ≤ E := by dsimp only [E]; split_ifs <;> positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hb := rate_pos i
  have hma := gridMass_pos (P := P) ka
  have hmi := gridMass_pos (P := P) i
  have hfa := (div_le_one hma).mpr (gridMass_bounds H ha).1
  have hbi := (div_le_one hmi).mpr (gridMass_bounds H hi).1
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  change min _ _ ≤ (max F (256 * T ^ 3) * 33554432) * _ * E
  by_cases hia : i < ka
  · apply (min_le_left _ _).trans
    rw [ite_eq_left hia, max_eq_left hia.le]
    have he : (F / rate ka) *
        ((rate i * (rate ka / gridMass P ka)) *
          (gridMass P ka / gridMass P ka) * 33554432 * E) =
        F * (rate i / rate ka) * (rate ka / gridMass P ka) * 33554432 * E := by
      field_simp
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hfa (mul_nonneg hF (div_nonneg hb.le hf.le))
    have hj := mul_le_mul_of_nonneg_right hh (by positivity : (0 : ℝ) ≤ 33554432 * E)
    have hk := mul_le_mul_of_nonneg_right (le_max_left F (256 * T ^ 3))
      (by positivity : 0 ≤ (rate i / rate ka) * 33554432 * E)
    nlinarith
  · apply (min_le_right _ _).trans
    rw [ite_eq_right hia, max_eq_right (by omega : ka ≤ i)]
    have hr : ((rate i * (rate ka / gridMass P ka) * T) ^ ((3 : ℝ) / 4)) ^ 4 =
        (rate i * (rate ka / gridMass P ka) * T) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity :
        0 ≤ rate i * (rate ka / gridMass P ka) * T)]
      norm_num
    rw [mul_pow, hr]
    have he : (1 / rate ka) ^ 4 * (4 ^ 4 *
        (rate i * (rate ka / gridMass P ka) * T) ^ 3) *
        ((rate i * (rate ka / gridMass P ka)) *
          (gridMass P ka / gridMass P i) * 33554432 * E) =
        (256 * T ^ 3) * (rate i / rate ka) ^ 3 *
          (rate ka / gridMass P ka) ^ 3 * (rate i / gridMass P i) * 33554432 * E := by
      field_simp
      ring
    rw [he]
    have hh : (rate ka / gridMass P ka) ^ 3 * (rate i / gridMass P i) ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hfa)
        (by positivity)).trans (by simpa only [one_mul] using hbi)
    have hj := mul_le_mul_of_nonneg_left hh
      (by positivity : 0 ≤ (256 * T ^ 3) * (rate i / rate ka) ^ 3 * 33554432 * E)
    have hk := mul_le_mul_of_nonneg_right (le_max_right F (256 * T ^ 3))
      (by positivity : 0 ≤ (rate i / rate ka) ^ 3 * 33554432 * E)
    nlinarith

omit [Fact P.Prime] in
/-- The literal left and reset-right moment payments share one geometric norm
salary. Source release cancels only after using the right child's own precision.
The strictly coarse left payment remains exactly zero. -/
theorem residualProduct_scale_salary (M ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)
    let scale := if i < ka then rate i / rate ka else (rate i / rate ka) ^ 3
    let t := (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
      (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4)
    scale * ((if ka ≤ i then 2 * B.binCap else 0) * HP.K *
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) Q.left)) ^ 4 +
      (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
        (r.terminal.rate / r.source.rate) *
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) Q.right)) ^ 4) ≤
      ((2 * B.binCap) * HP.K +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊) * t ^ 4 := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)
  let scale := if i < ka then rate i / rate ka else (rate i / rate ka) ^ 3
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) *
    (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
    (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4)
  have hcap := B.binCap_nonneg
  have hK : (0 : ℝ) ≤ HP.K := Nat.cast_nonneg _
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hf := rate_pos ka
  have hu := rate_pos ks
  have hks : (ka : ℝ) ≤ ks := by exact_mod_cast hka
  have hb := B.binBudget_precision_loss M ka i r hrate ht
  have hL := B.requestPrecision_residual_left M (B.binBudget M i r) ks ka i r hs ht
  have hR := B.requestPrecision_residual_right M (B.binBudget M i r) ks ka i r hs ht
    (congrFun hrate i)
  have hlg : (Q.left.task.rank : ℝ) + 32 = r.task.rank := by
    rw [hr]; exact_mod_cast (residual_correction_rank_gap (HP := HP))
  have hrg : (Q.right.task.rank : ℝ) + (80 * (HP.k : ℝ) + 94) = r.task.rank := by
    rw [hr]; exact_mod_cast (residual_base_rank_gap (HP := HP) i)
  change B.requestPrecision (B.binBudget M i r) Q.left - B.requestPrecision M r = _ at hL
  change B.requestPrecision (B.binBudget M i r) Q.right - B.requestPrecision M r = _ at hR
  rw [← hlg] at hL
  rw [← hrg] at hR
  rw [sub_div] at hb hL hR
  have hright : scale * (r.terminal.rate / r.source.rate) *
      ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) Q.right)) ^ 4 ≤ t ^ 4 := by
    dsimp only [scale, t]
    rw [hs, ht, rate_ratio_two_rpow, rate_ratio_two_rpow]
    simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    split_ifs with hi
    all_goals
      simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    · have hir : (i : ℝ) ≤ ka := by exact_mod_cast hi.le
      rw [abs_of_nonpos (sub_nonpos.mpr hir)] at hb ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) HP.k]
    · have hir : (ka : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_not_gt hi)
      rw [abs_of_nonneg (sub_nonneg.mpr hir)] at hb ⊢
      nlinarith [Nat.cast_nonneg (α := ℝ) HP.k]
  have hleft : scale * ((if ka ≤ i then 2 * B.binCap else 0) * HP.K *
      ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) Q.left)) ^ 4) ≤
      (2 * B.binCap) * HP.K * t ^ 4 := by
    by_cases hi : ka ≤ i
    · rw [ite_eq_left hi]
      have hh : scale *
          ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) Q.left)) ^ 4 ≤ t ^ 4 := by
        dsimp only [scale, t]
        rw [ite_eq_right (not_lt.mpr hi), rate_ratio_two_rpow]
        simp only [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        have hir : (ka : ℝ) ≤ i := by exact_mod_cast hi
        rw [abs_of_nonneg (sub_nonneg.mpr hir)] at hb ⊢
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (by positivity : 0 ≤ 2 * B.binCap) hK)]
    · rw [ite_eq_right hi, zero_mul, zero_mul, mul_zero]
      positivity
  have hh := mul_le_mul_of_nonneg_left hright (by positivity :
    0 ≤ (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊)
  change scale * _ ≤ _
  nlinarith

/-- Primitive fourth-root cost of one active product bin, before scale salary. -/
@[expose] def residualProductRootCost (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (cap : ℝ) : ℝ :=
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let T := HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * cap)
  (max F (256 * T ^ 3) * 33554432 *
    ((2 * cap) * HP.K +
      (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊)) ^ (4⁻¹ : ℝ)

/-- The literal active product minimum has summable norm decay on both sides
at own-request precision. The boundary retains its left correction payment. -/
theorem residualProduct_min_root_salary (H : Horizon P) (M ks ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
    let pc := (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    (min pc po) ^ (4⁻¹ : ℝ) ≤
      residualProductRootCost HP B.binCap * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
        (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4) := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
  let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let T := HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)
  let C := max F (256 * T ^ 3) * 33554432
  let L := (2 * B.binCap) * HP.K +
    (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊
  let t := (2 : ℝ) ^ (-B.requestPrecision M r) *
    (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) *
    (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4)
  have hcap := B.binCap_nonneg
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hC : 0 ≤ C := by dsimp only [C, F]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have henv := B.residualProduct_min_envelope H ka i ha hi r.source.rate
    (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
    (by rw [hs]; exact rate_pos ks)
  rw [← ht, ← hrate] at henv
  have hsalary := B.residualProduct_scale_salary M ks ka i r hrate hs ht hr hka hcharge
  change _ ≤ L * t ^ 4 at hsalary
  rw [← ht, ← hrate] at hsalary
  have hh := henv.trans (by
    convert mul_le_mul_of_nonneg_left hsalary hC using 1; dsimp only [C, F, T]; ring)
  have hnonneg : 0 ≤ min ((F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) *
          ε (B.binBudget M i r) (Q i).right ^ 4))) ((1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))) := by
    have hu : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
    have hf := rate_pos ka
    have ht0 : 0 < r.terminal.rate := by rw [ht]; exact hf
    have hb : 0 < B.binRate i := by rw [hrate]; exact rate_pos i
    have hm := gridMass_pos (P := P) ka
    have hmm := gridMass_pos (P := P) (max ka i)
    dsimp only [F]
    split_ifs <;> positivity
  simp only [ht] at hh hnonneg ⊢
  have hj := Real.rpow_le_rpow hnonneg hh (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  rw [show C * (L * t ^ 4) = (C * L) * t ^ 4 by ring,
    Real.mul_rpow (mul_nonneg hC hL) (by positivity : 0 ≤ t ^ 4)] at hj
  have htroot : (t ^ 4) ^ (4⁻¹ : ℝ) = t := by
    convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ t) (by decide : (4 : ℕ) ≠ 0)
      using 1
  rw [htroot] at hj
  simpa only [residualProductRootCost, C, F, T, L, t, mul_assoc] using hj

/-- Count-free geometric summation of the literal product minimum on arbitrary
finite admitted bin sets. It uses actual bin budgets, not a common child budget. -/
theorem residualProduct_min_sum_salary (H : Horizon P) (M ks ka : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    (∑ i ∈ B.bins, (min (pc i) (po i)) ^ (4⁻¹ : ℝ)) ≤
      (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) * residualProductRootCost HP B.binCap *
        (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) := by
  dsimp only
  apply (sum_le_sum fun i hib =>
    B.residualProduct_min_root_salary H M ks ka i ha (hi i hib) r hrate hs ht hr
      hka hcharge).trans
  simp only [← mul_sum]
  have hh := mul_le_mul_of_nonneg_left (sum_two_rpow_offset_le B.bins ka)
    (by have := B.binCap_nonneg
        have hcost : 0 ≤ residualProductRootCost HP B.binCap := by
          dsimp only [residualProductRootCost]
          have := HP.Q_nonneg HP.toHierarchyParams.atomCap
          positivity
        positivity : 0 ≤ residualProductRootCost HP B.binCap *
          (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge))
  convert hh using 1
  ring

omit [Fact P.Prime] in
/-- The final negative correction is paid once at its zero-scale child budget,
with the actual 32-slot gap. This also covers budget exhaustion. -/
theorem residualNegative_root_salary (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hr : r.task = .residual 0) :
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    (F * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) neg)) ^ 4) ^ (4⁻¹ : ℝ) ≤
      F ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) := by
  dsimp only
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  apply (payment_root_le hF (by positivity) le_rfl).trans
  rw [B.requestPrecision_residual_negative M (B.childBudget M) ks ka r hs ht hr]
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (sub_le_sub_right (B.childBudget_precision_loss M) (32 * B.rankCharge))
  convert mul_le_mul_of_nonneg_left hh (by positivity :
    0 ≤ F ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r)) using 1
  ring

/-- Primitive cost of the once-negative term and the complete product sum. -/
@[expose] def residualProductNegativeRootCost
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (cap : ℝ) : ℝ :=
  (512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3) ^ (4⁻¹ : ℝ) +
    (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) * residualProductRootCost HP cap

omit [Fact P.Prime] in
/-- Increasing the common charge preserves the direct-quarter salary. This is
monotonicity of the normalized allocation coefficient; changing charge also changes
parent precision, so absolute error allowances are not compared across data. -/
theorem residualDirect_charge_mono (cap : ℝ) (hcap : 0 ≤ cap) {A A' : ℝ} (hA : A ≤ A') :
    residualDirectRootCost HP cap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A') ≤
    residualDirectRootCost HP cap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) := by
  have hc : 0 ≤ residualDirectRootCost HP cap := by
    dsimp only [residualDirectRootCost]
    have hg : 0 < 1 - (2 : ℝ) ^ (-3 / 4 : ℝ) := sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
    positivity
  apply mul_le_mul_of_nonneg_left _ hc
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  nlinarith [Nat.cast_nonneg (α := ℝ) HP.k]

omit [Fact P.Prime] in
/-- A single natural charge, as large as any already fixed charge, pays direct by
one quarter and product plus negative by three quarters. The choice depends only
on fixed HP and cap, before fields, source/terminal/bin exponents or budgets. -/
theorem exists_residualJoint_charge (cap : ℝ) (hcap : 0 ≤ cap) (A₀ : ℕ) :
    ∃ A : ℕ, A₀ ≤ A ∧
      residualDirectRootCost HP cap *
        (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) ≤ 1 / 4 ∧
      residualProductNegativeRootCost HP cap *
        (2 : ℝ) ^ (1 / 16 - 32 * (A : ℝ)) ≤ 3 / 4 := by
  obtain ⟨Ad, hd⟩ := exists_residualDirect_charge (HP := HP) cap
  obtain ⟨n, hn⟩ := exists_nat_gt (residualProductNegativeRootCost HP cap)
  let A := max A₀ (max Ad (n + 4))
  refine ⟨A, le_max_left _ _, ?_, ?_⟩
  · exact (residualDirect_charge_mono cap hcap
      (by exact_mod_cast ((le_max_left Ad (n + 4)).trans (le_max_right A₀ _)))).trans hd
  · have hp : (n : ℝ) ≤ (2 : ℝ) ^ n := by
      exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have hc : residualProductNegativeRootCost HP cap ≤ (2 : ℝ) ^ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact hn.le.trans hp
    apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hAn : (n : ℝ) + 4 ≤ A := by
      exact_mod_cast ((le_max_right Ad (n + 4)).trans (le_max_right A₀ _))
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (n : ℝ) + (1 / 16 - 32 * (A : ℝ)) ≤ -2 by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    norm_num at hh ⊢
    linarith

/-- The exact remaining signed-consumer expression is paid by three quarters of
parent precision. No field-width or bin-count factor enters the salary. -/
theorem residualProduct_negative_sum_le (H : Horizon P) (M ks ka : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0)
    (hka : ka ≤ ks) (hcharge : 0 ≤ B.rankCharge)
    (hfixed : residualProductNegativeRootCost HP B.binCap *
      (2 : ℝ) ^ (1 / 16 - 32 * B.rankCharge) ≤ 3 / 4) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let ε := fun m q => (2 : ℝ) ^ (-B.requestPrecision m q)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    (F * ε (B.childBudget M) neg ^ 4) ^ (4⁻¹ : ℝ) +
      (∑ i ∈ B.bins, (min (pc i) (po i)) ^ (4⁻¹ : ℝ)) ≤
      3 * (2 : ℝ) ^ (-B.requestPrecision M r) / 4 := by
  dsimp only
  have hn := B.residualNegative_root_salary M ks ka r hs ht hr
  have hp := B.residualProduct_min_sum_salary H M ks ka ha hi r hrate hs ht hr hka hcharge
  apply (add_le_add hn hp).trans
  have hh := mul_le_mul_of_nonneg_right hfixed
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-B.requestPrecision M r))
  dsimp only [residualProductNegativeRootCost] at hh
  convert hh using 1 <;> ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
