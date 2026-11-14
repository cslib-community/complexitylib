/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Balance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Variance-Aware `2m`-th Moment and Collision-Concentration Bounds for `k`-Wise Independence

This module provides two high-probability concentration tools for `k`-wise independent hash families
(`Cslib.Probability.IsKWiseIndependentHash`):

1. **Heterogeneous variance-aware `2 m`-th moment and tail bounds**
   (`expect_sum_pow_le_of_sq_le`, `dens_filter_le_abs_sum_of_sq_le`,
   `dens_filter_le_abs_sum_sub_expect_of_Icc`):
   Refines `IsKWiseIndependentHash.expect_sum_pow_le` when centered terms `Z x` (`|Z x| ≤ 1`)
   satisfy per-coordinate second-moment bounds `𝔼 y, (Z x y) ^ 2 ≤ v x` (`0 ≤ v x`). Replacing `#S`
   with `max (∑ x ∈ S, v x) 1` yields polynomial `1 - n ^ (-c)` balls-into-bins and Feistel-bucket
   concentration under `O(c log n / log log n)`-wise independence.
2. **Multi-salt collision-freedom and batch collision-count tail bounds**
   (`dens_forall_salt_exists_collision_le`, `dens_card_salt_colliding_ge_le`):
   Bounds the probability that all `s_max` salts collide on a bucket under `2 * s_max`-wise
   independence, and bounds via greedy independent-witness extraction the probability that at least
   `2 * r` keys in a batch `Q_set` collide with a window `W_set` across `s_max` salts under
   `2 * r`-wise independence.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_sum_pow_le_of_sq_le`:
  `𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤ m * m ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_of_sq_le`:
  `dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} ≤ m * (m ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_filter_le_abs_sum_sub_expect_of_Icc`:
  specialization to `[0, 1]`-valued random variables `g x : Y → [0, 1]`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_forall_salt_exists_collision_le`:
  probability that every salt `s : Fin s_max` has an intra-bucket collision on `S_b` is at most
  `(#S_b ^ 2 / |Y|) ^ s_max`.
* `Cslib.Probability.IsKWiseIndependentHash.dens_card_salt_colliding_ge_le`,
  `Cslib.Probability.IsKWiseIndependentHash.dens_card_local_salt_colliding_ge_le`:
  probability that at least `2 * r` keys in `Q_set` collide with `W_set` (or per-key neighborhoods
  `W_of u` of size `≤ w_cap`) under some salt in `Fin s_max`.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Probability

open Finset Fintype
open scoped BigOperators

namespace IsKWiseIndependentHash

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

/-! ## Section 1: Heterogeneous variance-aware `2 m`-th moment bound -/

/-- Factoring tuples `t ∈ S ^ n` whose image has exact cardinality `r ≥ 1` through
`(Fin n → Fin r) × (Fin r → S)` bounds the sum of `∏ x ∈ univ.image t, v x` by
`r ^ n * (∑ x ∈ S, v x) ^ r` for any nonnegative weights `v : X → ℝ`. -/
private theorem sum_prod_image_eq_card_le [DecidableEq X] (S : Finset X) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x) (n : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (∑ t ∈ (piFinset fun _ : Fin n => S).filter (fun t => #(univ.image t) = r),
      ∏ x ∈ univ.image t, v x) ≤
      (r : ℝ) ^ n * (∑ x ∈ S, v x) ^ r := by
  set T_filt := (piFinset fun _ : Fin n => S).filter (fun t => #(univ.image t) = r)
  by_cases hT_emp : T_filt = ∅
  · rw [hT_emp, Finset.sum_empty]
    have hsum_nonneg : 0 ≤ ∑ x ∈ S, v x := sum_nonneg hv
    positivity
  · obtain ⟨t₀, ht₀⟩ := nonempty_iff_ne_empty.mpr hT_emp
    have hS_ne : S.Nonempty := by
      have ht₀_pi := (mem_filter.mp ht₀).1
      rw [mem_piFinset] at ht₀_pi
      have hn_pos : 0 < n := by
        by_contra hn0
        have hn_eq : n = 0 := by omega
        subst hn_eq
        have hc0 : #(univ.image t₀) = 0 := by simp
        have hcr : #(univ.image t₀) = r := (mem_filter.mp ht₀).2
        omega
      exact ⟨t₀ ⟨0, hn_pos⟩, ht₀_pi ⟨0, hn_pos⟩⟩
    let P_idx := piFinset fun _ : Fin n => (univ : Finset (Fin r))
    let P_val := piFinset fun _ : Fin r => S
    let φ : (Fin n → Fin r) × (Fin r → X) → (Fin n → X) := fun q => q.2 ∘ q.1
    have hnonneg_pair : ∀ q ∈ P_idx ×ˢ P_val, 0 ≤ ∏ k : Fin r, v (q.2 k) := by
      intro q hq
      have hq2 := (mem_product.mp hq).2
      rw [mem_piFinset] at hq2
      exact prod_nonneg fun k _ => hv (q.2 k) (hq2 k)
    have hsec : ∀ t ∈ T_filt,
        ∃ q ∈ P_idx ×ˢ P_val, φ q = t ∧ (∏ x ∈ univ.image t, v x) = ∏ k : Fin r, v (q.2 k) := by
      intro t ht
      rw [mem_filter, mem_piFinset] at ht
      obtain ⟨htS, hcard⟩ := ht
      let I := univ.image t
      let e : I ≃ Fin r := I.equivFin.trans (finCongr hcard)
      have hmem (j : Fin n) : t j ∈ I := mem_image_of_mem t (mem_univ j)
      let f : Fin n → Fin r := fun j => e ⟨t j, hmem j⟩
      let w : Fin r → X := fun k => (e.symm k).1
      refine ⟨(f, w), ?_, ?_, ?_⟩
      · refine mem_product.mpr ⟨by simp [P_idx], mem_piFinset.mpr fun k => ?_⟩
        obtain ⟨j, -, hj⟩ := mem_image.mp (e.symm k).2
        dsimp only [w]
        rw [← hj]
        exact htS j
      · funext j
        dsimp only [φ, Function.comp_apply, w, f]
        rw [Equiv.symm_apply_apply]
      · have himg : I = univ.image w := by
          ext x
          simp only [I, w, mem_image, mem_univ, true_and]
          constructor
          · rintro ⟨j, rfl⟩
            exact ⟨e ⟨t j, hmem j⟩, by simp⟩
          · rintro ⟨k, rfl⟩
            obtain ⟨j, -, hj⟩ := mem_image.mp (e.symm k).2
            exact ⟨j, hj⟩
        have hinj : Set.InjOn w ↑(univ : Finset (Fin r)) := by
          intro k₁ _ k₂ _ hwk
          exact e.symm.injective (Subtype.ext hwk)
        change (∏ x ∈ I, v x) = ∏ k : Fin r, v (w k)
        rw [himg, prod_image hinj]
    choose sec hsec_mem hsec_comp hsec_prod using hsec
    let defPair : (Fin n → Fin r) × (Fin r → X) :=
      (fun _ => ⟨0, hr⟩, fun _ => hS_ne.choose)
    let secFn : (Fin n → X) → (Fin n → Fin r) × (Fin r → X) := fun t =>
      if ht : t ∈ T_filt then sec t ht else defPair
    have hinj_sec : Set.InjOn secFn (T_filt : Set (Fin n → X)) := by
      intro t₁ ht₁ t₂ ht₂ heq
      have h1 : φ (secFn t₁) = t₁ := by
        simp only [secFn, mem_coe.mp ht₁, ↓reduceDIte]
        exact hsec_comp t₁ ht₁
      have h2 : φ (secFn t₂) = t₂ := by
        simp only [secFn, mem_coe.mp ht₂, ↓reduceDIte]
        exact hsec_comp t₂ ht₂
      rw [← h1, ← h2, heq]
    have himg_sub : T_filt.image secFn ⊆ P_idx ×ˢ P_val := by
      intro q hq
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hq
      simp only [secFn, ht, ↓reduceDIte]
      exact hsec_mem t ht
    calc
      (∑ t ∈ T_filt, ∏ x ∈ univ.image t, v x)
        = ∑ t ∈ T_filt, ∏ k : Fin r, v ((secFn t).2 k) := by
            refine sum_congr rfl fun t ht => ?_
            simp only [secFn, ht, ↓reduceDIte]
            exact hsec_prod t ht
      _ = ∑ q ∈ T_filt.image secFn, ∏ k : Fin r, v (q.2 k) :=
            (sum_image (f := fun q : (Fin n → Fin r) × (Fin r → X) =>
              ∏ k : Fin r, v (q.2 k)) hinj_sec).symm
      _ ≤ ∑ q ∈ P_idx ×ˢ P_val, ∏ k : Fin r, v (q.2 k) :=
            sum_le_sum_of_subset_of_nonneg himg_sub fun q hq _ => hnonneg_pair q hq
      _ = (#P_idx : ℝ) * ∑ w ∈ P_val, ∏ k : Fin r, v (w k) := by
            rw [sum_product]
            simp only [sum_const, nsmul_eq_mul]
      _ = (r : ℝ) ^ n * (∑ x ∈ S, v x) ^ r := by
            have hcard_idx : (#P_idx : ℝ) = (r : ℝ) ^ n := by
              simp [P_idx]
            have hsum_val : (∑ w ∈ P_val, ∏ k : Fin r, v (w k)) = (∑ x ∈ S, v x) ^ r := by
              dsimp only [P_val]
              rw [← sum_pow']
            rw [hcard_idx, hsum_val]

/-- **Heterogeneous variance-aware `2 m`-th moment bound for limited independence**:
For `1 ≤ m`, a `2 * m`-wise independent family `h : ι → X → Y`, a finite set `S : Finset X`, and
centered scores `Z : X → Y → ℝ` with `|Z x y| ≤ 1` and `𝔼 y, (Z x y) ^ 2 ≤ v x` (`0 ≤ v x`),
`𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤ m * m ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m`. -/
theorem expect_sum_pow_le_of_sq_le {m : ℕ} (hm : 1 ≤ m) (hh : IsKWiseIndependentHash (2 * m) h)
    (S : Finset X) (Z : X → Y → ℝ) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x)
    (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1)
    (hZ₂ : ∀ x ∈ S, 𝔼 y, (Z x y) ^ 2 ≤ v x) :
    𝔼 i, (∑ x ∈ S, Z x (h i x)) ^ (2 * m) ≤
      (m : ℝ) * (m : ℝ) ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m := by
  classical
  have := hh.nonempty
  simp only [sum_pow']
  rw [expect_sum_comm]
  have hterm : ∀ t ∈ piFinset fun _ : Fin (2 * m) => S,
      𝔼 i, ∏ j, Z (t j) (h i (t j)) ≤
        if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0 := by
    intro t ht
    have htS : ∀ x ∈ univ.image t, x ∈ S := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := mem_image.mp hx
      exact mem_piFinset.mp ht j
    have hprod (i : ι) : ∏ j, Z (t j) (h i (t j)) =
        ∏ x ∈ univ.image t, Z x (h i x) ^ #{j | t j = x} :=
      prod_comp (fun x => Z x (h i x)) t
    simp only [hprod]
    rw [hh.expect_prod (card_image_le.trans (by simp)) fun x y => Z x y ^ #{j | t j = x}]
    by_cases hex1 : ∃ x ∈ univ.image t, #{j | t j = x} = 1
    · obtain ⟨x, hx, hc1⟩ := hex1
      rw [prod_eq_zero hx (by simp only [hc1, pow_one]; exact hZ x (htS x hx))]
      split_ifs with hI
      · exact prod_nonneg fun z hz => hv z (htS z hz)
      · exact le_rfl
    · push Not at hex1
      have hcard_le : #(univ.image t) ≤ m := by
        have hsum := card_eq_sum_card_image t (univ : Finset (Fin (2 * m)))
        have h2 : ∑ x ∈ univ.image t, 2 ≤ ∑ x ∈ univ.image t, #{j | t j = x} := by
          refine sum_le_sum fun x hx => ?_
          obtain ⟨j, -, rfl⟩ := mem_image.mp hx
          have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
          have hne1 := hex1 (t j) hx
          omega
        rw [← hsum, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h2
        omega
      simp only [hcard_le, ↓reduceIte]
      refine (le_abs_self _).trans ?_
      rw [abs_prod]
      gcongr with x hx
      have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
      have hd_ge2 : 2 ≤ #{j | t j = x} := by
        obtain ⟨j, -, rfl⟩ := mem_image.mp hx
        have hpos : 0 < #{j' | t j' = t j} := card_pos.mpr ⟨j, by simp⟩
        have hne1 := hex1 (t j) hx
        omega
      refine (abs_expect_le _ _).trans ((Finset.expect_le_expect fun y _ => ?_).trans
        (hZ₂ x (htS x hx)))
      rw [abs_pow]
      obtain ⟨k, hk⟩ : ∃ k, #{j | t j = x} = 2 + k := ⟨#{j | t j = x} - 2, by omega⟩
      rw [hk, pow_add, sq_abs]
      calc (Z x y) ^ 2 * |Z x y| ^ k
          ≤ (Z x y) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) (hZ₁ x (htS x hx) y))
              (sq_nonneg _)
        _ = (Z x y) ^ 2 := mul_one _
  let P_all := piFinset fun _ : Fin (2 * m) => S
  have hpart :
      (∑ t ∈ P_all, if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0) =
        ∑ r ∈ Icc 1 m,
          ∑ t ∈ P_all.filter (fun t => #(univ.image t) = r), ∏ x ∈ univ.image t, v x := by
    rw [← sum_filter]
    have hfilt_eq : P_all.filter (fun t => #(univ.image t) ≤ m) =
        (Icc 1 m).biUnion (fun r => P_all.filter (fun t => #(univ.image t) = r)) := by
      ext t
      simp only [mem_filter, mem_biUnion, mem_Icc]
      constructor
      · rintro ⟨ht, hle⟩
        have hpos : 1 ≤ #(univ.image t) := by
          have hj : (⟨0, by omega⟩ : Fin (2 * m)) ∈ univ := mem_univ _
          exact card_pos.mpr ⟨t ⟨0, by omega⟩, mem_image_of_mem t hj⟩
        exact ⟨#(univ.image t), ⟨hpos, hle⟩, ht, rfl⟩
      · rintro ⟨r, ⟨_, hle⟩, ht, rfl⟩
        exact ⟨ht, hle⟩
    rw [hfilt_eq, sum_biUnion]
    intro r₁ _ r₂ _ hne
    dsimp only [Function.onFun]
    rw [disjoint_left]
    intro t ht₁ ht₂
    exact hne ((mem_filter.mp ht₁).2.symm.trans (mem_filter.mp ht₂).2)
  set V := max (∑ x ∈ S, v x) 1
  have hV_ge1 : 1 ≤ V := le_max_right _ _
  have hV_ge_sum : ∑ x ∈ S, v x ≤ V := le_max_left _ _
  have hsum_nonneg : 0 ≤ ∑ x ∈ S, v x := sum_nonneg hv
  calc
    (∑ t ∈ P_all, 𝔼 i, ∏ j, Z (t j) (h i (t j)))
      ≤ ∑ t ∈ P_all, if #(univ.image t) ≤ m then ∏ x ∈ univ.image t, v x else 0 :=
          sum_le_sum hterm
    _ = ∑ r ∈ Icc 1 m,
          ∑ t ∈ P_all.filter (fun t => #(univ.image t) = r), ∏ x ∈ univ.image t, v x := hpart
    _ ≤ ∑ r ∈ Icc 1 m, (r : ℝ) ^ (2 * m) * (∑ x ∈ S, v x) ^ r := by
          refine sum_le_sum fun r hr => ?_
          exact sum_prod_image_eq_card_le S v hv (2 * m) (mem_Icc.mp hr).1
    _ ≤ ∑ _r ∈ Icc 1 m, (m : ℝ) ^ (2 * m) * V ^ m := by
          refine sum_le_sum fun r hr => ?_
          rcases mem_Icc.mp hr with ⟨_, hrm⟩
          have hr_pow : (r : ℝ) ^ (2 * m) ≤ (m : ℝ) ^ (2 * m) :=
            pow_le_pow_left₀ (Nat.cast_nonneg r) (by exact_mod_cast hrm) (2 * m)
          have hv_pow : (∑ x ∈ S, v x) ^ r ≤ V ^ m :=
            (pow_le_pow_left₀ hsum_nonneg hV_ge_sum r).trans (pow_le_pow_right₀ hV_ge1 hrm)
          exact mul_le_mul hr_pow hv_pow (pow_nonneg hsum_nonneg r) (by positivity)
    _ = (m : ℝ) * (m : ℝ) ^ (2 * m) * V ^ m := by
          rw [sum_const, Nat.card_Icc, show m + 1 - 1 = m by omega, nsmul_eq_mul, mul_assoc]

/-- **Two-sided variance-aware tail bound for limited independence**:
For `1 ≤ m`, `0 < a`, and `2 * m`-wise independent centered sums bounded in `[-1, 1]` with
per-coordinate variance `≤ v x` (`0 ≤ v x`),
`dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} ≤ m * (m ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m`. -/
theorem dens_filter_le_abs_sum_of_sq_le {m : ℕ} (hm : 1 ≤ m)
    (hh : IsKWiseIndependentHash (2 * m) h) (S : Finset X) (Z : X → Y → ℝ) (v : X → ℝ)
    (hv : ∀ x ∈ S, 0 ≤ v x) (hZ : ∀ x ∈ S, 𝔼 y, Z x y = 0)
    (hZ₁ : ∀ x ∈ S, ∀ y, |Z x y| ≤ 1) (hZ₂ : ∀ x ∈ S, 𝔼 y, (Z x y) ^ 2 ≤ v x)
    {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤
      (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m := by
  have hmarkov := Fintype.mul_dens_filter_le_expect
    (f := fun i => (∑ x ∈ S, Z x (h i x)) ^ (2 * m))
    (fun _ => (even_two_mul m).pow_nonneg _) (a ^ (2 * m))
  have hsub : ({i | a ≤ |∑ x ∈ S, Z x (h i x)|} : Finset ι) ⊆
      ({i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} : Finset ι) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [← (even_two_mul m).pow_abs (∑ x ∈ S, Z x (h i x))]
    exact pow_le_pow_left₀ ha.le hi _
  have hdens : (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ) ≤
      dens {i | a ^ (2 * m) ≤ (∑ x ∈ S, Z x (h i x)) ^ (2 * m)} := by
    exact_mod_cast dens_le_dens hsub
  have hpow : 0 < a ^ (2 * m) := pow_pos ha _
  calc (dens {i | a ≤ |∑ x ∈ S, Z x (h i x)|} : ℝ)
      ≤ (m : ℝ) * (m : ℝ) ^ (2 * m) * max (∑ x ∈ S, v x) 1 ^ m / a ^ (2 * m) := by
          rw [le_div_iff₀ hpow, mul_comm]
          exact (mul_le_mul_of_nonneg_left hdens hpow.le).trans
            (hmarkov.trans (hh.expect_sum_pow_le_of_sq_le hm S Z v hv hZ hZ₁ hZ₂))
    _ = (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, v x) 1 / a ^ 2) ^ m := by
          rw [mul_div_assoc, div_pow, mul_pow, ← pow_mul, ← pow_mul]
          ring

/-- **Variance-aware tail bound for `[0, 1]`-valued scores**:
For `g x : Y → [0, 1]`, each centered variable `Z x y = g x y - 𝔼 y', g x y'` automatically
satisfies `|Z x y| ≤ 1` and `𝔼 y, (Z x y) ^ 2 ≤ 𝔼 y, g x y`, yielding concentration in terms of
the mean sum `μ = ∑ x ∈ S, 𝔼 y, g x y` rather than `#S`. -/
theorem dens_filter_le_abs_sum_sub_expect_of_Icc {m : ℕ} (hm : 1 ≤ m)
    (hh : IsKWiseIndependentHash (2 * m) h) (S : Finset X) (g : X → Y → ℝ)
    (hg : ∀ x ∈ S, ∀ y, g x y ∈ Set.Icc 0 1) {a : ℝ} (ha : 0 < a) :
    (dens {i | a ≤ |∑ x ∈ S, (g x (h i x) - 𝔼 y, g x y)|} : ℝ) ≤
      (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ x ∈ S, 𝔼 y, g x y) 1 / a ^ 2) ^ m := by
  refine hh.dens_filter_le_abs_sum_of_sq_le hm S (fun x y => g x y - 𝔼 y', g x y')
    (fun x => 𝔼 y, g x y) (fun x hx => ?_) (fun x _ => Fintype.expect_balance (g x))
    (fun x hx y => ?_) (fun x hx => ?_) ha
  · exact expect_nonneg fun y _ => (hg x hx y).1
  · have : Nonempty Y := ⟨y⟩
    have h0 : 0 ≤ 𝔼 y', g x y' := expect_nonneg fun y' _ => (hg x hx y').1
    have h1 : 𝔼 y', g x y' ≤ 1 := expect_le univ_nonempty fun y' _ => (hg x hx y').2
    rw [abs_le]
    constructor <;> linarith [(hg x hx y).1, (hg x hx y).2]
  · have : Nonempty Y := ⟨h hh.nonempty.some x⟩
    have hcard_pos : (0 : ℝ) < (Fintype.card Y : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    set μ : ℝ := 𝔼 y', g x y'
    have hμ_eq : ∑ y : Y, g x y = (Fintype.card Y : ℝ) * μ := by
      dsimp only [μ]
      rw [Finset.expect_eq_sum_div_card, card_univ, mul_div_cancel₀ _ hcard_pos.ne']
    have hsq_le : ∀ y : Y, (g x y) ^ 2 ≤ g x y := fun y => by
      have h0 := (hg x hx y).1
      have h1 := (hg x hx y).2
      nlinarith
    have hsum_id :
        ∑ y : Y, (g x y - μ) ^ 2 =
          (∑ y : Y, (g x y) ^ 2) - (Fintype.card Y : ℝ) * μ ^ 2 := by
      have hexp : ∀ y : Y, (g x y - μ) ^ 2 = (g x y) ^ 2 - 2 * μ * g x y + μ ^ 2 :=
        fun _ => by ring
      simp_rw [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
        nsmul_eq_mul, hμ_eq]
      ring
    rw [Finset.expect_eq_sum_div_card, card_univ, div_le_iff₀ hcard_pos, mul_comm μ]
    have h1 : ∑ y : Y, (g x y) ^ 2 ≤ ∑ y : Y, g x y := sum_le_sum fun y _ => hsq_le y
    have h2 : 0 ≤ (Fintype.card Y : ℝ) * μ ^ 2 := by positivity
    linarith [hsum_id, hμ_eq]

/-! ## Section 2: Multi-salt collision-freedom and batch collision-count tail bounds -/

section PairCollisions

variable {Z : Type*}

private theorem dens_biUnion_eq {α : Type*} [DecidableEq ι] (s : Finset α) (t : α → Finset ι)
    (hd : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ a ∈ s, (t a).dens := by
  simp_rw [dens, card_biUnion hd, Nat.cast_sum, sum_div]

private theorem dens_biUnion_le_sum_real {α : Type*} [DecidableEq ι] (s : Finset α)
    (t : α → Finset ι) :
    ((s.biUnion t).dens : ℝ) ≤ ∑ a ∈ s, ((t a).dens : ℝ) := by
  simp_rw [nnratCast_dens, ← sum_div, ← Nat.cast_sum]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast card_biUnion_le

/-- **Fresh-endpoint pair-collision bound under `2 * r`-wise independence**:
Suppose `a, b : Fin r → Z` satisfy `∀ k, a k ≠ b k` and `∀ j < k, a k ≠ a j ∧ a k ≠ b j` (each
`a k` is distinct from its partner `b k` and all earlier endpoints `a j, b j` for `j < k`). Then
for any `2 * r`-wise independent family `H : ι → Z → Y`,
`dens {i | ∀ k, H i (a k) = H i (b k)} ≤ (|Y|⁻¹) ^ r`. -/
theorem dens_fresh_pair_collisions_le {r : ℕ} {H : ι → Z → Y}
    (hh : IsKWiseIndependentHash (2 * r) H)
    (a b : Fin r → Z)
    (hne : ∀ k, a k ≠ b k)
    (hfresh : ∀ j k : Fin r, j < k → a k ≠ a j ∧ a k ≠ b j) :
    (dens ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) : ℝ) ≤
      ((Fintype.card Y : ℝ)⁻¹) ^ r := by
  classical
  have := hh.nonempty
  rcases isEmpty_or_nonempty Y with hY_emp | hY_ne
  · rcases Nat.eq_zero_or_pos r with rfl | hr_pos
    · simp
    · exfalso
      exact hY_emp.false (H hh.nonempty.some (a ⟨0, hr_pos⟩))
  let U_pts : Finset Z := univ.image a
  let V_pts : Finset Z := univ.image b
  let T : Finset Z := U_pts ∪ V_pts
  have ha_inj : Function.Injective a := by
    intro j k hjk
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · exact absurd hjk.symm (hfresh j k hlt).1
    · rfl
    · exact absurd hjk (hfresh k j hgt).1
  have hcard_U : #U_pts = r := by
    rw [card_image_of_injective _ ha_inj, card_univ, Fintype.card_fin]
  have hcard_T : #T ≤ 2 * r := by
    calc #T ≤ #U_pts + #V_pts := card_union_le _ _
      _ ≤ r + r := Nat.add_le_add (le_of_eq hcard_U) (card_image_le.trans (by simp))
      _ = 2 * r := (two_mul r).symm
  have hU_sub : U_pts ⊆ T := subset_union_left
  let R_rest : Finset Z := T \ U_pts
  have hcard_R : #T = r + #R_rest := by
    have hs := card_sdiff_add_card_eq_card hU_sub
    dsimp only [R_rest]
    omega
  have hmem_a (k : Fin r) : a k ∈ T := hU_sub (mem_image_of_mem _ (mem_univ k))
  have hmem_b (k : Fin r) : b k ∈ T := subset_union_right (mem_image_of_mem _ (mem_univ k))
  let GoodF : Finset (T → Y) :=
    univ.filter fun f => ∀ k : Fin r, f ⟨a k, hmem_a k⟩ = f ⟨b k, hmem_b k⟩
  let projR : (T → Y) → (R_rest → Y) := fun f z => f ⟨z.1, sdiff_subset z.2⟩
  have hinj_proj : Set.InjOn projR (GoodF : Set (T → Y)) := by
    intro f₁ hf₁ f₂ hf₂ heq
    have hf₁_eq := (mem_filter.mp hf₁).2
    have hf₂_eq := (mem_filter.mp hf₂).2
    have hk_eq : ∀ (n : ℕ) (k : Fin r), k.val = n →
        f₁ ⟨a k, hmem_a k⟩ = f₂ ⟨a k, hmem_a k⟩ := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro k hk_n
        rw [hf₁_eq k, hf₂_eq k]
        by_cases hbU : b k ∈ U_pts
        · obtain ⟨j, -, hj_eq⟩ := mem_image.mp hbU
          have hj_lt : j < k := by
            rcases lt_trichotomy j k with hlt | rfl | hgt
            · exact hlt
            · exact absurd hj_eq (hne j)
            · exact absurd hj_eq (hfresh k j hgt).2
          have hsub_eq : (⟨a j, hmem_a j⟩ : T) = ⟨b k, hmem_b k⟩ := Subtype.ext hj_eq
          rw [← hsub_eq]
          exact ih j.val (hk_n ▸ hj_lt) j rfl
        · exact congrFun heq ⟨b k, mem_sdiff.mpr ⟨hmem_b k, hbU⟩⟩
    funext z
    by_cases hzU : z.1 ∈ U_pts
    · obtain ⟨k, -, hk_z⟩ := mem_image.mp hzU
      have hsub_z : (⟨a k, hmem_a k⟩ : T) = z := Subtype.ext hk_z
      rw [← hsub_z]
      exact hk_eq k.val k rfl
    · exact congrFun heq ⟨z.1, mem_sdiff.mpr ⟨z.2, hzU⟩⟩
  have hcard_GoodF : #GoodF ≤ Fintype.card Y ^ #R_rest := by
    calc #GoodF = #(GoodF.image projR) := (card_image_of_injOn hinj_proj).symm
      _ ≤ #(univ : Finset (R_rest → Y)) := card_le_card (subset_univ _)
      _ = Fintype.card Y ^ #R_rest := by simp
  have hevent_eq :
      ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) =
        GoodF.biUnion (fun f => {i : ι | T.restrict (H i) = f}) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, GoodF]
    exact ⟨fun hi => ⟨T.restrict (H i), hi, rfl⟩, fun ⟨_, hf, rfl⟩ k => hf k⟩
  have hdisj : (GoodF : Set (T → Y)).PairwiseDisjoint
      (fun f => ({i : ι | T.restrict (H i) = f} : Finset ι)) := by
    intro f₁ _ f₂ _ hne_f
    exact disjoint_left.mpr fun i hi₁ hi₂ =>
      hne_f ((mem_filter.mp hi₁).2.symm.trans (mem_filter.mp hi₂).2)
  have hdens_q :
      dens ({i : ι | ∀ k : Fin r, H i (a k) = H i (b k)} : Finset ι) ≤
        ((Fintype.card Y : ℚ≥0)⁻¹) ^ r := by
    have hcard_Y_pos : 0 < (Fintype.card Y : ℚ≥0) := Nat.cast_pos.mpr Fintype.card_pos
    have hpow_R_ne : (Fintype.card Y : ℚ≥0) ^ #R_rest ≠ 0 := pow_ne_zero _ hcard_Y_pos.ne'
    rw [hevent_eq, dens_biUnion_eq _ _ hdisj]
    have hsum_eq :
        (∑ f ∈ GoodF, dens ({i : ι | T.restrict (H i) = f} : Finset ι)) =
          (#GoodF : ℚ≥0) * ((Fintype.card Y : ℚ≥0) ^ #T)⁻¹ := by
      simp_rw [hh.dens_filter_restrict_eq hcard_T, sum_const, nsmul_eq_mul]
    rw [hsum_eq]
    calc (#GoodF : ℚ≥0) * ((Fintype.card Y : ℚ≥0) ^ #T)⁻¹
        ≤ ((Fintype.card Y : ℚ≥0) ^ #R_rest) *
            (((Fintype.card Y : ℚ≥0) ^ r)⁻¹ * ((Fintype.card Y : ℚ≥0) ^ #R_rest)⁻¹) := by
          rw [hcard_R, pow_add, mul_inv]
          gcongr
          exact_mod_cast hcard_GoodF
      _ = ((Fintype.card Y : ℚ≥0) ^ r)⁻¹ *
            ((Fintype.card Y : ℚ≥0) ^ #R_rest * ((Fintype.card Y : ℚ≥0) ^ #R_rest)⁻¹) := by
          ring
      _ = ((Fintype.card Y : ℚ≥0)⁻¹) ^ r := by
          rw [mul_inv_cancel₀ hpow_R_ne, mul_one, inv_pow]
  simpa using (NNRat.cast_le (K := ℝ)).mpr hdens_q

/-- **Multi-salt intra-bucket collision-freedom bound**:
Under a `2 * s_max`-wise independent family `H : ι → Fin s_max × Q → Y`, the fraction of seeds `i`
for which *every* salt `s : Fin s_max` has a colliding pair `u ≠ v` inside `S_b : Finset Q` is at
most `(#S_b ^ 2 / |Y|) ^ s_max`. -/
theorem dens_forall_salt_exists_collision_le {s_max : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * s_max) H)
    (S_b : Finset Q) :
    (dens ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
      Finset ι) : ℝ) ≤ ((#S_b : ℝ) ^ 2 / Fintype.card Y) ^ s_max := by
  classical
  let Pairs := (S_b ×ˢ S_b).filter fun p => p.1 ≠ p.2
  let Tuples := piFinset fun _ : Fin s_max => Pairs
  have hsub :
      ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
        Finset ι) ⊆
        Tuples.biUnion (fun t =>
          {i : ι | ∀ s : Fin s_max, H i (s, (t s).1) = H i (s, (t s).2)}) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    choose u hu_mem v hv_mem hne hcoll using hi
    refine mem_biUnion.mpr ⟨fun s => (u s, v s), ?_, ?_⟩
    · rw [mem_piFinset]
      intro s
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hu_mem s, hv_mem s⟩, hne s⟩
    · simp only [mem_filter, mem_univ, true_and]
      exact hcoll
  have hcard_Pairs : #Pairs ≤ #S_b ^ 2 := by
    calc #Pairs ≤ #(S_b ×ˢ S_b) := card_filter_le _ _
      _ = #S_b ^ 2 := by rw [card_product, sq]
  have hcard_Tuples : (#Tuples : ℝ) ≤ ((#S_b : ℝ) ^ 2) ^ s_max := by
    have hc : #Tuples ≤ (#S_b ^ 2) ^ s_max := by
      rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
      exact Nat.pow_le_pow_left hcard_Pairs s_max
    exact_mod_cast hc
  have hstep1 :
      (dens ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
        Finset ι) : ℝ) ≤
        ∑ t ∈ Tuples,
          (dens ({i : ι | ∀ s : Fin s_max, H i (s, (t s).1) = H i (s, (t s).2)} :
            Finset ι) : ℝ) := by
    have hle : (dens ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b,
        u ≠ v ∧ H i (s, u) = H i (s, v)} : Finset ι) : ℝ) ≤
        ((Tuples.biUnion (fun t =>
          {i : ι | ∀ s : Fin s_max, H i (s, (t s).1) = H i (s, (t s).2)})).dens : ℝ) :=
      (NNRat.cast_le (K := ℝ)).mpr (dens_le_dens hsub)
    exact hle.trans (dens_biUnion_le_sum_real Tuples _)
  calc (dens ({i : ι | ∀ s : Fin s_max, ∃ u ∈ S_b, ∃ v ∈ S_b, u ≠ v ∧ H i (s, u) = H i (s, v)} :
          Finset ι) : ℝ)
      ≤ ∑ t ∈ Tuples,
          (dens ({i : ι | ∀ s : Fin s_max, H i (s, (t s).1) = H i (s, (t s).2)} :
            Finset ι) : ℝ) := hstep1
    _ ≤ ∑ _t ∈ Tuples, ((Fintype.card Y : ℝ)⁻¹) ^ s_max := by
        refine sum_le_sum fun t ht => ?_
        rw [mem_piFinset] at ht
        refine hh.dens_fresh_pair_collisions_le
          (fun s => (s, (t s).1)) (fun s => (s, (t s).2))
          (fun s h => (mem_filter.mp (ht s)).2 (congrArg Prod.snd h))
          (fun j k hjk => ⟨fun h => hjk.ne' (congrArg Prod.fst h),
            fun h => hjk.ne' (congrArg Prod.fst h)⟩)
    _ = (#Tuples : ℝ) * ((Fintype.card Y : ℝ)⁻¹) ^ s_max := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((#S_b : ℝ) ^ 2) ^ s_max * ((Fintype.card Y : ℝ)⁻¹) ^ s_max :=
        mul_le_mul_of_nonneg_right hcard_Tuples (by positivity)
    _ = ((#S_b : ℝ) ^ 2 / Fintype.card Y) ^ s_max := by
        rw [← mul_pow, div_eq_mul_inv]

/-- Greedy extraction of `r` fresh-endpoint pairs from a finite set `B` of cardinality `≥ 2 * r`
equipped with a partner function `vFn : Q → Q` satisfying `∀ u ∈ B, vFn u ≠ u`. -/
private theorem exists_fresh_chain_of_card_ge {Q : Type*}
    (r : ℕ) (B : Finset Q) (vFn : Q → Q) (hB : 2 * r ≤ #B) (hne : ∀ u ∈ B, vFn u ≠ u) :
    ∃ u : Fin r → Q,
      (∀ k, u k ∈ B) ∧
      (∀ j k : Fin r, j < k → u k ≠ u j ∧ u k ≠ vFn (u j)) := by
  classical
  induction r generalizing B with
  | zero =>
    exact ⟨Fin.elim0, fun k => k.elim0, fun j => j.elim0⟩
  | succ r ih =>
    have hB_ne : B.Nonempty := card_pos.mp (by omega)
    let u₀ := hB_ne.choose
    have hu₀ : u₀ ∈ B := hB_ne.choose_spec
    let B' := (B.erase u₀).erase (vFn u₀)
    have hcard_B' : 2 * r ≤ #B' := by
      have h1 : #(B.erase u₀) = #B - 1 := card_erase_of_mem hu₀
      have h2 : #(B.erase u₀) - 1 ≤ #B' := pred_card_le_card_erase
      omega
    have hne' : ∀ u ∈ B', vFn u ≠ u := fun u hu =>
      hne u (mem_of_mem_erase (mem_of_mem_erase hu))
    obtain ⟨u_tail, hmem_tail, hfresh_tail⟩ := ih B' hcard_B' hne'
    refine ⟨Fin.cons u₀ u_tail, ?_, ?_⟩
    · intro k
      refine Fin.cases hu₀ (fun k' => ?_) k
      exact mem_of_mem_erase (mem_of_mem_erase (hmem_tail k'))
    · intro j k hjk
      cases k using Fin.cases with
      | zero => exact absurd hjk (Nat.not_lt_zero _)
      | succ k' =>
        cases j using Fin.cases with
        | zero =>
          simp only [Fin.cons_succ, Fin.cons_zero]
          have hm := hmem_tail k'
          dsimp only [B'] at hm
          have hnot_v : u_tail k' ≠ vFn u₀ := ne_of_mem_erase hm
          have hnot_u : u_tail k' ≠ u₀ := ne_of_mem_erase (mem_of_mem_erase hm)
          exact ⟨hnot_u, hnot_v⟩
        | succ j' =>
          simp only [Fin.cons_succ]
          exact hfresh_tail j' k' (Fin.succ_lt_succ_iff.mp hjk)

/-- **Batch salt-collision count tail bound**:
Under a `2 * r`-wise independent family `H : ι → Fin s_max × Q → Y`, given a batch
`Q_set : Finset Q` and a window `W_set : Finset Q`, the fraction of seeds `i` for which at least
`2 * r` keys `u ∈ Q_set` collide with some `v ∈ W_set \ {u}` under some salt `s : Fin s_max` is at
most `((#Q_set * #W_set * s_max) / |Y|) ^ r`. -/
theorem dens_card_salt_colliding_ge_le {r s_max : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * r) H)
    (Q_set W_set : Finset Q) :
    (dens ({i : ι | 2 * r ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (((#Q_set * #W_set * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · simp only [pow_zero]
    exact_mod_cast Finset.dens_le_one (s := ({i : ι | 2 * 0 ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι))
  let Triples := ((Q_set ×ˢ W_set).filter fun p => p.1 ≠ p.2) ×ˢ (univ : Finset (Fin s_max))
  let Chains := (piFinset fun _ : Fin r => Triples).filter fun t =>
    ∀ j k : Fin r, j < k → (t k).1.1 ≠ (t j).1.1 ∧ (t k).1.1 ≠ (t j).1.2
  have hsub :
      ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) ⊆
        Chains.biUnion (fun t =>
          {i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)}) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    set B := Q_set.filter fun u =>
      ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v)
    have hB_ne : B.Nonempty := card_pos.mp (by omega)
    have hex_wit : ∀ u, ∃ vs : Q × Fin s_max,
        u ∈ B → vs.1 ∈ W_set ∧ u ≠ vs.1 ∧ H i (vs.2, u) = H i (vs.2, vs.1) := by
      intro u
      by_cases hu : u ∈ B
      · obtain ⟨_, v, hvW, hne_uv, s, hcoll⟩ := mem_filter.mp hu
        exact ⟨(v, s), fun _ => ⟨hvW, hne_uv, hcoll⟩⟩
      · have ⟨_, v₀, _, _, s₀, _⟩ := mem_filter.mp hB_ne.choose_spec
        exact ⟨(v₀, s₀), fun h => absurd h hu⟩
    choose vs hvs using hex_wit
    obtain ⟨u_ch, hu_mem, hfresh⟩ := exists_fresh_chain_of_card_ge r B (fun u => (vs u).1) hi
      (fun u hu => (hvs u hu).2.1.symm)
    refine mem_biUnion.mpr ⟨fun k => ((u_ch k, (vs (u_ch k)).1), (vs (u_ch k)).2), ?_, ?_⟩
    · refine mem_filter.mpr ⟨mem_piFinset.mpr fun k => ?_, fun j k hjk => hfresh j k hjk⟩
      have hkB := hu_mem k
      have hkQ := (mem_filter.mp hkB).1
      obtain ⟨hvW, hne_uv, _⟩ := hvs (u_ch k) hkB
      exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨hkQ, hvW⟩, hne_uv⟩, mem_univ _⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro k
      exact (hvs (u_ch k) (hu_mem k)).2.2
  have hcard_Triples : #Triples ≤ #Q_set * #W_set * s_max := by
    calc #Triples = #((Q_set ×ˢ W_set).filter fun p => p.1 ≠ p.2) * s_max := by
            simp [Triples, card_product]
      _ ≤ #(Q_set ×ˢ W_set) * s_max := Nat.mul_le_mul_right _ (card_filter_le _ _)
      _ = #Q_set * #W_set * s_max := by rw [card_product]
  have hcard_Chains : (#Chains : ℝ) ≤ ((#Q_set * #W_set * s_max : ℕ) : ℝ) ^ r := by
    have hc : #Chains ≤ (#Q_set * #W_set * s_max) ^ r := by
      calc #Chains ≤ #(piFinset fun _ : Fin r => Triples) := card_filter_le _ _
        _ = #Triples ^ r := by rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
        _ ≤ (#Q_set * #W_set * s_max) ^ r := Nat.pow_le_pow_left hcard_Triples r
    exact_mod_cast hc
  have hstep1 :
      (dens ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
        ∑ t ∈ Chains,
          (dens ({i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)} :
            Finset ι) : ℝ) := by
    have hle : (dens ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
        ((Chains.biUnion (fun t =>
          {i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)})).dens : ℝ) :=
      (NNRat.cast_le (K := ℝ)).mpr (dens_le_dens hsub)
    exact hle.trans (dens_biUnion_le_sum_real Chains _)
  calc (dens ({i : ι | 2 * r ≤
          #(Q_set.filter fun u =>
            ∃ v ∈ W_set, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ)
      ≤ ∑ t ∈ Chains,
          (dens ({i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)} :
            Finset ι) : ℝ) := hstep1
    _ ≤ ∑ _t ∈ Chains, ((Fintype.card Y : ℝ)⁻¹) ^ r := by
        refine sum_le_sum fun t ht => ?_
        obtain ⟨ht_pi, ht_fr⟩ := mem_filter.mp ht
        rw [mem_piFinset] at ht_pi
        refine hh.dens_fresh_pair_collisions_le
          (fun k => ((t k).2, (t k).1.1)) (fun k => ((t k).2, (t k).1.2))
          (fun k h => (mem_filter.mp (mem_product.mp (ht_pi k)).1).2 (congrArg Prod.snd h))
          (fun j k hjk => ⟨fun h => (ht_fr j k hjk).1 (congrArg Prod.snd h),
            fun h => (ht_fr j k hjk).2 (congrArg Prod.snd h)⟩)
    _ = (#Chains : ℝ) * ((Fintype.card Y : ℝ)⁻¹) ^ r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((#Q_set * #W_set * s_max : ℕ) : ℝ) ^ r * ((Fintype.card Y : ℝ)⁻¹) ^ r :=
        mul_le_mul_of_nonneg_right hcard_Chains (by positivity)
    _ = (((#Q_set * #W_set * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r := by
        rw [← mul_pow, div_eq_mul_inv]

/-- **Per-key neighborhood salt-collision count tail bound**:
Under a `2 * r`-wise independent family `H : ι → Fin s_max × Q → Y`, given a batch
`Q_set : Finset Q` and per-key candidate collision sets `W_of : Q → Finset Q` with
`∀ u ∈ Q_set, #(W_of u) ≤ w_cap`, the fraction of seeds `i` for which at least `2 * r` keys
`u ∈ Q_set` collide with some `v ∈ W_of u \ {u}` under some salt `s : Fin s_max` is at most
`(((#Q_set * w_cap * s_max) / |Y|) ^ r)`. -/
theorem dens_card_local_salt_colliding_ge_le {r s_max w_cap : ℕ} {Q : Type*} [DecidableEq Q]
    {H : ι → Fin s_max × Q → Y} (hh : IsKWiseIndependentHash (2 * r) H)
    (Q_set : Finset Q) (W_of : Q → Finset Q)
    (hw_cap : ∀ u ∈ Q_set, #(W_of u) ≤ w_cap) :
    (dens ({i : ι | 2 * r ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
      (((#Q_set * w_cap * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · simp only [pow_zero]
    exact_mod_cast Finset.dens_le_one (s := ({i : ι | 2 * 0 ≤
      #(Q_set.filter fun u =>
        ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι))
  let Pairs := Q_set.biUnion fun u => ({u} : Finset Q) ×ˢ ((W_of u).erase u)
  let Triples := Pairs ×ˢ (univ : Finset (Fin s_max))
  let Chains := (piFinset fun _ : Fin r => Triples).filter fun t =>
    ∀ j k : Fin r, j < k → (t k).1.1 ≠ (t j).1.1 ∧ (t k).1.1 ≠ (t j).1.2
  have hsub :
      ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) ⊆
        Chains.biUnion (fun t =>
          {i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)}) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    set B := Q_set.filter fun u =>
      ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v)
    have hB_ne : B.Nonempty := card_pos.mp (by omega)
    have hex_wit : ∀ u, ∃ vs : Q × Fin s_max,
        u ∈ B → vs.1 ∈ W_of u ∧ u ≠ vs.1 ∧ H i (vs.2, u) = H i (vs.2, vs.1) := by
      intro u
      by_cases hu : u ∈ B
      · obtain ⟨_, v, hvW, hne_uv, s, hcoll⟩ := mem_filter.mp hu
        exact ⟨(v, s), fun _ => ⟨hvW, hne_uv, hcoll⟩⟩
      · have ⟨_, v₀, _, _, s₀, _⟩ := mem_filter.mp hB_ne.choose_spec
        exact ⟨(v₀, s₀), fun h => absurd h hu⟩
    choose vs hvs using hex_wit
    obtain ⟨u_ch, hu_mem, hfresh⟩ := exists_fresh_chain_of_card_ge r B (fun u => (vs u).1) hi
      (fun u hu => (hvs u hu).2.1.symm)
    refine mem_biUnion.mpr ⟨fun k => ((u_ch k, (vs (u_ch k)).1), (vs (u_ch k)).2), ?_, ?_⟩
    · refine mem_filter.mpr ⟨mem_piFinset.mpr fun k => ?_, fun j k hjk => hfresh j k hjk⟩
      have hkB := hu_mem k
      have hkQ := (mem_filter.mp hkB).1
      obtain ⟨hvW, hne_uv, _⟩ := hvs (u_ch k) hkB
      refine mem_product.mpr ⟨mem_biUnion.mpr ⟨u_ch k, hkQ, ?_⟩, mem_univ _⟩
      exact mem_product.mpr ⟨mem_singleton_self _, mem_erase.mpr ⟨hne_uv.symm, hvW⟩⟩
    · simp only [mem_filter, mem_univ, true_and]
      intro k
      exact (hvs (u_ch k) (hu_mem k)).2.2
  have hcard_Pairs : #Pairs ≤ #Q_set * w_cap := by
    calc #Pairs ≤ ∑ u ∈ Q_set, #( ({u} : Finset Q) ×ˢ ((W_of u).erase u) ) := card_biUnion_le
      _ ≤ ∑ _u ∈ Q_set, w_cap := by
          refine sum_le_sum fun u hu => ?_
          rw [card_product, card_singleton, one_mul]
          exact card_erase_le.trans (hw_cap u hu)
      _ = #Q_set * w_cap := by rw [sum_const, smul_eq_mul]
  have hcard_Triples : #Triples ≤ #Q_set * w_cap * s_max := by
    calc #Triples = #Pairs * s_max := by simp [Triples, card_product]
      _ ≤ (#Q_set * w_cap) * s_max := Nat.mul_le_mul_right _ hcard_Pairs
  have hcard_Chains : (#Chains : ℝ) ≤ ((#Q_set * w_cap * s_max : ℕ) : ℝ) ^ r := by
    have hc : #Chains ≤ (#Q_set * w_cap * s_max) ^ r := by
      calc #Chains ≤ #(piFinset fun _ : Fin r => Triples) := card_filter_le _ _
        _ = #Triples ^ r := by rw [card_piFinset, prod_const, card_univ, Fintype.card_fin]
        _ ≤ (#Q_set * w_cap * s_max) ^ r := Nat.pow_le_pow_left hcard_Triples r
    exact_mod_cast hc
  have hstep1 :
      (dens ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
        ∑ t ∈ Chains,
          (dens ({i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)} :
            Finset ι) : ℝ) := by
    have hle : (dens ({i : ι | 2 * r ≤
        #(Q_set.filter fun u =>
          ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ) ≤
        ((Chains.biUnion (fun t =>
          {i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)})).dens : ℝ) :=
      (NNRat.cast_le (K := ℝ)).mpr (dens_le_dens hsub)
    exact hle.trans (dens_biUnion_le_sum_real Chains _)
  calc (dens ({i : ι | 2 * r ≤
          #(Q_set.filter fun u =>
            ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin s_max, H i (s, u) = H i (s, v))} : Finset ι) : ℝ)
      ≤ ∑ t ∈ Chains,
          (dens ({i : ι | ∀ k : Fin r, H i ((t k).2, (t k).1.1) = H i ((t k).2, (t k).1.2)} :
            Finset ι) : ℝ) := hstep1
    _ ≤ ∑ _t ∈ Chains, ((Fintype.card Y : ℝ)⁻¹) ^ r := by
        refine sum_le_sum fun t ht => ?_
        obtain ⟨ht_pi, ht_fr⟩ := mem_filter.mp ht
        rw [mem_piFinset] at ht_pi
        refine hh.dens_fresh_pair_collisions_le
          (fun k => ((t k).2, (t k).1.1)) (fun k => ((t k).2, (t k).1.2))
          (fun k h => ?_)
          (fun j k hjk => ⟨fun h => (ht_fr j k hjk).1 (congrArg Prod.snd h),
            fun h => (ht_fr j k hjk).2 (congrArg Prod.snd h)⟩)
        obtain ⟨u, _, hp⟩ := mem_biUnion.mp (mem_product.mp (ht_pi k)).1
        obtain ⟨hu_eq, hv_er⟩ := mem_product.mp hp
        rw [mem_singleton.mp hu_eq] at h
        exact (mem_erase.mp hv_er).1 (congrArg Prod.snd h).symm
    _ = (#Chains : ℝ) * ((Fintype.card Y : ℝ)⁻¹) ^ r := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((#Q_set * w_cap * s_max : ℕ) : ℝ) ^ r * ((Fintype.card Y : ℝ)⁻¹) ^ r :=
        mul_le_mul_of_nonneg_right hcard_Chains (by positivity)
    _ = (((#Q_set * w_cap * s_max : ℕ) : ℝ) / Fintype.card Y) ^ r := by
        rw [← mul_pow, div_eq_mul_inv]

end PairCollisions

end IsKWiseIndependentHash

end Cslib.Probability

end


