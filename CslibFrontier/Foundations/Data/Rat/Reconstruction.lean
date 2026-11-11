/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib / Cslib, Wang rational reconstruction and height bounds)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Rat.Basic
public import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rational reconstruction, height bounds, and Chinese-remainder recovery

Implements Wang's extended-Euclidean rational reconstruction `Rat.reconstruct` over `ℤ / Mℤ`,
rational height bounds (`Rat.height`), uniqueness modulo `M` below the `2 * N * D < M` threshold,
completeness of Euclidean reconstruction under height/denominator bounds, and multi-modulus
Chinese-remainder rational recovery (`Rat.reconstructPi`) across pairwise coprime moduli (such as
finite-field primes `ZMod pᵢ`).

## Main definitions

* `Rat.height`: multiplicative rational height `max q.num.natAbs q.den`.
* `Rat.reconstruct`: extended-Euclidean rational reconstruction modulo `M` with numerator bound `N`
  and denominator bound `D`.
* `Rat.reconstructPi`: Chinese-remainder rational reconstruction from residues modulo pairwise
  coprime moduli `m : Fin k → ℕ`.

## Main results

* `Rat.eq_of_modEq_of_bounds`, `Rat.eq_of_modEq_of_height_mul_lt`: modular uniqueness of
  rationals with bounded numerator/denominator or bounded height product.
* `Rat.height_add_le`, `Rat.height_mul_le`, `Rat.height_inv`: arithmetic height bounds.
* `Rat.reconstruct_eq_some`: soundness (numerator, denominator, coprimality, and modular
  congruence invariants of every reconstructed rational).
* `Rat.reconstruct_of_eq`: completeness (recovering `some q` whenever `2 * N * D < M` and
  `q.den.Coprime M`).
* `Rat.reconstructPi_of_eq`: exact recovery from residues in `∀ i, ZMod (m i)`.

## References

* [P. S. Wang, *A p-adic Algorithm for Univariate Partial Fractions*][Wang1981]
* [J. von zur Gathen, J. Gerhard, *Modern Computer Algebra*][vonZurGathenGerhard2013], §5.10.
-/

public section

namespace Rat

open Finset

section HeightAndUniqueness

/-- Multiplicative height `max |num| den` of a rational number `q`. -/
@[expose] def height (q : ℚ) : ℕ :=
  max q.num.natAbs q.den

theorem height_def (q : ℚ) : q.height = max q.num.natAbs q.den :=
  rfl

theorem natAbs_num_le_height (q : ℚ) : q.num.natAbs ≤ height q :=
  le_max_left _ _

theorem den_le_height (q : ℚ) : q.den ≤ height q :=
  le_max_right _ _

theorem one_le_height (q : ℚ) : 1 ≤ height q :=
  le_trans q.den_nz.bot_lt (den_le_height q)

@[simp]
theorem height_zero : height 0 = 1 := by
  simp [height]

@[simp]
theorem height_one : height 1 = 1 := by
  simp [height]

@[simp]
theorem height_neg (q : ℚ) : height (-q) = height q := by
  simp [height]

private theorem mul_eq_mul_of_divInt_eq {r t : ℤ} {q : ℚ} (ht : t ≠ 0)
    (h : Rat.divInt r t = q) : q.num * t = r * (q.den : ℤ) := by
  have hnum_den : (q.num : ℚ) / (q.den : ℚ) = (r : ℚ) / (t : ℚ) := by
    rw [Rat.num_div_den, ← h, Rat.divInt_eq_div]
  have hden_q : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have ht_q : (t : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ht
  have heq : (q.num : ℚ) * (t : ℚ) = (r : ℚ) * (q.den : ℚ) :=
    (div_eq_div_iff hden_q ht_q).mp hnum_den
  exact_mod_cast heq

theorem height_inv {q : ℚ} (hq : q ≠ 0) : height q⁻¹ = height q := by
  have hnum_nz : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hinv_num : (q⁻¹).num.natAbs = q.den := by
    rw [Rat.num_inv, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hnum_nz, Int.natAbs_natCast,
      one_mul]
  rw [height, height, hinv_num, Rat.den_inv_of_ne_zero hq, max_comm]

theorem height_divInt_le (a b : ℤ) (hb : b ≠ 0) :
    height (Rat.divInt a b) ≤ max a.natAbs b.natAbs :=
  max_le (le_trans (Rat.natAbs_num_divInt_le a b hb) (le_max_left _ _))
    (le_trans (Rat.den_divInt_le a b hb) (le_max_right _ _))

private theorem den_mul_ne_zero (p q : ℚ) : (p.den : ℤ) * (q.den : ℤ) ≠ 0 :=
  mul_ne_zero (Int.natCast_ne_zero.mpr p.den_nz) (Int.natCast_ne_zero.mpr q.den_nz)

private theorem cross_natAbs_mul_le (p q : ℚ) :
    (p.num * (q.den : ℤ)).natAbs + (q.num * (p.den : ℤ)).natAbs ≤ 2 * height p * height q := by
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  have h1 : p.num.natAbs * q.den ≤ height p * height q :=
    Nat.mul_le_mul (natAbs_num_le_height p) (den_le_height q)
  have h2 : q.num.natAbs * p.den ≤ height p * height q :=
    (Nat.mul_le_mul (natAbs_num_le_height q) (den_le_height p)).trans_eq (mul_comm _ _)
  have h2eq : 2 * height p * height q = height p * height q + height p * height q := by ring
  omega

theorem height_mul_le (p q : ℚ) : height (p * q) ≤ height p * height q := by
  have hmul : p * q = Rat.divInt (p.num * q.num) ((p.den : ℤ) * (q.den : ℤ)) := by
    rw [Rat.divInt_eq_div]
    push_cast
    conv_lhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
    ring
  rw [hmul]
  refine (height_divInt_le _ _ (den_mul_ne_zero p q)).trans (max_le ?_ ?_)
  · rw [Int.natAbs_mul]
    exact Nat.mul_le_mul (natAbs_num_le_height p) (natAbs_num_le_height q)
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.mul_le_mul (den_le_height p) (den_le_height q)

theorem height_add_le (p q : ℚ) : height (p + q) ≤ 2 * height p * height q := by
  have hadd : p + q =
      Rat.divInt (p.num * (q.den : ℤ) + q.num * (p.den : ℤ)) ((p.den : ℤ) * (q.den : ℤ)) := by
    rw [Rat.divInt_eq_div]
    push_cast
    conv_lhs => rw [← Rat.num_div_den p, ← Rat.num_div_den q]
    have hp : (p.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.den_nz
    have hq : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    rw [div_add_div _ _ hp hq]
    ring
  rw [hadd]
  refine (height_divInt_le _ _ (den_mul_ne_zero p q)).trans (max_le ?_ ?_)
  · exact (Int.natAbs_add_le _ _).trans (cross_natAbs_mul_le p q)
  · rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
    have h12 : p.den * q.den ≤ height p * height q :=
      Nat.mul_le_mul (den_le_height p) (den_le_height q)
    have h2eq : 2 * height p * height q = height p * height q + height p * height q := by ring
    omega

private theorem div_eq_div_of_modEq_of_cross_lt {M : ℕ} {a₁ a₂ : ℤ} {b₁ b₂ : ℕ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hlt : (a₁ * (b₂ : ℤ) - a₂ * (b₁ : ℤ)).natAbs < M)
    (hmod : a₁ * (b₂ : ℤ) ≡ a₂ * (b₁ : ℤ) [ZMOD M]) :
    (a₁ : ℚ) / (b₁ : ℚ) = (a₂ : ℚ) / (b₂ : ℚ) := by
  have hdvd : (M : ℤ) ∣ a₁ * (b₂ : ℤ) - a₂ * (b₁ : ℤ) := Int.modEq_iff_dvd.mp hmod.symm
  have hzero : a₁ * (b₂ : ℤ) - a₂ * (b₁ : ℤ) = 0 := by
    by_contra hne
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)
    omega
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr hb₁.ne') (Nat.cast_ne_zero.mpr hb₂.ne')]
  exact_mod_cast sub_eq_zero.mp hzero

/-- Uniqueness of modular rational recovery: if `a₁ * b₂ ≡ a₂ * b₁ [ZMOD M]` with
`|aᵢ| ≤ N`, `0 < bᵢ ≤ D`, and `2 * N * D < M`, then `(a₁ : ℚ) / b₁ = (a₂ : ℚ) / b₂`. -/
theorem eq_of_modEq_of_bounds {M N D : ℕ} {a₁ a₂ : ℤ} {b₁ b₂ : ℕ}
    (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (ha₁ : a₁.natAbs ≤ N) (ha₂ : a₂.natAbs ≤ N)
    (hbd₁ : b₁ ≤ D) (hbd₂ : b₂ ≤ D) (hM : 2 * N * D < M)
    (hmod : a₁ * (b₂ : ℤ) ≡ a₂ * (b₁ : ℤ) [ZMOD M]) :
    (a₁ : ℚ) / (b₁ : ℚ) = (a₂ : ℚ) / (b₂ : ℚ) := by
  refine div_eq_div_of_modEq_of_cross_lt hb₁ hb₂ ?_ hmod
  have h2eq : 2 * N * D = N * D + N * D := by ring
  refine lt_of_le_of_lt ((Int.natAbs_sub_le _ _).trans ?_) hM
  rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast]
  have h1 : a₁.natAbs * b₂ ≤ N * D := Nat.mul_le_mul ha₁ hbd₂
  have h2 : a₂.natAbs * b₁ ≤ N * D := Nat.mul_le_mul ha₂ hbd₁
  omega

/-- Modular uniqueness stated directly in terms of rational heights: if `p, q : ℚ` satisfy
`(p.num : ZMod M) * (q.den : ZMod M) = (q.num : ZMod M) * (p.den : ZMod M)` and
`2 * height p * height q < M`, then `p = q`. -/
theorem eq_of_modEq_of_height_mul_lt {M : ℕ} {p q : ℚ}
    (hM : 2 * height p * height q < M)
    (hmod : p.num * (q.den : ℤ) ≡ q.num * (p.den : ℤ) [ZMOD M]) : p = q := by
  rw [← Rat.num_div_den p, ← Rat.num_div_den q]
  refine div_eq_div_of_modEq_of_cross_lt p.den_pos q.den_pos ?_ hmod
  exact lt_of_le_of_lt ((Int.natAbs_sub_le _ _).trans (cross_natAbs_mul_le p q)) hM

end HeightAndUniqueness

section WangReconstruction

private structure EuclidState where
  r0 : ℤ
  t0 : ℤ
  r1 : ℤ
  t1 : ℤ

private def reconstructLoop (N : ℕ) (r0 t0 r1 t1 : ℤ) : EuclidState :=
  if h : (N : ℤ) < r1 then
    let q := r0 / r1
    let r2 := r0 % r1
    let t2 := t0 - q * t1
    have _ : r2.toNat < r1.toNat := by
      have hpos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) h
      have hlt := Int.emod_lt_of_pos r0 hpos
      have hnneg := Int.emod_nonneg r0 hpos.ne'
      omega
    reconstructLoop N r1 t1 r2 t2
  else
    ⟨r0, t0, r1, t1⟩
termination_by r1.toNat

private structure StepInv (M : ℕ) (u r0 t0 r1 t1 : ℤ) : Prop where
  r0_pos : 0 < r0
  r1_nonneg : 0 ≤ r1
  r1_lt : r1 < r0
  mod0 : r0 ≡ t0 * u [ZMOD M]
  mod1 : r1 ≡ t1 * u [ZMOD M]
  t_sign : t0 * t1 ≤ 0
  t1_ne : t1 ≠ 0
  bezout : ∃ s : ℤ, s * s = 1 ∧ r0 * t1 - r1 * t0 = s * (M : ℤ)

private theorem t_prod_neg_step {r0 t0 r1 t1 : ℤ} (ht_sign : t0 * t1 ≤ 0) (ht1_ne : t1 ≠ 0)
    (hr1_pos : 0 < r1) (hr1_lt : r1 < r0) : t1 * (t0 - (r0 / r1) * t1) ≤ -1 := by
  have hdiv_ge : 1 ≤ r0 / r1 :=
    Int.le_ediv_of_mul_le hr1_pos (by simpa only [one_mul] using le_of_lt hr1_lt)
  have ht1_sq : 1 ≤ t1 * t1 := by
    by_cases hneg : t1 < 0
    · nlinarith
    · have hpos : 0 < t1 := lt_of_le_of_ne (not_lt.mp hneg) ht1_ne.symm
      nlinarith
  have hmul_eq : t1 * (t0 - (r0 / r1) * t1) = t0 * t1 - (r0 / r1) * (t1 * t1) := by ring
  rw [hmul_eq]
  have hq : 1 * (t1 * t1) ≤ (r0 / r1) * (t1 * t1) :=
    mul_le_mul_of_nonneg_right hdiv_ge (by nlinarith)
  linarith

private theorem stepInv_step {M N : ℕ} {u r0 t0 r1 t1 : ℤ}
    (hinv : StepInv M u r0 t0 r1 t1) (hlt : (N : ℤ) < r1) :
    StepInv M u r1 t1 (r0 % r1) (t0 - (r0 / r1) * t1) := by
  have hr1_pos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
  have hprod := t_prod_neg_step hinv.t_sign hinv.t1_ne hr1_pos hinv.r1_lt
  have heq : r0 % r1 = r0 - (r0 / r1) * r1 := by
    have h := Int.mul_ediv_add_emod r0 r1
    linarith
  refine
    { r0_pos := hr1_pos
      r1_nonneg := Int.emod_nonneg r0 hr1_pos.ne'
      r1_lt := Int.emod_lt_of_pos r0 hr1_pos
      mod0 := hinv.mod1
      mod1 := by
        rw [heq]
        simpa only [sub_mul, mul_assoc] using hinv.mod0.sub ((hinv.mod1).mul_left (r0 / r1))
      t_sign := by linarith
      t1_ne := by
        intro ht2
        rw [ht2, mul_zero] at hprod
        omega
      bezout := ?_ }
  rcases hinv.bezout with ⟨s, hs1, hs2⟩
  refine ⟨-s, by linear_combination hs1, ?_⟩
  rw [heq]
  linear_combination -hs2

private theorem reconstructLoop_spec {M N : ℕ} {u r0 t0 r1 t1 : ℤ}
    (hinv : StepInv M u r0 t0 r1 t1) :
    let st := reconstructLoop N r0 t0 r1 t1
    StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧
      ((st.r0 = r0 ∧ st.t0 = t0 ∧ st.r1 = r1 ∧ st.t1 = t1) ∨
        ((N : ℤ) < st.r0 ∧ st.t0 * st.t1 < 0)) := by
  unfold reconstructLoop
  split_ifs with hlt
  · have hinv' := stepInv_step hinv hlt
    have ih := reconstructLoop_spec (M := M) (N := N) (u := u) hinv'
    dsimp only at ih ⊢
    rcases ih with ⟨hs, hle, hor⟩
    refine ⟨hs, hle, Or.inr ?_⟩
    rcases hor with ⟨hr0_eq, ht0_eq, hr1_eq, ht1_eq⟩ | hrec
    · refine ⟨by rw [hr0_eq]; exact hlt, ?_⟩
      rw [ht0_eq, ht1_eq]
      have hr1_pos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
      exact lt_of_le_of_lt (t_prod_neg_step hinv.t_sign hinv.t1_ne hr1_pos hinv.r1_lt) (by norm_num)
    · exact hrec
  · refine ⟨hinv, not_lt.mp hlt, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
termination_by r1.toNat
decreasing_by
  have hpos : 0 < r1 := lt_of_le_of_lt (Int.natCast_nonneg N) hlt
  have hlt' := Int.emod_lt_of_pos r0 hpos
  have _hnneg := Int.emod_nonneg r0 hpos.ne'
  omega

/-- Wang's extended-Euclidean rational reconstruction modulo `M`. Returns `some q` when the
Euclidean sequence first reaches remainder `r ≤ N` with cofactor `t` satisfying `|t| ≤ D` and
`Nat.Coprime t.natAbs M`. -/
def reconstruct (M : ℕ) (u : ℤ) (N D : ℕ) : Option ℚ :=
  if M = 0 then none
  else
    let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
    if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
      some (Rat.divInt st.r1 st.t1)
    else
      none

private theorem initial_stepInv {M : ℕ} (hM : 0 < M) (u : ℤ) :
    StepInv M u (M : ℤ) 0 (u % (M : ℤ)) 1 := by
  have hMz : (0 : ℤ) < (M : ℤ) := Int.natCast_pos.mpr hM
  refine
    { r0_pos := hMz
      r1_nonneg := Int.emod_nonneg u hMz.ne'
      r1_lt := Int.emod_lt_of_pos u hMz
      mod0 := by simp [Int.ModEq]
      mod1 := by
        show u % (M : ℤ) ≡ 1 * u [ZMOD M]
        rw [one_mul, Int.ModEq, Int.emod_emod]
      t_sign := by simp
      t1_ne := one_ne_zero
      bezout := ⟨1, rfl, by ring⟩ }

private theorem sq_eq_one_natAbs {s : ℤ} (hs : s * s = 1) : s.natAbs = 1 := by
  have h := congrArg Int.natAbs hs
  rw [Int.natAbs_mul, Int.natAbs_one] at h
  exact (mul_eq_one.mp h).1

/-- Soundness of `Rat.reconstruct`: every output `q` satisfies `|q.num| ≤ N`, `q.den ≤ D`,
`Nat.Coprime q.den M`, and `q.num ≡ u * q.den [ZMOD M]`. -/
theorem reconstruct_eq_some {M N D : ℕ} {u : ℤ} {q : ℚ}
    (hq : reconstruct M u N D = some q) :
    0 < M ∧ q.num.natAbs ≤ N ∧ q.den ≤ D ∧ Nat.Coprime q.den M ∧
      q.num ≡ u * (q.den : ℤ) [ZMOD M] := by
  rw [reconstruct] at hq
  by_cases hM : M = 0
  · simp [hM] at hq
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM
    simp only [hM, ↓reduceIte] at hq
    let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
    change (if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
      some (Rat.divInt st.r1 st.t1) else none) = some q at hq
    split_ifs at hq with hcond
    rcases of_decide_eq_true hcond with ⟨htD, htM⟩
    have hqr : Rat.divInt st.r1 st.t1 = q := Option.some.inj hq
    have hspec := reconstructLoop_spec (N := N) (initial_stepInv hMpos u)
    change StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧ _ at hspec
    rcases hspec with ⟨hinv, hrN, _⟩
    have hcop_rt : Nat.Coprime st.r1.natAbs st.t1.natAbs := by
      refine Nat.coprime_of_dvd fun p hp_prime hpr hpt => ?_
      rcases hinv.bezout with ⟨s, hs1, hs2⟩
      have hpz_M : (p : ℤ) ∣ s * (M : ℤ) := by
        rw [← hs2]
        exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hpt) st.r0)
          (dvd_mul_of_dvd_left (Int.natCast_dvd.mpr hpr) st.t0)
      have hp_M : p ∣ M := by
        have h1 := Int.natAbs_dvd_natAbs.mpr hpz_M
        rw [Int.natAbs_mul, Int.natAbs_natCast, sq_eq_one_natAbs hs1, one_mul,
          Int.natAbs_natCast] at h1
        exact h1
      exact hp_prime.ne_one (Nat.eq_one_of_dvd_one (htM ▸ Nat.dvd_gcd hpt hp_M))
    have hrabs : st.r1.natAbs ≤ N := by
      have := hinv.r1_nonneg
      omega
    have hq_num : q.num.natAbs = st.r1.natAbs := by
      rw [← hqr, Rat.natAbs_num_divInt_of_ne_zero _ _ hinv.t1_ne, hcop_rt, Nat.div_one]
    have heqz : q.num * st.t1 = st.r1 * (q.den : ℤ) :=
      mul_eq_mul_of_divInt_eq hinv.t1_ne hqr
    have hq_den : q.den = st.t1.natAbs := by
      have hn := congrArg Int.natAbs heqz
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, hq_num] at hn
      by_cases hr0 : st.r1 = 0
      · have hd : st.t1.natAbs ∣ M := by
          rcases hinv.bezout with ⟨s, hs1, hs2⟩
          rw [hr0, zero_mul, sub_zero] at hs2
          have hd' : st.t1.natAbs ∣ (st.r0 * st.t1).natAbs := by
            rw [Int.natAbs_mul]
            exact dvd_mul_left _ _
          rw [hs2, Int.natAbs_mul, Int.natAbs_natCast, sq_eq_one_natAbs hs1, one_mul] at hd'
          exact hd'
        have htd : st.t1.natAbs = 1 := Nat.eq_one_of_dvd_one (htM ▸ Nat.dvd_gcd dvd_rfl hd)
        have hq0 : q = 0 := by rw [← hqr, hr0, Rat.zero_divInt]
        rw [hq0, Rat.den_zero, htd]
      · exact (Nat.mul_left_cancel (Int.natAbs_pos.mpr hr0) hn).symm
    have hq_mod : q.num ≡ u * (q.den : ℤ) [ZMOD M] := by
      have hmul : q.num * st.t1 ≡ u * (q.den : ℤ) * st.t1 [ZMOD M] := by
        rw [heqz]
        calc
          st.r1 * (q.den : ℤ) ≡ (st.t1 * u) * (q.den : ℤ) [ZMOD M] := hinv.mod1.mul_right _
          _ = u * (q.den : ℤ) * st.t1 := by ring
      have hzmod :
          ((q.num : ZMod M) - ((u * (q.den : ℤ) : ℤ) : ZMod M)) * (st.t1 : ZMod M) = 0 := by
        have hm := (ZMod.intCast_eq_intCast_iff _ _ M).mpr hmul
        push_cast at hm ⊢
        linear_combination hm
      have hunit : IsUnit (st.t1 : ZMod M) := by
        have hz : ((st.t1 : ZMod M)) = (st.t1.sign : ZMod M) * (st.t1.natAbs : ZMod M) := by
          rw [← Int.cast_natCast st.t1.natAbs, ← Int.cast_mul, Int.sign_mul_natAbs]
        rw [hz]
        refine IsUnit.mul ?_ ((ZMod.isUnit_iff_coprime st.t1.natAbs M).mpr htM)
        rcases Int.sign_trichotomy st.t1 with hs | hs | hs
        · simp [hs]
        · exact absurd (Int.sign_eq_zero_iff_zero.mp hs) hinv.t1_ne
        · simp [hs]
      exact (ZMod.intCast_eq_intCast_iff _ _ M).mp
        (sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hzmod))
    exact ⟨hMpos, hq_num ▸ hrabs, hq_den ▸ htD, hq_den ▸ htM, hq_mod⟩

/-- Completeness of `Rat.reconstruct`: if `q : ℚ` satisfies `|q.num| ≤ N`, `q.den ≤ D`,
`2 * N * D < M`, `Nat.Coprime q.den M`, and `(u : ZMod M)` represents `q`, then `reconstruct`
returns `some q`. -/
theorem reconstruct_of_eq {M N D : ℕ} {u : ℤ} {q : ℚ}
    (hN : q.num.natAbs ≤ N) (hD : q.den ≤ D) (hM : 2 * N * D < M)
    (hcop : Nat.Coprime q.den M) (hmod : q.num ≡ u * (q.den : ℤ) [ZMOD M]) :
    reconstruct M u N D = some q := by
  have hMpos : 0 < M := Nat.zero_lt_of_lt hM
  rw [reconstruct]
  simp only [hMpos.ne', ↓reduceIte]
  let st := reconstructLoop N (M : ℤ) 0 (u % (M : ℤ)) 1
  change (if decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) then
    some (Rat.divInt st.r1 st.t1) else none) = some q
  have hspec := reconstructLoop_spec (N := N) (initial_stepInv hMpos u)
  change StepInv M u st.r0 st.t0 st.r1 st.t1 ∧ st.r1 ≤ (N : ℤ) ∧
    ((st.r0 = (M : ℤ) ∧ st.t0 = 0 ∧ st.r1 = u % (M : ℤ) ∧ st.t1 = 1) ∨
      ((N : ℤ) < st.r0 ∧ st.t0 * st.t1 < 0)) at hspec
  rcases hspec with ⟨hinv, hrN, hcase⟩
  have hmod_rt : q.num * st.t1 ≡ (q.den : ℤ) * st.r1 [ZMOD M] := by
    calc
      q.num * st.t1 ≡ (u * (q.den : ℤ)) * st.t1 [ZMOD M] := hmod.mul_right _
      _ = (q.den : ℤ) * (st.t1 * u) := by ring
      _ ≡ (q.den : ℤ) * st.r1 [ZMOD M] := hinv.mod1.symm.mul_left _
  have h2eq : 2 * N * D = N * D + D * N := by ring
  have hdiv_rt : q.num * st.t1 = (q.den : ℤ) * st.r1 ∧ st.t1.natAbs = q.den := by
    rcases hcase with ⟨hr0_eq, ht0_eq, hr1_eq, ht1_eq⟩ | ⟨hr0_gt, ht01_neg⟩
    · have h1D : 1 ≤ D := le_trans q.den_pos hD
      have hr1_abs : st.r1.natAbs ≤ N := by
        have := hinv.r1_nonneg
        omega
      have hbound : (q.num * st.t1 - (q.den : ℤ) * st.r1).natAbs ≤ 2 * N * D := by
        refine (Int.natAbs_sub_le _ _).trans ?_
        rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, ht1_eq, Int.natAbs_one, mul_one]
        have h1 : q.num.natAbs ≤ N * D := le_trans hN (Nat.le_mul_of_pos_right N h1D)
        have h2 : q.den * st.r1.natAbs ≤ D * N := Nat.mul_le_mul hD hr1_abs
        omega
      have hdvd : (M : ℤ) ∣ q.num * st.t1 - (q.den : ℤ) * st.r1 :=
        Int.modEq_iff_dvd.mp hmod_rt.symm
      have heq0 : q.num * st.t1 - (q.den : ℤ) * st.r1 = 0 := by
        by_contra hne
        have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natAbs_dvd_natAbs.mpr hdvd)
        omega
      have heq : q.num * st.t1 = (q.den : ℤ) * st.r1 := sub_eq_zero.mp heq0
      have hn := congrArg Int.natAbs heq
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, ht1_eq, Int.natAbs_one, mul_one] at hn
      have hdvd1 : q.den ∣ 1 :=
        q.reduced.symm.dvd_of_dvd_mul_left ⟨st.r1.natAbs, by rw [mul_one, hn]⟩
      rw [ht1_eq]
      exact ⟨by simpa only [ht1_eq] using heq,
        by simpa only [Int.natAbs_one] using (Nat.eq_one_of_dvd_one hdvd1).symm⟩
    · rcases hinv.bezout with ⟨s, hs1, hs2⟩
      have hmod0 : (q.den : ℤ) * st.r0 ≡ q.num * st.t0 [ZMOD M] := by
        calc
          (q.den : ℤ) * st.r0 ≡ (q.den : ℤ) * (st.t0 * u) [ZMOD M] := hinv.mod0.mul_left _
          _ = (u * (q.den : ℤ)) * st.t0 := by ring
          _ ≡ q.num * st.t0 [ZMOD M] := hmod.symm.mul_right _
      have hdvd_x : (M : ℤ) ∣ s * (q.num * st.t1 - (q.den : ℤ) * st.r1) :=
        dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hmod_rt.symm) s
      have hdvd_y : (M : ℤ) ∣ s * ((q.den : ℤ) * st.r0 - q.num * st.t0) :=
        dvd_mul_of_dvd_right (Int.modEq_iff_dvd.mp hmod0.symm) s
      rcases hdvd_x with ⟨x, hx⟩
      rcases hdvd_y with ⟨y, hy⟩
      have hcramer : ∀ {a e0 e1 : ℤ},
          s * a * (st.r0 * st.t1 - st.r1 * st.t0) =
            (s * (q.num * st.t1 - (q.den : ℤ) * st.r1)) * e0 +
              (s * ((q.den : ℤ) * st.r0 - q.num * st.t0)) * e1 →
          (M : ℤ) * a = (M : ℤ) * (x * e0 + y * e1) := fun {a e0 e1} hlin => by
        calc
          (M : ℤ) * a = (s * s) * (M : ℤ) * a := by rw [hs1, one_mul]
          _ = s * a * (s * (M : ℤ)) := by ring
          _ = s * a * (st.r0 * st.t1 - st.r1 * st.t0) := by rw [hs2]
          _ = (s * (q.num * st.t1 - (q.den : ℤ) * st.r1)) * e0 +
              (s * ((q.den : ℤ) * st.r0 - q.num * st.t0)) * e1 := hlin
          _ = ((M : ℤ) * x) * e0 + ((M : ℤ) * y) * e1 := by rw [← hx, ← hy]
          _ = (M : ℤ) * (x * e0 + y * e1) := by ring
      have ha_eq : q.num = x * st.r0 + y * st.r1 :=
        Int.eq_of_mul_eq_mul_left (Int.natCast_ne_zero.mpr hMpos.ne') (hcramer (by ring))
      have hb_eq : (q.den : ℤ) = x * st.t0 + y * st.t1 :=
        Int.eq_of_mul_eq_mul_left (Int.natCast_ne_zero.mpr hMpos.ne') (hcramer (by ring))
      have hx0 : x = 0 := by
        by_contra hxne
        have hxabs : 1 ≤ x.natAbs := Int.natAbs_pos.mpr hxne
        have hy0 : y ≠ 0 := by
          intro hyz
          rw [hyz, zero_mul, add_zero] at ha_eq
          have h1 : q.num.natAbs = x.natAbs * st.r0.natAbs := by
            rw [ha_eq, Int.natAbs_mul]
          have h2 : N < st.r0.natAbs := by omega
          have h3 : st.r0.natAbs ≤ x.natAbs * st.r0.natAbs := Nat.le_mul_of_pos_left _ hxabs
          omega
        have hyabs : 1 ≤ y.natAbs := Int.natAbs_pos.mpr hy0
        have hxy_neg : x * y < 0 := by
          by_contra hxy_nneg
          have hxy_pos : 0 ≤ x * y := not_lt.mp hxy_nneg
          have hsame : 0 ≤ (x * st.r0) * (y * st.r1) := by
            have hmul : (x * st.r0) * (y * st.r1) = (x * y) * (st.r0 * st.r1) := by ring
            rw [hmul]
            exact mul_nonneg hxy_pos (mul_nonneg hinv.r0_pos.le hinv.r1_nonneg)
          have hnat : (x * st.r0 + y * st.r1).natAbs =
              (x * st.r0).natAbs + (y * st.r1).natAbs := by
            rcases le_or_gt 0 (x * st.r0) with hxr | hxr
            · have hyr : 0 ≤ y * st.r1 := by
                by_contra hneg
                have hlt : y * st.r1 < 0 := not_le.mp hneg
                rcases eq_or_lt_of_le hxr with h0 | hpos
                · rcases mul_eq_zero.mp h0.symm with rfl | hr0z
                  · exact hxne rfl
                  · exact hinv.r0_pos.ne' hr0z
                · nlinarith
              omega
            · have hyr : y * st.r1 ≤ 0 := by nlinarith
              omega
          rw [← ha_eq, Int.natAbs_mul, Int.natAbs_mul] at hnat
          have h2 : N < st.r0.natAbs := by omega
          have h3 : st.r0.natAbs ≤ x.natAbs * st.r0.natAbs := Nat.le_mul_of_pos_left _ hxabs
          omega
        have ht_same : 0 < (x * st.t0) * (y * st.t1) := by
          have hmul : (x * st.t0) * (y * st.t1) = (x * y) * (st.t0 * st.t1) := by ring
          rw [hmul]
          exact mul_pos_of_neg_of_neg hxy_neg ht01_neg
        have hb_nat : (q.den : ℤ).natAbs = (x * st.t0).natAbs + (y * st.t1).natAbs := by
          rw [hb_eq]
          rcases lt_or_gt_of_ne
            (show x * st.t0 ≠ 0 by
              intro h0
              rw [h0, zero_mul] at ht_same
              exact lt_irrefl 0 ht_same) with h1 | h1
          · have h2 : y * st.t1 < 0 := by nlinarith
            omega
          · have h2 : 0 < y * st.t1 := by nlinarith
            omega
        rw [Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_mul] at hb_nat
        have ht1_le_D : st.t1.natAbs ≤ D := by
          have h1 : st.t1.natAbs ≤ y.natAbs * st.t1.natAbs := Nat.le_mul_of_pos_left _ hyabs
          omega
        have hr1_abs : st.r1.natAbs ≤ N := by
          have := hinv.r1_nonneg
          omega
        have hbound : (q.num * st.t1 - (q.den : ℤ) * st.r1).natAbs ≤ 2 * N * D := by
          refine (Int.natAbs_sub_le _ _).trans ?_
          rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast]
          have h1 : q.num.natAbs * st.t1.natAbs ≤ N * D := Nat.mul_le_mul hN ht1_le_D
          have h2 : q.den * st.r1.natAbs ≤ D * N := Nat.mul_le_mul hD hr1_abs
          omega
        have hmul_ne : q.num * st.t1 - (q.den : ℤ) * st.r1 ≠ 0 := by
          intro hzero
          have hxz : (M : ℤ) * x = 0 := by rw [← hx, hzero, mul_zero]
          exact hxne ((mul_eq_zero.mp hxz).resolve_left (Int.natCast_ne_zero.mpr hMpos.ne'))
        have hdvd := Int.modEq_iff_dvd.mp hmod_rt.symm
        have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hmul_ne) (Int.natAbs_dvd_natAbs.mpr hdvd)
        omega
      rw [hx0, zero_mul, zero_add] at ha_eq hb_eq
      have hyabs_one : y.natAbs = 1 := by
        have ha_nat : q.num.natAbs = y.natAbs * st.r1.natAbs := by rw [ha_eq, Int.natAbs_mul]
        have hb_nat : q.den = y.natAbs * st.t1.natAbs := by
          have := congrArg Int.natAbs hb_eq
          simpa only [Int.natAbs_natCast, Int.natAbs_mul] using this
        have hg : y.natAbs ∣ Nat.gcd q.num.natAbs q.den :=
          Nat.dvd_gcd ⟨st.r1.natAbs, ha_nat⟩ ⟨st.t1.natAbs, hb_nat⟩
        rw [q.reduced] at hg
        exact Nat.eq_one_of_dvd_one hg
      have ht_den : st.t1.natAbs = q.den := by
        have := congrArg Int.natAbs hb_eq
        rw [Int.natAbs_natCast, Int.natAbs_mul, hyabs_one, one_mul] at this
        exact this.symm
      have heq_rt : q.num * st.t1 = (q.den : ℤ) * st.r1 := by
        rw [ha_eq, hb_eq]
        ring
      exact ⟨heq_rt, ht_den⟩
  have hcond : decide (st.t1.natAbs ≤ D ∧ Nat.Coprime st.t1.natAbs M) = true := by
    rw [decide_eq_true_iff, hdiv_rt.2]
    exact ⟨hD, hcop⟩
  simp only [hcond, ↓reduceIte]
  congr 1
  rw [Rat.divInt_eq_div, ← Rat.num_div_den q]
  have ht1_q : (st.t1 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hinv.t1_ne
  have hden_q : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  rw [div_eq_div_iff ht1_q hden_q]
  exact_mod_cast (by linarith [hdiv_rt.1] : st.r1 * (q.den : ℤ) = q.num * st.t1)

end WangReconstruction

section CRTReconstruction

open scoped Function

/-- Chinese-remainder rational reconstruction from residues in `∀ i, ZMod (m i)` across pairwise
coprime moduli `m : Fin k → ℕ`. -/
noncomputable def reconstructPi {k : ℕ} (m : Fin k → ℕ) (hcop : Pairwise (Nat.Coprime on m))
    (res : ∀ i, ZMod (m i)) (N D : ℕ) : Option ℚ :=
  reconstruct (∏ i, m i) (((ZMod.prodEquivPi m hcop).symm res).val : ℤ) N D

/-- Completeness of `Rat.reconstructPi`: if `∏ i, m i > 2 * N * D`, each `m i` is coprime to
`q.den`, and `res i` equals `(q.num : ZMod (m i)) * (q.den : ZMod (m i))⁻¹` for every `i`, then
`Rat.reconstructPi` recovers `some q`. -/
theorem reconstructPi_of_eq {k : ℕ} {m : Fin k → ℕ} (hcop : Pairwise (Nat.Coprime on m))
    {res : ∀ i, ZMod (m i)} {N D : ℕ} {q : ℚ}
    (hN : q.num.natAbs ≤ N) (hD : q.den ≤ D) (hM : 2 * N * D < ∏ i, m i)
    (hcop_den : ∀ i, Nat.Coprime q.den (m i))
    (hres : ∀ i, (q.num : ZMod (m i)) = res i * (q.den : ZMod (m i))) :
    reconstructPi m hcop res N D = some q := by
  let M := ∏ i, m i
  have : NeZero M := ⟨by have : 0 < M := Nat.zero_lt_of_lt hM; omega⟩
  let uZ : ZMod M := (ZMod.prodEquivPi m hcop).symm res
  have hcopM : Nat.Coprime q.den M := Nat.Coprime.prod_right fun i _ => hcop_den i
  have hcast : (q.num : ZMod M) = uZ * (q.den : ZMod M) := by
    apply (ZMod.prodEquivPi m hcop).injective
    ext i
    rw [map_mul, map_intCast, map_natCast, RingEquiv.apply_symm_apply]
    exact hres i
  have hmod : q.num ≡ (uZ.val : ℤ) * (q.den : ℤ) [ZMOD M] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    rw [← ZMod.natCast_zmod_val uZ] at hcast
    exact_mod_cast hcast
  exact reconstruct_of_eq hN hD hM hcopM hmod

end CRTReconstruction

end Rat
