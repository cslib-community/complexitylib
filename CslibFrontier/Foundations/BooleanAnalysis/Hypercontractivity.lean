/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.Derivative
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.Tensorization
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.TwoPoint
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Hypercontractivity on the Boolean cube

The noise operator `T_ρ` (`BitString.noiseOp`) is a *hypercontraction*: it is a contraction not
only of `L^2` but from `L^p` to `L^2` and from `L^2` to `L^q` for suitable `ρ` [Bonami1970]
[O'Donnell, Chapter 9][ODonnell2014]. Writing `‖f‖_p` for the `L^p` norm (`Cslib.lpNorm`),
this file proves:

* the **Weak Two-Function Hypercontractivity Theorem**: for `0 ≤ r, s ≤ 1` and
  `0 ≤ ρ ≤ √(r s)`, the expectation of `f x g y` over a `ρ`-correlated pair `(x, y)`, which is
  `𝔼_x f x · T_ρ g x`, is at most `‖f‖_{1 + r} ‖g‖_{1 + s}`
  (`BitString.expect_mul_noiseOp_le_lpNorm_mul_lpNorm`);
* the **`(p, 2)`-Hypercontractivity Theorem**: `‖T_ρ f‖_2 ≤ ‖f‖_p` for `1 ≤ p ≤ 2` and
  `0 ≤ ρ ≤ √(p - 1)` (`BitString.lpNorm_two_noiseOp_le`), equivalently
  `Stab_ρ[f] ≤ ‖f‖_{1 + ρ} ^ 2` for `0 ≤ ρ ≤ 1` (`BitString.noiseStability_le_lpNorm_sq`);
* the **`(2, q)`-Hypercontractivity Theorem**: `‖T_ρ f‖_q ≤ ‖f‖_2` for `2 ≤ q` and
  `0 ≤ ρ ≤ 1 / √(q - 1)` (`BitString.lpNorm_noiseOp_le_lpNorm_two`);
* their composition, `‖T_ρ f‖_q ≤ ‖f‖_p` for `1 ≤ p ≤ 2 ≤ q` and
  `0 ≤ ρ ≤ √((p - 1) / (q - 1))` (`BitString.lpNorm_noiseOp_le_lpNorm`), the Hypercontractivity
  Theorem in the range `p ≤ 2 ≤ q`;
* the special cases `‖T_{1/√3} f‖_4 ≤ ‖f‖_2` (the `(2, 4)`-Hypercontractivity Theorem,
  `BitString.expect_noiseOp_pow_four_le`) and `Stab_{1/3}[f] ≤ ‖f‖_{4/3} ^ 2` (the
  `(4/3, 2)`-Hypercontractivity Theorem, `BitString.noiseStability_one_third_le`).

The proofs follow [O'Donnell, Sections 9.3 and 9.4][ODonnell2014]. On a single bit, the two-point
inequality (`BitString.lpNorm_two_noiseOp_le_of_unit`) and the Cauchy–Schwarz inequality give the
two-function inequality, after splitting `T_ρ = T_{ρ₁} T_{ρ₂}` with `ρ₁ ≤ √r` and `ρ₂ ≤ √s` and
moving `T_{ρ₁}` across the expectation. The two-function inequality tensorizes
(`BitString.expect_mul_noiseOp_le_of_unit`), which gives it on every cube. Taking `r = s = p - 1`
gives the `(p, 2)` theorem, and taking `r = 1 / (q - 1)` and `s = 1` gives the `(2, q)` theorem by
duality: `‖T_ρ f‖_q ^ q` is the expectation of `h · T_ρ f` for `h = T_ρ f |T_ρ f| ^ (q - 2)`,
whose `L^{q / (q - 1)}` norm is `‖T_ρ f‖_q ^ (q - 1)`.

The case `q = ∞` of the `(2, q)` theorem is not covered: `‖·‖_q` is defined for real `q`.

## Main results

* `Cslib.BitString.expect_mul_noiseOp_le_lpNorm_mul_lpNorm`: the Weak Two-Function
  Hypercontractivity Theorem.
* `Cslib.BitString.lpNorm_two_noiseOp_le`, `Cslib.BitString.noiseStability_le_lpNorm_sq`: the
  `(p, 2)`-Hypercontractivity Theorem.
* `Cslib.BitString.lpNorm_noiseOp_le_lpNorm_two`: the `(2, q)`-Hypercontractivity Theorem.
* `Cslib.BitString.lpNorm_noiseOp_le_lpNorm`: hypercontractivity for `p ≤ 2 ≤ q`.
* `Cslib.BitString.expect_noiseOp_pow_four_le`, `Cslib.BitString.noiseStability_one_third_le`:
  the `(2, 4)`- and `(4/3, 2)`-Hypercontractivity Theorems.

## References

* [A. Bonami, *Étude des coefficients de Fourier des fonctions de `L^p(G)`*][Bonami1970]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Splitting the correlation -/

/-- Splitting the correlation: the expectation of `f` against `T_{ρ σ} g` is the expectation of
`T_ρ f` against `T_σ g`. -/
theorem expect_mul_noiseOp_mul (ρ σ : ℝ) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp (ρ * σ) g x = 𝔼 x, noiseOp ρ f x * noiseOp σ g x := by
  rw [← noiseOp_noiseOp, expect_mul_noiseOp_comm]

/-- The expectation of `f` against `T_{ρ σ} g` is at most `‖T_ρ f‖_2 ‖T_σ g‖_2`. -/
theorem expect_mul_noiseOp_mul_le (ρ σ : ℝ) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp (ρ * σ) g x ≤ lpNorm 2 (noiseOp ρ f) * lpNorm 2 (noiseOp σ g) := by
  rw [expect_mul_noiseOp_mul, lpNorm_two, lpNorm_two]
  exact Real.expect_mul_le_sqrt_mul_sqrt _ _ _

/-- A correlation `0 ≤ ρ ≤ √(r s)` factors as `ρ₁ ρ₂` with `0 ≤ ρ₁ ≤ √r` and `0 ≤ ρ₂ ≤ √s`. -/
private theorem exists_eq_mul_le_sqrt {r s ρ : ℝ} (hr : 0 ≤ r) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ √(r * s)) :
    ∃ ρ₁ ρ₂ : ℝ, ρ = ρ₁ * ρ₂ ∧ 0 ≤ ρ₁ ∧ ρ₁ ≤ √r ∧ 0 ≤ ρ₂ ∧ ρ₂ ≤ √s := by
  rw [Real.sqrt_mul hr] at hρ'
  rcases (Real.sqrt_nonneg r).eq_or_lt with h | h
  · rw [← h, zero_mul] at hρ'
    exact ⟨0, 0, by rw [zero_mul, le_antisymm hρ' hρ], le_rfl, h ▸ le_rfl, le_rfl,
      Real.sqrt_nonneg s⟩
  · refine ⟨√r, ρ / √r, (mul_div_cancel₀ ρ h.ne').symm, h.le, le_rfl, div_nonneg hρ h.le, ?_⟩
    rw [div_le_iff₀ h, mul_comm]
    exact hρ'

/-! ### Two-function hypercontractivity -/

/-- **The Weak Two-Function Hypercontractivity Theorem**: for `0 ≤ r, s ≤ 1` and
`0 ≤ ρ ≤ √(r s)`, the expectation `𝔼_x f x · T_ρ g x` of `f x g y` over a `ρ`-correlated pair
`(x, y)` is at most `‖f‖_{1 + r} ‖g‖_{1 + s}` [O'Donnell, Section 9.4][ODonnell2014]. -/
theorem expect_mul_noiseOp_le_lpNorm_mul_lpNorm {r s ρ : ℝ} (hr : 0 ≤ r) (hr' : r ≤ 1)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √(r * s)) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x ≤ lpNorm (1 + r) f * lpNorm (1 + s) g := by
  have hrs : √(r * s) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
  refine expect_mul_noiseOp_le_of_unit (by linarith) (by linarith) hρ (hρ'.trans hrs)
    (fun f g => ?_) f g
  obtain ⟨ρ₁, ρ₂, rfl, h₁, h₁', h₂, h₂'⟩ := exists_eq_mul_le_sqrt hr hρ hρ'
  refine (expect_mul_noiseOp_mul_le ρ₁ ρ₂ f g).trans
    (mul_le_mul ?_ ?_ (lpNorm_nonneg _ _) (lpNorm_nonneg _ _))
  · exact lpNorm_two_noiseOp_le_of_unit (by linarith) (by linarith) h₁
      (by rwa [add_sub_cancel_left]) f
  · exact lpNorm_two_noiseOp_le_of_unit (by linarith) (by linarith) h₂
      (by rwa [add_sub_cancel_left]) g

/-! ### `(p, 2)`-hypercontractivity -/

/-- **The `(p, 2)`-Hypercontractivity Theorem**: for `1 ≤ p ≤ 2` and `0 ≤ ρ ≤ √(p - 1)`,
`‖T_ρ f‖_2 ≤ ‖f‖_p` [O'Donnell, Section 9.4][ODonnell2014]. -/
theorem lpNorm_two_noiseOp_le {p ρ : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ √(p - 1)) (f : (ι → Bool) → ℝ) : lpNorm 2 (noiseOp ρ f) ≤ lpNorm p f := by
  have hρρ : ρ * ρ ≤ √((p - 1) * (p - 1)) := by
    rw [Real.sqrt_mul_self (by linarith)]
    nlinarith [Real.sq_sqrt (show 0 ≤ p - 1 by linarith), Real.sqrt_nonneg (p - 1)]
  have h := expect_mul_noiseOp_le_lpNorm_mul_lpNorm (by linarith) (by linarith) (by linarith)
    (by linarith) (mul_nonneg hρ hρ) hρρ f f
  rw [expect_mul_noiseOp_mul, add_sub_cancel] at h
  refine (pow_le_pow_iff_left₀ (lpNorm_nonneg _ _) (lpNorm_nonneg _ _) two_ne_zero).1 ?_
  rw [lpNorm_two_sq, sq (lpNorm p f)]
  simpa only [sq] using h

/-- **The `(p, 2)`-Hypercontractivity Theorem, as a bound on noise stability**: for
`0 ≤ ρ ≤ 1`, `Stab_ρ[f] ≤ ‖f‖_{1 + ρ} ^ 2` [O'Donnell, Chapter 9][ODonnell2014]. -/
theorem noiseStability_le_lpNorm_sq {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ ≤ 1) (f : (ι → Bool) → ℝ) :
    noiseStability ρ f ≤ lpNorm (1 + ρ) f ^ 2 := by
  rw [sq]
  exact expect_mul_noiseOp_le_lpNorm_mul_lpNorm hρ hρ' hρ hρ' hρ
    (Real.sqrt_mul_self hρ).ge f f

/-- **The `(4/3, 2)`-Hypercontractivity Theorem**: `Stab_{1/3}[f] ≤ ‖f‖_{4/3} ^ 2`
[O'Donnell, Section 9.2][ODonnell2014]. -/
theorem noiseStability_one_third_le (f : (ι → Bool) → ℝ) :
    noiseStability (1 / 3) f ≤ lpNorm (4 / 3) f ^ 2 := by
  have h := noiseStability_le_lpNorm_sq (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num) f
  rwa [show (1 : ℝ) + 1 / 3 = 4 / 3 by norm_num] at h

/-! ### `(2, q)`-hypercontractivity -/

/-- **The `(2, q)`-Hypercontractivity Theorem**: for `2 ≤ q` and `0 ≤ ρ ≤ 1 / √(q - 1)`,
`‖T_ρ f‖_q ≤ ‖f‖_2` [O'Donnell, Section 9.4][ODonnell2014]. -/
theorem lpNorm_noiseOp_le_lpNorm_two {q ρ : ℝ} (hq : 2 ≤ q) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ (√(q - 1))⁻¹) (f : (ι → Bool) → ℝ) : lpNorm q (noiseOp ρ f) ≤ lpNorm 2 f := by
  set u := noiseOp ρ f
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  set r := (q - 1)⁻¹ with hr
  have hr0 : 0 ≤ r := inv_nonneg.2 hq1.le
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  -- the dual function `h = u |u| ^ (q - 2)`: `h u = |u| ^ q` and `|h| = |u| ^ (q - 1)`
  set h : (ι → Bool) → ℝ := fun x => u x * |u x| ^ (q - 2)
  have hhu (x : ι → Bool) : h x * u x = |u x| ^ q := by
    have e : h x * u x = |u x| ^ (2 : ℝ) * |u x| ^ (q - 2) := by
      rw [Real.rpow_two, sq_abs]
      ring
    rw [e, ← Real.rpow_add' (abs_nonneg _) (by linarith), add_sub_cancel]
  have habs (x : ι → Bool) : |h x| ^ (1 + r) = |u x| ^ q := by
    have e : |h x| = |u x| ^ (q - 1) := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        show q - 1 = 1 + (q - 2) by ring, Real.rpow_add' (abs_nonneg _) (by linarith),
        Real.rpow_one]
    rw [e, ← Real.rpow_mul (abs_nonneg _), hr, mul_add, mul_one,
      mul_inv_cancel₀ hq1.ne', sub_add_cancel]
  have key := expect_mul_noiseOp_le_lpNorm_mul_lpNorm hr0 hr1 zero_le_one le_rfl hρ
    (by rwa [mul_one, hr, Real.sqrt_inv]) h f
  rw [show 𝔼 x, h x * noiseOp ρ f x = 𝔼 x, |u x| ^ q from expect_congr rfl fun x _ => hhu x]
    at key
  set A := 𝔼 x, |u x| ^ q
  have hA : 0 ≤ A := expect_abs_rpow_nonneg q u
  have hlp : lpNorm (1 + r) h = A ^ (1 + r)⁻¹ := by
    simp only [lpNorm, habs, A]
  rw [hlp, one_add_one_eq_two] at key
  change A ^ q⁻¹ ≤ lpNorm 2 f
  rcases hA.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow (inv_ne_zero hq0.ne')]
    exact lpNorm_nonneg _ _
  · have hexp : q⁻¹ + (1 + r)⁻¹ = 1 := by
      rw [hr]
      field_simp
      ring
    refine le_of_mul_le_mul_right ?_ (Real.rpow_pos_of_pos hpos (1 + r)⁻¹)
    rw [← Real.rpow_add hpos, hexp, Real.rpow_one, mul_comm]
    exact key

/-- **Hypercontractivity for `p ≤ 2 ≤ q`**: for `1 ≤ p ≤ 2 ≤ q` and
`0 ≤ ρ ≤ √((p - 1) / (q - 1))`, `‖T_ρ f‖_q ≤ ‖f‖_p`, composing the `(p, 2)` and `(2, q)`
theorems [O'Donnell, Chapter 9][ODonnell2014]. -/
theorem lpNorm_noiseOp_le_lpNorm {p q ρ : ℝ} (hp : 1 ≤ p) (hp' : p ≤ 2) (hq : 2 ≤ q)
    (hρ : 0 ≤ ρ) (hρ' : ρ ≤ √((p - 1) / (q - 1))) (f : (ι → Bool) → ℝ) :
    lpNorm q (noiseOp ρ f) ≤ lpNorm p f := by
  have hq1 : 0 < q - 1 := by linarith
  have hs : 0 < √(q - 1) := Real.sqrt_pos.2 hq1
  have hsplit : noiseOp ρ f = noiseOp (√(q - 1))⁻¹ (noiseOp (ρ * √(q - 1)) f) := by
    rw [noiseOp_noiseOp, mul_comm ρ, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
  rw [hsplit]
  refine (lpNorm_noiseOp_le_lpNorm_two hq (inv_nonneg.2 hs.le) le_rfl _).trans
    (lpNorm_two_noiseOp_le hp hp' (mul_nonneg hρ hs.le) ?_ f)
  calc ρ * √(q - 1) ≤ √((p - 1) / (q - 1)) * √(q - 1) := mul_le_mul_of_nonneg_right hρ' hs.le
    _ = √(p - 1) := by
      rw [← Real.sqrt_mul (div_nonneg (by linarith) hq1.le), div_mul_cancel₀ _ hq1.ne']

/-- **The `(2, 4)`-Hypercontractivity Theorem**: `‖T_{1/√3} f‖_4 ≤ ‖f‖_2`, that is,
`𝔼 (T_{1/√3} f) ^ 4 ≤ (𝔼 f ^ 2) ^ 2` [O'Donnell, Section 9.2][ODonnell2014]. -/
theorem expect_noiseOp_pow_four_le (f : (ι → Bool) → ℝ) :
    𝔼 x, noiseOp (√3)⁻¹ f x ^ 4 ≤ (𝔼 x, f x ^ 2) ^ 2 := by
  have h := lpNorm_noiseOp_le_lpNorm_two (by norm_num : (2 : ℝ) ≤ 4)
    (inv_nonneg.2 (Real.sqrt_nonneg 3)) (by norm_num) f
  have h4 := pow_le_pow_left₀ (lpNorm_nonneg _ _) h 4
  rw [show lpNorm 2 f ^ 4 = (lpNorm 2 f ^ 2) ^ 2 by ring, lpNorm_two_sq,
    ← Real.rpow_natCast, Nat.cast_ofNat, lpNorm_rpow (by norm_num)] at h4
  simpa only [Real.rpow_ofNat, Even.pow_abs (by decide : Even 4)] using h4

end Cslib.BitString
