/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Linearity
import Complexity.Foundations.Data.Hamming
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The rejection probability of the BLR test

If the Blum–Luby–Rubinfeld test accepts `f` with probability at least `1 - ε`, then `f` is at
relative Hamming distance at most `ε` from some parity
(`BitString.exists_hammingDist_parityOn_le_of_le_blrAcceptance`). Conversely, a function at relative
distance `δ` from a parity is rejected with probability about `3δ` when `δ` is small, and this
constant is sharp [O'Donnell, Exercise 1.28][ODonnell2014].

Read `f` as the signs `F x = (-1) ^ f x`. If `f` is at relative distance `δ` from the parity on
`S`, then `F̂(S) = 1 - 2δ`, and every other coefficient has absolute value at most `2δ`
(`BitString.abs_fourierCoeff_signVal_le_of_ne`), since distinct parities are half the cube apart.
Splitting `∑_T F̂(T)³` into the term at `S` and the rest, bounded with Parseval's identity, the
acceptance probability `1/2 + 1/2 ∑_T F̂(T)³` is at most `1 - 3δ + 10δ² - 8δ³`
(`BitString.blrAcceptance_le_of_hammingDist_parityOn`). The bound holds for every parity, not
only for the nearest one, and for every `δ`; it is attained at `δ = 0` (parities) and `δ = 1`
(their negations).

The indicator of a single nonzero point `a`, `x ↦ decide (x = a)`, shows that `3` cannot be
improved. Its coefficients are `[S = ∅] - 2 χ_S(a) / 2ⁿ`
(`BitString.fourierCoeff_signVal_decide_eq`), so the test accepts it with probability exactly
`1 - 3/2ⁿ + 6/4ⁿ` (`BitString.blrAcceptance_decide_eq`). When there are at least two coordinates,
its nearest parity is the zero parity, at relative distance `δ = 2⁻ⁿ`
(`BitString.hammingDist_decide_eq_parityOn_empty`,
`BitString.one_le_hammingDist_decide_eq_parityOn`). Its rejection probability is therefore
exactly `3δ - 6δ²`. Hence, for every `c > 3`, no bound of the form `cδ - Cδ²` on the rejection
probability holds for all functions at small distance `δ` from their nearest parity
(`BitString.not_forall_mul_sub_mul_sq_le_one_sub_blrAcceptance`).

## Main results

* `Cslib.BitString.abs_fourierCoeff_signVal_le_of_ne`: Exercise 1.28(a), the coefficients away
  from a close parity are small.
* `Cslib.BitString.blrAcceptance_le_of_hammingDist_parityOn`: Exercise 1.28(b), the test rejects
  with probability at least `3δ - 10δ² + 8δ³`.
* `Cslib.BitString.fourierCoeff_ite_eq`, `Cslib.BitString.fourierCoeff_signVal_decide_eq`: the
  Fourier coefficients of the indicator of a point.
* `Cslib.BitString.blrAcceptance_decide_eq`: the exact acceptance probability of the indicator of
  a nonzero point.
* `Cslib.BitString.hammingDist_decide_eq_parityOn_empty`,
  `Cslib.BitString.one_le_hammingDist_decide_eq_parityOn`: the zero parity is a nearest parity to
  the indicator of a nonzero point.
* `Cslib.BitString.not_forall_mul_sub_mul_sq_le_one_sub_blrAcceptance`: Exercise 1.28(c), the
  constant `3` is sharp.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Small coefficients away from a close parity -/

/-- **Coefficients away from a close parity are small**: if `f` is at relative Hamming distance
`δ` from the parity on `T`, then, reading `f` as signs, its coefficient on every other set has
absolute value at most `2δ` [O'Donnell, Exercise 1.28(a)][ODonnell2014]. -/
theorem abs_fourierCoeff_signVal_le_of_ne (f : (ι → Bool) → Bool) {S T : Finset ι} (h : S ≠ T) :
    |fourierCoeff (fun x => signVal (f x)) S| ≤
      2 * ((hammingDist f (parityOn T) : ℝ) / 2 ^ Fintype.card ι) := by
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hST : (2 * hammingDist (parityOn S) (parityOn T) : ℝ) = 2 ^ Fintype.card ι := by
    exact_mod_cast two_mul_hammingDist_parityOn h
  have h₁ : (hammingDist (parityOn S) (parityOn T) : ℝ) ≤
      hammingDist f (parityOn S) + hammingDist f (parityOn T) := by
    rw [← hammingDist_comm (parityOn S) f]
    exact_mod_cast hammingDist_triangle _ _ _
  have h₂ : (hammingDist f (parityOn S) : ℝ) ≤
      hammingDist f (parityOn T) + hammingDist (parityOn S) (parityOn T) := by
    rw [hammingDist_comm (parityOn S) (parityOn T)]
    exact_mod_cast hammingDist_triangle _ _ _
  rw [fourierCoeff_signVal, abs_le, mul_div_assoc]
  set N : ℝ := 2 ^ Fintype.card ι
  have hdST : (hammingDist (parityOn S) (parityOn T) : ℝ) / N = 1 / 2 := by
    rw [div_eq_iff hN.ne']
    linarith
  have i₁ : (hammingDist (parityOn S) (parityOn T) : ℝ) / N ≤
      (hammingDist f (parityOn S) : ℝ) / N + (hammingDist f (parityOn T) : ℝ) / N := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right h₁ hN.le
  have i₂ : (hammingDist f (parityOn S) : ℝ) / N ≤
      (hammingDist f (parityOn T) : ℝ) / N + (hammingDist (parityOn S) (parityOn T) : ℝ) / N := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right h₂ hN.le
  constructor <;> linarith

/-! ### The rejection probability -/

/-- **The BLR test rejects with probability at least `3δ - 10δ² + 8δ³`**: if `f` is at relative
Hamming distance `δ` from some parity, then the test accepts `f` with probability at most
`1 - 3δ + 10δ² - 8δ³` [O'Donnell, Exercise 1.28(b)][ODonnell2014]. The parity need not be the
nearest one. -/
theorem blrAcceptance_le_of_hammingDist_parityOn (f : (ι → Bool) → Bool) {S : Finset ι} {δ : ℝ}
    (hδ : (hammingDist f (parityOn S) : ℝ) / 2 ^ Fintype.card ι = δ) :
    blrAcceptance f ≤ 1 - 3 * δ + 10 * δ ^ 2 - 8 * δ ^ 3 := by
  rw [blrAcceptance_eq_sum_fourierCoeff_pow_three]
  set c := fourierCoeff fun x => signVal (f x)
  have hcS : c S = 1 - 2 * δ := by
    rw [← hδ, mul_div_assoc']
    exact fourierCoeff_signVal f S
  have hpars : ∑ T ∈ univ.erase S, c T ^ 2 = 1 - (1 - 2 * δ) ^ 2 := by
    rw [← hcS, ← sum_fourierCoeff_sq_signVal f, ← add_sum_erase _ (fun T => c T ^ 2) (mem_univ S)]
    ring
  have hrest : ∑ T ∈ univ.erase S, c T ^ 3 ≤ 2 * δ * ∑ T ∈ univ.erase S, c T ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun T hT => ?_
    have hle : |c T| ≤ 2 * δ := hδ ▸ abs_fourierCoeff_signVal_le_of_ne f (ne_of_mem_erase hT)
    calc c T ^ 3 = c T * c T ^ 2 := pow_succ' _ _
      _ ≤ |c T| * c T ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
      _ ≤ 2 * δ * c T ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
  rw [hpars] at hrest
  rw [← add_sum_erase _ (fun T => c T ^ 3) (mem_univ S), hcS]
  linarith

/-! ### The indicator of a point -/

/-- The indicator of a point `a` has Fourier coefficients `χ_S(a) / 2ⁿ`. -/
theorem fourierCoeff_ite_eq (a : ι → Bool) (S : Finset ι) :
    fourierCoeff (fun x => if x = a then (1 : ℝ) else 0) S = chi ℝ S a / 2 ^ Fintype.card ι := by
  rw [fourierCoeff_eq_sum]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

/-- The Boolean indicator of a point `a`, read as signs, has Fourier coefficients
`[S = ∅] - 2 χ_S(a) / 2ⁿ`. -/
theorem fourierCoeff_signVal_decide_eq (a : ι → Bool) (S : Finset ι) :
    fourierCoeff (fun x => signVal (decide (x = a))) S =
      (if S = ∅ then 1 else 0) - 2 * (chi ℝ S a / 2 ^ Fintype.card ι) := by
  have h : (fun x => signVal (decide (x = a))) =
      fun x => (1 : ℝ) - 2 * (if x = a then 1 else 0) := by
    funext x
    by_cases hx : x = a <;> norm_num [hx]
  rw [h, fourierCoeff_sub, fourierCoeff_const_mul, fourierCoeff_const, fourierCoeff_ite_eq]

/-- **The BLR test on the indicator of a point**: the test accepts the indicator of a nonzero
point with probability exactly `1 - 3/2ⁿ + 6/4ⁿ`. -/
theorem blrAcceptance_decide_eq {a : ι → Bool} (ha : a ≠ 0) :
    blrAcceptance (fun x => decide (x = a)) =
      1 - 3 / 2 ^ Fintype.card ι + 6 / (2 ^ Fintype.card ι) ^ 2 := by
  rw [blrAcceptance_eq_sum_fourierCoeff_pow_three]
  simp only [fourierCoeff_signVal_decide_eq]
  set N : ℝ := 2 ^ Fintype.card ι
  have hN : N ≠ 0 := by positivity
  have hsum : ∑ S ∈ univ.erase ∅, chi ℝ S a = -1 := by
    have h₁ := sum_chi_mul_chi a 0
    have h₂ := add_sum_erase _ (fun S => chi ℝ S a) (mem_univ ∅)
    simp only [chi_zero, mul_one, ha, ite_false, chi_empty] at h₁ h₂
    linarith
  have hrest : ∑ S ∈ univ.erase ∅,
      ((if S = ∅ then (1 : ℝ) else 0) - 2 * (chi ℝ S a / N)) ^ 3 =
      -8 / N ^ 3 * ∑ S ∈ univ.erase ∅, chi ℝ S a := by
    rw [mul_sum]
    refine sum_congr rfl fun S hS => ?_
    rw [ite_eq_right (ne_of_mem_erase hS)]
    have hcube : chi ℝ S a ^ 3 = chi ℝ S a := by
      rw [pow_succ, sq, chi_mul_self, one_mul]
    field_simp
    linear_combination (-8 : ℝ) * hcube
  rw [← add_sum_erase _ _ (mem_univ ∅), hrest, hsum, ite_eq_left rfl, chi_empty]
  field_simp
  ring

/-- The indicator of a point differs from the zero parity at exactly one input. -/
theorem hammingDist_decide_eq_parityOn_empty (a : ι → Bool) :
    hammingDist (fun x => decide (x = a)) (parityOn ∅) = 1 := by
  refine hammingDist_eq_one_iff.2 ⟨a, by simp, fun x hx => ?_⟩
  simp [hx]

/-- With at least two coordinates, the indicator of a point is at Hamming distance at least one
from every parity, so the zero parity is a nearest parity to it. -/
theorem one_le_hammingDist_decide_eq_parityOn (a : ι → Bool) (hι : 2 ≤ Fintype.card ι)
    (S : Finset ι) : 1 ≤ hammingDist (fun x => decide (x = a)) (parityOn S) := by
  rcases eq_or_ne S ∅ with rfl | hS
  · rw [hammingDist_decide_eq_parityOn_empty a]
  · have h₁ := two_mul_hammingDist_parityOn hS.symm
    have h₂ := hammingDist_triangle (parityOn ∅) (fun x => decide (x = a)) (parityOn S)
    rw [hammingDist_comm (parityOn ∅) (fun x => decide (x = a)),
      hammingDist_decide_eq_parityOn_empty a] at h₂
    have h₄ : 2 ^ 2 ≤ 2 ^ Fintype.card ι := Nat.pow_le_pow_right (by norm_num) hι
    omega

/-! ### Sharpness of the constant three -/

/-- **The constant `3` in the BLR rejection bound is sharp**: for every `c > 3`, every `C` and
every `δ₀ > 0`, it is not the case that every function `f` on `n` bits at relative Hamming distance
`δ ≤ δ₀` from its nearest parity is rejected with probability at least `cδ - Cδ²`
[O'Donnell, Exercise 1.28(c)][ODonnell2014]. The indicator of a nonzero point on `n ≥ 2` bits,
with `δ = 2⁻ⁿ`, is rejected with probability exactly `3δ - 6δ²`. -/
theorem not_forall_mul_sub_mul_sq_le_one_sub_blrAcceptance {c : ℝ} (hc : 3 < c) (C : ℝ) {δ₀ : ℝ}
    (hδ₀ : 0 < δ₀) :
    ¬ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (S : Finset (Fin n)),
      (∀ T, hammingDist f (parityOn S) ≤ hammingDist f (parityOn T)) →
      (hammingDist f (parityOn S) : ℝ) / 2 ^ n ≤ δ₀ →
      c * ((hammingDist f (parityOn S) : ℝ) / 2 ^ n) -
          C * ((hammingDist f (parityOn S) : ℝ) / 2 ^ n) ^ 2 ≤ 1 - blrAcceptance f := by
  intro h
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / δ₀) ((|C| + 6) / (c - 3)))
  set n := m + 2
  have hpow : (m : ℝ) < 2 ^ n := by
    have : m < 2 ^ n :=
      Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))
    exact_mod_cast this
  set a : Fin n → Bool := fun _ => true
  have ha : a ≠ 0 := fun h => by simpa [a] using congr_fun h 0
  have hS (T : Finset (Fin n)) : hammingDist (fun x => decide (x = a)) (parityOn ∅) ≤
      hammingDist (fun x => decide (x = a)) (parityOn T) := by
    rw [hammingDist_decide_eq_parityOn_empty a]
    exact one_le_hammingDist_decide_eq_parityOn a (by simp [n]) T
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hd := h n _ ∅ hS
  rw [hammingDist_decide_eq_parityOn_empty a, blrAcceptance_decide_eq ha, Fintype.card_fin] at hd
  push_cast at hd
  have hm₁ : 1 / δ₀ < 2 ^ n := (le_max_left _ _).trans_lt (hm.trans hpow)
  have hm₂ : (|C| + 6) / (c - 3) < 2 ^ n := (le_max_right _ _).trans_lt (hm.trans hpow)
  have hδ : 1 / 2 ^ n ≤ δ₀ := by
    rw [div_le_iff₀ hN]
    rw [div_lt_iff₀ hδ₀] at hm₁
    linarith
  have key := hd hδ
  rw [div_lt_iff₀ (by linarith)] at hm₂
  set N : ℝ := 2 ^ n
  have hC : C ≤ |C| := le_abs_self C
  have hgap : 0 < c * (1 / N) - C * (1 / N) ^ 2 - (1 - (1 - 3 / N + 6 / N ^ 2)) := by
    have e : c * (1 / N) - C * (1 / N) ^ 2 - (1 - (1 - 3 / N + 6 / N ^ 2)) =
        ((c - 3) * N - (C - 6)) / N ^ 2 := by
      field_simp
      ring
    rw [e]
    exact div_pos (by nlinarith) (by positivity)
  linarith

end Cslib.BitString
