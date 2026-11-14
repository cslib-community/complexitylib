/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Rat/Cast/Order.lean`)

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Farey spacing and uniqueness of rational approximation

Elementary Diophantine separation bounds for distinct rational numbers (`1 / (q.den * r.den)` and
`1 / N ^ 2`) and uniqueness of rational and coprime-fraction approximations within `1 / (2 N ^ 2)`
of any real number `α`. These bounds underlie unique continued-fraction recovery in quantum period
and order finding ([Arora and Barak][AroraBarak07], Chapter 20, Exercises 7 and 11).

## Main results

* `Rat.one_div_mul_den_le_abs_sub`: two distinct rationals `q ≠ r` satisfy
  `1 / (q.den * r.den) ≤ |q - r|`.
* `Rat.one_div_sq_le_abs_sub_of_den_le`, `Rat.one_div_sq_lt_abs_sub_of_den_le_of_den_lt`: separation
  by `1 / N ^ 2` (weak and strict) for distinct rationals with denominators at most `N`.
* `Rat.eq_of_den_le_of_abs_sub_lt`, `Rat.eq_of_den_lt_of_abs_sub_le`: uniqueness of a rational
  approximation with denominator `≤ N` (or `< N`) within `1 / (2 N ^ 2)` of any real `α`
  ([Arora and Barak][AroraBarak07], Chapter 20, Exercise 7).
* `Rat.eq_of_coprime_of_abs_div_sub_lt`, `Rat.eq_of_coprime_of_abs_sub_div_lt`: uniqueness of a
  coprime pair `(j, r)` with `0 < r ≤ N` within `1 / (2 N ^ 2)` of any real `α`
  ([Arora and Barak][AroraBarak07], Chapter 20, Exercises 7 and 11).

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

namespace Rat

/-- Two distinct rational numbers `q ≠ r` are separated by at least `1 / (q.den * r.den)`. -/
theorem one_div_mul_den_le_abs_sub {q r : ℚ} (hne : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * r.den) ≤ |(q : ℝ) - r| := by
  have hq0 : (0 : ℝ) < q.den := Nat.cast_pos.2 q.den_pos
  have hr0 : (0 : ℝ) < r.den := Nat.cast_pos.2 r.den_pos
  rw [div_le_iff₀ (mul_pos hq0 hr0), ← abs_of_pos (mul_pos hq0 hr0), ← abs_mul]
  have hident : ((q : ℝ) - r) * ((q.den : ℝ) * r.den) =
      ((q.num * (r.den : ℤ) - r.num * (q.den : ℤ) : ℤ) : ℝ) := by
    rw [Rat.cast_def q, Rat.cast_def r]
    push_cast
    field_simp
  rw [hident, ← Int.cast_abs]
  have hzne : q.num * (r.den : ℤ) - r.num * (q.den : ℤ) ≠ 0 := by
    intro hz
    apply hne
    rw [← Rat.num_div_den q, ← Rat.num_div_den r,
      div_eq_div_iff (Nat.cast_ne_zero.2 q.den_nz) (Nat.cast_ne_zero.2 r.den_nz)]
    exact_mod_cast sub_eq_zero.1 hz
  exact_mod_cast Int.one_le_abs hzne

/-- Two distinct rational numbers with denominators at most `N` are separated by at least
`1 / N ^ 2`. -/
theorem one_div_sq_le_abs_sub_of_den_le {q r : ℚ} {N : ℕ} (hq : q.den ≤ N)
    (hr : r.den ≤ N) (hne : q ≠ r) : (1 : ℝ) / (N : ℝ) ^ 2 ≤ |(q : ℝ) - r| := by
  refine (one_div_le_one_div_of_le (mul_pos (Nat.cast_pos.2 q.den_pos) (Nat.cast_pos.2 r.den_pos))
    ?_).trans (one_div_mul_den_le_abs_sub hne)
  rw [sq]
  exact mul_le_mul (Nat.cast_le.2 hq) (Nat.cast_le.2 hr) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Two distinct rational numbers with denominators `q.den ≤ N` and `r.den < N` are strictly more
than `1 / N ^ 2` apart ([Arora and Barak][AroraBarak07], Chapter 20, Exercises 7 and 11). -/
theorem one_div_sq_lt_abs_sub_of_den_le_of_den_lt {q r : ℚ} {N : ℕ} (hq : q.den ≤ N)
    (hr : r.den < N) (hne : q ≠ r) : (1 : ℝ) / (N : ℝ) ^ 2 < |(q : ℝ) - r| := by
  refine (one_div_lt_one_div_of_lt (mul_pos (Nat.cast_pos.2 q.den_pos) (Nat.cast_pos.2 r.den_pos))
    ?_).trans_le (one_div_mul_den_le_abs_sub hne)
  rw [sq]
  exact mul_lt_mul_of_le_of_lt_of_nonneg_of_pos (Nat.cast_le.2 hq) (Nat.cast_lt.2 hr)
    (Nat.cast_nonneg _) (Nat.cast_pos.2 (q.den_pos.trans_le hq))

/-- **Uniqueness of rational approximation within `1 / (2 N ^ 2)`**
([Arora and Barak][AroraBarak07], Chapter 20, Exercise 7): for any real `α` and `N : ℕ`, at most
one rational `q` with `q.den ≤ N` satisfies `|α - q| < 1 / (2 * N ^ 2)`. -/
theorem eq_of_den_le_of_abs_sub_lt {α : ℝ} {q r : ℚ} {N : ℕ} (hq : q.den ≤ N)
    (hr : r.den ≤ N) (hαq : |α - q| < 1 / (2 * (N : ℝ) ^ 2))
    (hαr : |α - r| ≤ 1 / (2 * (N : ℝ) ^ 2)) : q = r := by
  by_contra hne
  have hsep := one_div_sq_le_abs_sub_of_den_le hq hr hne
  have htri : |(q : ℝ) - r| ≤ |α - q| + |α - r| := by
    rw [abs_sub_comm α q]
    exact abs_sub_le (q : ℝ) α r
  have hsum : |α - q| + |α - r| < 1 / (N : ℝ) ^ 2 := by
    calc |α - q| + |α - r| < 1 / (2 * (N : ℝ) ^ 2) + 1 / (2 * (N : ℝ) ^ 2) :=
          add_lt_add_of_lt_of_le hαq hαr
      _ = 1 / (N : ℝ) ^ 2 := by ring
  linarith

/-- **Uniqueness of rational approximation with one denominator `< N`**
([Arora and Barak][AroraBarak07], Chapter 20, Exercise 7): for any real `α` and `N : ℕ`, if
`q.den ≤ N` and `r.den < N` both lie within `1 / (2 * N ^ 2)` of `α`, then `q = r`. -/
theorem eq_of_den_lt_of_abs_sub_le {α : ℝ} {q r : ℚ} {N : ℕ} (hq : q.den ≤ N)
    (hr : r.den < N) (hαq : |α - q| ≤ 1 / (2 * (N : ℝ) ^ 2))
    (hαr : |α - r| ≤ 1 / (2 * (N : ℝ) ^ 2)) : q = r := by
  by_contra hne
  have hsep := one_div_sq_lt_abs_sub_of_den_le_of_den_lt hq hr hne
  have htri : |(q : ℝ) - r| ≤ |α - q| + |α - r| := by
    rw [abs_sub_comm α q]
    exact abs_sub_le (q : ℝ) α r
  have hsum : |α - q| + |α - r| ≤ 1 / (N : ℝ) ^ 2 := by
    calc |α - q| + |α - r| ≤ 1 / (2 * (N : ℝ) ^ 2) + 1 / (2 * (N : ℝ) ^ 2) := add_le_add hαq hαr
      _ = 1 / (N : ℝ) ^ 2 := by ring
  linarith

/-- **Uniqueness of coprime fractions with denominators at most `N`**
([Arora and Barak][AroraBarak07], Chapter 20, Exercise 11): if `(j₁, r₁)` and `(j₂, r₂)` are
coprime pairs of natural numbers with `0 < r₁ ≤ N`, `0 < r₂ ≤ N`, and
`|j₁ / r₁ - j₂ / r₂| < 1 / N ^ 2`, then `j₁ = j₂` and `r₁ = r₂`. -/
theorem eq_of_coprime_of_abs_div_sub_lt {j₁ r₁ j₂ r₂ N : ℕ} (hr₁0 : 0 < r₁) (hr₁ : r₁ ≤ N)
    (hr₂0 : 0 < r₂) (hr₂ : r₂ ≤ N) (hcop₁ : Nat.Coprime j₁ r₁) (hcop₂ : Nat.Coprime j₂ r₂)
    (hdist : |(j₁ : ℝ) / r₁ - (j₂ : ℝ) / r₂| < 1 / (N : ℝ) ^ 2) : j₁ = j₂ ∧ r₁ = r₂ := by
  have hden₁ : ((j₁ : ℚ) / r₁).den = r₁ := by
    have h := den_div_eq_of_coprime (a := j₁) (b := r₁) (Int.natCast_pos.mpr hr₁0) hcop₁
    exact Int.ofNat.inj (by simpa using h)
  have hden₂ : ((j₂ : ℚ) / r₂).den = r₂ := by
    have h := den_div_eq_of_coprime (a := j₂) (b := r₂) (Int.natCast_pos.mpr hr₂0) hcop₂
    exact Int.ofNat.inj (by simpa using h)
  have hq : (j₁ : ℚ) / r₁ = (j₂ : ℚ) / r₂ := by
    by_contra hne
    have hsep := one_div_sq_le_abs_sub_of_den_le (hden₁.trans_le hr₁) (hden₂.trans_le hr₂) hne
    push_cast at hsep
    linarith
  have hinj := div_int_inj (a := j₁) (b := r₁) (c := j₂) (d := r₂)
    (Int.natCast_pos.mpr hr₁0) (Int.natCast_pos.mpr hr₂0) hcop₁ hcop₂ (by simpa using hq)
  exact ⟨Int.ofNat.inj hinj.1, Int.ofNat.inj hinj.2⟩

/-- **Uniqueness of coprime fraction recovery from an approximation within `1 / (2 N ^ 2)`**
([Arora and Barak][AroraBarak07], Chapter 20, Exercises 7 and 11): if `(j₁, r₁)` and `(j₂, r₂)` are
coprime pairs of natural numbers with `0 < r₁ ≤ N` and `0 < r₂ ≤ N` whose quotients both lie within
`1 / (2 N ^ 2)` of `α : ℝ` (one strictly), then `j₁ = j₂` and `r₁ = r₂`. -/
theorem eq_of_coprime_of_abs_sub_div_lt {α : ℝ} {j₁ r₁ j₂ r₂ N : ℕ} (hr₁0 : 0 < r₁)
    (hr₁ : r₁ ≤ N) (hr₂0 : 0 < r₂) (hr₂ : r₂ ≤ N) (hcop₁ : Nat.Coprime j₁ r₁)
    (hcop₂ : Nat.Coprime j₂ r₂) (hα₁ : |α - (j₁ : ℝ) / r₁| < 1 / (2 * (N : ℝ) ^ 2))
    (hα₂ : |α - (j₂ : ℝ) / r₂| ≤ 1 / (2 * (N : ℝ) ^ 2)) : j₁ = j₂ ∧ r₁ = r₂ := by
  refine eq_of_coprime_of_abs_div_sub_lt hr₁0 hr₁ hr₂0 hr₂ hcop₁ hcop₂ ?_
  have htri : |(j₁ : ℝ) / r₁ - (j₂ : ℝ) / r₂| ≤ |α - (j₁ : ℝ) / r₁| + |α - (j₂ : ℝ) / r₂| := by
    rw [abs_sub_comm α ((j₁ : ℝ) / r₁)]
    exact abs_sub_le ((j₁ : ℝ) / r₁) α ((j₂ : ℝ) / r₂)
  have hsum : 1 / (2 * (N : ℝ) ^ 2) + 1 / (2 * (N : ℝ) ^ 2) = 1 / (N : ℝ) ^ 2 := by ring
  linarith

end Rat
