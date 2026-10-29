/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Probability.Fooling
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# One-sided approximation and `k`-wise independence

This file isolates the analytic part of [Braverman][Braverman2010]'s proof that bounded
independence fools `AC⁰`, which does not mention circuits. Braverman approximates a Boolean
function `F` from below by a low-degree polynomial that may depend on the distribution, so the
bounds here are one-sided; the two-sided bound follows by applying them to `F` and to its
negation (`Cslib.BitString.fools_bitVal_of_le`).

* **Mollification** [Braverman, Lemma 10]: suppose a real function `f` agrees with `F` off an
  error event `E`, is bounded by `L`, and `Ẽ` approximates the indicator of `E` in `L²` with error
  `δ`. Then `f (1 - Ẽ)` vanishes wherever `F ∨ E` is false, and its squared `L²` distance from
  `F ∨ E` is at most `2 P[E] + 2 L² δ`
  (`Cslib.BitString.expect_sq_bitVal_or_sub_mul_one_sub_le`).
* **Squaring trick** [Braverman, Lemma 11]: if `f` vanishes wherever a Boolean function `F'` is
  false, then `1 - (1 - f)²` lies below `F'`, has at most twice the degree of `f`, and its
  expected gap to `F'` is the squared `L²` distance from `f` to `F'`.
* **One-sided chain** [Braverman, proof of Lemma 12]: if a `k`-wise independent distribution `μ`
  and the uniform distribution both see `F ≠ F'` with probability at most `a`, and a polynomial
  of degree at most `k` lies below `F'` with expected gap at most `b`, then the expectation of `F`
  under `μ` is at least its uniform expectation minus `2 a + b`.

## Main results

* `Cslib.BitString.expect_sq_bitVal_or_sub_mul_one_sub_le`: the mollification bound.
* `Cslib.BitString.one_sub_one_sub_sq_le_bitVal`,
  `Cslib.BitString.expect_bitVal_sub_one_sub_one_sub_sq`,
  `Cslib.BitString.one_sub_one_sub_sq_mem_lowDegree`: the squaring trick.
* `Cslib.BitString.IsKWiseIndependent.expect_bitVal_sub_le_of_le`: the one-sided chain.
* `Cslib.BitString.IsKWiseIndependent.expect_bitVal_sub_le_of_eq_zero`: the squaring trick and the
  chain combined, [Braverman, Lemmas 11 and 12].
* `Cslib.BitString.IsKWiseIndependent.expect_bitVal_sub_le_of_witness`,
  `Cslib.BitString.IsKWiseIndependent.fools_bitVal_of_witness`: all three combined, for a function
  approximated off a rare witness event whose indicator has a low-degree `L²` approximation.

## References

Lemma numbers follow the ECCC report TR09-011.

* [M. Braverman, *Polylogarithmic independence fools `AC⁰` circuits*][Braverman2010]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*}

/-! ### Mollification -/

section Mollification

variable {F E : (ι → Bool) → Bool} {f e : (ι → Bool) → ℝ}

/-- If `f` agrees with `F` off `E`, then `F ∨ E` minus `f (1 - E)` is the indicator of `E`. -/
theorem bitVal_or_sub_mul_one_sub {x : ι → Bool} (hf : E x = false → f x = bitVal ℝ (F x)) :
    bitVal ℝ (F x || E x) - f x * (1 - bitVal ℝ (E x)) = bitVal ℝ (E x) := by
  cases hE : E x
  · rw [hf hE]
    simp
  · simp

/-- If `f` agrees with `F` off `E`, then `f (1 - e)` vanishes wherever `F ∨ E` is false. -/
theorem mul_one_sub_eq_zero_of_or_eq_false {x : ι → Bool}
    (hf : E x = false → f x = bitVal ℝ (F x)) (h : (F x || E x) = false) :
    f x * (1 - e x) = 0 := by
  rw [Bool.or_eq_false_iff] at h
  rw [hf h.2, h.1, bitVal_false, zero_mul]

/-- **Mollification** [Braverman, Lemma 10]: if `f` agrees with `F` off `E` and is bounded by `L`,
then the squared `L²` distance from `F ∨ E` to `f (1 - e)` is at most twice the probability of `E`
plus `2 L²` times the squared `L²` distance from the indicator of `E` to `e`. -/
theorem expect_sq_bitVal_or_sub_mul_one_sub_le [Fintype ι] [DecidableEq ι] {L : ℝ}
    (hf : ∀ x, E x = false → f x = bitVal ℝ (F x)) (hL : ∀ x, |f x| ≤ L) :
    𝔼 x, (bitVal ℝ (F x || E x) - f x * (1 - e x)) ^ 2 ≤
      2 * 𝔼 x, bitVal ℝ (E x) + 2 * L ^ 2 * 𝔼 x, (bitVal ℝ (E x) - e x) ^ 2 := by
  rw [mul_expect, mul_expect, ← expect_add_distrib]
  refine expect_le_expect fun x _ => ?_
  have h := bitVal_or_sub_mul_one_sub (hf x)
  have hsq : f x ^ 2 ≤ L ^ 2 := sq_le_sq' (abs_le.1 (hL x)).1 (abs_le.1 (hL x)).2
  have hE : bitVal ℝ (E x) ^ 2 = bitVal ℝ (E x) := bitVal_pow _ two_ne_zero
  have hd : bitVal ℝ (F x || E x) - f x * (1 - e x) =
      bitVal ℝ (E x) + f x * (e x - bitVal ℝ (E x)) := by
    linear_combination h
  rw [hd]
  nlinarith [sq_nonneg (bitVal ℝ (E x) - f x * (e x - bitVal ℝ (E x))),
    mul_le_mul_of_nonneg_right hsq (sq_nonneg (bitVal ℝ (E x) - e x))]

end Mollification

/-! ### The squaring trick -/

section Squaring

variable {F' : (ι → Bool) → Bool} {f : (ι → Bool) → ℝ}

/-- If `f` vanishes wherever `F'` is false, then the gap from `1 - (1 - f)²` to `F'` is the
square of the gap from `f` to `F'` [Braverman, Lemma 11]. -/
theorem bitVal_sub_one_sub_one_sub_sq {x : ι → Bool} (hf : F' x = false → f x = 0) :
    bitVal ℝ (F' x) - (1 - (1 - f x) ^ 2) = (bitVal ℝ (F' x) - f x) ^ 2 := by
  cases hF : F' x
  · simp [hf hF]
  · simp only [bitVal_true]
    ring

/-- If `f` vanishes wherever `F'` is false, then `1 - (1 - f)²` lies below `F'`
[Braverman, Lemma 11]. -/
theorem one_sub_one_sub_sq_le_bitVal {x : ι → Bool} (hf : F' x = false → f x = 0) :
    1 - (1 - f x) ^ 2 ≤ bitVal ℝ (F' x) := by
  have h := bitVal_sub_one_sub_one_sub_sq hf
  nlinarith [sq_nonneg (bitVal ℝ (F' x) - f x)]

/-- If `f` vanishes wherever `F'` is false, then the expected gap from `1 - (1 - f)²` to `F'` is
the squared `L²` distance from `f` to `F'` [Braverman, Lemma 11]. -/
theorem expect_bitVal_sub_one_sub_one_sub_sq [Fintype ι] [DecidableEq ι]
    (hf : ∀ x, F' x = false → f x = 0) :
    𝔼 x, (bitVal ℝ (F' x) - (1 - (1 - f x) ^ 2)) = 𝔼 x, (bitVal ℝ (F' x) - f x) ^ 2 :=
  expect_congr rfl fun x _ => bitVal_sub_one_sub_one_sub_sq (hf x)

/-- If `f` has degree at most `D`, then `1 - (1 - f)²` has degree at most `2 D`
[Braverman, Lemma 11]. -/
theorem one_sub_one_sub_sq_mem_lowDegree {R : Type*} [CommRing R] {g : (ι → Bool) → R} {D : ℕ}
    (hg : g ∈ lowDegree R ι D) : (fun x => 1 - (1 - g x) ^ 2) ∈ lowDegree R ι (2 * D) :=
  one_sub_mem_lowDegree (pow_mem_lowDegree (one_sub_mem_lowDegree hg) 2)

end Squaring

/-! ### The one-sided chain -/

namespace IsKWiseIndependent

variable [Fintype ι] [DecidableEq ι] {k : ℕ} {X : PMF (ι → Bool)} {F F' : (ι → Bool) → Bool}
  {a b : ℝ}

/-- Expectations under a distribution are monotone. -/
private theorem sum_mul_le_sum_mul (X : PMF (ι → Bool)) {g h : (ι → Bool) → ℝ}
    (hgh : ∀ x, g x ≤ h x) : ∑ x, (X x).toReal * g x ≤ ∑ x, (X x).toReal * h x :=
  sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hgh x) ENNReal.toReal_nonneg

/-- Two Boolean functions differ by at most the indicator of their disagreement. -/
private theorem bitVal_sub_bitVal_xor_le (b c : Bool) :
    bitVal ℝ b - bitVal ℝ (b ^^ c) ≤ bitVal ℝ c := by
  cases b <;> cases c <;> norm_num

/-- **The one-sided chain** [Braverman, proof of Lemma 12]: suppose `F'` disagrees with `F` with
probability at most `a` under both a `k`-wise independent distribution `X` and the uniform
distribution, and `p` has degree at most `k`, lies below `F'` and has expected gap at most `b` to
`F'`. Then the expectation of `F` under `X` is at least its uniform expectation minus
`2 a + b`. -/
theorem expect_bitVal_sub_le_of_le (hX : IsKWiseIndependent k X) {p : (ι → Bool) → ℝ}
    (hpk : p ∈ lowDegree ℝ ι k) (hpF : ∀ x, p x ≤ bitVal ℝ (F' x))
    (hXa : ∑ x, (X x).toReal * bitVal ℝ (F x ^^ F' x) ≤ a)
    (hUa : 𝔼 x, bitVal ℝ (F x ^^ F' x) ≤ a) (hb : 𝔼 x, (bitVal ℝ (F' x) - p x) ≤ b) :
    𝔼 x, bitVal ℝ (F x) - 2 * a - b ≤ ∑ x, (X x).toReal * bitVal ℝ (F x) := by
  have hXF : ∑ x, (X x).toReal * p x - a ≤ ∑ x, (X x).toReal * bitVal ℝ (F x) := by
    have h := sum_mul_le_sum_mul X fun x =>
      (hpF x).trans ((sub_le_iff_le_add.1 (bitVal_sub_bitVal_xor_le (F' x) (F x))).trans_eq
        (by rw [Bool.xor_comm]))
    simp only [mul_add, sum_add_distrib] at h
    linarith
  have hUF : 𝔼 x, bitVal ℝ (F x) - a ≤ 𝔼 x, bitVal ℝ (F' x) := by
    have h : 𝔼 x, bitVal ℝ (F x) ≤ 𝔼 x, (bitVal ℝ (F' x) + bitVal ℝ (F x ^^ F' x)) :=
      expect_le_expect fun x _ => by linarith [bitVal_sub_bitVal_xor_le (F x) (F' x)]
    rw [expect_add_distrib] at h
    linarith
  rw [expect_sub_distrib] at hb
  rw [hX.sum_mul_eq_expect_of_mem_lowDegree hpk] at hXF
  linarith

/-- **Low-degree approximations vanishing off `F'` give one-sided bounds**
[Braverman, Lemmas 11 and 12]: suppose `F'` disagrees with `F` with probability at most `a` under
both a `k`-wise independent distribution `X` and the uniform distribution, and `f` has degree at
most `D` with `2 D ≤ k`, vanishes wherever `F'` is false and has squared `L²` distance at most `b`
to `F'`. Then the expectation of `F` under `X` is at least its uniform expectation minus
`2 a + b`. -/
theorem expect_bitVal_sub_le_of_eq_zero (hX : IsKWiseIndependent k X) {f : (ι → Bool) → ℝ}
    {D : ℕ} (hf : f ∈ lowDegree ℝ ι D) (hDk : 2 * D ≤ k) (hf0 : ∀ x, F' x = false → f x = 0)
    (hXa : ∑ x, (X x).toReal * bitVal ℝ (F x ^^ F' x) ≤ a)
    (hUa : 𝔼 x, bitVal ℝ (F x ^^ F' x) ≤ a) (hb : 𝔼 x, (bitVal ℝ (F' x) - f x) ^ 2 ≤ b) :
    𝔼 x, bitVal ℝ (F x) - 2 * a - b ≤ ∑ x, (X x).toReal * bitVal ℝ (F x) :=
  hX.expect_bitVal_sub_le_of_le (lowDegree_mono hDk (one_sub_one_sub_sq_mem_lowDegree hf))
    (fun x => one_sub_one_sub_sq_le_bitVal (hf0 x)) hXa hUa
    ((expect_bitVal_sub_one_sub_one_sub_sq hf0).trans_le hb)

section Witness

variable {E : (ι → Bool) → Bool} {f e : (ι → Bool) → ℝ} {D t : ℕ} {L δ : ℝ}

/-- **One-sided bound from an approximation with a witness** [Braverman, Lemmas 10–12]: suppose
`f` has degree at most `D`, is bounded by `L` and agrees with `F` wherever an event `E` fails, `E`
has probability at most `a` under both a `k`-wise independent distribution `X` and the uniform
distribution, and `e` of degree at most `t`, with `2 (D + t) ≤ k`, approximates the indicator of
`E` with squared `L²` error at most `δ`. Then the expectation of `F` under `X` is at least its
uniform expectation minus `4 a + 2 L² δ`. -/
theorem expect_bitVal_sub_le_of_witness (hX : IsKWiseIndependent k X)
    (hf : f ∈ lowDegree ℝ ι D) (he : e ∈ lowDegree ℝ ι t) (hk : 2 * (D + t) ≤ k)
    (hfE : ∀ x, E x = false → f x = bitVal ℝ (F x)) (hL : ∀ x, |f x| ≤ L)
    (hXE : ∑ x, (X x).toReal * bitVal ℝ (E x) ≤ a) (hUE : 𝔼 x, bitVal ℝ (E x) ≤ a)
    (hδ : 𝔼 x, (bitVal ℝ (E x) - e x) ^ 2 ≤ δ) :
    𝔼 x, bitVal ℝ (F x) - 4 * a - 2 * L ^ 2 * δ ≤ ∑ x, (X x).toReal * bitVal ℝ (F x) := by
  have hxor (x : ι → Bool) : bitVal ℝ (F x ^^ (F x || E x)) ≤ bitVal ℝ (E x) := by
    cases F x <;> cases E x <;> norm_num
  have hb : 𝔼 x, (bitVal ℝ (F x || E x) - f x * (1 - e x)) ^ 2 ≤ 2 * a + 2 * L ^ 2 * δ :=
    (expect_sq_bitVal_or_sub_mul_one_sub_le hfE hL).trans (by gcongr)
  have h := hX.expect_bitVal_sub_le_of_eq_zero (F' := fun x => F x || E x)
    (mul_mem_lowDegree hf (one_sub_mem_lowDegree he)) hk
    (fun x hx => mul_one_sub_eq_zero_of_or_eq_false (hfE x) hx)
    ((sum_mul_le_sum_mul X hxor).trans hXE) ((expect_le_expect fun x _ => hxor x).trans hUE) hb
  linarith

/-- **Fooling from an approximation with a witness** [Braverman, Lemmas 10–12 and Main Theorem]:
under the hypotheses of `expect_bitVal_sub_le_of_witness`, the `k`-wise independent distribution
`X` fools `F` with error `4 a + 2 (L + 1)² δ`.

Braverman obtains the other direction by applying Lemma 12 to `1 - F`, with a fresh
approximation; reusing `f` and the witness via `1 - f` is our variant (it avoids a NOT layer). -/
theorem fools_bitVal_of_witness (hX : IsKWiseIndependent k X)
    (hf : f ∈ lowDegree ℝ ι D) (he : e ∈ lowDegree ℝ ι t) (hk : 2 * (D + t) ≤ k)
    (hfE : ∀ x, E x = false → f x = bitVal ℝ (F x)) (hL : ∀ x, |f x| ≤ L)
    (hXE : ∑ x, (X x).toReal * bitVal ℝ (E x) ≤ a) (hUE : 𝔼 x, bitVal ℝ (E x) ≤ a)
    (hδ : 𝔼 x, (bitVal ℝ (E x) - e x) ^ 2 ≤ δ) :
    Fools X (4 * a + 2 * (L + 1) ^ 2 * δ) fun x => bitVal ℝ (F x) := by
  refine fools_bitVal_of_le ?_ ?_
  · have h := hX.expect_bitVal_sub_le_of_witness hf he hk hfE
      (fun x => (hL x).trans (le_add_of_nonneg_right zero_le_one)) hXE hUE hδ
    linarith
  · have h := hX.expect_bitVal_sub_le_of_witness (F := fun x => !F x) (f := fun x => 1 - f x)
      (one_sub_mem_lowDegree hf) he hk (fun x hx => by rw [hfE x hx, bitVal_not])
      (fun x => show |1 - f x| ≤ L + 1 from
        abs_le.2 ⟨by linarith [(abs_le.1 (hL x)).2], by linarith [(abs_le.1 (hL x)).1]⟩)
      hXE hUE hδ
    linarith

end Witness

end IsKWiseIndependent

end Cslib.BitString
