/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent
public import Mathlib.Data.Finset.Prod
import CslibFrontier.Foundations.Data.Finset.OffDiag
import CslibFrontier.Probability.KWiseIndependent.SecondMoment
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Moments of tug-of-war sums

Let `h i : X → Y` be a hash family with seed `i` drawn uniformly, and `ε : Y → ℝ` a sign of mean
zero and square one, so that `ε (h i x)` is a random sign attached to each point `x`. For weights
`f : X → ℝ` on a finite set `S`, the **tug-of-war sum** `Z = ∑ x ∈ S, f x ε (h i x)` of Alon,
Matias and Szegedy [AlonMatiasSzegedy1999] estimates `∑ x ∈ S, f x ²`:

* under pairwise independence `𝔼 Z² = ∑ f²`
  (`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign`);
* under four-wise independence `𝔼 (Z² - ∑ f²)² = 2 ((∑ f²)² - ∑ f⁴) ≤ 2 (∑ f²)²`
  (`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`,
  `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq_le`), and so
  `𝔼 Z⁴ = 3 (∑ f²)² - 2 ∑ f⁴`.

These are the two moment computations in the proof of [AlonMatiasSzegedy1999, Theorem 2.2]. The
first is an instance of the additivity of second moments under pairwise independence
(`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum`, in
`CslibFrontier.Probability.KWiseIndependent.SecondMoment`); both expand squares of sums with
`Finset.sq_sum_eq_sum_sq_add_sum_offDiag`.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_prod_sign`: averages of products of signs at
  at most `k` points.
* `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign`: the tug-of-war estimator is
  unbiased.
* `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_offDiag_mul_sign_mul_sign`: the second
  moment of a sum over ordered pairs of signs, the common step of the variance computations here
  and in `CslibFrontier.Probability.KWiseIndependent.TugOfWarProduct`.
* `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`,
  `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq_le`,
  `Cslib.Probability.IsKWiseIndependentHash.expect_sum_mul_sign_pow_four`: its variance and fourth
  moment.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*, Theorem 2.2][AlonMatiasSzegedy1999]
-/

public section

open Finset Fintype
open scoped BigOperators

namespace Cslib.Probability

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]

namespace IsKWiseIndependentHash

variable {k : ℕ} {h : ι → X → Y} {ε : Y → ℝ}

omit [DecidableEq Y] in
/-- An average of powers of a sign with mean zero. -/
private theorem expect_pow_sign [Nonempty Y] (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0)
    (m : ℕ) : 𝔼 y, ε y ^ m = if Even m then 1 else 0 := by
  obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' m
  · simp only [pow_mul, hε, one_pow, Fintype.expect_const, even_two_mul, ite_true]
  · have hodd : ¬Even (2 * q + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one q)
    simp only [pow_succ, pow_mul, hε, one_pow, one_mul, hε₀, hodd, ite_false]

/-- Signs with mean zero and square one: a product of signs at the points of a tuple of at most
`k` distinct points has average one when every point occurs an even number of times, and zero
otherwise. -/
theorem expect_prod_sign [DecidableEq X] (hh : IsKWiseIndependentHash k h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) {n : ℕ} (t : Fin n → X)
    (ht : #(univ.image t) ≤ k) :
    𝔼 i, ∏ j, ε (h i (t j)) = if ∀ j, Even #{j' | t j' = t j} then 1 else 0 := by
  have hι := hh.nonempty
  have hgroup (i : ι) : ∏ j, ε (h i (t j)) =
      ∏ x ∈ univ.image t, ε (h i x) ^ #{j | t j = x} :=
    prod_comp (fun x => ε (h i x)) t
  simp only [hgroup]
  rw [hh.expect_prod ht (fun x y => ε y ^ #{j | t j = x})]
  rw [prod_congr rfl fun x _ =>
    have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
    expect_pow_sign hε hε₀ #{j | t j = x}]
  rw [Finset.prod_boole]
  congr 1
  simp only [mem_image, mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]

/-- Signs at two distinct points are uncorrelated. -/
theorem expect_sign_mul_sign (hh : IsKWiseIndependentHash 2 h) (hε₀ : 𝔼 y, ε y = 0) {x x' : X}
    (hx : x ≠ x') : 𝔼 i, ε (h i x) * ε (h i x') = 0 := by
  classical
  have := hh.expect_prod (T := {x, x'}) card_le_two fun _ y => ε y
  simp only [prod_pair hx, hε₀, zero_mul] at this
  exact this

/-- The product of the signs at two pairs of distinct points has average one if the pairs agree
up to order, and zero otherwise. -/
theorem expect_sign_mul_sign_mul_sign_mul_sign [DecidableEq X] (hh : IsKWiseIndependentHash 4 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d) :
    𝔼 i, ε (h i a) * ε (h i b) * (ε (h i c) * ε (h i d)) =
      if (c = a ∧ d = b) ∨ (c = b ∧ d = a) then 1 else 0 := by
  have h4 := hh.expect_prod_sign hε hε₀ ![a, b, c, d]
    (card_image_le.trans (by simp))
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h4
  simp only [mul_assoc] at h4 ⊢
  rw [h4]
  congr 1
  simp only [Fin.forall_fin_succ, Fin.isValue, IsEmpty.forall_iff, and_true, Finset.card_filter,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ]
  apply propext
  by_cases hca : c = a <;> by_cases hda : d = a <;> by_cases hcb : c = b <;>
    by_cases hdb : d = b <;>
    simp only [hca, hda, hcb, hdb, hab, hab.symm, hcd, hcd.symm, ite_true, ite_false,
      Nat.even_iff] <;> (try split_ifs) <;> simp_all

/-- **The tug-of-war estimator is unbiased** [AlonMatiasSzegedy1999, Theorem 2.2]: for a pairwise
independent family of signs `ε (h i x)` with mean zero and square one,
`Z = ∑ x ∈ S, f x ε (h i x)` has `𝔼 Z² = ∑ x ∈ S, f x ²`. -/
theorem expect_sq_sum_mul_sign (hh : IsKWiseIndependentHash 2 h) (hε : ∀ y, ε y ^ 2 = 1)
    (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f : X → ℝ) :
    𝔼 i, (∑ x ∈ S, f x * ε (h i x)) ^ 2 = ∑ x ∈ S, f x ^ 2 := by
  have hι := hh.nonempty
  rw [hh.expect_sq_sum S (fun x y => f x * ε y) fun x _ => by rw [← mul_expect, hε₀, mul_zero]]
  refine sum_congr rfl fun x _ => ?_
  have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
  simp only [mul_pow, hε, mul_one, Fintype.expect_const]

/-- **The second moment of a sum over ordered pairs of signs**: for a four-wise independent family
of signs of mean zero and square one, `W = ∑_{x ≠ y ∈ S} f x g y ε (h i x) ε (h i y)` has
`𝔼 W² = ∑_{x ≠ y ∈ S} f x g y (f x g y + f y g x)`, since the products of the signs at two pairs of
distinct points average to zero unless the pairs agree up to order. Both the variance of the
tug-of-war estimator and that of the join signature reduce to it. -/
theorem expect_sq_sum_offDiag_mul_sign_mul_sign (hh : IsKWiseIndependentHash 4 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f g : X → ℝ) :
    𝔼 i, (∑ p ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2))) ^ 2 =
      ∑ p ∈ S.offDiag, (f p.1 ^ 2 * g p.2 ^ 2 + f p.1 * g p.1 * (f p.2 * g p.2)) := by
  classical
  have hW2 (i : ι) : (∑ p ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2))) ^ 2 =
      ∑ p ∈ S.offDiag, ∑ q ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) *
        (f q.1 * g q.2 * (ε (h i q.1) * ε (h i q.2))) := by
    rw [sq, Finset.sum_mul_sum]
  simp only [hW2, expect_sum_comm]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, hne⟩ := mem_offDiag.1 hp
  -- Only the pairs `q = p` and `q = p.swap` contribute.
  have hterm : ∀ q ∈ S.offDiag,
      𝔼 i, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) *
        (f q.1 * g q.2 * (ε (h i q.1) * ε (h i q.2))) =
      f p.1 * g p.2 * (f q.1 * g q.2) *
        (if (q.1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.2 ∧ q.2 = p.1) then 1 else 0) := by
    intro q hq
    rw [← hh.expect_sign_mul_sign_mul_sign_mul_sign hε hε₀ hne (mem_offDiag.1 hq).2.2,
      mul_expect]
    exact expect_congr rfl fun i _ => by ring
  have hfilt : S.offDiag.filter
      (fun q : X × X => (q.1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.2 ∧ q.2 = p.1)) = {p, p.swap} := by
    ext ⟨q1, q2⟩
    simp only [mem_filter, mem_offDiag, mem_insert, mem_singleton, Prod.ext_iff,
      Prod.fst_swap, Prod.snd_swap]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨⟨h1, h2, hne⟩, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨⟨h2, h1, hne.symm⟩, Or.inr ⟨rfl, rfl⟩⟩
  have hswap : p ≠ p.swap := fun h => hne ((congrArg Prod.fst h).trans Prod.fst_swap)
  rw [sum_congr rfl hterm]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter, hfilt, sum_pair hswap, Prod.fst_swap, Prod.snd_swap]
  ring

/-- **The variance of the tug-of-war estimator** [AlonMatiasSzegedy1999, Theorem 2.2]: for a
four-wise independent family of signs, `Z = ∑ x ∈ S, f x ε (h i x)` has
`𝔼 (Z² - ∑ f²)² = 2 ((∑ f²)² - ∑ f⁴)`. -/
theorem expect_sq_sum_mul_sign_sub_sq (hh : IsKWiseIndependentHash 4 h) (hε : ∀ y, ε y ^ 2 = 1)
    (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f : X → ℝ) :
    𝔼 i, ((∑ x ∈ S, f x * ε (h i x)) ^ 2 - ∑ x ∈ S, f x ^ 2) ^ 2 =
      2 * ((∑ x ∈ S, f x ^ 2) ^ 2 - ∑ x ∈ S, f x ^ 4) := by
  classical
  have hW (i : ι) : (∑ x ∈ S, f x * ε (h i x)) ^ 2 - ∑ x ∈ S, f x ^ 2 =
      ∑ p ∈ S.offDiag, f p.1 * f p.2 * (ε (h i p.1) * ε (h i p.2)) := by
    rw [sq_sum_eq_sum_sq_add_sum_offDiag]
    simp only [mul_pow, hε, mul_one, add_sub_cancel_left]
    exact sum_congr rfl fun p _ => by ring
  simp only [hW]
  rw [hh.expect_sq_sum_offDiag_mul_sign_mul_sign hε hε₀ S f f]
  have hpair : ∀ p ∈ S.offDiag, f p.1 ^ 2 * f p.2 ^ 2 + f p.1 * f p.1 * (f p.2 * f p.2) =
      2 * (f p.1 ^ 2 * f p.2 ^ 2) := fun p _ => by ring
  rw [sum_congr rfl hpair, ← mul_sum, sq_sum_eq_sum_sq_add_sum_offDiag S fun x => f x ^ 2]
  have h4 : ∀ x ∈ S, (f x ^ 2) ^ 2 = f x ^ 4 := fun x _ => by ring
  rw [sum_congr rfl h4]
  ring

/-- **The fourth moment of the tug-of-war sum** [AlonMatiasSzegedy1999, Theorem 2.2]: for a
four-wise independent family of signs, `𝔼 Z⁴ = 3 (∑ f²)² - 2 ∑ f⁴`, that is
`∑ f⁴ + 6 ∑_{x < y} f(x)² f(y)²`. -/
theorem expect_sum_mul_sign_pow_four (hh : IsKWiseIndependentHash 4 h) (hε : ∀ y, ε y ^ 2 = 1)
    (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f : X → ℝ) :
    𝔼 i, (∑ x ∈ S, f x * ε (h i x)) ^ 4 = 3 * (∑ x ∈ S, f x ^ 2) ^ 2 - 2 * ∑ x ∈ S, f x ^ 4 := by
  have hι := hh.nonempty
  have hdecomp (i : ι) : (∑ x ∈ S, f x * ε (h i x)) ^ 4 =
      ((∑ x ∈ S, f x * ε (h i x)) ^ 2 - ∑ x ∈ S, f x ^ 2) ^ 2 +
        2 * (∑ x ∈ S, f x ^ 2) * (∑ x ∈ S, f x * ε (h i x)) ^ 2 - (∑ x ∈ S, f x ^ 2) ^ 2 := by
    ring
  simp only [hdecomp, expect_sub_distrib, expect_add_distrib, ← mul_expect, Fintype.expect_const,
    hh.expect_sq_sum_mul_sign_sub_sq hε hε₀,
    (hh.mono (by norm_num : 2 ≤ 4)).expect_sq_sum_mul_sign hε hε₀]
  ring

/-- **The variance bound for the tug-of-war estimator** [AlonMatiasSzegedy1999, Theorem 2.2]: for
a four-wise independent family of signs, `𝔼 (Z² - ∑ f²)² ≤ 2 (∑ f²)²`. -/
theorem expect_sq_sum_mul_sign_sub_sq_le (hh : IsKWiseIndependentHash 4 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f : X → ℝ) :
    𝔼 i, ((∑ x ∈ S, f x * ε (h i x)) ^ 2 - ∑ x ∈ S, f x ^ 2) ^ 2 ≤
      2 * (∑ x ∈ S, f x ^ 2) ^ 2 := by
  rw [hh.expect_sq_sum_mul_sign_sub_sq hε hε₀]
  have : 0 ≤ ∑ x ∈ S, f x ^ 4 := sum_nonneg fun x _ => by positivity
  linarith

end IsKWiseIndependentHash

end Cslib.Probability
