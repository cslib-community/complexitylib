/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent
import Complexity.Foundations.Data.Finset.OffDiag
import Complexity.Probability.KWiseIndependent.TugOfWar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Products of tug-of-war sums

Let `h i : X → Y` be a hash family with seed `i` drawn uniformly, and `ε : Y → ℝ` a sign of mean
zero and square one. For two weight functions `f g : X → ℝ` on a finite set `S`, the tug-of-war
sums `X = ∑ x ∈ S, f x ε (h i x)` and `Y = ∑ x ∈ S, g x ε (h i x)` with **shared signs** form the
**tug-of-war join signature** of Alon, Gibbons, Matias and Szegedy [AlonGibbonsMatiasSzegedy1999,
Lemma 4.4]: their product `XY` estimates the inner product `∑ x ∈ S, f x g x`, which for the
frequency vectors of two relations is their join size.

* under pairwise independence `𝔼 XY = ∑ f g`
  (`Cslib.Probability.IsKWiseIndependentHash.expect_sum_mul_sign_mul_sum_mul_sign`);
* under four-wise independence the variance is exactly
  `𝔼 (XY - ∑ f g)² = (∑ f²)(∑ g²) + (∑ f g)² - 2 ∑ f² g²`
  (`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub`), and
  so by the Cauchy–Schwarz inequality at most `2 (∑ f²)(∑ g²)`
  (`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub_le`).

For `f = g` these are the moments of the tug-of-war estimator of `F₂`
(`Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_sub_sq`). The source proves the
bound `2 (∑ f²)(∑ g²)` through the same exact expression, equation (3) of its proof.

## Main results

* `Cslib.Probability.IsKWiseIndependentHash.expect_sum_mul_sign_mul_sum_mul_sign`: the product of
  two tug-of-war sums with shared signs is an unbiased estimate of the inner product.
* `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub`,
  `Cslib.Probability.IsKWiseIndependentHash.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub_le`: its
  variance.

## References

* [N. Alon, P. B. Gibbons, Y. Matias, M. Szegedy, *Tracking join and self-join sizes in limited
  storage*, Lemma 4.4][AlonGibbonsMatiasSzegedy1999]
-/

public section

open Finset Fintype
open scoped BigOperators

namespace Cslib.Probability

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y]

namespace IsKWiseIndependentHash

variable {k : ℕ} {h : ι → X → Y} {ε : Y → ℝ}

/-- **The tug-of-war join signature is unbiased** [AlonGibbonsMatiasSzegedy1999, Lemma 4.4]: for a
pairwise independent family of signs of mean zero, the product of the tug-of-war sums of `f` and
`g` with shared signs has average `∑ x ∈ S, f x g x`. -/
theorem expect_sum_mul_sign_mul_sum_mul_sign (hh : IsKWiseIndependentHash 2 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f g : X → ℝ) :
    𝔼 i, (∑ x ∈ S, f x * ε (h i x)) * (∑ x ∈ S, g x * ε (h i x)) = ∑ x ∈ S, f x * g x := by
  classical
  have hι := hh.nonempty
  have hsplit (i : ι) : (∑ x ∈ S, f x * ε (h i x)) * (∑ x ∈ S, g x * ε (h i x)) =
      ∑ x ∈ S, f x * g x + ∑ p ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) := by
    rw [sum_mul_sum_eq_sum_mul_add_sum_offDiag]
    congr 1
    · refine sum_congr rfl fun x _ => ?_
      linear_combination f x * g x * hε (h i x)
    · exact sum_congr rfl fun p _ => by ring
  simp only [hsplit, expect_add_distrib, Fintype.expect_const, expect_sum_comm]
  rw [add_eq_left]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [← mul_expect, hh.expect_sign_mul_sign hε₀ (mem_offDiag.1 hp).2.2, mul_zero]

/-- **The variance of the tug-of-war join signature** [AlonGibbonsMatiasSzegedy1999, Lemma 4.4,
equation (3)]: for a four-wise independent family of signs of mean zero, the product of the
tug-of-war sums of `f` and `g` with shared signs has
`𝔼 (XY - ∑ f g)² = (∑ f²)(∑ g²) + (∑ f g)² - 2 ∑ f² g²`. -/
theorem expect_sq_sum_mul_sign_mul_sum_mul_sign_sub (hh : IsKWiseIndependentHash 4 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f g : X → ℝ) :
    𝔼 i, ((∑ x ∈ S, f x * ε (h i x)) * (∑ x ∈ S, g x * ε (h i x)) - ∑ x ∈ S, f x * g x) ^ 2 =
      (∑ x ∈ S, f x ^ 2) * (∑ x ∈ S, g x ^ 2) + (∑ x ∈ S, f x * g x) ^ 2 -
        2 * ∑ x ∈ S, f x ^ 2 * g x ^ 2 := by
  classical
  have hW (i : ι) : (∑ x ∈ S, f x * ε (h i x)) * (∑ x ∈ S, g x * ε (h i x)) -
      ∑ x ∈ S, f x * g x =
      ∑ p ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) := by
    rw [sum_mul_sum_eq_sum_mul_add_sum_offDiag]
    have hdiag : ∑ x ∈ S, f x * ε (h i x) * (g x * ε (h i x)) = ∑ x ∈ S, f x * g x :=
      sum_congr rfl fun x _ => by linear_combination f x * g x * hε (h i x)
    rw [hdiag, add_sub_cancel_left]
    exact sum_congr rfl fun p _ => by ring
  have hW2 (i : ι) : (∑ p ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2))) ^ 2 =
      ∑ p ∈ S.offDiag, ∑ q ∈ S.offDiag, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) *
        (f q.1 * g q.2 * (ε (h i q.1) * ε (h i q.2))) := by
    rw [sq, Finset.sum_mul_sum]
  simp only [hW, hW2, expect_sum_comm]
  have hterm : ∀ p ∈ S.offDiag, ∀ q ∈ S.offDiag,
      𝔼 i, f p.1 * g p.2 * (ε (h i p.1) * ε (h i p.2)) *
        (f q.1 * g q.2 * (ε (h i q.1) * ε (h i q.2))) =
      f p.1 * g p.2 * (f q.1 * g q.2) *
        (if (q.1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.2 ∧ q.2 = p.1) then 1 else 0) := by
    intro p hp q hq
    rw [← hh.expect_sign_mul_sign_mul_sign_mul_sign hε hε₀ (mem_offDiag.1 hp).2.2
      (mem_offDiag.1 hq).2.2, mul_expect]
    exact expect_congr rfl fun i _ => by ring
  have hinner : ∀ p ∈ S.offDiag, ∑ q ∈ S.offDiag, f p.1 * g p.2 * (f q.1 * g q.2) *
      (if (q.1 = p.1 ∧ q.2 = p.2) ∨ (q.1 = p.2 ∧ q.2 = p.1) then 1 else 0) =
      f p.1 ^ 2 * g p.2 ^ 2 + f p.1 * g p.1 * (f p.2 * g p.2) := by
    intro p hp
    obtain ⟨h1, h2, hne⟩ := mem_offDiag.1 hp
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
    simp only [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, hfilt, sum_pair hswap, Prod.fst_swap, Prod.snd_swap]
    ring
  rw [sum_congr rfl fun p hp => sum_congr rfl fun q hq => hterm p hp q hq,
    sum_congr rfl hinner, sum_add_distrib]
  have h1 := sum_mul_sum_eq_sum_mul_add_sum_offDiag S (fun x => f x ^ 2) fun x => g x ^ 2
  have h2 := sq_sum_eq_sum_sq_add_sum_offDiag S fun x => f x * g x
  have h3 : ∑ x ∈ S, (f x * g x) ^ 2 = ∑ x ∈ S, f x ^ 2 * g x ^ 2 :=
    sum_congr rfl fun x _ => by ring
  rw [h3] at h2
  linear_combination -h1 - h2

/-- **The variance bound for the tug-of-war join signature** [AlonGibbonsMatiasSzegedy1999,
Lemma 4.4]: for a four-wise independent family of signs of mean zero,
`𝔼 (XY - ∑ f g)² ≤ 2 (∑ f²)(∑ g²)`. -/
theorem expect_sq_sum_mul_sign_mul_sum_mul_sign_sub_le (hh : IsKWiseIndependentHash 4 h)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) (S : Finset X) (f g : X → ℝ) :
    𝔼 i, ((∑ x ∈ S, f x * ε (h i x)) * (∑ x ∈ S, g x * ε (h i x)) - ∑ x ∈ S, f x * g x) ^ 2 ≤
      2 * ((∑ x ∈ S, f x ^ 2) * (∑ x ∈ S, g x ^ 2)) := by
  rw [hh.expect_sq_sum_mul_sign_mul_sum_mul_sign_sub hε hε₀]
  have hcs := sum_mul_sq_le_sq_mul_sq S f g
  have : 0 ≤ ∑ x ∈ S, f x ^ 2 * g x ^ 2 := sum_nonneg fun x _ => by positivity
  linarith

end IsKWiseIndependentHash

end Cslib.Probability
