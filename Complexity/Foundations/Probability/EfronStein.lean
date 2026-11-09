/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The Efron–Stein inequality for uniform averages

For a function `f` of a spectator `y` and of a uniformly random tuple `w : Fin n → A`, the second
moment of `f` about its average over `w` is at most the sum, over the coordinates `i`, of the second
moments of `f` about its averages over the single coordinate `w i`
(`Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update`):
`𝔼 (f - 𝔼_w f)² ≤ ∑ i, 𝔼 (f - 𝔼_{w i} f)²`. This is the Efron–Stein inequality
[Efron and Stein][EfronStein1981] in the general form for functions that need not be symmetric
[Steele][Steele1986], for the uniform product measure and with the spectator as an extra fixed
coordinate. It reduces the distance of `f`
from the functions of `y` alone to its distances from the functions not depending on one coordinate
at a time.

The proof is by induction on `n`: split `w = Fin.cons a r`, decompose orthogonally over the fibers
of `(y, a)`, apply the induction hypothesis with the spectator `(y, a)` to the part of average zero
on these fibers, and bound the fiber averages by Jensen's inequality.

## Main results

* `Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update`: the Efron–Stein inequality.
* `Fintype.expect_sq_sub_expect_update_le`: the average over one coordinate is the best
  approximation by functions not depending on it.

## References

* [B. Efron, C. Stein, *The Jackknife Estimate of Variance*][EfronStein1981]
* [J. M. Steele, *An Efron-Stein Inequality for Nonsymmetric Statistics*][Steele1986]
-/

public section

open Finset Function
open scoped BigOperators

namespace Fintype

/-- The second moment about a constant is the second moment about the average plus the squared
distance of the average from the constant. -/
private theorem expect_sub_sq_eq {R : Type*} [Fintype R] [Nonempty R] (X : R → ℝ) (c : ℝ) :
    𝔼 r, (X r - c) ^ 2 = 𝔼 r, (X r - 𝔼 s, X s) ^ 2 + (𝔼 s, X s - c) ^ 2 := by
  set m := 𝔼 s, X s
  have h : 𝔼 r, (X r - m) = 0 := by rw [expect_sub_distrib, Fintype.expect_const, sub_self]
  calc 𝔼 r, (X r - c) ^ 2 = 𝔼 r, ((X r - m) ^ 2 + 2 * (m - c) * (X r - m) + (m - c) ^ 2) :=
        expect_congr rfl fun r _ ↦ by ring
    _ = _ := by rw [expect_add_distrib, expect_add_distrib, ← mul_expect, h, mul_zero, add_zero,
        Fintype.expect_const]

/-- **The average over one coordinate is the best approximation** by functions not depending on
that coordinate: if `G` does not change when `w i` is resampled, then the second moment of `f` about
its average over `w i` is at most the second moment of `f - G`. -/
theorem expect_sq_sub_expect_update_le {ι Y A : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y]
    [Fintype A] [Nonempty A] (i : ι) (f G : Y × (ι → A) → ℝ)
    (hG : ∀ p c, G (p.1, update p.2 i c) = G p) :
    𝔼 p, (f p - 𝔼 a, f (p.1, update p.2 i a)) ^ 2 ≤ 𝔼 p, (f p - G p) ^ 2 := by
  set R : Y × (ι → A) → ℝ := fun p ↦ 𝔼 a, f (p.1, update p.2 i a) with hR
  -- The part of `f` of average zero over `w i` is orthogonal to the functions not depending on it.
  have horth : 𝔼 p, (f p - R p) * (R p - G p) = 0 := by
    rw [Fintype.expect_prod_type]
    refine expect_eq_zero fun y _ ↦ ?_
    rw [← Fintype.expect_expect_update _ i]
    refine expect_eq_zero fun w _ ↦ ?_
    have h2 (a : A) : G (y, update w i a) = G (y, w) := hG (y, w) a
    simp only [hR, update_idem, h2]
    rw [← expect_mul, expect_sub_distrib, Fintype.expect_const, sub_self, zero_mul]
  calc 𝔼 p, (f p - R p) ^ 2 ≤ 𝔼 p, ((f p - R p) ^ 2 + 2 * ((f p - R p) * (R p - G p)) +
        (R p - G p) ^ 2) := by
        rw [expect_add_distrib, expect_add_distrib, ← mul_expect, horth, mul_zero, add_zero]
        exact le_add_of_nonneg_right (expect_nonneg fun _ _ ↦ sq_nonneg _)
    _ = 𝔼 p, (f p - G p) ^ 2 := expect_congr rfl fun p _ ↦ by ring

universe u

variable {A : Type u} [Fintype A] [Nonempty A]

/-- **The Efron–Stein inequality** for a uniformly random tuple `w : Fin n → A` and a spectator
`y`: the second moment of `f` about its average over `w` is at most the sum over the coordinates
`i` of the second moments of `f` about its averages over `w i`. The spectator lives in the
universe of `A`, so that the induction can absorb coordinates into it. -/
theorem expect_sq_sub_expect_le_sum_expect_sq_sub_update {n : ℕ} {Y : Type u} [Fintype Y]
    (f : Y × (Fin n → A) → ℝ) :
    𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 ≤ ∑ i, 𝔼 p, (f p - 𝔼 a, f (p.1, update p.2 i a)) ^ 2 := by
  induction n generalizing Y with
  | zero =>
    have h (p : Y × (Fin 0 → A)) : f p - 𝔼 w, f (p.1, w) = 0 := by
      rw [Fintype.expect_unique, sub_eq_zero]
      exact congrArg f (Prod.ext rfl (Subsingleton.elim _ _))
    simp only [h]
    simp
  | succ n ih =>
    -- Split the tuple into its head `a` and tail `r`.
    have hsplit (G : Y × (Fin (n + 1) → A) → ℝ) :
        𝔼 p, G p = 𝔼 y, 𝔼 a, 𝔼 r : Fin n → A, G (y, Fin.cons a r) := by
      rw [Fintype.expect_prod_type]
      exact expect_congr rfl fun y _ ↦ Fin.expect_univ_cons fun w ↦ G (y, w)
    set g : (Y × A) × (Fin n → A) → ℝ := fun q ↦ f (q.1.1, Fin.cons q.1.2 q.2) with hg
    have hIH := ih g
    have hsplit' (G : (Y × A) × (Fin n → A) → ℝ) :
        𝔼 q, G q = 𝔼 y, 𝔼 a, 𝔼 r, G ((y, a), r) := by
      rw [Fintype.expect_prod_type, Fintype.expect_prod_type]
    -- The average over the whole tuple, and over its tail.
    set h : Y × A → ℝ := fun q ↦ 𝔼 r, g (q, r) with hh
    have hM (y : Y) : 𝔼 w, f (y, w) = 𝔼 a, h (y, a) := Fin.expect_univ_cons fun w ↦ f (y, w)
    -- Orthogonal decomposition over the fibers of `(y, a)`.
    have hLHS : 𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 =
        𝔼 q, (g q - 𝔼 r, g (q.1, r)) ^ 2 + 𝔼 y, 𝔼 a, (h (y, a) - 𝔼 a', h (y, a')) ^ 2 := by
      rw [hsplit, hsplit', ← expect_add_distrib]
      refine expect_congr rfl fun y _ ↦ ?_
      rw [← expect_add_distrib]
      refine expect_congr rfl fun a _ ↦ ?_
      simp only [hM]
      exact expect_sub_sq_eq (fun r ↦ g ((y, a), r)) _
    -- The tail coordinates, by the induction hypothesis.
    have htail (i : Fin n) : 𝔼 q, (g q - 𝔼 b, g (q.1, update q.2 i b)) ^ 2 =
        𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 i.succ b)) ^ 2 := by
      rw [hsplit, hsplit']
      simp only [hg, Fin.cons_update]
    -- The head coordinate, by Jensen's inequality.
    have hhead : 𝔼 y, 𝔼 a, (h (y, a) - 𝔼 a', h (y, a')) ^ 2 ≤
        𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 0 b)) ^ 2 := by
      rw [hsplit]
      refine expect_le_expect fun y _ ↦ expect_le_expect fun a _ ↦ ?_
      have : h (y, a) - 𝔼 a', h (y, a') =
          𝔼 r, (f (y, Fin.cons a r) - 𝔼 b, f (y, update (Fin.cons a r) 0 b)) := by
        simp only [hh, hg, Fin.update_cons_zero, expect_sub_distrib]
        rw [expect_comm]
      rw [this]
      exact sq_expect_le_expect_sq _ _
    rw [hLHS, Fin.sum_univ_succ]
    calc _ ≤ ∑ i : Fin n, 𝔼 q, (g q - 𝔼 b, g (q.1, update q.2 i b)) ^ 2 +
          𝔼 p, (f p - 𝔼 b, f (p.1, update p.2 0 b)) ^ 2 := add_le_add hIH hhead
      _ = _ := by rw [add_comm]; simp only [htail]

end Fintype
