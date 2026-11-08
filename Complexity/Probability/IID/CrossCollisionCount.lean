/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.IID.CollisionCount

/-!
# Cross-collision counts of two independent samples

`Cslib.Probability.PMF.crossCollisionCount x y` is the number of pairs `(i, j)` of positions with
`x i = y j`, for samples `x : Fin k → α` and `y : Fin l → α`. It is the sum over values `a` of the
products of the occurrence counts of `a` in `x` and in `y` (`crossCollisionCount_eq_sum`).

Let `x` be `k` independent draws from `p` and `y`, independently, `l` independent draws from `q`.
Write `t = ∑ a, p(a) q(a)`, `u = ∑ a, p(a) q(a)²` and `v = ∑ a, p(a)² q(a)`. Then:
* the cross-collision count has mean `k l t` (`sum_sum_iid_mul_crossCollisionCount`);
* its second moment is `k l t + k (k - 1) l v + k l (l - 1) u + k (k - 1) l (l - 1) t²`
  (`sum_sum_iid_mul_crossCollisionCount_sq`);
* its joint moment with the collision count of `x` is
  `k (k - 1) (k - 2) l ‖p‖₂² t / 2 + k (k - 1) l v`
  (`sum_sum_iid_mul_collisionCount_mul_crossCollisionCount`); the joint moment with the
  collision count of `y` is symmetric
  (`sum_sum_iid_mul_crossCollisionCount_mul_collisionCount`).

These are the moments of the collision-based closeness tester
[Diakonikolas–Gouleakis–Peebles–Price, §3][DiakonikolasGouleakisPeeblesPrice2019] (section numbers
follow arXiv:1611.03579v1). Each follows from the occurrence-count moments of
`Complexity.Probability.IID.CollisionCount` and the independence of the two samples.

## Main definitions

* `Cslib.Probability.PMF.crossCollisionCount`: the number of colliding pairs across two samples.

## Main results

* `Cslib.Probability.PMF.crossCollisionCount_eq_sum`: the count as a sum of products of occurrence
  counts.
* `Cslib.Probability.PMF.sum_sum_iid_mul_crossCollisionCount`: the mean.
* `Cslib.Probability.PMF.sum_sum_iid_mul_crossCollisionCount_sq`: the second moment.
* `Cslib.Probability.PMF.sum_sum_iid_mul_collisionCount_mul_crossCollisionCount`,
  `sum_sum_iid_mul_crossCollisionCount_mul_collisionCount`: the joint moments with the collision
  counts of each sample.

## References

* [I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, *Collision-based testers are optimal
  for uniformity and closeness*][DiakonikolasGouleakisPeeblesPrice2019]
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [DecidableEq α]

/-- The number of pairs `(i, j)` of positions with `x i = y j`. -/
@[expose] def crossCollisionCount {k l : ℕ} (x : Fin k → α) (y : Fin l → α) : ℕ :=
  #{ij : Fin k × Fin l | x ij.1 = y ij.2}

variable [Fintype α]

/-- The cross-collision count is the sum over values of the products of their occurrence counts
in the two samples. -/
theorem crossCollisionCount_eq_sum {k l : ℕ} (x : Fin k → α) (y : Fin l → α) :
    (crossCollisionCount x y : ℝ) = ∑ a, (occurrenceCount x a : ℝ) * occurrenceCount y a := by
  simp only [crossCollisionCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Fintype.sum_prod_type, occurrenceCount_eq_sum, sum_mul_sum]
  have h (i : Fin k) (j : Fin l) :
      ∑ a : α, (if x i = a then (1 : ℝ) else 0) * (if y j = a then 1 else 0) =
        if x i = y j then 1 else 0 := by
    simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    exact if_congr eq_comm rfl rfl
  simp only [← h]
  exact (sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm

section Moments

variable (p q : PMF α) (k l : ℕ)

omit [DecidableEq α] in
/-- Independence: the double expectation of a sum of products of a function of `x` and a function
of `y` is the sum of the products of their expectations. -/
private theorem sum_sum_mul_sum {ι : Type*} [Fintype ι] (f : ι → (Fin k → α) → ℝ)
    (g : ι → (Fin l → α) → ℝ) :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q l y).toReal * ∑ i, f i x * g i y =
      ∑ i, (∑ x, (iid p k x).toReal * f i x) * ∑ y, (iid q l y).toReal * g i y := by
  simp only [sum_mul_sum]
  simp only [mul_sum]
  symm
  rw [Finset.sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun i _ => ?_
  ring

/-- **Mean of the cross-collision count**: for `k` draws from `p` and `l` independent draws from
`q`, the expected number of colliding pairs across the samples is `k l ∑ a, p(a) q(a)`. -/
theorem sum_sum_iid_mul_crossCollisionCount :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q l y).toReal * crossCollisionCount x y =
      k * l * ∑ a, (p a).toReal * (q a).toReal := by
  simp only [crossCollisionCount_eq_sum]
  rw [sum_sum_mul_sum, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_iid_mul_occurrenceCount, sum_iid_mul_occurrenceCount]
  ring

/-- **Second moment of the cross-collision count**: with `t = ∑ a, p(a) q(a)`,
`u = ∑ a, p(a) q(a)²` and `v = ∑ a, p(a)² q(a)`, it is
`k l t + k (k - 1) l v + k l (l - 1) u + k (k - 1) l (l - 1) t²`. -/
theorem sum_sum_iid_mul_crossCollisionCount_sq :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q l y).toReal * (crossCollisionCount x y : ℝ) ^ 2 =
      k * l * ∑ a, (p a).toReal * (q a).toReal +
        k * (k - 1) * l * ∑ a, (p a).toReal ^ 2 * (q a).toReal +
        k * l * (l - 1) * ∑ a, (p a).toReal * (q a).toReal ^ 2 +
        k * (k - 1) * l * (l - 1) * (∑ a, (p a).toReal * (q a).toReal) ^ 2 := by
  have hsq (x : Fin k → α) (y : Fin l → α) : (crossCollisionCount x y : ℝ) ^ 2 =
      ∑ ab : α × α, ((occurrenceCount x ab.1 : ℝ) * occurrenceCount x ab.2) *
        ((occurrenceCount y ab.1 : ℝ) * occurrenceCount y ab.2) := by
    rw [crossCollisionCount_eq_sum, sq, sum_mul_sum, ← Finset.univ_product_univ, sum_product]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    ring
  simp only [hsq]
  rw [sum_sum_mul_sum, Fintype.sum_prod_type]
  simp only [sum_iid_mul_occurrenceCount_mul_occurrenceCount]
  have hinner (a : α) : ∑ b : α,
      (k * (k - 1) * (p a).toReal * (p b).toReal + k * (if a = b then (p a).toReal else 0)) *
        (l * (l - 1) * (q a).toReal * (q b).toReal + l * (if a = b then (q a).toReal else 0)) =
      k * (k - 1) * l * (l - 1) * ((p a).toReal * (q a).toReal) *
          ∑ b, (p b).toReal * (q b).toReal +
        k * (k - 1) * l * ((p a).toReal ^ 2 * (q a).toReal) +
        k * l * (l - 1) * ((p a).toReal * (q a).toReal ^ 2) +
        k * l * ((p a).toReal * (q a).toReal) := by
    have hexp (b : α) :
        (k * (k - 1) * (p a).toReal * (p b).toReal + k * (if a = b then (p a).toReal else 0)) *
          (l * (l - 1) * (q a).toReal * (q b).toReal + l * (if a = b then (q a).toReal else 0)) =
        k * (k - 1) * l * (l - 1) * ((p a).toReal * (q a).toReal) *
            ((p b).toReal * (q b).toReal) +
          (if a = b then k * (k - 1) * l * ((p a).toReal ^ 2 * (q a).toReal) +
            k * l * (l - 1) * ((p a).toReal * (q a).toReal ^ 2) +
            k * l * ((p a).toReal * (q a).toReal) else 0) := by
      split_ifs with h
      · subst h; ring
      · ring
    simp only [hexp, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true]
    ring
  simp only [hinner, sum_add_distrib, ← sum_mul, ← mul_sum]
  ring

/-- **Joint moment of the collision count of `x` and the cross-collision count**: with
`t = ∑ a, p(a) q(a)` and `v = ∑ a, p(a)² q(a)`, it is
`k (k - 1) (k - 2) l ‖p‖₂² t / 2 + k (k - 1) l v`. -/
theorem sum_sum_iid_mul_collisionCount_mul_crossCollisionCount :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q l y).toReal *
        ((collisionCount x : ℝ) * crossCollisionCount x y) =
      k * (k - 1) * (k - 2) / 2 * l * collisionProbability p *
          ∑ a, (p a).toReal * (q a).toReal +
        k * (k - 1) * l * ∑ a, (p a).toReal ^ 2 * (q a).toReal := by
  have h (x : Fin k → α) (y : Fin l → α) : (collisionCount x : ℝ) * crossCollisionCount x y =
      ∑ a, ((collisionCount x : ℝ) * occurrenceCount x a) * occurrenceCount y a := by
    rw [crossCollisionCount_eq_sum, mul_sum]
    exact sum_congr rfl fun a _ => by ring
  simp only [h]
  rw [sum_sum_mul_sum]
  simp only [sum_iid_mul_collisionCount_mul_occurrenceCount, sum_iid_mul_occurrenceCount]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun a _ => by ring

/-- **Joint moment of the cross-collision count and the collision count of `y`**: with
`t = ∑ a, p(a) q(a)` and `u = ∑ a, p(a) q(a)²`, it is
`k l (l - 1) (l - 2) ‖q‖₂² t / 2 + k l (l - 1) u`. -/
theorem sum_sum_iid_mul_crossCollisionCount_mul_collisionCount :
    ∑ x, ∑ y, (iid p k x).toReal * (iid q l y).toReal *
        ((crossCollisionCount x y : ℝ) * collisionCount y) =
      k * (l * (l - 1) * (l - 2) / 2) * collisionProbability q *
          ∑ a, (p a).toReal * (q a).toReal +
        k * (l * (l - 1)) * ∑ a, (p a).toReal * (q a).toReal ^ 2 := by
  have h (x : Fin k → α) (y : Fin l → α) : (crossCollisionCount x y : ℝ) * collisionCount y =
      ∑ a, (occurrenceCount x a : ℝ) * ((collisionCount y : ℝ) * occurrenceCount y a) := by
    rw [crossCollisionCount_eq_sum, sum_mul]
    exact sum_congr rfl fun a _ => by ring
  simp only [h]
  rw [sum_sum_mul_sum]
  simp only [sum_iid_mul_collisionCount_mul_occurrenceCount, sum_iid_mul_occurrenceCount]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun a _ => by ring

end Moments

end Cslib.Probability.PMF
