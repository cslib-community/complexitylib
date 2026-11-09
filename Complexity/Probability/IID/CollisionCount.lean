/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Collision
public import Complexity.Probability.IID.Occurrence
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# Collision counts of independent samples

`Cslib.Probability.PMF.collisionCount x` is the number of pairs `i < j` of sample positions with
`x i = x j`. Among `k` independent draws from `μ` it has mean `C(k, 2) ‖μ‖₂²`, where
`‖μ‖₂² = ∑ a, μ(a)²` is the collision probability (`sum_iid_mul_collisionCount`), and, writing
`s = ‖μ‖₂²` and `t = ∑ a, μ(a)³`, variance exactly
`C(k, 2) (s - s²) + k (k - 1) (k - 2) (t - s²)` (`sum_iid_mul_collisionCount_sub_sq`). These are the
moments behind the collision tester for uniformity [Goldreich–Ron][GoldreichRon2000]. The mean is
[Diakonikolas–Gouleakis–Peebles–Price, Lemma 2][DiakonikolasGouleakisPeeblesPrice2019] and the
variance identity is the equality chain in the proof of
[Diakonikolas–Gouleakis–Peebles–Price, Lemma 3][DiakonikolasGouleakisPeeblesPrice2019] (numbering
of arXiv:1611.03579v1), the basis of their sharp analysis.

The proof inducts on the number of samples, peeling off the first draw (`sum_iid_succ_mul`), and
tracks the joint moments of the collision count and the occurrence counts of single values
(`occurrenceCount`, both from `Complexity.Probability.IID.Occurrence`). These joint moments are
public because the cross-collision count of two independent samples is a sum of products of
occurrence counts.

## Main definitions

* `Cslib.Probability.PMF.collisionCount`: the number of colliding pairs of sample positions.

## Main results

* `Cslib.Probability.PMF.sum_iid_mul_collisionCount`: the mean of the collision count.
* `Cslib.Probability.PMF.sum_iid_mul_collisionCount_sub_sq`: the variance of the collision count.
* `Cslib.Probability.PMF.sum_iid_mul_occurrenceCount`,
  `sum_iid_mul_occurrenceCount_mul_occurrenceCount`,
  `sum_iid_mul_collisionCount_mul_occurrenceCount`, `sum_iid_mul_collisionCount_sq`: the
  supporting first and second moments.

## References

* [O. Goldreich and D. Ron, *On testing expansion in bounded-degree graphs*][GoldreichRon2000]
* [I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, *Collision-based testers are optimal
  for uniformity and closeness*][DiakonikolasGouleakisPeeblesPrice2019]
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of colliding pairs `i < j` with `x i = x j` among the samples `x`. -/
@[expose] def collisionCount {k : ℕ} (x : Fin k → α) : ℕ :=
  #{ij : Fin k × Fin k | ij.1 < ij.2 ∧ x ij.1 = x ij.2}

omit [Fintype α] in
private theorem collisionCount_cons {k : ℕ} (a : α) (x : Fin k → α) :
    (collisionCount (Fin.cons a x : Fin (k + 1) → α) : ℝ) =
      (occurrenceCount x a : ℝ) + collisionCount x := by
  simp only [collisionCount, occurrenceCount_eq_sum, Finset.card_filter, Fintype.sum_prod_type,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, false_and, ite_false, Fin.succ_pos, true_and,
    Fin.not_lt_zero, Fin.succ_lt_succ_iff, zero_add, eq_comm (a := a), Nat.cast_add, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

section Moments

variable (μ : PMF α)

private noncomputable def ex (k : ℕ) (f : (Fin k → α) → ℝ) : ℝ := ∑ x, (iid μ k x).toReal * f x

omit [DecidableEq α] in
private theorem ex_add (k : ℕ) (f g : (Fin k → α) → ℝ) :
    ex μ k (fun x => f x + g x) = ex μ k f + ex μ k g := by
  simp only [ex, mul_add, sum_add_distrib]

omit [DecidableEq α] in
private theorem ex_const_mul (k : ℕ) (c : ℝ) (f : (Fin k → α) → ℝ) :
    ex μ k (fun x => c * f x) = c * ex μ k f := by
  simp only [ex, mul_left_comm _ c, ← mul_sum]

omit [DecidableEq α] in
private theorem ex_const (k : ℕ) (c : ℝ) : ex μ k (fun _ => c) = c := by
  rw [ex, ← sum_mul, sum_toReal, one_mul]

omit [DecidableEq α] in
private theorem ex_succ (k : ℕ) (f : (Fin (k + 1) → α) → ℝ) :
    ex μ (k + 1) f = ∑ a, (μ a).toReal * ex μ k (fun x => f (Fin.cons a x)) :=
  sum_iid_succ_mul μ k f

private theorem sum_mul_ite (b : α) (g : α → ℝ) :
    ∑ a, (μ a).toReal * (if a = b then g a else 0) = (μ b).toReal * g b := by
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]

omit [DecidableEq α] in
private theorem sum_mul_mul_left (c : ℝ) (g : α → ℝ) :
    ∑ a, (μ a).toReal * (c * g a) = c * ∑ a, (μ a).toReal * g a := by
  simp only [mul_left_comm _ c, ← mul_sum]

omit [DecidableEq α] in
private theorem sum_mul_quadratic (A B C : ℝ) :
    ∑ c, (μ c).toReal * (A + B * (μ c).toReal + C * (μ c).toReal ^ 2) =
      A + B * ∑ a, (μ a).toReal ^ 2 + C * ∑ a, (μ a).toReal ^ 3 := by
  have h1 : ∑ c, (μ c).toReal * A = A := by rw [← sum_mul, sum_toReal, one_mul]
  have h2 : ∑ c, (μ c).toReal * (B * (μ c).toReal) = B * ∑ a, (μ a).toReal ^ 2 := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  have h3 : ∑ c, (μ c).toReal * (C * (μ c).toReal ^ 2) = C * ∑ a, (μ a).toReal ^ 3 := by
    rw [mul_sum]
    exact sum_congr rfl fun _ _ => by ring
  simp only [mul_add, sum_add_distrib, h1, h2, h3]

private theorem sum_mul_ite_mul (b : α) (g : α → ℝ) :
    ∑ a, (μ a).toReal * ((if a = b then 1 else 0) * g a) = (μ b).toReal * g b := by
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]

private theorem ex_occ (b : α) (k : ℕ) :
    ex μ k (fun x => (occurrenceCount x b : ℝ)) = k * (μ b).toReal := by
  induction k with
  | zero => simp [ex, occurrenceCount_eq_sum]
  | succ k ih =>
    rw [ex_succ]
    simp only [occurrenceCount_cons]
    simp only [ex_add, ex_const, ih, mul_add, sum_add_distrib, sum_mul_ite μ b (fun _ => 1),
      ← sum_mul, sum_toReal]
    push_cast
    ring

private theorem ex_occ_mul_occ (a b : α) (k : ℕ) :
    ex μ k (fun x => (occurrenceCount x a : ℝ) * occurrenceCount x b) =
      k * (k - 1) * (μ a).toReal * (μ b).toReal + k * (if a = b then (μ a).toReal else 0) := by
  induction k with
  | zero => simp [ex, occurrenceCount_eq_sum]
  | succ k ih =>
    rw [ex_succ]
    have hinner (c : α) : ex μ k (fun x =>
        (occurrenceCount (Fin.cons c x : Fin (k + 1) → α) a : ℝ) *
          occurrenceCount (Fin.cons c x : Fin (k + 1) → α) b) =
        ((if c = a then 1 else 0) * (if c = b then 1 else 0) +
          ((if c = a then 1 else 0) * (k * (μ b).toReal) +
          (if c = b then 1 else 0) * (k * (μ a).toReal))) +
          (k * (k - 1) * (μ a).toReal * (μ b).toReal +
            k * (if a = b then (μ a).toReal else 0)) := by
      have hfun : (fun x : Fin k → α =>
          (occurrenceCount (Fin.cons c x : Fin (k + 1) → α) a : ℝ) *
            occurrenceCount (Fin.cons c x : Fin (k + 1) → α) b) = fun x =>
          ((if c = a then 1 else 0) * (if c = b then 1 else 0) +
            ((if c = a then 1 else 0) * (occurrenceCount x b : ℝ) +
              (if c = b then 1 else 0) * (occurrenceCount x a : ℝ))) +
            (occurrenceCount x a : ℝ) * occurrenceCount x b := by
        funext x
        rw [occurrenceCount_cons, occurrenceCount_cons]
        ring
      rw [hfun, ex_add, ex_add, ex_const, ex_add, ex_const_mul, ex_const_mul, ex_occ, ex_occ, ih]
    simp only [hinner]
    by_cases hab : a = b
    · subst hab
      simp [mul_add, sum_add_distrib, ← sum_mul, sum_toReal]
      ring
    · simp [mul_add, sum_add_distrib, ← sum_mul, sum_toReal, hab, Ne.symm hab]
      ring

private theorem ex_collisionCount (k : ℕ) :
    ex μ k (fun x => (collisionCount x : ℝ)) = k * (k - 1) / 2 * ∑ a, (μ a).toReal ^ 2 := by
  induction k with
  | zero => simp [ex, collisionCount]
  | succ k ih =>
    rw [ex_succ]
    have hinner (c : α) : ex μ k (fun x => (collisionCount (Fin.cons c x : Fin (k + 1) → α) : ℝ)) =
        k * (μ c).toReal + k * (k - 1) / 2 * ∑ a, (μ a).toReal ^ 2 := by
      simp only [collisionCount_cons]
      rw [ex_add, ex_occ, ih]
    simp only [hinner, mul_add, sum_add_distrib, ← sum_mul, sum_toReal, mul_left_comm _ (k : ℝ),
      ← mul_sum, ← sq]
    push_cast
    ring

private theorem ex_collisionCount_mul_occ (b : α) (k : ℕ) :
    ex μ k (fun x => (collisionCount x : ℝ) * occurrenceCount x b) =
      k * (k - 1) * (k - 2) / 2 * (∑ a, (μ a).toReal ^ 2) * (μ b).toReal +
        k * (k - 1) * (μ b).toReal ^ 2 := by
  induction k with
  | zero => simp [ex, collisionCount]
  | succ k ih =>
    rw [ex_succ]
    have hinner (c : α) : ex μ k (fun x => (collisionCount (Fin.cons c x : Fin (k + 1) → α) : ℝ) *
        occurrenceCount (Fin.cons c x : Fin (k + 1) → α) b) =
        (if c = b then 1 else 0) * (k * (μ c).toReal + k * (k - 1) / 2 * ∑ a, (μ a).toReal ^ 2) +
          ((k * (k - 1) * (μ c).toReal * (μ b).toReal +
            k * (if c = b then (μ c).toReal else 0)) +
          (k * (k - 1) * (k - 2) / 2 * (∑ a, (μ a).toReal ^ 2) * (μ b).toReal +
            k * (k - 1) * (μ b).toReal ^ 2)) := by
      have hfun : (fun x : Fin k → α => (collisionCount (Fin.cons c x : Fin (k + 1) → α) : ℝ) *
          occurrenceCount (Fin.cons c x : Fin (k + 1) → α) b) = fun x =>
          (if c = b then 1 else 0) * ((occurrenceCount x c : ℝ) + collisionCount x) +
            ((occurrenceCount x c : ℝ) * occurrenceCount x b +
              (collisionCount x : ℝ) * occurrenceCount x b) := by
        funext x
        rw [collisionCount_cons, occurrenceCount_cons]
        ring
      rw [hfun, ex_add, ex_const_mul, ex_add, ex_add, ex_occ, ex_collisionCount, ih,
        ex_occ_mul_occ]
    have hsq : ∑ a, (μ a).toReal * (k * (k - 1) * (μ a).toReal * (μ b).toReal) =
        k * (k - 1) * (∑ a, (μ a).toReal ^ 2) * (μ b).toReal := by
      rw [mul_sum, sum_mul]
      exact sum_congr rfl fun a _ => by ring
    have hite : ∑ a, (μ a).toReal * (k * if a = b then (μ a).toReal else 0) =
        k * (μ b).toReal ^ 2 := by
      rw [sum_mul_mul_left, sum_mul_ite, sq]
    simp only [hinner, mul_add, sum_add_distrib, sum_mul_ite_mul, hsq, hite, ← sum_mul,
      sum_toReal]
    push_cast
    ring

private theorem ex_collisionCount_sq (k : ℕ) :
    ex μ k (fun x => (collisionCount x : ℝ) ^ 2) =
      k * (k - 1) / 2 * (∑ a, (μ a).toReal ^ 2) +
        k * (k - 1) * (k - 2) * (∑ a, (μ a).toReal ^ 3) +
          k * (k - 1) * (k - 2) * (k - 3) / 4 * (∑ a, (μ a).toReal ^ 2) ^ 2 := by
  induction k with
  | zero => simp [ex, collisionCount]
  | succ k ih =>
    rw [ex_succ]
    have hinner (c : α) :
        ex μ k (fun x => (collisionCount (Fin.cons c x : Fin (k + 1) → α) : ℝ) ^ 2) =
        (k * (k - 1) / 2 * (∑ a, (μ a).toReal ^ 2) +
            k * (k - 1) * (k - 2) * (∑ a, (μ a).toReal ^ 3) +
            k * (k - 1) * (k - 2) * (k - 3) / 4 * (∑ a, (μ a).toReal ^ 2) ^ 2) +
          (k + k * (k - 1) * (k - 2) * (∑ a, (μ a).toReal ^ 2)) * (μ c).toReal +
          3 * k * (k - 1) * (μ c).toReal ^ 2 := by
      have hfun : (fun x : Fin k → α =>
          (collisionCount (Fin.cons c x : Fin (k + 1) → α) : ℝ) ^ 2) =
          fun x => (occurrenceCount x c : ℝ) * occurrenceCount x c +
            (2 * ((collisionCount x : ℝ) * occurrenceCount x c) + (collisionCount x : ℝ) ^ 2) := by
        funext x
        rw [collisionCount_cons]
        ring
      rw [hfun, ex_add, ex_add, ex_const_mul, ex_occ_mul_occ, ex_collisionCount_mul_occ, ih,
        ite_eq_left rfl]
      ring
    simp only [hinner, sum_mul_quadratic]
    push_cast
    ring

/-- **Mean of the collision count**: among `k` independent draws from `μ`, the expected number
of colliding pairs is `C(k, 2)` times the collision probability `∑ a, μ(a)²`. -/
theorem sum_iid_mul_collisionCount (k : ℕ) :
    ∑ x, (iid μ k x).toReal * collisionCount x = k.choose 2 * collisionProbability μ := by
  rw [Nat.cast_choose_two, collisionProbability_eq_sum]
  exact ex_collisionCount μ k

/-- **Variance of the collision count**: among `k` independent draws from `μ`, with
`s = ∑ a, μ(a)²` and `t = ∑ a, μ(a)³`, the collision count has variance
`C(k, 2) (s - s²) + k (k - 1) (k - 2) (t - s²)`. -/
theorem sum_iid_mul_collisionCount_sub_sq (k : ℕ) :
    ∑ x, (iid μ k x).toReal *
        ((collisionCount x : ℝ) - k.choose 2 * collisionProbability μ) ^ 2 =
      k.choose 2 * (collisionProbability μ - collisionProbability μ ^ 2) +
        k * (k - 1) * (k - 2) * (∑ a, (μ a).toReal ^ 3 - collisionProbability μ ^ 2) := by
  have hfun : (fun x : Fin k → α =>
      ((collisionCount x : ℝ) - k.choose 2 * collisionProbability μ) ^ 2) = fun x =>
      (collisionCount x : ℝ) ^ 2 + ((-2 * (k.choose 2 * collisionProbability μ)) *
        collisionCount x + (k.choose 2 * collisionProbability μ) ^ 2) := by
    funext x
    ring
  change ex μ k _ = _
  rw [hfun, ex_add, ex_add, ex_const_mul, ex_const, ex_collisionCount_sq, ex_collisionCount,
    Nat.cast_choose_two, collisionProbability_eq_sum]
  ring

/-- **Mean of an occurrence count**: among `k` independent draws from `μ`, the value `b` occurs
`k μ(b)` times on average. -/
theorem sum_iid_mul_occurrenceCount (b : α) (k : ℕ) :
    ∑ x, (iid μ k x).toReal * occurrenceCount x b = k * (μ b).toReal := by
  exact ex_occ μ b k

/-- **Joint moment of two occurrence counts** among `k` independent draws from `μ`:
`E[N_a N_b] = k (k - 1) μ(a) μ(b) + k [a = b] μ(a)`. -/
theorem sum_iid_mul_occurrenceCount_mul_occurrenceCount (a b : α) (k : ℕ) :
    ∑ x, (iid μ k x).toReal * ((occurrenceCount x a : ℝ) * occurrenceCount x b) =
      k * (k - 1) * (μ a).toReal * (μ b).toReal + k * (if a = b then (μ a).toReal else 0) := by
  exact ex_occ_mul_occ μ a b k

/-- **Joint moment of the collision count and an occurrence count** among `k` independent draws
from `μ`: `E[C N_b] = k (k - 1) (k - 2) ‖μ‖₂² μ(b) / 2 + k (k - 1) μ(b)²`. -/
theorem sum_iid_mul_collisionCount_mul_occurrenceCount (b : α) (k : ℕ) :
    ∑ x, (iid μ k x).toReal * ((collisionCount x : ℝ) * occurrenceCount x b) =
      k * (k - 1) * (k - 2) / 2 * collisionProbability μ * (μ b).toReal +
        k * (k - 1) * (μ b).toReal ^ 2 := by
  rw [collisionProbability_eq_sum]
  exact ex_collisionCount_mul_occ μ b k

/-- **Second moment of the collision count** among `k` independent draws from `μ`, with
`s = ‖μ‖₂²` and `t = ∑ a, μ(a)³`: `E[C²] = C(k, 2) s + k (k - 1) (k - 2) t +
k (k - 1) (k - 2) (k - 3) s² / 4`. -/
theorem sum_iid_mul_collisionCount_sq (k : ℕ) :
    ∑ x, (iid μ k x).toReal * (collisionCount x : ℝ) ^ 2 =
      k.choose 2 * collisionProbability μ + k * (k - 1) * (k - 2) * ∑ a, (μ a).toReal ^ 3 +
        k * (k - 1) * (k - 2) * (k - 3) / 4 * collisionProbability μ ^ 2 := by
  rw [Nat.cast_choose_two, collisionProbability_eq_sum]
  exact ex_collisionCount_sq μ k

end Moments

end Cslib.Probability.PMF
