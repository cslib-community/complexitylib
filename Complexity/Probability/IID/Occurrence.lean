/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.IID
import Complexity.Probability.PMF

/-!
# Occurrence counts of independent samples

Real expectations under `k` independent draws `iid μ k` split along the first draw
(`sum_iid_succ_mul`) and along a split `Fin (m + k)` of the positions (`sum_iid_add_mul`). They are
invariant under permuting the positions (`sum_iid_comp_perm`).

`Cslib.Probability.PMF.occurrenceCount x b` is the number of positions `i` with `x i = b`. The
counts of all values add up to the number of samples (`sum_occurrenceCount`). Among `m`
independent draws from `μ`, the count `N` of a value `a` has the inverse moment bound
`(m + 1) μ(a) E[1 / (N + 1)] ≤ 1` (`mul_sum_iid_mul_inv_occurrenceCount_le`). The proof is by
exchangeability: under `m + 1` draws, the events that position `i` holds `a`, weighted by the
inverse number of occurrences of `a`, have equal expectations, and these expectations add up to
at most one. This bound gives the fixed-sample-size form of the second part of
[Diakonikolas–Kane, Lemma 2.6][DiakonikolasKane2016] (lemma numbering of arXiv:1601.05557v1), which
takes a Poisson number of samples.

## Main definitions

* `Cslib.Probability.PMF.occurrenceCount`: the number of sample positions holding a given value.

## Main results

* `Cslib.Probability.PMF.sum_iid_succ_mul`: expectations under `k + 1` draws via the first draw.
* `Cslib.Probability.PMF.sum_iid_add_mul`: expectations under `m + k` draws via the first `m`.
* `Cslib.Probability.PMF.sum_iid_comp_perm`: expectations are invariant under permuting draws.
* `Cslib.Probability.PMF.sum_occurrenceCount`: the occurrence counts add up to the sample size.
* `Cslib.Probability.PMF.mul_sum_iid_mul_inv_occurrenceCount_le`: the inverse moment bound.

## References

* [I. Diakonikolas and D. M. Kane, *A new approach for testing properties of discrete
  distributions*][DiakonikolasKane2016]
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*} [Fintype α]

/-- Expectation under `k + 1` independent draws: draw the first, then the rest. -/
theorem sum_iid_succ_mul (μ : PMF α) (k : ℕ) (f : (Fin (k + 1) → α) → ℝ) :
    ∑ x, (iid μ (k + 1) x).toReal * f x =
      ∑ a, (μ a).toReal * ∑ x, (iid μ k x).toReal * f (Fin.cons a x) := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => α).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [Fin.consEquiv_apply, iid_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  ring

/-- Expectation under `m + k` independent draws: draw the first `m`, then the other `k`. -/
theorem sum_iid_add_mul (μ : PMF α) (m k : ℕ) (f : (Fin (m + k) → α) → ℝ) :
    ∑ x, (iid μ (m + k) x).toReal * f x =
      ∑ x₁, (iid μ m x₁).toReal * ∑ x₂, (iid μ k x₂).toReal * f (Fin.append x₁ x₂) := by
  rw [← (Fin.appendEquiv m k).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x₁ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun x₂ _ => ?_
  change (iid μ (m + k) (Fin.append x₁ x₂)).toReal * f (Fin.append x₁ x₂) = _
  simp only [iid_apply, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    ENNReal.toReal_mul, ENNReal.toReal_prod]
  ring

/-- Expectations under independent draws are invariant under permuting the draws. -/
theorem sum_iid_comp_perm (μ : PMF α) {k : ℕ} (σ : Equiv.Perm (Fin k))
    (f : (Fin k → α) → ℝ) :
    ∑ y, (iid μ k y).toReal * f (y ∘ σ) = ∑ y, (iid μ k y).toReal * f y := by
  refine Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl α)) _ _ fun y => ?_
  have hy : (Equiv.arrowCongr σ.symm (Equiv.refl α)) y = y ∘ σ := by
    funext i
    simp [Equiv.arrowCongr_apply]
  rw [hy, iid_apply, iid_apply]
  congr 2
  exact (Equiv.prod_comp σ fun i => μ (y i)).symm

variable [DecidableEq α]

omit [Fintype α] in
/-- The number of sample positions `i` with `x i = b`. -/
def occurrenceCount {k : ℕ} (x : Fin k → α) (b : α) : ℕ := #{i | x i = b}

omit [Fintype α] in
/-- The occurrence count is a sum of indicators. -/
theorem occurrenceCount_eq_sum {k : ℕ} (x : Fin k → α) (b : α) :
    (occurrenceCount x b : ℝ) = ∑ i, if x i = b then 1 else 0 := by
  simp only [occurrenceCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero]

omit [Fintype α] in
/-- Prepending a sample adds its indicator to the occurrence count. -/
theorem occurrenceCount_cons {k : ℕ} (a : α) (x : Fin k → α) (b : α) :
    (occurrenceCount (Fin.cons a x : Fin (k + 1) → α) b : ℝ) =
      (if a = b then 1 else 0) + occurrenceCount x b := by
  simp only [occurrenceCount_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

omit [Fintype α] in
/-- Occurrence counts are invariant under permuting the positions. -/
theorem occurrenceCount_comp_perm {k : ℕ} (y : Fin k → α) (σ : Equiv.Perm (Fin k)) (b : α) :
    occurrenceCount (y ∘ σ) b = occurrenceCount y b := by
  have h : (occurrenceCount (y ∘ σ) b : ℝ) = occurrenceCount y b := by
    rw [occurrenceCount_eq_sum, occurrenceCount_eq_sum]
    exact Equiv.sum_comp σ fun i => if y i = b then (1 : ℝ) else 0
  exact_mod_cast h

/-- The occurrence counts of all values add up to the number of samples. -/
theorem sum_occurrenceCount {k : ℕ} (x : Fin k → α) : ∑ b, occurrenceCount x b = k := by
  have h : (∑ b, occurrenceCount x b : ℝ) = k := by
    simp only [occurrenceCount_eq_sum]
    rw [Finset.sum_comm]
    simp
  exact_mod_cast h

/-- **Inverse occurrence moment.** Among `m` independent draws from `μ`, the value `a` occurs `N`
times with `(m + 1) μ(a) E[1 / (N + 1)] ≤ 1`. -/
theorem mul_sum_iid_mul_inv_occurrenceCount_le (μ : PMF α) (m : ℕ) (a : α) :
    (m + 1) * ((μ a).toReal * ∑ x, (iid μ m x).toReal / (occurrenceCount x a + 1)) ≤ 1 := by
  -- `E i`: the mass of `y i = a`, weighted by the inverse number of occurrences of `a` in `y`.
  set E : Fin (m + 1) → ℝ := fun i => ∑ y, (iid μ (m + 1) y).toReal *
    ((if y i = a then 1 else 0) / occurrenceCount y a) with hE
  have h0 : E 0 = (μ a).toReal * ∑ x, (iid μ m x).toReal / (occurrenceCount x a + 1) := by
    rw [hE]
    dsimp only
    rw [sum_iid_succ_mul, Finset.sum_eq_single a]
    · congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [occurrenceCount_cons]
      simp only [Fin.cons_zero, ite_true, mul_one_div]
      ring
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (mem_univ a) h
  have hi (i : Fin (m + 1)) : E i = E 0 := by
    rw [hE]
    dsimp only
    rw [← sum_iid_comp_perm μ (Equiv.swap 0 i)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [occurrenceCount_comp_perm]
    simp
  have hsum : ∑ i, E i ≤ 1 := by
    rw [hE]
    dsimp only
    rw [Finset.sum_comm]
    calc ∑ y, ∑ i, (iid μ (m + 1) y).toReal *
          ((if y i = a then 1 else 0) / (occurrenceCount y a : ℝ))
        = ∑ y, (iid μ (m + 1) y).toReal *
            ((occurrenceCount y a : ℝ) / occurrenceCount y a) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← mul_sum, ← sum_div, ← occurrenceCount_eq_sum]
      _ ≤ ∑ y, (iid μ (m + 1) y).toReal * 1 := by
          refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          exact div_self_le_one _
      _ = 1 := by rw [← sum_mul, sum_toReal, one_mul]
  have : ∑ i, E i = (m + 1) * E 0 := by
    rw [Finset.sum_congr rfl fun i _ => hi i, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [← h0]
  linarith

end Cslib.Probability.PMF
