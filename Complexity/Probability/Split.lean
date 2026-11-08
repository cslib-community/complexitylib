/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Collision
public import Complexity.Probability.IID.Occurrence
import Complexity.Probability.PMF

/-!
# Split distributions

Given counts `c : α → ℕ`, the split distribution `Cslib.Probability.PMF.split p c` lives on
`Σ i, Fin (c i + 1)`: a sample is `⟨i, j⟩` with `i` drawn from `p` and `j` uniform among the
`c i + 1` cells of `i` [Diakonikolas–Kane, Definition 2.4][DiakonikolasKane2016] (numbering of
arXiv:1601.05557v1). So the cell `⟨i, j⟩` has mass `p(i) / (c i + 1)` (`split_apply`), and the
domain has `|α| + ∑ c` points (`card_sigma_split`). A sample of `split p c` is a sample of `p`
passed through the kernel `splitKernel c` (`split_eq_bind`), and splitting preserves statistical
distance (`dist_split`). These are the two parts of
[Diakonikolas–Kane, Fact 2.5][DiakonikolasKane2016].

Splitting lowers the collision probability: it equals `∑ p(i)² / (c i + 1)`
(`collisionProbability_split`), and is antitone in `c` (`collisionProbability_split_antitone`),
the first part of [Diakonikolas–Kane, Lemma 2.6][DiakonikolasKane2016]. When `c` counts the
occurrences in `m` independent samples of `p` itself, the expected collision probability is at
most `1 / (m + 1)` (`sum_iid_mul_collisionProbability_split_le`). This is the second part of
[Diakonikolas–Kane, Lemma 2.6][DiakonikolasKane2016], which takes a Poisson number of samples with
mean `m` and gets `1 / m`, in the fixed-sample-size form used by the flattening closeness tester.

## Main definitions

* `Cslib.Probability.PMF.splitKernel`: the kernel sending `i` to a uniform cell of `i`.
* `Cslib.Probability.PMF.split`: the split distribution.

## Main results

* `Cslib.Probability.PMF.split_apply`: the mass of a cell.
* `Cslib.Probability.PMF.dist_split`: splitting preserves statistical distance.
* `Cslib.Probability.PMF.collisionProbability_split_antitone`: more cells, fewer collisions.
* `Cslib.Probability.PMF.sum_iid_mul_collisionProbability_split_le`: flattening by `m` samples
  brings the expected collision probability down to `1 / (m + 1)`.

## References

* [I. Diakonikolas and D. M. Kane, *A new approach for testing properties of discrete
  distributions*][DiakonikolasKane2016]
-/

public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*}

/-- The split kernel: `i` goes to a uniformly random cell `⟨i, j⟩` among its `c i + 1` cells. -/
noncomputable def splitKernel (c : α → ℕ) (i : α) : PMF (Σ i, Fin (c i + 1)) :=
  (PMF.uniformOfFintype (Fin (c i + 1))).map (Sigma.mk i)

/-- The split distribution of `p` with `c i + 1` cells for each `i`
[Diakonikolas–Kane, Definition 2.4][DiakonikolasKane2016]. -/
noncomputable def split (p : PMF α) (c : α → ℕ) : PMF (Σ i, Fin (c i + 1)) :=
  p.bind (splitKernel c)

/-- A sample of the split distribution is a sample of `p` passed through the split kernel. -/
theorem split_eq_bind (p : PMF α) (c : α → ℕ) : split p c = p.bind (splitKernel c) := by
  rw [split]

/-- The cell `⟨i, j⟩` has mass `p(i) / (c i + 1)`. -/
theorem split_apply (p : PMF α) (c : α → ℕ) (z : Σ i, Fin (c i + 1)) :
    split p c z = p z.1 / (c z.1 + 1 : ℕ) := by
  obtain ⟨i, j⟩ := z
  rw [split, PMF.bind_apply, tsum_eq_single i]
  · rw [splitKernel, PMF.map_apply, tsum_eq_single j]
    · simp [PMF.uniformOfFintype_apply, div_eq_mul_inv]
    · intro j' hj'
      simp [Ne.symm hj']
  · intro i' hi'
    rw [splitKernel, PMF.map_apply, tsum_eq_zero_iff.mpr, mul_zero]
    intro j'
    simp only [ite_eq_right_iff]
    intro h
    exact absurd (congrArg Sigma.fst h).symm hi'

/-- The real mass of the cell `⟨i, j⟩` is `p(i) / (c i + 1)`. -/
theorem split_apply_toReal (p : PMF α) (c : α → ℕ) (z : Σ i, Fin (c i + 1)) :
    (split p c z).toReal = (p z.1).toReal / (c z.1 + 1) := by
  rw [split_apply, ENNReal.toReal_div]
  push_cast
  rfl

variable [Fintype α]

/-- The split domain has `|α| + ∑ c` points. -/
theorem card_sigma_split (c : α → ℕ) :
    Fintype.card (Σ i, Fin (c i + 1)) = Fintype.card α + ∑ i, c i := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, sum_add_distrib, sum_const, card_univ, smul_eq_mul, mul_one]
  ring

/-- Splitting preserves statistical distance [Diakonikolas–Kane, Fact 2.5][DiakonikolasKane2016].
-/
theorem dist_split (p q : PMF α) (c : α → ℕ) : dist (split p c) (split q c) = dist p q := by
  rw [dist_eq, dist_eq, Fintype.sum_sigma]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  simp only [split_apply_toReal, ← sub_div, abs_div]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (0 : ℝ) < c i + 1 := by positivity
  rw [abs_of_pos h]
  push_cast
  field_simp

/-- The collision probability of a split distribution. -/
theorem collisionProbability_split (p : PMF α) (c : α → ℕ) :
    collisionProbability (split p c) = ∑ i, (p i).toReal ^ 2 / (c i + 1) := by
  rw [collisionProbability_eq_sum, Fintype.sum_sigma]
  refine sum_congr rfl fun i _ => ?_
  simp only [split_apply_toReal, div_pow]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h : (0 : ℝ) < c i + 1 := by positivity
  push_cast
  field_simp

omit [Fintype α] in
/-- More cells give a smaller collision probability
[Diakonikolas–Kane, Lemma 2.6][DiakonikolasKane2016]. -/
theorem collisionProbability_split_antitone [Finite α] (p : PMF α) {c c' : α → ℕ}
    (h : ∀ i, c i ≤ c' i) :
    collisionProbability (split p c') ≤ collisionProbability (split p c) := by
  have := Fintype.ofFinite α
  rw [collisionProbability_split, collisionProbability_split]
  refine sum_le_sum fun i _ => div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) ?_
  exact_mod_cast Nat.add_le_add_right (h i) 1

variable [DecidableEq α]

/-- **Flattening.** Splitting `μ` along the occurrence counts of `m` independent samples of `μ`
gives expected collision probability at most `1 / (m + 1)`: the fixed-sample-size form of
[Diakonikolas–Kane, Lemma 2.6][DiakonikolasKane2016]. -/
theorem sum_iid_mul_collisionProbability_split_le (μ : PMF α) (m : ℕ) :
    ∑ x, (iid μ m x).toReal * collisionProbability (split μ (occurrenceCount x)) ≤
      1 / (m + 1) := by
  simp only [collisionProbability_split, mul_sum]
  rw [Finset.sum_comm]
  calc ∑ i, ∑ x, (iid μ m x).toReal * ((μ i).toReal ^ 2 / (occurrenceCount x i + 1))
      = ∑ i, (μ i).toReal * ((μ i).toReal *
          ∑ x, (iid μ m x).toReal / (occurrenceCount x i + 1)) := by
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ∑ i, (μ i).toReal * (1 / (m + 1)) := by
        refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        rw [le_div_iff₀ (by positivity), mul_comm]
        exact mul_sum_iid_mul_inv_occurrenceCount_le μ m i
    _ = 1 / (m + 1) := by rw [← sum_mul, sum_toReal, one_mul]

end Cslib.Probability.PMF
