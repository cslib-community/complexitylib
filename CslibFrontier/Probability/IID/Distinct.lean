/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID.CollisionCount
public import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Distinct independent samples

A noninjective sample tuple has at least one colliding pair. The first moment of the
existing collision count therefore bounds the probability of repetitions by
`choose k 2 * collisionProbability μ`. A bound on each point mass gives the usual birthday
union bound without a uniformity assumption. This is the sampling estimate used in
[ChukhinKulikovMihajlinSmal2026], proof of Lemma 5.2, printed p. 10 (PDF p. 11).

## Main results

* `collisionCount_eq_zero_iff`: a tuple has no colliding pairs exactly when it is injective.
* `iid_not_injective_le`: the collision first-moment bound.
* `iid_not_injective_le_of_mass_le`: the point-mass version used for distinct input tuples.
* `iid_injective_pair_ge`: the sum of the two light-atom tuple-validity probabilities.
-/

public section
namespace Cslib.Probability.PMF
open Finset
variable {α : Type*}

/-- A sample tuple has no colliding pair precisely when all entries are distinct. -/
theorem collisionCount_eq_zero_iff [DecidableEq α] {k : ℕ} (x : Fin k → α) :
    collisionCount x = 0 ↔ Function.Injective x := by
  rw [collisionCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp only [Finset.mem_univ, true_implies, not_and]
  constructor
  · intro h i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact @h (i, j) hij heq
    · exact @h (j, i) hji heq.symm
  · intro h ij hlt heq
    exact (ne_of_lt hlt) (h heq)

variable [Finite α]

/-- The probability of any repetition is at most the expected number of colliding pairs. -/
theorem iid_not_injective_le (μ : PMF α) (k : ℕ) :
    ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤
      k.choose 2 * collisionProbability μ := by
  classical
  have := Fintype.ofFinite α
  rw [toOuterMeasure_apply_toReal, ← sum_iid_mul_collisionCount]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : Function.Injective x
  · simp only [Set.mem_ofPred_eq, hx, not_true_eq_false, ite_false]
    positivity
  · simp only [Set.mem_ofPred_eq, hx, not_false_eq_true, ite_true]
    have hcount : 1 ≤ collisionCount x := Nat.one_le_iff_ne_zero.mpr
      (fun h => hx ((collisionCount_eq_zero_iff x).mp h))
    have hc : (1 : ℝ) ≤ collisionCount x := by exact_mod_cast hcount
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hc
      (ENNReal.toReal_nonneg (a := iid μ k x))

/-- If every atom has mass at most `bound`, repetitions among `k` independent draws
have probability at most `choose k 2 * bound`, even for a nonuniform source. -/
theorem iid_not_injective_le_of_mass_le (μ : PMF α) (k : ℕ) {bound : ℝ}
    (h : ∀ a, (μ a).toReal ≤ bound) :
    ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤ k.choose 2 * bound :=
  (iid_not_injective_le μ k).trans
    (mul_le_mul_of_nonneg_left (collisionProbability_le_of_mass_le μ h) (by positivity))

/-- A lower bound for receiving an injective tuple, in real probability units. -/
theorem iid_injective_ge_of_mass_le (μ : PMF α) (k : ℕ) {bound : ℝ}
    (h : ∀ a, (μ a).toReal ≤ bound) :
    1 - k.choose 2 * bound ≤ ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal := by
  have hc := toOuterMeasure_toReal_add_compl (iid μ k) {x | Function.Injective x}
  have hb := iid_not_injective_le_of_mass_le μ k h
  change _ + ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal = 1 at hc
  linarith

/-- The two distinct-tuple probabilities in the light-atom case of submission 865.
Their sum exceeds one by at least `1/k`; the source subsequently telescopes `k` hybrid steps. -/
theorem iid_injective_pair_ge {β : Type*} [Finite β] (μ : PMF α) (ν : PMF β)
    (k : ℕ) (hk : 0 < k)
    (hμ : ∀ a, (μ a).toReal ≤ ((k : ℝ) ^ 2)⁻¹)
    (hν : ∀ b, (ν b).toReal ≤ ((k : ℝ) ^ 2)⁻¹) :
    1 + (k : ℝ)⁻¹ ≤ ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal +
      ((iid ν k).toOuterMeasure {y | Function.Injective y}).toReal := by
  have hl := iid_injective_ge_of_mass_le μ k hμ
  have hr := iid_injective_ge_of_mass_le ν k hν
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have heq : 2 - 2 * (k.choose 2 : ℝ) * ((k : ℝ) ^ 2)⁻¹ = 1 + (k : ℝ)⁻¹ := by
    rw [Nat.cast_choose_two]
    field_simp [hk']; ring
  linarith

end Cslib.Probability.PMF
