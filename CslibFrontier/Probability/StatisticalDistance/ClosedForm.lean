/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.StatisticalDistance

/-!
# Closed forms for statistical distance

Closed forms for cslib's statistical distance `dist` on finite PMFs. The distance from a point
mass `PMF.pure a` is the mass the other distribution places off `a` (`dist_pure_left`). On `Bool`,
the distance is the difference of the probabilities of `true` (`dist_bool`). Between uniform
distributions on finite sets `A` and `B` with `|A| ≤ |B|`, it is the fraction of `B` outside `A`
(`dist_uniformOfFinset_of_card_le`).

## Main results

* `Cslib.Probability.PMF.dist_pure_left`: distance from a point mass.
* `Cslib.Probability.PMF.dist_bool`: distance on `Bool`.
* `Cslib.Probability.PMF.dist_uniformOfFinset_of_card_le`,
  `Cslib.Probability.PMF.dist_uniformOfFinset_le`: distance between uniform distributions on
  finite sets.
-/

public section

open scoped Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α : Type*}

/-- The statistical distance from a point mass is the mass the other distribution places
elsewhere. -/
theorem dist_pure_left [Fintype α] (a : α) (q : PMF α) :
    dist (PMF.pure a) q = 1 - (q a).toReal := by
  classical
  rw [dist_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  have hrest : ∑ b ∈ Finset.univ.erase a, |((PMF.pure a) b).toReal - (q b).toReal| =
      ∑ b ∈ Finset.univ.erase a, (q b).toReal := by
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [PMF.pure_apply_of_ne _ _ (Finset.ne_of_mem_erase hb), ENNReal.toReal_zero, zero_sub,
      abs_neg, abs_of_nonneg ENNReal.toReal_nonneg]
  have hsum : (q a).toReal + ∑ b ∈ Finset.univ.erase a, (q b).toReal = 1 := by
    rw [Finset.add_sum_erase _ (fun b => (q b).toReal) (Finset.mem_univ a)]
    exact sum_toReal q
  have hle : (q a).toReal ≤ 1 := by
    linarith [Finset.sum_nonneg fun b (_ : b ∈ Finset.univ.erase a) =>
      (ENNReal.toReal_nonneg : 0 ≤ (q b).toReal)]
  rw [hrest, PMF.pure_apply_self, ENNReal.toReal_one, abs_of_nonneg (by linarith)]
  linarith

/-- Statistical distance on `Bool` is the difference of the probabilities of `true`. -/
theorem dist_bool (p q : PMF Bool) :
    dist p q = |(p true).toReal - (q true).toReal| := by
  have hfalse (r : PMF Bool) : (r false).toReal = 1 - (r true).toReal := by
    have h := sum_toReal r
    rw [Fintype.sum_bool] at h
    linarith
  rw [dist_eq, Fintype.sum_bool, hfalse p, hfalse q,
    show 1 - (p true).toReal - (1 - (q true).toReal) = -((p true).toReal - (q true).toReal) by
      ring, abs_neg]
  ring

/-- The statistical distance between uniform distributions on finite sets `A` and `B` with
`|A| ≤ |B|` is the fraction of `B` outside `A`. -/
theorem dist_uniformOfFinset_of_card_le [Fintype α] [DecidableEq α] {A B : Finset α}
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A.card ≤ B.card) :
    dist (uniformOfFinset A hA) (uniformOfFinset B hB) = (B \ A).card / B.card := by
  classical
  have hAc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hinv : (B.card : ℝ)⁻¹ ≤ (A.card : ℝ)⁻¹ := inv_anti₀ hAc (by exact_mod_cast hAB)
  have happly (s : Finset α) (hs : s.Nonempty) (a : α) :
      (uniformOfFinset s hs a).toReal = if a ∈ s then (s.card : ℝ)⁻¹ else 0 := by
    rw [uniformOfFinset_apply]
    split_ifs <;> simp
  rw [dist_comm, dist_eq_sum_filter_lt]
  have hfilter : (Finset.univ.filter fun a =>
      (uniformOfFinset A hA a).toReal < (uniformOfFinset B hB a).toReal) = B \ A := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, happly]
    by_cases haA : a ∈ A <;> by_cases haB : a ∈ B <;>
      simp [haA, haB, not_lt.mpr hinv, hB.card_pos]
  rw [hfilter, Finset.sum_congr rfl fun a ha => by
    rw [happly, happly, ite_eq_left (Finset.mem_sdiff.1 ha).1,
      ite_eq_right (Finset.mem_sdiff.1 ha).2, sub_zero], Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv]

/-- Uniform distributions on finite sets of size at least `m > 0` that differ by at most `k`
elements on each side are within statistical distance `k / m`. -/
theorem dist_uniformOfFinset_le [Fintype α] [DecidableEq α] {A B : Finset α}
    (hA : A.Nonempty) (hB : B.Nonempty) {k m : ℕ} (hm : 0 < m) (hmA : m ≤ A.card)
    (hmB : m ≤ B.card) (hBA : (B \ A).card ≤ k) (hAB : (A \ B).card ≤ k) :
    dist (uniformOfFinset A hA) (uniformOfFinset B hB) ≤ k / m := by
  have key {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) (hmB : m ≤ B.card)
      (hBA : (B \ A).card ≤ k) (hle : A.card ≤ B.card) :
      dist (uniformOfFinset A hA) (uniformOfFinset B hB) ≤ k / m := by
    rw [dist_uniformOfFinset_of_card_le hA hB hle]
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    calc ((B \ A).card : ℝ) / B.card ≤ k / B.card :=
          div_le_div_of_nonneg_right (by exact_mod_cast hBA) (Nat.cast_nonneg _)
      _ ≤ k / m := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hm' (by exact_mod_cast hmB)
  rcases le_total A.card B.card with hle | hle
  · exact key hA hB hmB hBA hle
  · rw [dist_comm]
    exact key hB hA hmA hAB hle

end Cslib.Probability.PMF
