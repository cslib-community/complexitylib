/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Probability.Divergence
import Complexity.Probability.Shearer
import Complexity.Probability.Pinsker

/-! Kullback–Leibler divergence, Gibbs and Pinsker, subadditivity, Han and Shearer: concrete
instances, satisfiable hypotheses and a strict case. -/

namespace ComplexityTests.ProbabilityToolkit2

open Cslib Cslib.Probability Finset InformationTheory MeasureTheory
open scoped BigOperators Cslib.Probability.PMF

/-! ### Divergence of a point mass from a fair coin -/

private theorem support_pure_subset :
    (PMF.pure true).support ⊆ (Probability.PMF.uniformOfFintype Bool).support := by
  intro b _
  simp [PMF.mem_support_iff]

-- The divergence of a certain outcome from a fair coin is `log 2` nats.
example : (klDiv (PMF.pure true).toMeasure
    (Probability.PMF.uniformOfFintype Bool).toMeasure).toReal = Real.log 2 := by
  rw [PMF.toReal_klDiv_toMeasure support_pure_subset]
  simp [PMF.pure_apply]

/-- Their statistical distance is `1 / 2`, so Pinsker's inequality reads `1 / 2 ≤ log 2`. -/
private theorem dist_pure_true_uniform :
    dist (PMF.pure true) (Probability.PMF.uniformOfFintype Bool) = 1 / 2 := by
  rw [PMF.dist_eq]
  norm_num [PMF.pure_apply]

/-- Mathlib's total variation distance is twice the statistical distance. -/
private theorem tvDist_pure_true_uniform :
    tvDist (PMF.pure true).toMeasure (Probability.PMF.uniformOfFintype Bool).toMeasure = 1 := by
  have h := PMF.dist_eq_tvDist_toMeasure_div_two (PMF.pure true)
    (Probability.PMF.uniformOfFintype Bool)
  rw [dist_pure_true_uniform] at h
  linarith

example : ENNReal.ofReal (1 / 2) ≤
    klDiv (PMF.pure true).toMeasure (Probability.PMF.uniformOfFintype Bool).toMeasure := by
  have h := ofReal_tvDist_sq_div_two_le_klDiv (PMF.pure true).toMeasure
    (Probability.PMF.uniformOfFintype Bool).toMeasure
  rwa [tvDist_pure_true_uniform, one_pow] at h

example : (1 / 2 : ℝ) ≤
    ∑ b, ((PMF.pure true) b).toReal *
      Real.log (((PMF.pure true) b).toReal /
        ((Probability.PMF.uniformOfFintype Bool) b).toReal) := by
  have h := PMF.two_mul_dist_sq_le_sum_mul_log_div support_pure_subset
  rw [dist_pure_true_uniform] at h
  linarith

-- Gibbs' inequality is strict for distinct distributions.
example : 0 < ∑ b, ((PMF.pure true) b).toReal *
    Real.log (((PMF.pure true) b).toReal /
      ((Probability.PMF.uniformOfFintype Bool) b).toReal) := by
  refine lt_of_le_of_ne (PMF.sum_mul_log_div_nonneg support_pure_subset) (Ne.symm ?_)
  rw [Ne, PMF.sum_mul_log_div_eq_zero_iff support_pure_subset]
  intro h
  have := congrArg (fun p : PMF Bool => p false) h
  simp only [PMF.pure_apply, Bool.false_eq_true, ite_false,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat] at this
  exact ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top this.symm

-- A fair coin has one bit of entropy.
example : PMF.entropy (Probability.PMF.uniformOfFintype Bool) = 1 := by
  simp

/-! ### Subadditivity is strict for a correlated pair -/

/-- Two copies of one fair coin. -/
private noncomputable def twin : PMF (Bool × Bool) :=
  (Probability.PMF.uniformOfFintype Bool).map fun b => (b, b)

example : PMF.entropy twin ≠ PMF.entropy (twin.map Prod.fst) + PMF.entropy (twin.map Prod.snd) := by
  rw [Ne, PMF.entropy_eq_entropy_map_fst_add_entropy_map_snd_iff]
  intro h
  have := congrArg (fun p : PMF (Bool × Bool) => p (true, false)) h
  simp only [twin, PMF.map_comp, Function.comp_def] at this
  rw [PMF.map_apply, PMF.bind_apply] at this
  simp [PMF.map_apply, tsum_fintype] at this

example : PMF.conditionalEntropy twin ≤ 1 := by
  refine (PMF.conditionalEntropy_le_entropy_map_snd twin).trans_eq ?_
  have hmap : twin.map Prod.snd = Probability.PMF.uniformOfFintype Bool := by
    simp only [twin, PMF.map_comp]
    exact PMF.map_id _
  rw [hmap]
  simp

/-! ### Han's inequality and Shearer's lemma on three bits -/

-- Every coordinate of three avoids exactly one of the three deleted coordinates.
private theorem two_le_card_erase (i : Fin 3) :
    2 ≤ #{j | i ∈ (univ : Finset (Fin 3)).erase j} := by
  rw [show (univ.filter fun j => i ∈ (univ : Finset (Fin 3)).erase j) = univ.erase i by
    ext j; simp [eq_comm], card_erase_of_mem (mem_univ i)]
  simp

example (P : PMF (Fin 3 → Bool)) :
    (2 : ℕ) * PMF.entropy P ≤ ∑ j, PMF.entropy (P.map (univ.erase j).restrict) :=
  PMF.mul_entropy_le_sum_entropy_map_restrict P (fun j => univ.erase j) two_le_card_erase

-- The counting form is tight for the whole cube (`8 ^ 2 = 4 * 4 * 4`) and strict on a 3-point
-- L-shaped subset (`3 ^ 2 ≤ 2 * 2 * 3 = 12`).
private theorem card_image_restrict_erase (j : Fin 3) :
    #((univ : Finset (Fin 3 → Bool)).image (univ.erase j).restrict) = 4 := by
  rw [image_univ_of_surjective (fun y => ⟨fun i => if h : i ∈ univ.erase j then y ⟨i, h⟩
    else false, by funext ⟨i, hi⟩; simp [hi]⟩), card_univ, Fintype.card_pi]
  simp [card_erase_of_mem]

example : ∏ j : Fin 3, #((univ : Finset (Fin 3 → Bool)).image (univ.erase j).restrict) = 64 := by
  simp only [card_image_restrict_erase, prod_const, card_univ, Fintype.card_fin]
  norm_num

/-- A 3-point L-shaped subset of the 3-bit cube. -/
private def cornerSet : Finset (Fin 3 → Bool) :=
  {![false, false, false], ![true, false, false], ![false, true, false]}

example : 9 ≤ ∏ j : Fin 3, #(cornerSet.image (univ.erase j).restrict) := by
  have h := Cslib.Finset.card_pow_le_prod_card_image_restrict (α := fun _ => Bool) (k := 2)
    cornerSet (fun j => univ.erase j) (by norm_num) two_le_card_erase
  have hcard : #cornerSet ^ 2 = 9 := by decide
  rwa [hcard] at h

example : ∏ j : Fin 3, #(cornerSet.image (univ.erase j).restrict) = 12 := by decide

example : #(univ : Finset (Fin 3 → Bool)) ^ 2 = 64 := by simp

end ComplexityTests.ProbabilityToolkit2
