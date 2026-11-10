/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Event
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Guessing a hidden value with low conditional entropy

Fano's inequality (`conditionalEntropy_le_binEntropy_add_mul_logb`) says that a hidden value that
can be guessed well has low conditional entropy. This module proves a converse: if `X` has
conditional entropy `H(X | Y)` given an observation `Y`, the maximum a posteriori estimator
guesses `X` from `Y` with error probability at most `1 - 2^(-H(X | Y)) ≤ (ln 2) H(X | Y)`.
Guessing bounds of this kind turn entropy estimates into guessing attacks, as in
information-theoretic lower bounds for garbled circuits [JanuzelliRosulekRoy2025]. Joint laws list
the observation first, as for `Cslib.Probability.PMF.conditionalEntropy`.

The proof compares each conditional law with its most likely value: that value has probability
at least `2^(-H)` because min-entropy is at most Shannon entropy, and Jensen's inequality for the
convex function `t ↦ 2^(-t)` averages these bounds over the observation.

## Main definitions

* `Cslib.Probability.PMF.maxPosteriorGuess`: a most likely hidden value for each observation.

## Main results

* `Cslib.Probability.PMF.errorProb_maxPosteriorGuess_le`: the estimator errs least among all
  deterministic estimators.
* `Cslib.Probability.PMF.errorProb_maxPosteriorGuess_le_one_sub_rpow`: its error probability is at
  most `1 - 2^(-H(X | Y))`.
* `Cslib.Probability.PMF.errorProb_maxPosteriorGuess_le_log_two_mul`: its error probability is at
  most `(ln 2) H(X | Y)`.

## References

* [J. Januzelli, M. Rosulek, L. Roy, *Lower Bounds for Garbled Circuits from Shannon-Type
  Information Inequalities*][JanuzelliRosulekRoy2025]
-/

public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- A **maximum a posteriori estimator**: for each observation, a hidden value of largest
conditional probability. -/
noncomputable def maxPosteriorGuess [Fintype α] [Nonempty α] (joint : PMF (β × α)) (y : β) : α :=
  (Finset.univ.exists_max_image (conditionalSnd joint y) Finset.univ_nonempty).choose

theorem conditionalSnd_le_conditionalSnd_maxPosteriorGuess [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) (y : β) (x : α) :
    conditionalSnd joint y x ≤ conditionalSnd joint y (maxPosteriorGuess joint y) :=
  (Finset.univ.exists_max_image (conditionalSnd joint y) Finset.univ_nonempty).choose_spec.2 x
    (Finset.mem_univ x)

/-- The error probability of an estimator is one minus the mass of the correct guesses. -/
private theorem errorProb_eq [Fintype β] [Finite α] (joint : PMF (β × α)) (g : β → α) :
    (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal =
      1 - ∑ y, ((joint.map Prod.fst) y).toReal * (conditionalSnd joint y (g y)).toReal := by
  classical
  let := Fintype.ofFinite α
  have hcorrect : ∑ z : β × α, (if g z.1 = z.2 then (joint z).toReal else 0) =
      ∑ y, ((joint.map Prod.fst) y).toReal * (conditionalSnd joint y (g y)).toReal := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    dsimp only
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), ← ENNReal.toReal_mul,
      marginal_mul_conditionalSnd]
  rw [toOuterMeasure_apply_toReal, ← hcorrect, ← sum_toReal joint, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp_all

/-- The maximum a posteriori estimator errs least among all deterministic estimators. -/
theorem errorProb_maxPosteriorGuess_le [Finite β] [Fintype α] [Nonempty α] (joint : PMF (β × α))
    (g : β → α) :
    (joint.toOuterMeasure {z | maxPosteriorGuess joint z.1 ≠ z.2}).toReal ≤
      (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal := by
  let := Fintype.ofFinite β
  rw [errorProb_eq, errorProb_eq]
  refine sub_le_sub_left (Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_
    ENNReal.toReal_nonneg) 1
  exact ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (conditionalSnd_le_conditionalSnd_maxPosteriorGuess joint y (g y))

/-- A most likely value of a law has probability at least `2^(-H)`. -/
private theorem rpow_neg_entropy_le_conditionalSnd_maxPosteriorGuess [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) (y : β) :
    (2 : ℝ) ^ (-entropy (conditionalSnd joint y)) ≤
      (conditionalSnd joint y (maxPosteriorGuess joint y)).toReal := by
  obtain ⟨a, ha, hsur⟩ := exists_surprisal_eq_minEntropy (conditionalSnd joint y)
  have hle : surprisal (conditionalSnd joint y) a ≤ entropy (conditionalSnd joint y) :=
    hsur ▸ minEntropy_le_entropy _
  exact ((surprisal_le_iff_mass_ge _ a ha).mp hle).trans (ENNReal.toReal_mono
    (PMF.apply_ne_top _ _) (conditionalSnd_le_conditionalSnd_maxPosteriorGuess joint y a))

/-- The maximum a posteriori estimator guesses the hidden value `X` from the observation `Y`
except with probability at most `1 - 2^(-H(X | Y))`. -/
theorem errorProb_maxPosteriorGuess_le_one_sub_rpow [Finite β] [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) :
    (joint.toOuterMeasure {z | maxPosteriorGuess joint z.1 ≠ z.2}).toReal ≤
      1 - (2 : ℝ) ^ (-conditionalEntropy joint) := by
  let := Fintype.ofFinite β
  rw [errorProb_eq]
  refine sub_le_sub_left ?_ 1
  set w : β → ℝ := fun y => ((joint.map Prod.fst) y).toReal
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := w)
    (p := fun y => Real.log 2 * -entropy (conditionalSnd joint y))
    (fun _ _ => ENNReal.toReal_nonneg) (sum_toReal _) (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hrpow : ∀ t : ℝ, (2 : ℝ) ^ t = Real.exp (Real.log 2 * t) := fun t =>
    Real.rpow_def_of_pos two_pos t
  calc (2 : ℝ) ^ (-conditionalEntropy joint)
      = Real.exp (∑ y, w y * (Real.log 2 * -entropy (conditionalSnd joint y))) := by
        rw [hrpow, conditionalEntropy_eq_sum]
        congr 1
        rw [← Finset.sum_neg_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ ≤ ∑ y, w y * Real.exp (Real.log 2 * -entropy (conditionalSnd joint y)) := hJ
    _ ≤ ∑ y, w y * (conditionalSnd joint y (maxPosteriorGuess joint y)).toReal :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          ((hrpow _).symm.le.trans (rpow_neg_entropy_le_conditionalSnd_maxPosteriorGuess joint y))
          ENNReal.toReal_nonneg

/-- The maximum a posteriori estimator errs with probability at most `(ln 2) H(X | Y)`. -/
theorem errorProb_maxPosteriorGuess_le_log_two_mul [Finite β] [Fintype α] [Nonempty α]
    (joint : PMF (β × α)) :
    (joint.toOuterMeasure {z | maxPosteriorGuess joint z.1 ≠ z.2}).toReal ≤
      Real.log 2 * conditionalEntropy joint := by
  refine (errorProb_maxPosteriorGuess_le_one_sub_rpow joint).trans ?_
  have h := Real.add_one_le_exp (Real.log 2 * -conditionalEntropy joint)
  rw [← Real.rpow_def_of_pos two_pos] at h
  linarith

end Cslib.Probability.PMF
