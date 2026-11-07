/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Product
public import Cslib.Probability.StatisticalDistance
import Complexity.Probability.Divergence
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Mathlib.Algebra.Order.Chebyshev

/-!
# Conditioning a product distribution on an event

Condition independent coordinates `U₁, …, U_k` on an event `W`. Then the coordinates barely move:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2`
(`Cslib.Probability.PMF.sum_sq_dist_map_filter_pi_le`). This is Raz's conditioning lemma
[Raz, Claim 5.1][Raz1998], [Holenstein, Lemma 4.1][Holenstein2009], and it drives the coordinate
selection in the proof of the parallel repetition theorem. Holenstein states it as
`Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)` (`toOuterMeasure_toReal_le_two_rpow`), which follows
since `ln x / 2 ≤ log₂ x` for `x ≥ 1`, and uses it through Cauchy–Schwarz in the form
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))` (`sum_dist_map_filter_pi_le`).

The proof has three steps. Conditioning on `W` costs exactly `ln (1 / Pr[W])` nats of divergence
(`sum_mul_log_div_filter`). Divergence from a product distribution is superadditive over the
coordinates (`sum_sum_mul_log_div_map_le`): the gap is the divergence of the joint distribution
from the product of its own marginals, which is nonnegative by Gibbs' inequality. Pinsker's
inequality and Cauchy–Schwarz then bound the sum of statistical distances.

## Main results

* `Cslib.Probability.PMF.sum_mul_log_div_filter`: conditioning on `W` has divergence
  `ln (1 / Pr[W])`.
* `Cslib.Probability.PMF.sum_sum_mul_log_div_map_le`: superadditivity of divergence from a product.
* `Cslib.Probability.PMF.sum_sq_dist_map_filter_pi_le`: Raz's conditioning lemma.
* `Cslib.Probability.PMF.toOuterMeasure_toReal_le_two_rpow`: Holenstein's form
  `Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)`.
* `Cslib.Probability.PMF.sq_sum_dist_map_filter_pi_le`,
  `Cslib.Probability.PMF.sum_dist_map_filter_pi_le`: the forms summed by Cauchy–Schwarz,
  `∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))`.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
* [R. Raz, *A parallel repetition theorem*][Raz1998]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset
open scoped Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- Conditioning on an event `W` has divergence `ln (1 / Pr[W])` from the original distribution,
in nats. -/
theorem sum_mul_log_div_filter (p : PMF α) (event : Set α) (hevent : ∃ a ∈ event, a ∈ p.support) :
    ∑ a, ((p.filter event hevent) a).toReal *
        Real.log (((p.filter event hevent) a).toReal / (p a).toReal) =
      Real.log (1 / (p.toOuterMeasure event).toReal) := by
  classical
  set w := (p.toOuterMeasure event).toReal
  have hw : 0 < w := (toOuterMeasure_toReal_pos_iff p event).mpr hevent
  have hterm : ∀ a, ((p.filter event hevent) a).toReal *
      Real.log (((p.filter event hevent) a).toReal / (p a).toReal) =
        (if a ∈ event then (p a).toReal else 0) / w * Real.log (1 / w) := by
    intro a
    rw [filter_apply_toReal]
    by_cases ha : a ∈ event
    · rw [ite_eq_left ha, ite_eq_left ha]
      by_cases hpa : (p a).toReal = 0
      · simp [hpa]
      · congr 2
        field_simp
        exact div_self hw.ne'
    · simp [ha]
  rw [sum_congr rfl fun a _ => hterm a, ← sum_mul, ← sum_div, ← toOuterMeasure_apply_toReal,
    div_self hw.ne', one_mul]

section Product

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)]

/-- **Superadditivity of divergence from a product.** The divergences of the marginals of `P` from
the factors `p j` add up to at most the divergence of `P` from the product `pi p`, in nats. -/
theorem sum_sum_mul_log_div_map_le [DecidableEq ι] (P : PMF (∀ i, β i)) (p : ∀ i, PMF (β i))
    (h : P.support ⊆ (pi p).support) :
    ∑ j, ∑ a, ((P.map fun u => u j) a).toReal *
        Real.log (((P.map fun u => u j) a).toReal / (p j a).toReal) ≤
      ∑ u, (P u).toReal * Real.log ((P u).toReal / (pi p u).toReal) := by
  set M : ∀ j, PMF (β j) := fun j => P.map fun u => u j
  have hmarg : ∀ j, ∑ a, (M j a).toReal * Real.log ((M j a).toReal / (p j a).toReal) =
      ∑ u, (P u).toReal * Real.log ((M j (u j)).toReal / (p j (u j)).toReal) := fun j =>
    sum_map_mul P (fun u => u j) fun a => Real.log ((M j a).toReal / (p j a).toReal)
  have hsupp : P.support ⊆ (pi M).support := by
    intro u hu
    rw [mem_support_pi_iff]
    intro j
    exact (PMF.mem_support_iff _ _).mpr (ne_of_gt (lt_of_lt_of_le
      (pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp hu)) (le_map_apply P _ u)))
  have hgibbs := sum_mul_log_div_nonneg hsupp
  have hpt : ∀ u, (P u).toReal * Real.log ((P u).toReal / (pi p u).toReal) =
      (P u).toReal * Real.log ((P u).toReal / (pi M u).toReal) +
        ∑ j, (P u).toReal * Real.log ((M j (u j)).toReal / (p j (u j)).toReal) := by
    intro u
    by_cases hu : P u = 0
    · simp [hu]
    have hu' : u ∈ P.support := (PMF.mem_support_iff _ _).mpr hu
    have hp : ∀ j, (p j (u j)).toReal ≠ 0 := fun j => ENNReal.toReal_ne_zero.mpr
      ⟨(PMF.mem_support_iff _ _).mp ((mem_support_pi_iff p u).mp (h hu') j),
        PMF.apply_ne_top _ _⟩
    have hM : ∀ j, (M j (u j)).toReal ≠ 0 := fun j => ENNReal.toReal_ne_zero.mpr
      ⟨(PMF.mem_support_iff _ _).mp ((mem_support_pi_iff M u).mp (hsupp hu') j),
        PMF.apply_ne_top _ _⟩
    have hP : (P u).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hu, PMF.apply_ne_top _ _⟩
    rw [← mul_sum, ← mul_add]
    congr 1
    simp only [pi_apply, ENNReal.toReal_prod]
    rw [Real.log_div hP (prod_ne_zero_iff.mpr fun j _ => hp j),
      Real.log_div hP (prod_ne_zero_iff.mpr fun j _ => hM j),
      Real.log_prod (fun j _ => hp j), Real.log_prod (fun j _ => hM j)]
    simp only [Real.log_div (hM _) (hp _), sum_sub_distrib]
    ring
  rw [sum_congr rfl fun u _ => hpt u, sum_add_distrib, sum_comm (s := univ) (t := univ)]
  simp only [← hmarg]
  linarith

/-- **Raz's conditioning lemma** [Raz, Claim 5.1][Raz1998], [Holenstein, Lemma 4.1][Holenstein2009].
Conditioning independent coordinates on an event `W` moves them little:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2`. -/
theorem sum_sq_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ^ 2 ≤
      Real.log (1 / ((pi p).toOuterMeasure W).toReal) / 2 := by
  classical
  set Q := (pi p).filter W hW
  have hQ : Q.support ⊆ (pi p).support := by
    rw [PMF.support_filter]
    exact Set.inter_subset_right
  have hsup := sum_sum_mul_log_div_map_le Q p hQ
  rw [sum_mul_log_div_filter] at hsup
  have hpinsker : ∀ j, 2 * dist (Q.map fun u => u j) (p j) ^ 2 ≤
      ∑ a, ((Q.map fun u => u j) a).toReal *
        Real.log (((Q.map fun u => u j) a).toReal / (p j a).toReal) := by
    intro j
    refine two_mul_dist_sq_le_sum_mul_log_div fun a ha => ?_
    rw [PMF.support_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    exact (mem_support_pi_iff p u).mp (hQ hu) j
  have := sum_le_sum fun j (_ : j ∈ univ) => hpinsker j
  rw [← mul_sum] at this
  linarith

/-- **Raz's conditioning lemma** in the form of [Holenstein, Lemma 4.1, (4.1)][Holenstein2009]:
`Pr[W] ≤ 2 ^ (-∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖²)`. -/
theorem toOuterMeasure_toReal_le_two_rpow (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ((pi p).toOuterMeasure W).toReal ≤
      (2 : ℝ) ^ (-∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ^ 2) := by
  set w := ((pi p).toOuterMeasure W).toReal
  have hw0 : 0 < w := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  have hw1 : w ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one (pi p) W)
  have hlog : 0 ≤ Real.log (1 / w) := Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  have hln2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `ln (1 / w) / 2 ≤ log₂ (1 / w)` because `ln 2 < 2`.
  have hle : Real.log (1 / w) / 2 ≤ Real.logb 2 (1 / w) := by
    rw [Real.logb, div_le_div_iff₀ two_pos hln2]
    have : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
    nlinarith
  have hsum := (sum_sq_dist_map_filter_pi_le p W hW).trans hle
  calc w = (2 : ℝ) ^ (-Real.logb 2 (1 / w)) := by
        rw [Real.rpow_neg zero_le_two, Real.rpow_logb two_pos (by norm_num) (by positivity),
          one_div, inv_inv]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le one_le_two (neg_le_neg hsum)

/-- **Raz's conditioning lemma**, summed: `(∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖)² ≤ k · ln (1 / Pr[W]) / 2`
for `k` independent coordinates, by Cauchy–Schwarz. -/
theorem sq_sum_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    (∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j)) ^ 2 ≤
      Fintype.card ι * Real.log (1 / ((pi p).toOuterMeasure W).toReal) / 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ)
    (f := fun j => dist (((pi p).filter W hW).map fun u => u j) (p j))
  rw [card_univ] at hcs
  calc _ ≤ _ := hcs
    _ ≤ Fintype.card ι * (Real.log (1 / ((pi p).toOuterMeasure W).toReal) / 2) := by
        gcongr
        exact sum_sq_dist_map_filter_pi_le p W hW
    _ = _ := by ring

/-- **Raz's conditioning lemma** in the form of [Holenstein, (4.2)][Holenstein2009]:
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖ ≤ √(k · ln (1 / Pr[W]))` for `k` independent coordinates. -/
theorem sum_dist_map_filter_pi_le (p : ∀ i, PMF (β i)) (W : Set (∀ i, β i))
    (hW : ∃ u ∈ W, u ∈ (pi p).support) :
    ∑ j, dist (((pi p).filter W hW).map fun u => u j) (p j) ≤
      Real.sqrt (Fintype.card ι * Real.log (1 / ((pi p).toOuterMeasure W).toReal)) := by
  have hw : ((pi p).toOuterMeasure W).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one (pi p) W)
  have hw0 : 0 < ((pi p).toOuterMeasure W).toReal := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  have hlog : 0 ≤ Real.log (1 / ((pi p).toOuterMeasure W).toReal) :=
    Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  refine Real.le_sqrt_of_sq_le ((sq_sum_dist_map_filter_pi_le p W hW).trans ?_)
  have : (0 : ℝ) ≤ Fintype.card ι * Real.log (1 / ((pi p).toOuterMeasure W).toReal) := by
    positivity
  linarith

end Product

end Cslib.Probability.PMF
