/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Statistical distance with public side information

Revealing a shared sample makes the joint distance exactly the average conditional distance.
Its square is bounded by the corresponding average squared distance. Statistical distance is the
probability gap on the event where one distribution exceeds the other, and half of Mathlib's
total variation distance `tvDist` of the induced measures.
These statements reuse the upstream finite-PMF metric and its enumeration instances.

## Main results

* `Cslib.Probability.PMF.dist_filter`: conditioning costs the discarded probability.
* `Cslib.Probability.PMF.abs_sum_mul_sub_le`: bounded-score changes under statistical distance.
* `Cslib.Probability.PMF.dist_bind_pair`: exact average distance with a shared public sample.
* `Cslib.Probability.PMF.dist_bind_pair_sq_le`: the squared-distance bound used in leftover hashing.
* `Cslib.Probability.PMF.dist_bind_left_le`: convexity of statistical distance in `PMF.bind`.
* `Cslib.Probability.PMF.dist_bind_left_le_of_le`: uniform distance bound across a `PMF.bind`
  mixture.
* `Cslib.Probability.PMF.dist_uniformOfFintype_bool`: statistical distance from uniform on `Bool`.
* `Cslib.Probability.PMF.dist_eq_sum_filter_lt`: statistical distance as the excess on `{p > q}`.
* `Cslib.Probability.PMF.dist_eq_tvDist_toMeasure_div_two`: statistical distance is half of
  `tvDist`.

## References

Adapted from Probability/StatisticalDistance.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. The metric itself remains the upstream one.
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- Conditioning on a possible event changes the distribution by exactly the probability
discarded outside that event. -/
theorem dist_filter [Fintype α] (p : PMF α) (event : Set α)
    (hevent : ∃ a ∈ event, a ∈ p.support) :
    dist p (p.filter event hevent) = (p.toOuterMeasure eventᶜ).toReal := by
  classical
  have hpositive := (toOuterMeasure_toReal_pos_iff p event).mpr hevent
  have hprobability : (p.toOuterMeasure event).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one p event)
  have habsolute (a : α) : |(p a).toReal - ((p.filter event hevent) a).toReal| =
      ((p.filter event hevent) a).toReal - (p a).toReal +
        2 * (if a ∈ eventᶜ then (p a).toReal else 0) := by
    by_cases ha : a ∈ event
    · have hle : (p a).toReal ≤ ((p.filter event hevent) a).toReal := by
        rw [filter_apply_toReal, ite_eq_left ha]
        exact (le_div_iff₀ hpositive).mpr
          (mul_le_of_le_one_right ENNReal.toReal_nonneg hprobability)
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      simp [ha, neg_sub]
    · simp only [filter_apply_toReal, ha, ite_false, Set.mem_compl_iff, not_false_eq_true, ite_true,
        sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
      ring
  rw [dist_eq, toOuterMeasure_apply_toReal]
  simp_rw [habsolute]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_toReal, sub_self, zero_add,
    ← Finset.mul_sum]
  ring_nf

/-- With a shared revealed input, distance is the average distance of the conditional outputs. -/
theorem dist_bind_pair [Fintype α] [Fintype β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) =
      ∑ a, (p a).toReal * dist (f a) (g a) := by
  simp only [dist_eq, Fintype.sum_prod_type, bind_map_prodMk_apply,
    ENNReal.toReal_mul, ← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
    ← Finset.mul_sum, Finset.sum_div, mul_div_assoc]

/-- Squared distance with a shared revealed input is at most the average squared distance. -/
theorem dist_bind_pair_sq_le [Fintype α] [Fintype β] (p : PMF α) (f g : α → PMF β) :
    dist (p.bind (fun a => (f a).map (a, ·)))
        (p.bind (fun a => (g a).map (a, ·))) ^ 2 ≤
      ∑ a, (p a).toReal * dist (f a) (g a) ^ 2 := by
  rw [dist_bind_pair]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a => (p a).toReal * dist (f a) (g a))
    (f := fun a => (p a).toReal) (g := fun a => (p a).toReal * dist (f a) (g a) ^ 2)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    (fun _ _ => by ring_nf; rfl)
  simpa only [sum_toReal, one_mul] using h

/-- Changing the distribution changes a bounded real-valued score by at most twice its
absolute bound times statistical distance. Signed prediction scores may use `bound = 1`. -/
theorem abs_sum_mul_sub_le [Fintype α] (p q : PMF α) (score : α → ℝ)
    {bound : ℝ} (hscore : ∀ a, |score a| ≤ bound) :
    |(∑ a, (p a).toReal * score a) - ∑ a, (q a).toReal * score a| ≤
      2 * bound * dist p q := by
  rw [← Finset.sum_sub_distrib]
  simp only [← sub_mul]
  calc
    _ ≤ ∑ a, |((p a).toReal - (q a).toReal) * score a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |(p a).toReal - (q a).toReal| * bound := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hscore a) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, dist_eq]; ring

/-- Convexity of statistical distance in the first argument: the distance of a mixture `p.bind f`
from `q` is at most the `p`-weighted average distance of `f a` from `q`. -/
theorem dist_bind_left_le [Fintype α] [Fintype β] (p : PMF α) (f : α → PMF β) (q : PMF β) :
    dist (p.bind f) q ≤ ∑ a, (p a).toReal * dist (f a) q := by
  have h1 : (p.bind fun a => (f a).map (a, ·)).map Prod.snd = p.bind f := by
    rw [PMF.map_bind]
    refine congrArg (p.bind ·) (funext fun a => ?_)
    exact (PMF.map_comp _ _ _).trans (PMF.map_id _)
  have h2 : (p.bind fun a => q.map (a, ·)).map Prod.snd = q := by
    rw [PMF.map_bind]
    have hq : (fun a : α => (q.map (a, ·)).map Prod.snd) = fun _ => q :=
      funext fun a => (PMF.map_comp _ _ _).trans (PMF.map_id _)
    rw [hq, PMF.bind_const]
  calc
    dist (p.bind f) q
      = dist ((p.bind fun a => (f a).map (a, ·)).map Prod.snd)
          ((p.bind fun a => q.map (a, ·)).map Prod.snd) := by rw [h1, h2]
    _ ≤ dist (p.bind fun a => (f a).map (a, ·)) (p.bind fun a => q.map (a, ·)) :=
      dist_map_le _ _ Prod.snd
    _ = ∑ a, (p a).toReal * dist (f a) q := dist_bind_pair p f fun _ => q

/-- If every component `f a` in the support of `p` is within `δ` of `q`, so is `p.bind f`. -/
theorem dist_bind_left_le_of_le [Finite α] [Fintype β] (p : PMF α) (f : α → PMF β) (q : PMF β)
    {δ : ℝ} (h : ∀ a ∈ p.support, dist (f a) q ≤ δ) :
    dist (p.bind f) q ≤ δ := by
  cases nonempty_fintype α
  calc
    dist (p.bind f) q ≤ ∑ a, (p a).toReal * dist (f a) q := dist_bind_left_le p f q
    _ ≤ ∑ a, (p a).toReal * δ := by
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases ha : a ∈ p.support
      · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg
      · rw [(p.apply_eq_zero_iff a).mpr ha, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = δ := by rw [← Finset.sum_mul, sum_toReal, one_mul]

/-- Statistical distance on `Bool` from the uniform distribution is the bias `|p(true) - 1 / 2|`. -/
theorem dist_uniformOfFintype_bool (p : PMF Bool) :
    dist p (uniformOfFintype Bool) = |(p true).toReal - 1 / 2| := by
  have hsum : (p true).toReal + (p false).toReal = 1 := by
    have h := p.tsum_coe
    rw [tsum_fintype, Fintype.sum_bool] at h
    have h' := congrArg ENNReal.toReal h
    rwa [ENNReal.toReal_add (p.apply_ne_top _) (p.apply_ne_top _), ENNReal.toReal_one] at h'
  rw [dist_eq, Fintype.sum_bool]
  simp only [uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat]
  have hfalse : |(p false).toReal - 2⁻¹| = |(p true).toReal - 2⁻¹| := by
    rw [show (p false).toReal - 2⁻¹ = -((p true).toReal - 2⁻¹) by linarith, abs_neg]
  linarith

section TotalVariation

open MeasureTheory ProbabilityTheory

variable [Fintype α]

/-- Statistical distance is the probability gap on the event where `p` exceeds `q`. -/
theorem dist_eq_sum_filter_lt (p q : PMF α) :
    dist p q = ∑ a ∈ Finset.univ.filter (fun a => (q a).toReal < (p a).toReal),
      ((p a).toReal - (q a).toReal) := by
  rw [dist_eq, Finset.sum_filter]
  have hsum : ∑ a, ((p a).toReal - (q a).toReal) = 0 := by
    rw [Finset.sum_sub_distrib, sum_toReal, sum_toReal, sub_self]
  have habs (a : α) : |(p a).toReal - (q a).toReal| =
      2 * (if (q a).toReal < (p a).toReal then (p a).toReal - (q a).toReal else 0) -
        ((p a).toReal - (q a).toReal) := by
    split_ifs with h
    · rw [abs_of_pos (sub_pos.mpr h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp h))]; ring
  simp only [habs, Finset.sum_sub_distrib, hsum, ← Finset.mul_sum]
  ring

omit [Fintype α] in
/-- The probability of an event under a PMF measure is the sum of its masses. -/
private theorem measureReal_toMeasure_eq_sum [MeasurableSpace α] [MeasurableSingletonClass α]
    (r : PMF α) (event : Finset α) :
    r.toMeasure.real (event : Set α) = ∑ a ∈ event, (r a).toReal := by
  rw [measureReal_def, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top r a)]

/-- Statistical distance is half of Mathlib's total variation distance `tvDist` of the PMF
measures. -/
theorem dist_eq_tvDist_toMeasure_div_two [MeasurableSpace α] [MeasurableSingletonClass α]
    (p q : PMF α) : dist p q = tvDist p.toMeasure q.toMeasure / 2 := by
  classical
  let below : Finset α := Finset.univ.filter fun a => (p a).toReal ≤ (q a).toReal
  have hbelow : (↑below : Set α)ᶜ = ↑(Finset.univ.filter
      fun a => (q a).toReal < (p a).toReal) := by
    ext a; simp [below]
  have hhahn : IsHahnDecomposition p.toMeasure q.toMeasure below := by
    have hle (μ ν : PMF α) (t : Set α) (ht : ∀ a ∈ t, (μ a).toReal ≤ (ν a).toReal) :
        μ.toMeasure t ≤ ν.toMeasure t := by
      rw [PMF.toMeasure_apply_fintype, PMF.toMeasure_apply_fintype]
      refine Finset.sum_le_sum fun a _ => ?_
      by_cases ha : a ∈ t
      · simpa [ha] using (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
          (PMF.apply_ne_top _ _)).mp (ht a ha)
      · simp [ha]
    refine ⟨(Set.to_countable _).measurableSet, Measure.le_iff'.mpr fun t => ?_,
      Measure.le_iff'.mpr fun t => ?_⟩
    · rw [Measure.restrict_apply' (Set.to_countable _).measurableSet,
        Measure.restrict_apply' (Set.to_countable _).measurableSet]
      exact hle p q _ fun a ha => by simpa [below] using ha.2
    · rw [Measure.restrict_apply' (Set.to_countable _).measurableSet,
        Measure.restrict_apply' (Set.to_countable _).measurableSet, hbelow]
      exact hle q p _ fun a ha => (Finset.mem_filter.mp (Finset.mem_coe.mp ha.2)).2.le
  rw [hhahn.tvDist_eq, probReal_compl_eq_one_sub (μ := p.toMeasure) hhahn.measurableSet,
    probReal_compl_eq_one_sub (μ := q.toMeasure) hhahn.measurableSet,
    dist_eq_sum_filter_lt, Finset.sum_sub_distrib, ← measureReal_toMeasure_eq_sum p,
    ← measureReal_toMeasure_eq_sum q, ← hbelow,
    probReal_compl_eq_one_sub (μ := p.toMeasure) hhahn.measurableSet,
    probReal_compl_eq_one_sub (μ := q.toMeasure) hhahn.measurableSet]
  ring

end TotalVariation

end Cslib.Probability.PMF
