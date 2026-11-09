/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map

/-!
# Conditioning discrete distributions on events

`PMF.filter p s h` conditions `p` on an event `s` of positive probability. This file relates
conditioning to the other operations on discrete distributions.

* Conditioning on an event that contains the support changes nothing
  (`filter_eq_self_of_support_subset`).
* The probability of `t` under `p` conditioned on `s`, times the probability of `s`, is the
  probability of `s ∩ t` (`toOuterMeasure_filter_mul_eq_inter`). Conditioning on `s` and then on
  `t` is conditioning on `s ∩ t` (`filter_filter`).
* Conditioning commutes with relabeling when the event is a preimage (`filter_map`).
* In the law `μ.bind fun a => (K a).map (a, ·)`, which draws `a` from `μ` and then `b` from `K a`,
  conditioning on an event about `a` conditions `μ` and keeps the kernel (`filter_bind_pair`).
* If `b` is drawn independently of `a`, a rectangle `s ×ˢ t` has probability `Pr[s] Pr[t]`
  (`toOuterMeasure_bind_pair_prod`), and conditioning on it conditions each factor
  (`filter_bind_pair_prod`). In particular, the condition on `a` does not affect the law of `b`
  (`map_snd_filter_bind_pair_prod`).

## Main results

* `Cslib.Probability.PMF.filter_eq_self_of_support_subset`: conditioning on an almost sure event.
* `Cslib.Probability.PMF.toOuterMeasure_filter_mul_eq_inter`,
  `Cslib.Probability.PMF.filter_filter`: conditioning on an intersection.
* `Cslib.Probability.PMF.filter_map`: conditioning on a preimage commutes with relabeling.
* `Cslib.Probability.PMF.filter_bind_pair`: conditioning the first stage of a two-stage law.
* `Cslib.Probability.PMF.toOuterMeasure_bind_pair_prod`,
  `Cslib.Probability.PMF.filter_bind_pair_prod`,
  `Cslib.Probability.PMF.map_snd_filter_bind_pair_prod`: rectangles under independent pairs.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- A conditioned mass is the restricted mass divided by the probability of the event. -/
private theorem filter_apply_eq (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) (a : α) :
    p.filter s h a = s.indicator p a * (p.toOuterMeasure s)⁻¹ := by
  rw [PMF.filter_apply, PMF.toOuterMeasure_apply]

/-- An event containing a possible outcome has nonzero probability. -/
private theorem toOuterMeasure_ne_zero (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support) :
    p.toOuterMeasure s ≠ 0 := by
  obtain ⟨a, ha, hp⟩ := h
  rw [Ne, PMF.toOuterMeasure_apply_eq_zero_iff, Set.not_disjoint_iff]
  exact ⟨a, hp, ha⟩

/-- The conditioned masses restricted to `t` are the masses on `s ∩ t`, divided by `Pr[s]`. -/
private theorem indicator_filter_apply (p : PMF α) (s t : Set α) (h : ∃ a ∈ s, a ∈ p.support)
    (a : α) :
    t.indicator (p.filter s h) a = (s ∩ t).indicator p a * (p.toOuterMeasure s)⁻¹ := by
  rw [Set.inter_comm, ← Set.indicator_indicator]
  by_cases ha : a ∈ t
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, filter_apply_eq]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha, zero_mul]

/-- Conditioning on an event that contains the support changes nothing. -/
theorem filter_eq_self_of_support_subset (p : PMF α) (s : Set α) (h : ∃ a ∈ s, a ∈ p.support)
    (hs : p.support ⊆ s) : p.filter s h = p := by
  ext a
  rw [filter_apply_eq, (PMF.toOuterMeasure_apply_eq_one_iff p s).mpr hs, inv_one, mul_one]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem ha]
  · rw [Set.indicator_of_notMem ha]
    exact ((PMF.apply_eq_zero_iff p a).mpr fun hp => ha (hs hp)).symm

/-- The probability of `t` given `s`, times the probability of `s`, is the probability of
`s ∩ t`. -/
theorem toOuterMeasure_filter_mul_eq_inter (p : PMF α) (s t : Set α)
    (h : ∃ a ∈ s, a ∈ p.support) :
    (p.filter s h).toOuterMeasure t * p.toOuterMeasure s = p.toOuterMeasure (s ∩ t) := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply (s := s ∩ t)]
  simp only [indicator_filter_apply, ENNReal.tsum_mul_right, mul_assoc]
  rw [ENNReal.inv_mul_cancel (toOuterMeasure_ne_zero p s h) (toOuterMeasure_ne_top p s), mul_one]

/-- Conditioning on `s` and then on `t` is conditioning on `s ∩ t`. -/
theorem filter_filter (p : PMF α) (s t : Set α) (hs : ∃ a ∈ s, a ∈ p.support)
    (ht : ∃ a ∈ t, a ∈ (p.filter s hs).support) (hst : ∃ a ∈ s ∩ t, a ∈ p.support) :
    (p.filter s hs).filter t ht = p.filter (s ∩ t) hst := by
  ext a
  have hs0 := toOuterMeasure_ne_zero p s hs
  have hstop := toOuterMeasure_ne_top p s
  have hprob : (p.filter s hs).toOuterMeasure t =
      p.toOuterMeasure (s ∩ t) * (p.toOuterMeasure s)⁻¹ := by
    rw [← toOuterMeasure_filter_mul_eq_inter p s t hs, mul_assoc,
      ENNReal.mul_inv_cancel hs0 hstop, mul_one]
  rw [filter_apply_eq, filter_apply_eq, hprob, indicator_filter_apply,
    ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hs0)) (Or.inr (ENNReal.inv_ne_zero.mpr hstop)),
    inv_inv, mul_assoc, mul_left_comm (p.toOuterMeasure s)⁻¹, ENNReal.inv_mul_cancel hs0 hstop,
    mul_one]

/-- Conditioning a relabeled distribution on `s` is relabeling the distribution conditioned on
the preimage of `s`. -/
theorem filter_map (p : PMF α) (f : α → β) (s : Set β) (h : ∃ b ∈ s, b ∈ (p.map f).support)
    (h' : ∃ a ∈ f ⁻¹' s, a ∈ p.support) :
    (p.map f).filter s h = (p.filter (f ⁻¹' s) h').map f := by
  classical
  ext b
  rw [filter_apply_eq, PMF.toOuterMeasure_map_apply, PMF.map_apply]
  simp only [filter_apply_eq]
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb, PMF.map_apply, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun a => ?_
    by_cases hab : b = f a
    · have ha : a ∈ f ⁻¹' s := by rw [Set.mem_preimage, ← hab]; exact hb
      rw [ite_eq_left hab, ite_eq_left hab, Set.indicator_of_mem ha]
    · rw [ite_eq_right hab, ite_eq_right hab, zero_mul]
  · rw [Set.indicator_of_notMem hb, zero_mul]
    refine (tsum_eq_zero_iff.mpr fun a => ?_).symm
    by_cases hab : b = f a
    · have ha : a ∉ f ⁻¹' s := by rw [Set.mem_preimage, ← hab]; exact hb
      rw [ite_eq_left hab, Set.indicator_of_notMem ha, zero_mul]
    · rw [ite_eq_right hab]

/-- Drawing `a` from `μ` and then `b` from `K a`, and conditioning on an event about `a`, is
drawing `a` from `μ` conditioned on that event and then `b` from `K a`. -/
theorem filter_bind_pair (μ : PMF α) (K : α → PMF β) (s : Set α)
    (h : ∃ z ∈ Prod.fst ⁻¹' s, z ∈ (μ.bind fun a => (K a).map (a, ·)).support)
    (hs : ∃ a ∈ s, a ∈ μ.support) :
    (μ.bind fun a => (K a).map (a, ·)).filter (Prod.fst ⁻¹' s) h =
      (μ.filter s hs).bind fun a => (K a).map (a, ·) := by
  ext ⟨a, b⟩
  rw [filter_apply_eq, ← PMF.toOuterMeasure_map_apply, map_fst_bind_pair, bind_map_prodMk_apply,
    filter_apply_eq]
  by_cases ha : a ∈ s
  · rw [Set.indicator_of_mem (show (a, b) ∈ Prod.fst ⁻¹' s from ha), Set.indicator_of_mem ha,
      bind_map_prodMk_apply, mul_right_comm]
  · rw [Set.indicator_of_notMem (show (a, b) ∉ Prod.fst ⁻¹' s from ha),
      Set.indicator_of_notMem ha, zero_mul, zero_mul]

/-- Under independent draws, a rectangle has the product of the probabilities of its sides. -/
theorem toOuterMeasure_bind_pair_prod (μ : PMF α) (ν : PMF β) (s : Set α) (t : Set β) :
    (μ.bind fun a => ν.map (a, ·)).toOuterMeasure (s ×ˢ t) =
      μ.toOuterMeasure s * ν.toOuterMeasure t := by
  classical
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply μ s, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun a => ?_
  rw [PMF.toOuterMeasure_map_apply]
  by_cases ha : a ∈ s
  · rw [Set.mk_preimage_prod_right ha, Set.indicator_of_mem ha]
  · rw [Set.mk_preimage_prod_right_eq_empty ha, Set.indicator_of_notMem ha,
      MeasureTheory.measure_empty, mul_zero, zero_mul]

/-- Under independent draws, conditioning on a rectangle `s ×ˢ t` conditions the first draw on
`s` and the second on `t`, and keeps them independent. -/
theorem filter_bind_pair_prod (μ : PMF α) (ν : PMF β) (s : Set α) (t : Set β)
    (h : ∃ z ∈ s ×ˢ t, z ∈ (μ.bind fun a => ν.map (a, ·)).support)
    (hs : ∃ a ∈ s, a ∈ μ.support) (ht : ∃ b ∈ t, b ∈ ν.support) :
    (μ.bind fun a => ν.map (a, ·)).filter (s ×ˢ t) h =
      (μ.filter s hs).bind fun a => (ν.filter t ht).map (a, ·) := by
  ext ⟨a, b⟩
  rw [filter_apply_eq, toOuterMeasure_bind_pair_prod, bind_map_prodMk_apply, filter_apply_eq,
    filter_apply_eq,
    ENNReal.mul_inv (Or.inl (toOuterMeasure_ne_zero μ s hs)) (Or.inl (toOuterMeasure_ne_top μ s))]
  by_cases ha : a ∈ s
  · by_cases hb : b ∈ t
    · rw [Set.indicator_of_mem (Set.mk_mem_prod ha hb), Set.indicator_of_mem ha,
        Set.indicator_of_mem hb, bind_map_prodMk_apply]
      ring
    · rw [Set.indicator_of_notMem (fun hab => hb (Set.mem_prod.mp hab).2),
        Set.indicator_of_notMem hb, zero_mul, zero_mul, mul_zero]
  · rw [Set.indicator_of_notMem (fun hab => ha (Set.mem_prod.mp hab).1),
      Set.indicator_of_notMem ha, zero_mul, zero_mul, zero_mul]

/-- **Conditioning on an independent coordinate.** Under independent draws, conditioning on
`s ×ˢ t` gives the second draw the law of `ν` conditioned on `t`: the condition `s` on the first
draw has no effect on it. -/
theorem map_snd_filter_bind_pair_prod (μ : PMF α) (ν : PMF β) (s : Set α) (t : Set β)
    (h : ∃ z ∈ s ×ˢ t, z ∈ (μ.bind fun a => ν.map (a, ·)).support)
    (ht : ∃ b ∈ t, b ∈ ν.support) :
    ((μ.bind fun a => ν.map (a, ·)).filter (s ×ˢ t) h).map Prod.snd = ν.filter t ht := by
  have hs : ∃ a ∈ s, a ∈ μ.support := by
    obtain ⟨⟨a, b⟩, hab, hJ⟩ := h
    refine ⟨a, (Set.mem_prod.mp hab).1, ?_⟩
    have := (PMF.mem_support_iff _ _).mp hJ
    rw [bind_map_prodMk_apply] at this
    exact (PMF.mem_support_iff _ _).mpr (left_ne_zero_of_mul this)
  have hk : ∀ a : α, ((ν.filter t ht).map (a, ·)).map Prod.snd = ν.filter t ht := fun a =>
    (PMF.map_comp _ _ _).trans (PMF.map_id _)
  rw [filter_bind_pair_prod μ ν s t h hs ht, PMF.map_bind]
  simp only [hk, PMF.bind_const]

end Cslib.Probability.PMF
