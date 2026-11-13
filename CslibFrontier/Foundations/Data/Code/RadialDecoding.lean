/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.NearestDecoding
public import CslibFrontier.Foundations.Data.BitString.Weight
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.BitString.Neg
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map

/-!
# Deterministic decoding ties under radial noise

A uniform message is encoded and corrupted by independent additive binary noise. If the noise
mass depends only on its Hamming weight, every nearest message has the same joint mass with a
fixed received word. Consequently any deterministic nearest decoder succeeds with probability
`1 / |T(y)|`, conditional on receiving `y` and the sent message belonging to the tie set `T(y)`.
The joint-mass identity is valid even when that conditioning event has probability zero.

Messages are indexed by a finite type `M`. For a finite code `C`, take `M = C` and the subtype
inclusion as encoder. More generally an injective encoder identifies uniform messages with
uniform codewords; injectivity is not needed for the message-count formulation proved here.

This is the deterministic part of [HQC v5.1][HQC2026], §6.1.5, Lemma 6.2 (p. 60).
The radial-noise premise is explicit. No property of actual HQC noise, Reed–Solomon block
independence, concrete decoder, decoding-failure rate or cryptographic security is established here.

## Main definitions

* `Cslib.BitString.additiveNoiseJoint`: the joint law of received word and transmitted message.
* `Cslib.BitString.IsRadial`: equal Hamming weights have equal noise masses.

## Main results

* `Cslib.BitString.nearestMessages_card_mul_joint`: the null-event-safe tie identity.
* `Cslib.BitString.nearestMessages_conditional_success`: success at a nonnull observation.
* `Cslib.BitString.twoWayTie_failure_eq_half`: exact half-error probability at each noise weight.

## References

* [P. Gaborit et al., *Hamming Quasi-Cyclic (HQC)*, version 5.1][HQC2026], §6.1.5, p. 60.
-/

public section

namespace Cslib.BitString

open scoped ENNReal
open Cslib.Probability

variable {ι M : Type} [Fintype ι]

/-- The noise mass depends only on its Hamming weight. This does not assert independence of
individual noise coordinates. -/
@[expose] def IsRadial (ν : PMF (ι → Bool)) : Prop :=
  ∀ u v, hammingNorm u = hammingNorm v → ν u = ν v

/-- Independently draw a message and a noise vector, returning the received word together with
its transmitted message. The first marginal is the received-word law. -/
noncomputable def additiveNoiseJoint (E : M → ι → Bool) (prior : PMF M)
    (ν : PMF (ι → Bool)) : PMF ((ι → Bool) × M) := do
  let m ← prior
  let e ← ν
  pure (E m + e, m)

omit [Fintype ι] in
/-- The joint mass factors as prior times the mass of the unique compatible noise vector. -/
theorem additiveNoiseJoint_apply (E : M → ι → Bool) (prior : PMF M)
    (ν : PMF (ι → Bool)) (y : ι → Bool) (m : M) :
    additiveNoiseJoint E prior ν (y, m) = prior m * ν (E m + y) := by
  let e := (Equiv.prodCongrRight fun m => Equiv.addLeft (E m)).trans
    (Equiv.prodComm M (ι → Bool))
  have hjoint : additiveNoiseJoint E prior ν =
      (prior.bind fun m => ν.map (m, ·)).map e := by
    simp only [PMF.map_bind, PMF.map_comp]
    rfl
  rw [hjoint, PMF.map_equiv_apply, PMF.bind_map_prodMk_apply]
  simp [e, BitString.neg_eq_self]

variable [Fintype M] [Nonempty M]

/-- Under a uniform prior, radial noise assigns equal joint masses to nearest messages. -/
theorem additiveNoiseJoint_eq_of_mem_nearestMessages (E : M → ι → Bool)
    {ν : PMF (ι → Bool)} (hν : IsRadial ν) (y : ι → Bool) {m m' : M}
    (hm : m ∈ nearestMessages E y) (hm' : m' ∈ nearestMessages E y) :
    additiveNoiseJoint E (PMF.uniformOfFintype M) ν (y, m) =
      additiveNoiseJoint E (PMF.uniformOfFintype M) ν (y, m') := by
  rw [additiveNoiseJoint_apply, additiveNoiseJoint_apply,
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  congr 1
  apply hν
  simpa only [← weight_eq_hammingNorm, ← hammingDist_eq_weight_add] using
    hammingDist_eq_of_mem_nearestMessages hm hm'

omit [Nonempty M] in
/-- The nearest-message event at a fixed received word is the sum of its joint masses. -/
theorem nearestMessages_event_eq_sum (E : M → ι → Bool) (prior : PMF M)
    (ν : PMF (ι → Bool)) (y : ι → Bool) :
    (additiveNoiseJoint E prior ν).toOuterMeasure
        {p | p.1 = y ∧ p.2 ∈ nearestMessages E y} =
      ∑ m ∈ nearestMessages E y, additiveNoiseJoint E prior ν (y, m) := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, Fintype.sum_prod_type]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_and]
  rw [Finset.sum_eq_single y]
  · simp only [ite_true, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  · intro y' _ hy
    simp [hy]
  · simp

/-- **The null-event-safe tie law.** The number of nearest messages times the joint success
mass is the probability of receiving `y` with the transmitted message among the nearest ones.
In particular this identity does not divide by a possibly zero event probability. -/
theorem nearestMessages_card_mul_joint (E : M → ι → Bool) {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) {ν : PMF (ι → Bool)} (hν : IsRadial ν) (y : ι → Bool) :
    (nearestMessages E y).card * additiveNoiseJoint E (PMF.uniformOfFintype M) ν (y, D y) =
      (additiveNoiseJoint E (PMF.uniformOfFintype M) ν).toOuterMeasure
        {p | p.1 = y ∧ p.2 ∈ nearestMessages E y} := by
  rw [nearestMessages_event_eq_sum]
  calc
    _ = ∑ _m ∈ nearestMessages E y,
        additiveNoiseJoint E (PMF.uniformOfFintype M) ν (y, D y) := by simp
    _ = _ := Finset.sum_congr rfl fun m hm =>
      additiveNoiseJoint_eq_of_mem_nearestMessages E hν y (hD.mem_nearestMessages y) hm

/-- At a positive-probability tie event, the conditional success probability is the reciprocal
of the number of nearest messages. The numerator is the joint event `Y = y` and `D(y) = m`;
because the decoder returns a nearest message, success implies membership in the tie set. -/
theorem nearestMessages_conditional_success (E : M → ι → Bool) {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) {ν : PMF (ι → Bool)} (hν : IsRadial ν) (y : ι → Bool)
    (hpos : (additiveNoiseJoint E (PMF.uniformOfFintype M) ν).toOuterMeasure
      {p | p.1 = y ∧ p.2 ∈ nearestMessages E y} ≠ 0) :
    additiveNoiseJoint E (PMF.uniformOfFintype M) ν (y, D y) /
        (additiveNoiseJoint E (PMF.uniformOfFintype M) ν).toOuterMeasure
          {p | p.1 = y ∧ p.2 ∈ nearestMessages E y} =
      ((nearestMessages E y).card : ℝ≥0∞)⁻¹ := by
  have hcard : ((nearestMessages E y).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr ⟨D y, hD.mem_nearestMessages y⟩
  symm
  apply (ENNReal.eq_div_iff hpos (PMF.toOuterMeasure_ne_top _ _)).mpr
  rw [← nearestMessages_card_mul_joint E hD hν y, mul_right_comm,
    ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _), one_mul]

/-- **Two-way ties cause exactly half errors at each noise weight.** The noise vector is
recovered from the joint outcome as `E m + y`. No positive-mass premise is needed. -/
theorem twoWayTie_failure_eq_half (E : M → ι → Bool) {D : (ι → Bool) → M}
    (hD : IsNearestDecoder E D) {ν : PMF (ι → Bool)} (hν : IsRadial ν) (r : ℕ) :
    ((additiveNoiseJoint E (PMF.uniformOfFintype M) ν).toOuterMeasure
      {p | D p.1 ≠ p.2 ∧ p.2 ∈ nearestMessages E p.1 ∧
        (nearestMessages E p.1).card = 2 ∧ hammingNorm (E p.2 + p.1) = r}).toReal =
      1 / 2 * ((additiveNoiseJoint E (PMF.uniformOfFintype M) ν).toOuterMeasure
        {p | p.2 ∈ nearestMessages E p.1 ∧ (nearestMessages E p.1).card = 2 ∧
          hammingNorm (E p.2 + p.1) = r}).toReal := by
  classical
  let q := additiveNoiseJoint E (PMF.uniformOfFintype M) ν
  have hslice (y : ι → Bool) :
      (∑ m, if D y ≠ m ∧ m ∈ nearestMessages E y ∧ (nearestMessages E y).card = 2 ∧
          hammingNorm (E m + y) = r then (q (y, m)).toReal else 0) =
        1 / 2 * ∑ m, if m ∈ nearestMessages E y ∧ (nearestMessages E y).card = 2 ∧
          hammingNorm (E m + y) = r then (q (y, m)).toReal else 0 := by
    by_cases hcard : (nearestMessages E y).card = 2
    · have hmass (m : M) (hm : m ∈ nearestMessages E y) : q (y, m) = q (y, D y) :=
        additiveNoiseJoint_eq_of_mem_nearestMessages E hν y hm (hD.mem_nearestMessages y)
      have hweight (m : M) (hm : m ∈ nearestMessages E y) :
          hammingNorm (E m + y) = hammingNorm (E (D y) + y) := by
        simpa only [← weight_eq_hammingNorm, ← hammingDist_eq_weight_add] using
          hammingDist_eq_of_mem_nearestMessages hm (hD.mem_nearestMessages y)
      simp only [hcard, true_and]
      have hpred (m : M) :
          (D y ≠ m ∧ m ∈ nearestMessages E y ∧ hammingNorm (E m + y) = r) ↔
            (m ∈ (nearestMessages E y).erase (D y) ∧ hammingNorm (E m + y) = r) := by
        simp [Finset.mem_erase, ne_comm, and_assoc]
      simp_rw [hpred, ite_and]
      rw [Finset.sum_ite_mem_eq, Finset.sum_ite_mem_eq]
      have hsum (s : Finset M) (hs : s ⊆ nearestMessages E y) :
          (∑ m ∈ s, if hammingNorm (E m + y) = r then (q (y, m)).toReal else 0) =
            s.card * (if hammingNorm (E (D y) + y) = r then (q (y, D y)).toReal else 0) := by
        calc
          _ = ∑ _m ∈ s, if hammingNorm (E (D y) + y) = r
              then (q (y, D y)).toReal else 0 :=
            Finset.sum_congr rfl fun m hm => by rw [hweight m (hs hm), hmass m (hs hm)]
          _ = _ := by simp
      rw [hsum _ (Finset.erase_subset _ _), hsum _ Finset.Subset.rfl,
        Finset.card_erase_of_mem (hD.mem_nearestMessages y), hcard]
      split_ifs <;> norm_num; ring
    · simp [hcard]
  rw [PMF.toOuterMeasure_apply_toReal, PMF.toOuterMeasure_apply_toReal,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  convert hslice y using 1 <;> congr 2 <;> ext m <;>
    split_ifs <;> simp_all only [Set.mem_ofPred_eq, q] <;> tauto

end Cslib.BitString
