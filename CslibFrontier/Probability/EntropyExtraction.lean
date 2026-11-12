/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.UniversalHash
public import CslibFrontier.Probability.EntropyConcentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind

/-!
# Extracting from concentrated conditional entropy

A source need not satisfy a pointwise probability bound everywhere. Discarding rare heavy
outcomes yields a source to which leftover hashing applies, with explicit error for the discarded
probability. This error is averaged over revealed side information, so rare observations do not
need separate worst-case entropy assumptions.

`IsTwoUniversal.leftover_hash_pi_conditional` combines this bound with concentration. Independent
samples with total conditional entropy `H` can be hashed with error at most
`2 exp(-2 t^2 / (count * bound^2)) + sqrt(2 * |Output| * 2^(-(H - t))) / 2`.
The concentration term uses a bound on each sample's information content, supplied for uniform
finite seeds by `uniform_map_mass_ge`.

## Main results

* `IsTwoUniversal.leftover_hash_of_heavy_probability`: smooth a source by discarding heavy outcomes.
* `IsTwoUniversal.leftover_hash_joint_of_heavy_probability`: retain all public side information.
* `IsTwoUniversal.leftover_hash_pi_conditional`: extract from independent conditional sources.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 3.3, Proposition 1 and Lemma 2.
  [Holenstein2006].
  We combine smoothing with the bounded-information concentration variant in
  `EntropyConcentration`; its loss depends on the uniform seed length rather than claiming
  Proposition 1's sharper alphabet-size bound.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the pinned finite-PMF metric.
-/

public section

namespace Cslib.Probability

open Cslib.Probability.PMF

variable {Seed Input Output : Type*} [Fintype Seed] [Finite Input] [Fintype Output]

/-- Heavy outcomes can be charged to extraction error. If their total probability is `δ`,
hashing costs at most `2δ` plus the leftover-hash error for a source with mass bound `2 * mass`.
No efficient sampler for the conditioned source is required by this statistical theorem. -/
theorem IsTwoUniversal.leftover_hash_of_heavy_probability [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) (source : PMF Input)
    {mass : ℝ} (hmass : 0 ≤ mass) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      2 * (source.toOuterMeasure {x | mass < (source x).toReal}).toReal +
        Real.sqrt (Fintype.card Output * (2 * mass)) / 2 := by
  classical
  let := Fintype.ofFinite Input
  let good := {x | (source x).toReal ≤ mass}
  have hpartition : (source.toOuterMeasure good).toReal +
      (source.toOuterMeasure {x | mass < (source x).toReal}).toReal = 1 := by
    simpa only [good, Set.compl_ofPred, not_le] using
      toOuterMeasure_toReal_add_compl source good
  by_cases hbad : (source.toOuterMeasure {x | mass < (source x).toReal}).toReal < 1 / 2
  · have hgood : 0 < (source.toOuterMeasure good).toReal := by linarith
    have hhalf : 1 / 2 ≤ (source.toOuterMeasure good).toReal := by linarith
    obtain hevent := (toOuterMeasure_toReal_pos_iff source good).mp hgood
    let conditioned := source.filter good hevent
    have hbounded (x : Input) : (conditioned x).toReal ≤ 2 * mass := by
      rw [filter_apply_toReal]
      split_ifs with hx
      · apply (div_le_iff₀ hgood).mpr
        change (source x).toReal ≤ mass at hx
        nlinarith
      · positivity
    have hclose : dist source conditioned =
        (source.toOuterMeasure {x | mass < (source x).toReal}).toReal := by
      simpa only [conditioned, good, Set.compl_ofPred, not_le] using dist_filter source good hevent
    have h := (dist_triangle (seededHash seed source hash) (seededHash seed conditioned hash)
      (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·)))).trans
        (add_le_add (dist_seededHash_le seed source conditioned hash)
          (hhash.leftover_hash_of_mass_le conditioned hbounded))
    rw [hclose] at h
    linarith [ENNReal.toReal_nonneg
      (a := source.toOuterMeasure {x | mass < (source x).toReal})]
  · have h := dist_le_one (seededHash seed source hash)
      (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·)))
    linarith [Real.sqrt_nonneg (Fintype.card Output * (2 * mass))]

/-- With public side information, only the average probability of heavy conditional outcomes
is charged to error. The seed and the side information are both retained in the comparison. -/
theorem IsTwoUniversal.leftover_hash_conditional_of_heavy_probability [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (side : PMF Side) (source : Side → PMF Input)
    {mass : ℝ} (hmass : 0 ≤ mass) :
    dist (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ≤
      2 * (∑ info, (side info).toReal *
        ((source info).toOuterMeasure {x | mass < (source info x).toReal}).toReal) +
          Real.sqrt (Fintype.card Output * (2 * mass)) / 2 := by
  rw [dist_bind_pair]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun info _ =>
    mul_le_mul_of_nonneg_left (hhash.leftover_hash_of_heavy_probability (source info) hmass)
      (ENNReal.toReal_nonneg (a := side info)))
  simpa only [mul_add, Finset.sum_add_distrib, mul_left_comm, ← Finset.mul_sum,
    ← Finset.sum_mul, sum_toReal, one_mul] using h

/-- The smoothed conditional leftover hash bound for a joint source. Both experiments preserve
its public marginal and reveal the independent hash seed. -/
theorem IsTwoUniversal.leftover_hash_joint_of_heavy_probability [Nonempty Output]
    {Side : Type*} [Fintype Side] {seed : PMF Seed} {hash : Seed → Input → Output}
    (hhash : IsTwoUniversal seed hash) (joint : PMF (Side × Input))
    {mass : ℝ} (hmass : 0 ≤ mass) :
    dist (joint.bind (fun pair => seed.map (fun s => (pair.1, s, hash s pair.2))))
        ((joint.map Prod.fst).bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ≤
      2 * (joint.toOuterMeasure
        {pair | mass < (conditionalSnd joint pair.1 pair.2).toReal}).toReal +
          Real.sqrt (Fintype.card Output * (2 * mass)) / 2 := by
  have h := hhash.leftover_hash_conditional_of_heavy_probability
    (joint.map Prod.fst) (conditionalSnd joint) hmass
  have hlaw := congrArg (fun law : PMF (Side × Input) =>
    law.bind (fun pair => seed.map (fun s => (pair.1, s, hash s pair.2))))
      (bind_conditionalSnd joint)
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def] at hlaw
  simp only [seededHash_eq_bind, PMF.map_bind, PMF.map_comp, PMF.bind_map, Function.comp_def] at h
  rw [hlaw] at h
  have hbad := congrArg (fun law : PMF (Side × Input) =>
    (law.toOuterMeasure {pair | mass < (conditionalSnd joint pair.1 pair.2).toReal}).toReal)
      (bind_conditionalSnd joint)
  simp only [toOuterMeasure_bind_toReal, PMF.toOuterMeasure_map_apply,
    Set.preimage_ofPred_eq] at hbad
  rw [hbad] at h
  simpa only [PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def] using h

/-- Independent joint samples supply almost their total conditional Shannon entropy to a
two-universal extractor. The error separates the concentration loss from the leftover-hash loss;
all observations and the complete hash seed remain public. -/
theorem IsTwoUniversal.leftover_hash_pi_conditional [Nonempty Output]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α β : ι → Type*} [∀ i, Fintype (α i)] [∀ i, Finite (β i)]
    {seed : PMF Seed} {hash : Seed → (∀ i, β i) → Output}
    (hhash : IsTwoUniversal seed hash) (joint : ∀ i, PMF (α i × β i))
    {bound ε : ℝ} (hbound : 0 ≤ bound)
    (hmass : ∀ i pair, pair ∈ (joint i).support →
      (2 : ℝ) ^ (-bound) ≤ (joint i pair).toReal) (hε : 0 ≤ ε) :
    dist ((PMF.pi joint).bind (fun outcome => seed.map
        (fun s => (fun i => (outcome i).1, s, hash s (fun i => (outcome i).2)))))
      ((PMF.pi (fun i => (joint i).map Prod.fst)).bind (fun observed => (seed.bind
        (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (observed, ·))) ≤
      2 * Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) +
        Real.sqrt (Fintype.card Output *
          (2 * (2 : ℝ) ^ (-((∑ i, conditionalEntropy (joint i)) - ε)))) / 2 := by
  let jointTuple := (PMF.pi joint).map
    (fun outcome => (fun i => (outcome i).1, fun i => (outcome i).2))
  let mass := (2 : ℝ) ^ (-((∑ i, conditionalEntropy (joint i)) - ε))
  have h := hhash.leftover_hash_joint_of_heavy_probability jointTuple
    (show 0 ≤ mass by positivity)
  have hmarginal : jointTuple.map Prod.fst = PMF.pi (fun i => (joint i).map Prod.fst) := by
    dsimp only [jointTuple]
    rw [pi_joint_eq_bind_conditionalSnd, map_fst_bind_pair]
  have hbad : (jointTuple.toOuterMeasure
      {pair | mass < (conditionalSnd jointTuple pair.1 pair.2).toReal}).toReal ≤
        Real.exp (-2 * ε ^ 2 / (Fintype.card ι * bound ^ 2)) :=
    pi_conditional_mass_gt joint hbound hmass hε
  rw [hmarginal] at h
  have hfinal := h.trans (add_le_add
    (mul_le_mul_of_nonneg_left hbad (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  simpa only [jointTuple, mass, PMF.bind_map, Function.comp_def] using hfinal

end Cslib.Probability
