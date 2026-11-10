/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MinEntropy
public import CslibFrontier.Probability.UniversalHash

/-!
# Leftover hashing from weak random sources

The leftover hash lemma for `(k, ε)`-sources: hashing a `(k, ε)`-source with an independent
two-universal seed, which stays public, gives a distribution within
`ε + √(|Output| · 2⁻ᵏ) / 2` of the seed paired with an independent uniform value. With
`log₂ |Output| + 2 log₂ (1 / δ) ≤ k` the error is at most `ε + δ / 2`, so a two-universal family
is a strong extractor that loses `2 log₂ (1 / δ)` bits of min-entropy (stated with
`Cslib.Probability.IsStrongExtractor` as `IsTwoUniversal.isStrongExtractor_of_logb_le`)
[Vadhan, Chapter 6][Vadhan2012], [Håstad, Impagliazzo, Levin, Luby][HILL1999]. With public side
information it suffices that every possible conditional source is a `(k, ε)`-source.

These are corollaries of the pointwise-mass form `IsTwoUniversal.leftover_hash_of_mass_le` and of
`dist_seededHash_le`. Sources with rare heavy outcomes are `(k, ε)`-sources by
`Cslib.Probability.PMF.isSource_of_heavy_le`; `IsTwoUniversal.leftover_hash_of_heavy_probability`
states the resulting extraction bound directly.

## Main results

* `Cslib.Probability.IsTwoUniversal.leftover_hash_of_isSource`: the leftover hash lemma for
  `(k, ε)`-sources.
* `Cslib.Probability.IsTwoUniversal.leftover_hash_of_isSource_of_logb_le`: the entropy-loss form.
* `Cslib.Probability.IsTwoUniversal.leftover_hash_conditional_of_isSource`: extraction with side
  information.

## References

* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby, *A Pseudorandom Generator from any One-way
  Function*][HILL1999]
-/

public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped NNReal

variable {Seed Input Output : Type*} [Fintype Seed] [Fintype Input] [Fintype Output]
  [Nonempty Output]

/-- **The leftover hash lemma for `(k, ε)`-sources.** Hashing a `(k, ε)`-source with an
independent two-universal seed, revealed in the output, is within `ε + √(|Output| · 2⁻ᵏ) / 2` of
the seed paired with an independent uniform value. -/
theorem IsTwoUniversal.leftover_hash_of_isSource {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) {source : PMF Input}
    {k : ℝ} {ε : ℝ≥0} (hsource : IsSource source k ε) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤
      ε + Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2 := by
  obtain ⟨close, hclose, hdist⟩ := hsource
  calc
    _ ≤ dist (seededHash seed source hash) (seededHash seed close hash) +
        dist (seededHash seed close hash)
          (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) :=
      dist_triangle _ _ _
    _ ≤ ε + Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2 :=
      add_le_add ((dist_seededHash_le seed source close hash).trans hdist)
        (hhash.leftover_hash_of_mass_le close ((le_minEntropy_iff close).mp hclose))

/-- **Entropy loss of leftover hashing.** If the source is a `(k, ε)`-source with
`log₂ |Output| + 2 log₂ (1 / δ) ≤ k`, hashing with an independent public two-universal seed is
within `ε + δ / 2` of the seed paired with an independent uniform value. -/
theorem IsTwoUniversal.leftover_hash_of_isSource_of_logb_le {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash) {source : PMF Input}
    {k : ℝ} {ε : ℝ≥0} (hsource : IsSource source k ε) {δ : ℝ} (hδ : 0 < δ)
    (hk : Real.logb 2 (Fintype.card Output) + 2 * Real.logb 2 δ⁻¹ ≤ k) :
    dist (seededHash seed source hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) ≤ ε + δ / 2 := by
  have hcard : (0 : ℝ) < Fintype.card Output := by exact_mod_cast Fintype.card_pos
  have hmass : (Fintype.card Output : ℝ) * 2 ^ (-k) ≤ δ ^ 2 := by
    have hpow : (2 : ℝ) ^ (Real.logb 2 (Fintype.card Output) + 2 * Real.logb 2 δ⁻¹) =
        Fintype.card Output * δ⁻¹ * δ⁻¹ := by
      rw [two_mul, Real.rpow_add two_pos, Real.rpow_add two_pos,
        Real.rpow_logb two_pos (by norm_num) hcard,
        Real.rpow_logb two_pos (by norm_num) (inv_pos.mpr hδ), mul_assoc]
    calc
      (Fintype.card Output : ℝ) * 2 ^ (-k) ≤ Fintype.card Output *
          2 ^ (-(Real.logb 2 (Fintype.card Output) + 2 * Real.logb 2 δ⁻¹)) := by
        gcongr
        norm_num
      _ = δ ^ 2 := by
        rw [Real.rpow_neg zero_le_two, hpow]
        field_simp
  have hsqrt : Real.sqrt (Fintype.card Output * 2 ^ (-k)) ≤ δ :=
    (Real.sqrt_le_sqrt hmass).trans_eq (Real.sqrt_sq hδ.le)
  exact (hhash.leftover_hash_of_isSource hsource).trans (by linarith)

/-- **Leftover hashing with side information.** If every possible conditional source is a
`(k, ε)`-source, hashing with an independent two-universal seed hides the hash value up to
`ε + √(|Output| · 2⁻ᵏ) / 2`, even when the side information and the seed are revealed. -/
theorem IsTwoUniversal.leftover_hash_conditional_of_isSource {Side : Type*} [Fintype Side]
    {seed : PMF Seed} {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (side : PMF Side) {source : Side → PMF Input} {k : ℝ} {ε : ℝ≥0}
    (hsource : ∀ info ∈ side.support, IsSource (source info) k ε) :
    dist (side.bind (fun info => (seededHash seed (source info) hash).map (info, ·)))
        (side.bind (fun info => (seed.bind
          (fun s => (PMF.uniformOfFintype Output).map (s, ·))).map (info, ·))) ≤
      ε + Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2 := by
  rw [dist_bind_pair]
  calc
    _ ≤ ∑ info, (side info).toReal * (ε + Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2) := by
      refine Finset.sum_le_sum fun info _ => ?_
      by_cases hinfo : info ∈ side.support
      · exact mul_le_mul_of_nonneg_left
          (hhash.leftover_hash_of_isSource (hsource info hinfo)) ENNReal.toReal_nonneg
      · rw [(side.apply_eq_zero_iff info).mpr hinfo, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = ε + Real.sqrt (Fintype.card Output * 2 ^ (-k)) / 2 := by
      rw [← Finset.sum_mul, sum_toReal, one_mul]

end Cslib.Probability
