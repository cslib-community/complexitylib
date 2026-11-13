/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.UniformLearning.Basic
import CslibFrontier.MachineLearning.PACLearning.FiniteClass

/-!
# Learning by inverting the labelling map

Let `F : κ → (ι → Bool) → Bool` be a finite keyed family of Boolean functions. Its *labelling map*
sends a key `K` and `m` points `x` to the labelled sample `examples (F K) x`. A preimage of a sample
`S` under this map is a key `K'` whose function `F K'` agrees with every example of `S`. An inverter
for the labelling map is therefore a consistent learner for the family whenever it succeeds, and by
the union bound over the keys a consistent hypothesis has small error: this is the easy direction
of the equivalence between average-case learning and one-way functions
[BlumFurstKearnsLipton1993] [ImpagliazzoLevin1990].

`labelInversion F I K` draws `m` uniform examples of `F K` and runs the randomized inverter `I` on
them, returning the sample and the key `I` found. `labelInversion_lt_uniformError_le` bounds the
probability that the hypothesis `F K'` has uniform error above `ε` by the probability that `I`
fails to return a consistent key, plus `|κ| (1 - ε) ^ m`. The Occam form
`labelInversion_lt_uniformError_le_of_log_card_add_log_inv_le` replaces the second term by `δ` once
`log |κ| + log (1 / δ) ≤ ε m`, and `bind_labelInversion_lt_uniformError_le` averages over a prior on
the key. Everything here is information-theoretic: the inverter is any randomized map, and no
running time is counted.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.labelInversion`: an inverter run on uniform examples.

## Main results

* `Cslib.MachineLearning.UniformLearning.labelInversion_lt_uniformError_le`: the error of the
  inverted key is at most the inversion failure plus `|κ| (1 - ε) ^ m`.
* `labelInversion_lt_uniformError_le_of_log_card_add_log_inv_le`: the Occam sample-size form in
  `Cslib.MachineLearning.UniformLearning`.
* `Cslib.MachineLearning.UniformLearning.bind_labelInversion_lt_uniformError_le`: the same bound for
  a random key.

## References

* [A. Blum, M. Furst, M. Kearns, R. J. Lipton, *Cryptographic primitives based on hard learning
  problems*][BlumFurstKearnsLipton1993]
* [R. Impagliazzo, L. A. Levin, *No better ways to generate hard NP instances than picking
  uniformly at random*][ImpagliazzoLevin1990]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open PACLearning MeasureTheory Cslib.Probability
open scoped ENNReal

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

/-- Run the randomized inverter `I` on `m` uniform examples of `F K`, returning the sample and the
key that `I` outputs. -/
@[expose]
noncomputable def labelInversion (F : κ → (ι → Bool) → Bool)
    (I : LabeledSample (ι → Bool) Bool m → PMF κ) (K : κ) :
    PMF (LabeledSample (ι → Bool) Bool m × κ) :=
  (uniformExamples (F K) m).bind fun S => (I S).map fun K' => (S, K')

/-- The sample of `labelInversion F I K` consists of `m` uniform examples of `F K`. -/
theorem map_fst_labelInversion (F : κ → (ι → Bool) → Bool)
    (I : LabeledSample (ι → Bool) Bool m → PMF κ) (K : κ) :
    (labelInversion F I K).map Prod.fst = uniformExamples (F K) m := by
  have h (S : LabeledSample (ι → Bool) Bool m) : (I S).map (fun _ => S) = PMF.pure S :=
    PMF.map_const (I S) S
  simp only [labelInversion, PMF.map_bind, PMF.map_comp, Function.comp_def, h, PMF.bind_pure]

/-- **Learning by inversion.** The key `K'` returned by the inverter `I` on `m` uniform examples
of `F K` gives a hypothesis `F K'` with uniform error above `ε` with probability at most the
probability that `F K'` disagrees with some example, plus `|κ| (1 - ε) ^ m`. -/
theorem labelInversion_lt_uniformError_le [Fintype κ] (F : κ → (ι → Bool) → Bool)
    (I : LabeledSample (ι → Bool) Bool m → PMF κ) (K : κ) {ε : ℝ} (hε : 0 ≤ ε) :
    (labelInversion F I K).toOuterMeasure {p | ε < uniformError (F K) (F p.2)} ≤
      (labelInversion F I K).toOuterMeasure {p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} +
        Fintype.card κ * (1 - ENNReal.ofReal ε) ^ m := by
  classical
  set q := (PMF.uniformOfFintype (ι → Bool)).map fun x => (x, F K x)
  set G : Set (LabeledSample (ι → Bool) Bool m) :=
    {S | ∃ h ∈ Finset.univ.image F, ENNReal.ofReal ε < error q.toMeasure h ∧
      ∀ i, h (S i).1 = (S i).2}
  have hsub : {p : LabeledSample (ι → Bool) Bool m × κ | ε < uniformError (F K) (F p.2)} ⊆
      {p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} ∪ Prod.fst ⁻¹' G := by
    intro p hp
    by_cases hfail : ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2
    · exact Or.inl hfail
    refine Or.inr ⟨F p.2, Finset.mem_image_of_mem F (Finset.mem_univ _), ?_,
      fun i => not_not.1 fun h => hfail ⟨i, h⟩⟩
    rw [error_map_eq_ofReal_uniformError]
    exact (ENNReal.ofReal_lt_ofReal_iff (hε.trans_lt hp)).2 hp
  have hG : (labelInversion F I K).toOuterMeasure (Prod.fst ⁻¹' G) ≤
      Fintype.card κ * (1 - ENNReal.ofReal ε) ^ m := by
    rw [← PMF.toOuterMeasure_map_apply, map_fst_labelInversion,
    ← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ((Set.to_countable _).measurableSet),
      uniformExamples_eq_pi, PMF.toMeasure_pi]
    refine (measure_pi_exists_consistent_lt_error_le_card_mul_pow
      (fun _ _ => (Set.to_countable _).measurableSet) q.toMeasure _).trans ?_
    gcongr
    exact_mod_cast (Finset.card_image_le).trans_eq (Finset.card_univ)
  calc (labelInversion F I K).toOuterMeasure {p | ε < uniformError (F K) (F p.2)}
      ≤ (labelInversion F I K).toOuterMeasure
          ({p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} ∪ Prod.fst ⁻¹' G) :=
        (labelInversion F I K).toOuterMeasure.mono hsub
    _ ≤ (labelInversion F I K).toOuterMeasure {p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} +
          (labelInversion F I K).toOuterMeasure (Prod.fst ⁻¹' G) := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hG

/-- **Learning by inversion, Occam form.** With `log |κ| + log (1 / δ) ≤ ε m`, the hypothesis
returned through the inverter has uniform error above `ε` with probability at most the inversion
failure plus `δ`. -/
theorem labelInversion_lt_uniformError_le_of_log_card_add_log_inv_le [Fintype κ]
    (F : κ → (ι → Bool) → Bool) (I : LabeledSample (ι → Bool) Bool m → PMF κ) (K : κ) {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hm : Real.log (Fintype.card κ) + Real.log δ⁻¹ ≤ ε * m) :
    (labelInversion F I K).toOuterMeasure {p | ε < uniformError (F K) (F p.2)} ≤
      (labelInversion F I K).toOuterMeasure {p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} +
        ENNReal.ofReal δ :=
  (labelInversion_lt_uniformError_le F I K hε).trans
    (add_le_add le_rfl (natCast_mul_one_sub_ofReal_pow_le hε hδ hm))

/-- **Learning a random key by inversion.** For a key drawn from a prior `μ`, the hypothesis
returned through the inverter has uniform error above `ε` with probability at most the probability
that inversion fails, plus `|κ| (1 - ε) ^ m`. -/
theorem bind_labelInversion_lt_uniformError_le [Fintype κ] (F : κ → (ι → Bool) → Bool)
    (I : LabeledSample (ι → Bool) Bool m → PMF κ) (μ : PMF κ) {ε : ℝ} (hε : 0 ≤ ε) :
    (μ.bind fun K => (labelInversion F I K).map fun p => (K, p)).toOuterMeasure
        {(K, _, K') : κ × LabeledSample (ι → Bool) Bool m × κ | ε < uniformError (F K) (F K')} ≤
      (μ.bind fun K => (labelInversion F I K).map fun p => (K, p)).toOuterMeasure
          {(_, S, K') : κ × LabeledSample (ι → Bool) Bool m × κ | ∃ i, F K' (S i).1 ≠ (S i).2} +
        Fintype.card κ * (1 - ENNReal.ofReal ε) ^ m := by
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  calc _ ≤ ∑' K, μ K * ((labelInversion F I K).toOuterMeasure
          {p | ∃ i, F p.2 (p.1 i).1 ≠ (p.1 i).2} +
            Fintype.card κ * (1 - ENNReal.ofReal ε) ^ m) := by
        gcongr with K
        exact labelInversion_lt_uniformError_le F I K hε
    _ = _ := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        rfl

end Cslib.MachineLearning.UniformLearning
