/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCUniformConvergence

/-! # ε-approximations for classes of finite VC dimension on countable domains

A finite sequence `S` of points is an *ε-approximation* for a class `G` of Boolean functions under
a probability measure `μ` when, for every `g ∈ G`, the relative frequency of `{g = true}` in `S` is
within `ε` of `μ {g = true}`. Vapnik and Chervonenkis showed that a class of finite VC dimension
has ε-approximations of a size independent of `μ` [VapnikChervonenkis1971; MoranYehudayoff2016,
Theorem 2.1]. Here this follows from their uniform convergence theorem
(`VCUniformConvergence.lean`): `m` i.i.d. samples from `μ` fail to be an ε-approximation with
probability at most `δ` once `m ≥ uniformConvergenceSampleSize d ε δ`, so for `δ < 1` some sample
succeeds.

The size `uniformConvergenceSampleSize d ε δ = (16 / ε²) (2 d log (10 / ε) + log (4 / δ))` is
`O(d log (1 / ε) / ε²)`, weaker by the factor `log (1 / ε)` than the `O(d / ε²)` stated in
[MoranYehudayoff2016, Theorem 2.1], which credits that improvement to Li, Long and Srinivasan and
to Talagrand; their chaining arguments are not formalized here. The
domain is countable with measurable singletons, as in `VCUniformConvergence.lean`; distributions
given as probability mass functions on a countable type are covered through `PMF.toMeasure`.

## Main definitions

- `IsEpsApprox μ G ε S`: every `g ∈ G` has relative frequency in `S` within `ε` of
  `μ {g = true}`.

## Main results

- `measure_pi_not_isEpsApprox_le_of_uniformConvergenceSampleSize_le`: `m` i.i.d. samples fail to
  be an ε-approximation with probability at most `δ`.
- `exists_isEpsApprox_of_uniformConvergenceSampleSize_le`: **ε-approximations exist** for every
  probability measure, of a size depending only on `d`, `ε` and `δ < 1`.

## References

* [V. N. Vapnik, A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of events
  to their probabilities*][VapnikChervonenkis1971]
* [S. Moran, A. Yehudayoff, *Sample compression schemes for VC classes*][MoranYehudayoff2016]
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

variable {Z : Type*} [MeasurableSpace Z]

/-- The sequence `S` is an *ε-approximation* for the class `G` under the measure `μ`: for every
`g ∈ G`, the fraction of the points of `S` at which `g` is `true` differs from `μ {g = true}` by
less than `ε` [MoranYehudayoff2016, Theorem 2.1]. -/
@[expose] def IsEpsApprox (μ : Measure Z) (G : ConceptClass Z Bool) (ε : ℝ) {m : ℕ}
    (S : Fin m → Z) : Prop :=
  ∀ g ∈ G, |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
    (μ {z | g z = true}).toReal| < ε

variable [MeasurableSingletonClass Z] [Countable Z]

/-- On a countable domain, if every finite set shattered by `G` has at most `d` points, then `m`
i.i.d. samples from `μ` fail to be an ε-approximation for `G` with probability at most `δ` once
`m ≥ (16 / ε²) (2 d log (10 / ε) + log (4 / δ))`. -/
theorem measure_pi_not_isEpsApprox_le_of_uniformConvergenceSampleSize_le (μ : Measure Z)
    [IsProbabilityMeasure μ] {G : ConceptClass Z Bool} {d : ℕ}
    (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε10 : ε ≤ 10) (hδ : 0 < δ) (hm : uniformConvergenceSampleSize d ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsApprox μ G ε S} ≤ ENNReal.ofReal δ :=
  calc Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsApprox μ G ε S}
      ≤ Measure.pi (fun _ : Fin m => μ)
          {S | ∃ g ∈ G, ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
            (μ {z | g z = true}).toReal|} :=
        measure_mono fun S hS => by
          simpa only [IsEpsApprox, not_forall, not_lt, exists_prop] using hS
    _ ≤ ENNReal.ofReal (4 * growthFunction G (m + m) * Real.exp (-(m * ε ^ 2 / 8))) :=
        measure_pi_exists_le_abs_card_filter_div_sub_measure_le μ G m hε.le
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal
        (four_mul_growthFunction_mul_exp_le_of_uniformConvergenceSampleSize_le hG hε hε10 hδ hm)

/-- **ε-approximations for classes of finite VC dimension** on a countable domain
[VapnikChervonenkis1971; MoranYehudayoff2016, Theorem 2.1, with the weaker size
`O(d log (1 / ε) / ε²)`]: if every finite set shattered by `G` has at most `d` points, then every
probability measure `μ` has an ε-approximation for `G` with `m` points whenever
`m ≥ (16 / ε²) (2 d log (10 / ε) + log (4 / δ))` for some `δ < 1`. -/
theorem exists_isEpsApprox_of_uniformConvergenceSampleSize_le (μ : Measure Z)
    [IsProbabilityMeasure μ] {G : ConceptClass Z Bool} {d : ℕ}
    (hG : ∀ W : Finset Z, SetShatters G ↑W → W.card ≤ d) {m : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε10 : ε ≤ 10) (hδ : 0 < δ) (hδ1 : δ < 1) (hm : uniformConvergenceSampleSize d ε δ ≤ m) :
    ∃ S : Fin m → Z, IsEpsApprox μ G ε S := by
  by_contra h
  simp only [not_exists] at h
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal δ :=
    calc (1 : ℝ≥0∞) = Measure.pi (fun _ : Fin m => μ) Set.univ := measure_univ.symm
      _ ≤ Measure.pi (fun _ : Fin m => μ) {S | ¬ IsEpsApprox μ G ε S} :=
        measure_mono fun S _ => h S
      _ ≤ ENNReal.ofReal δ :=
        measure_pi_not_isEpsApprox_le_of_uniformConvergenceSampleSize_le μ hG hε hε10 hδ hm
  exact absurd hle (not_le.2 (ENNReal.ofReal_lt_one.2 hδ1))

end Cslib.MachineLearning.PACLearning
