/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Double samples and coordinate swaps

The double-sample (ghost-sample) argument bounds the probability of an event about one i.i.d.
sample `S` by the probability of an event `J` about a pair `(S, T)` of independent samples
[ShalevShwartzBenDavid2014, Section 28.3]. It has two measure-theoretic steps, collected here.

* **Ghost sample.** If every `S` in a set `B` extends to a pair in `J` with conditional probability
  at least `c`, then `c ν B ≤ (ν × ν') J` (`mul_measure_le_measure_prod`). The usual case is
  `c = 1 / 2` (`measure_le_two_mul_measure_prod`).
* **Swaps.** For `σ : Fin m → Bool`, `swapSamples σ` exchanges the coordinates `i` with
  `σ i = true` between the two samples. It preserves the product of two i.i.d. sample
  distributions (`map_swapSamples`). Averaging over all `2 ^ m` swaps gives
  `2 ^ m ρ J = ∫ #{σ | swapSamples σ z ∈ J} dρ(z)` (`lintegral_card_filter_swapSamples_mem`). So if
  at most `2 ^ m K` swaps of each double sample land in `J`, then `ρ J ≤ K`
  (`measure_prod_le_of_card_filter_swapSamples_mem_le`).

Applications bound the number of swaps that land in `J` combinatorially; see `EpsilonNet.lean`.
The steps involving measurability of arbitrary sets assume a countable domain with measurable
singletons.

## Main definitions

- `swapSamples σ z`: swap the coordinates `i` with `σ i = true` between the samples of `z`.

## Main results

- `map_swapSamples`: swapping coordinates preserves `μ^m × μ^m`.
- `lintegral_card_filter_swapSamples_mem`: the swap-averaging identity.
- `measure_prod_le_of_card_filter_swapSamples_mem_le`: the swap-counting bound.
- `mul_measure_le_measure_prod`, `measure_le_two_mul_measure_prod`: the ghost-sample bound.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

/-! ### Swapping coordinates -/

section Swap

variable {Z : Type*}

/-- Swap the coordinates `i` with `σ i = true` between the two samples of a double sample. -/
def swapSamples {m : ℕ} (σ : Fin m → Bool) (z : (Fin m → Z) × (Fin m → Z)) :
    (Fin m → Z) × (Fin m → Z) :=
  (fun i => if σ i then z.2 i else z.1 i, fun i => if σ i then z.1 i else z.2 i)

@[simp]
theorem fst_swapSamples_apply {m : ℕ} (σ : Fin m → Bool) (z : (Fin m → Z) × (Fin m → Z))
    (i : Fin m) : (swapSamples σ z).1 i = if σ i then z.2 i else z.1 i := by
  simp only [swapSamples]

@[simp]
theorem snd_swapSamples_apply {m : ℕ} (σ : Fin m → Bool) (z : (Fin m → Z) × (Fin m → Z))
    (i : Fin m) : (swapSamples σ z).2 i = if σ i then z.1 i else z.2 i := by
  simp only [swapSamples]

@[simp]
theorem swapSamples_swapSamples {m : ℕ} (σ : Fin m → Bool) (z : (Fin m → Z) × (Fin m → Z)) :
    swapSamples σ (swapSamples σ z) = z := by
  ext i <;> simp only [fst_swapSamples_apply, snd_swapSamples_apply] <;> cases σ i <;> rfl

variable [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]

/-- Swapping coordinates preserves the product of two i.i.d. sample distributions. -/
theorem map_swapSamples (μ : Measure Z) [SigmaFinite μ] {m : ℕ} (σ : Fin m → Bool) :
    ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)).map
      (swapSamples σ) = (Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ) := by
  refine Measure.ext_of_singleton fun p => ?_
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : swapSamples σ ⁻¹' {p} = {swapSamples σ p} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      rw [swapSamples_swapSamples]
    · rintro rfl
      rw [swapSamples_swapSamples]
  rw [hpre, ← Prod.mk.eta (p := swapSamples σ p), ← Set.singleton_prod_singleton,
    Measure.prod_prod, ← Prod.mk.eta (p := p), ← Set.singleton_prod_singleton,
    Measure.prod_prod, Measure.pi_singleton, Measure.pi_singleton, Measure.pi_singleton,
    Measure.pi_singleton, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fst_swapSamples_apply, snd_swapSamples_apply]
  cases σ i
  · rfl
  · exact mul_comm _ _

theorem measure_preimage_swapSamples (μ : Measure Z) [SigmaFinite μ] {m : ℕ} (σ : Fin m → Bool)
    (J : Set ((Fin m → Z) × (Fin m → Z))) :
    (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) (swapSamples σ ⁻¹' J) =
      (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J := by
  rw [← Measure.map_apply (measurable_of_countable _) .of_discrete, map_swapSamples]

open Classical in
/-- **Swap averaging**: summing over all `2 ^ m` swaps, the probability of `J` under `μ^m × μ^m`,
times `2 ^ m`, is the expected number of swaps of a random double sample that land in `J`. -/
theorem lintegral_card_filter_swapSamples_mem (μ : Measure Z) [SigmaFinite μ] {m : ℕ}
    (J : Set ((Fin m → Z) × (Fin m → Z))) :
    ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞)
        ∂(Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) =
      2 ^ m * (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J := by
  set ρ := (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ)
  symm
  calc (2 : ℝ≥0∞) ^ m * ρ J = ∑ σ : Fin m → Bool, ρ (swapSamples σ ⁻¹' J) := by
        simp only [ρ, measure_preimage_swapSamples, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]
    _ = ∑ σ : Fin m → Bool, ∫⁻ z, (swapSamples σ ⁻¹' J).indicator 1 z ∂ρ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [lintegral_indicator_one .of_discrete]
    _ = ∫⁻ z, ∑ σ : Fin m → Bool, (swapSamples σ ⁻¹' J).indicator 1 z ∂ρ :=
        (lintegral_finsetSum _ fun σ _ => measurable_of_countable _).symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        rw [Finset.sum_boole]

open Classical in
/-- **Swap counting**: if for every double sample `z` at most `2 ^ m K` of the `2 ^ m` swaps of `z`
land in `J`, then `J` has probability at most `K` under `μ^m × μ^m`. -/
theorem measure_prod_le_of_card_filter_swapSamples_mem_le (μ : Measure Z) [IsProbabilityMeasure μ]
    {m : ℕ} (J : Set ((Fin m → Z) × (Fin m → Z))) (K : ℝ≥0∞)
    (hK : ∀ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞) ≤
      2 ^ m * K) :
    (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J ≤ K := by
  set ρ := (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) with hρ
  have key : (2 : ℝ≥0∞) ^ m * ρ J ≤ 2 ^ m * K := by
    rw [hρ, ← lintegral_card_filter_swapSamples_mem]
    calc ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞) ∂ρ
        ≤ ∫⁻ _z, 2 ^ m * K ∂ρ := lintegral_mono hK
      _ = 2 ^ m * K := by rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1 key

end Swap

/-! ### The ghost sample -/

section Ghost

variable {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z] [Countable Z]

/-- **Ghost-sample bound**: if every sample `S ∈ B` extends to a double sample in `J` with
probability at least `c` over an independent second sample from `ν'`, then `c ν B ≤ (ν × ν') J`. -/
theorem mul_measure_le_measure_prod {m : ℕ} (ν ν' : Measure (Fin m → Z)) [SFinite ν']
    (B : Set (Fin m → Z)) (J : Set ((Fin m → Z) × (Fin m → Z))) (c : ℝ≥0∞)
    (hfib : ∀ S ∈ B, c ≤ ν' (Prod.mk S ⁻¹' J)) : c * ν B ≤ ν.prod ν' J := by
  rw [Measure.prod_apply .of_discrete]
  calc c * ν B = ∫⁻ _S in B, c ∂ν := by rw [setLIntegral_const]
    _ ≤ ∫⁻ S in B, ν' (Prod.mk S ⁻¹' J) ∂ν :=
        setLIntegral_mono (measurable_of_countable _) hfib
    _ ≤ ∫⁻ S, ν' (Prod.mk S ⁻¹' J) ∂ν := setLIntegral_le_lintegral _ _

/-- The ghost-sample bound at `c = 1 / 2`: `ν B ≤ 2 (ν × ν') J`. -/
theorem measure_le_two_mul_measure_prod {m : ℕ} (ν ν' : Measure (Fin m → Z)) [SFinite ν']
    (B : Set (Fin m → Z)) (J : Set ((Fin m → Z) × (Fin m → Z)))
    (hfib : ∀ S ∈ B, 1 / 2 ≤ ν' (Prod.mk S ⁻¹' J)) : ν B ≤ 2 * ν.prod ν' J := by
  calc ν B = 2 * (1 / 2 * ν B) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * ν.prod ν' J := by
        gcongr 2 * ?_
        exact mul_measure_le_measure_prod ν ν' B J _ hfib

end Ghost

end Cslib.MachineLearning.PACLearning
