/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
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
  distributions (`measurePreserving_swapSamples`). Averaging over all `2 ^ m` swaps gives
  `2 ^ m ρ J = ∫ #{σ | swapSamples σ z ∈ J} dρ(z)` (`lintegral_card_filter_swapSamples_mem`). So if
  at most `2 ^ m K` swaps of each double sample land in `J`, then `ρ J ≤ K`
  (`measure_prod_le_of_card_filter_swapSamples_mem_le`).

Applications bound the number of swaps that land in `J` combinatorially; see `EpsilonNet.lean`.
The domain `Z` is an arbitrary measurable space and the sample measures are σ-finite (s-finite for
the second sample of the ghost-sample bound). The swap-averaging and ghost-sample bounds assume the
event `J` is measurable; on a countable domain with measurable singletons every set is measurable
(`.of_discrete`).

## Main definitions

- `swapSamples σ z`: swap the coordinates `i` with `σ i = true` between the samples of `z`.

## Main results

- `measurePreserving_swapSamples`: swapping coordinates preserves `μ^m × μ^m`.
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

theorem swapSamples_involutive {m : ℕ} (σ : Fin m → Bool) :
    Function.Involutive (swapSamples (Z := Z) σ) :=
  swapSamples_swapSamples σ

variable [MeasurableSpace Z]

theorem measurable_swapSamples {m : ℕ} (σ : Fin m → Bool) :
    Measurable (swapSamples (Z := Z) σ) := by
  have h : ∀ (b : Bool) (i : Fin m), Measurable fun z : (Fin m → Z) × (Fin m → Z) =>
      if b then z.2 i else z.1 i := fun b i => by
    cases b
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd
  have h' : ∀ (b : Bool) (i : Fin m), Measurable fun z : (Fin m → Z) × (Fin m → Z) =>
      if b then z.1 i else z.2 i := fun b i => by
    cases b
    · exact (measurable_pi_apply i).comp measurable_snd
    · exact (measurable_pi_apply i).comp measurable_fst
  have hfun : swapSamples (Z := Z) σ = fun z =>
      (fun i => if σ i then z.2 i else z.1 i, fun i => if σ i then z.1 i else z.2 i) := by
    funext z
    ext i <;> simp only [fst_swapSamples_apply, snd_swapSamples_apply]
  rw [hfun]
  exact (measurable_pi_iff.2 fun i => h (σ i) i).prodMk (measurable_pi_iff.2 fun i => h' (σ i) i)

/-- **Swapping coordinates preserves the product of two i.i.d. sample distributions**, on any
measurable space and for any σ-finite `μ`. Under the identification of a double sample with a
sample of pairs, `swapSamples σ` swaps the pairs at the coordinates `i` with `σ i = true`, and each
such swap preserves `μ × μ`. -/
theorem measurePreserving_swapSamples (μ : Measure Z) [SigmaFinite μ] {m : ℕ}
    (σ : Fin m → Bool) :
    MeasurePreserving (swapSamples σ)
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ))
      ((Measure.pi fun _ : Fin m => μ).prod (Measure.pi fun _ : Fin m => μ)) := by
  have he := measurePreserving_arrowProdEquivProdArrow Z Z (Fin m) (fun _ => μ) (fun _ => μ)
  have hf : MeasurePreserving (fun (a : Fin m → Z × Z) i => if σ i then (a i).swap else a i)
      (Measure.pi fun _ => μ.prod μ) (Measure.pi fun _ => μ.prod μ) := by
    have := measurePreserving_pi (fun _ => μ.prod μ) (fun _ => μ.prod μ)
      (f := fun i => if σ i then Prod.swap else id) (fun i => by
        cases σ i
        · exact MeasurePreserving.id _
        · exact Measure.measurePreserving_swap)
    convert this using 2 with a
    funext i
    cases σ i <;> rfl
  convert (he.comp hf).comp he.symm using 1
  funext z
  ext i <;>
    simp only [fst_swapSamples_apply, snd_swapSamples_apply, Function.comp_apply,
      MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
      MeasurableEquiv.coe_mk, MeasurableEquiv.symm_mk, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk] <;>
    cases σ i <;> rfl

/-- Swapping coordinates preserves the probability of every set of double samples, measurable or
not, under the product of two i.i.d. sample distributions. -/
theorem measure_preimage_swapSamples (μ : Measure Z) [SigmaFinite μ] {m : ℕ} (σ : Fin m → Bool)
    (J : Set ((Fin m → Z) × (Fin m → Z))) :
    (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) (swapSamples σ ⁻¹' J) =
      (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J :=
  MeasurePreserving.measure_preimage_equiv
    (f := MeasurableEquiv.ofInvolutive _ (swapSamples_involutive σ) (measurable_swapSamples σ))
    (measurePreserving_swapSamples μ σ) J

open Classical in
/-- **Swap averaging**: summing over all `2 ^ m` swaps, the probability of a measurable set `J`
under `μ^m × μ^m`, times `2 ^ m`, is the expected number of swaps of a random double sample that
land in `J`. -/
theorem lintegral_card_filter_swapSamples_mem (μ : Measure Z) [SigmaFinite μ] {m : ℕ}
    {J : Set ((Fin m → Z) × (Fin m → Z))} (hJ : MeasurableSet J) :
    ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞)
        ∂(Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) =
      2 ^ m * (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J := by
  set ρ := (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ)
  have hmeas : ∀ σ : Fin m → Bool, MeasurableSet (swapSamples σ ⁻¹' J) := fun σ =>
    measurable_swapSamples σ hJ
  symm
  calc (2 : ℝ≥0∞) ^ m * ρ J = ∑ σ : Fin m → Bool, ρ (swapSamples σ ⁻¹' J) := by
        simp only [ρ, measure_preimage_swapSamples, Finset.sum_const, Finset.card_univ,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow,
          Nat.cast_ofNat]
    _ = ∑ σ : Fin m → Bool, ∫⁻ z, (swapSamples σ ⁻¹' J).indicator 1 z ∂ρ := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [lintegral_indicator_one (hmeas σ)]
    _ = ∫⁻ z, ∑ σ : Fin m → Bool, (swapSamples σ ⁻¹' J).indicator 1 z ∂ρ :=
        (lintegral_finsetSum _ fun σ _ => measurable_one.indicator (hmeas σ)).symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
        rw [Finset.sum_boole]

open Classical in
/-- **Swap counting**: if `J` is measurable and for every double sample `z` at most `2 ^ m K` of
the `2 ^ m` swaps of `z` land in `J`, then `J` has probability at most `K` under `μ^m × μ^m`. -/
theorem measure_prod_le_of_card_filter_swapSamples_mem_le (μ : Measure Z) [IsProbabilityMeasure μ]
    {m : ℕ} {J : Set ((Fin m → Z) × (Fin m → Z))} (hJ : MeasurableSet J) (K : ℝ≥0∞)
    (hK : ∀ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞) ≤
      2 ^ m * K) :
    (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) J ≤ K := by
  set ρ := (Measure.pi (fun _ : Fin m => μ)).prod (Measure.pi fun _ : Fin m => μ) with hρ
  have key : (2 : ℝ≥0∞) ^ m * ρ J ≤ 2 ^ m * K := by
    rw [hρ, ← lintegral_card_filter_swapSamples_mem μ hJ]
    calc ∫⁻ z, ((Finset.univ.filter fun σ : Fin m → Bool => swapSamples σ z ∈ J).card : ℝ≥0∞) ∂ρ
        ≤ ∫⁻ _z, 2 ^ m * K ∂ρ := lintegral_mono hK
      _ = 2 ^ m * K := by rw [lintegral_const, measure_univ, mul_one]
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1 key

end Swap

/-! ### The ghost sample -/

section Ghost

variable {Z : Type*} [MeasurableSpace Z]

/-- **Ghost-sample bound**: if `J` is measurable and every sample `S ∈ B` extends to a double
sample in `J` with probability at least `c` over an independent second sample from `ν'`, then
`c ν B ≤ (ν × ν') J`. -/
theorem mul_measure_le_measure_prod {m : ℕ} (ν ν' : Measure (Fin m → Z)) [SFinite ν']
    (B : Set (Fin m → Z)) {J : Set ((Fin m → Z) × (Fin m → Z))} (hJ : MeasurableSet J)
    (c : ℝ≥0∞) (hfib : ∀ S ∈ B, c ≤ ν' (Prod.mk S ⁻¹' J)) : c * ν B ≤ ν.prod ν' J := by
  rw [Measure.prod_apply hJ]
  calc c * ν B = ∫⁻ _S in B, c ∂ν := by rw [setLIntegral_const]
    _ ≤ ∫⁻ S in B, ν' (Prod.mk S ⁻¹' J) ∂ν :=
        setLIntegral_mono (measurable_measure_prodMk_left hJ) hfib
    _ ≤ ∫⁻ S, ν' (Prod.mk S ⁻¹' J) ∂ν := setLIntegral_le_lintegral _ _

/-- The ghost-sample bound at `c = 1 / 2`: `ν B ≤ 2 (ν × ν') J`. -/
theorem measure_le_two_mul_measure_prod {m : ℕ} (ν ν' : Measure (Fin m → Z)) [SFinite ν']
    (B : Set (Fin m → Z)) {J : Set ((Fin m → Z) × (Fin m → Z))} (hJ : MeasurableSet J)
    (hfib : ∀ S ∈ B, 1 / 2 ≤ ν' (Prod.mk S ⁻¹' J)) : ν B ≤ 2 * ν.prod ν' J := by
  calc ν B = 2 * (1 / 2 * ν B) := by
        rw [← mul_assoc, ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ 2 * ν.prod ν' J := by
        gcongr 2 * ?_
        exact mul_measure_le_measure_prod ν ν' B hJ _ hfib

end Ghost

end Cslib.MachineLearning.PACLearning
