/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Integral/IntervalIntegral/`)

public import Complexity.Init
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating a primitive against a measure

This file proves two facts about the primitive `v ↦ ∫ z in 0..v, g z`.

* **Measurability in a parameter.** If `G` is jointly measurable and `c`, `d` are measurable, then
  `a ↦ ∫ z in c a..d a, G a z` is measurable.
* **Tail formula.** For a finite measure `μ` concentrated on `[0, h]`,
  `∫ v, (∫ z in 0..v, g z) ∂μ = ∫ z in (0, h], μ([z, ∞)) · g z`.
  The proof swaps the order of integration over the triangle `0 < z ≤ v`. With `g = 1` this is the
  layer-cake formula `E[v] = ∫ P(v ≥ z) dz` on `[0, h]`.

## Main results

* `MeasureTheory.measurable_intervalIntegral`: measurability of parametric interval integrals.
* `MeasureTheory.integral_intervalIntegral_eq_integral_measureReal_Ici_mul`: the tail formula.
-/

open Set

public section

namespace MeasureTheory

/-- A parametric interval integral `a ↦ ∫ z in c a..d a, G a z` is measurable when `G` is jointly
measurable and the endpoints are measurable. -/
theorem measurable_intervalIntegral {α : Type*} [MeasurableSpace α] {G : α → ℝ → ℝ}
    (hG : Measurable (Function.uncurry G)) {c d : α → ℝ} (hc : Measurable c)
    (hd : Measurable d) :
    Measurable fun a => ∫ z in c a..d a, G a z := by
  have key : ∀ {c d : α → ℝ}, Measurable c → Measurable d →
      Measurable fun a => ∫ z in Ioc (c a) (d a), G a z := by
    intro c d hc hd
    set S : Set (α × ℝ) := {p | c p.1 < p.2 ∧ p.2 ≤ d p.1}
    have hS : MeasurableSet S :=
      (measurableSet_lt (hc.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hd.comp measurable_fst))
    have hm : StronglyMeasurable
        (Function.uncurry fun a z => S.indicator (Function.uncurry G) (a, z)) :=
      (hG.indicator hS).stronglyMeasurable
    convert (hm.integral_prod_right (ν := volume)).measurable using 1
    funext a
    rw [← integral_indicator measurableSet_Ioc]
    rfl
  convert (key hc hd).sub (key hd hc) using 1
  funext a
  rfl

/-- **Tail formula for a primitive.** If the finite measure `μ` is concentrated on `[0, h]` and `g`
is measurable and integrable on `(0, h]`, then
`∫ v, (∫ z in 0..v, g z) ∂μ = ∫ z in (0, h], μ([z, ∞)) · g z`. The proof swaps the order of
integration over the triangle `0 < z ≤ v`. -/
theorem integral_intervalIntegral_eq_integral_measureReal_Ici_mul {μ : Measure ℝ}
    [IsFiniteMeasure μ] {h : ℝ} (hμ : ∀ᵐ v ∂μ, v ∈ Icc 0 h) {g : ℝ → ℝ} (hgm : Measurable g)
    (hg : IntegrableOn g (Ioc 0 h)) :
    ∫ v, (∫ z in (0 : ℝ)..v, g z) ∂μ = ∫ z in Ioc 0 h, μ.real (Ici z) * g z := by
  set S : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ p.1}
  have hSm : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  set G : ℝ × ℝ → ℝ := S.indicator (fun p => g p.2) with hG
  have hGint : Integrable G (μ.prod volume) := by
    refine Integrable.mono' (g := fun p => (Ioc 0 h).indicator (fun z => ‖g z‖) p.2) ?_ ?_ ?_
    · exact (IntegrableOn.integrable_indicator (Integrable.norm hg) measurableSet_Ioc).comp_snd μ
    · exact ((hgm.comp measurable_snd).indicator hSm).aestronglyMeasurable
    · have : ∀ᵐ p ∂(μ.prod (volume : Measure ℝ)), p.1 ∈ Icc 0 h :=
        (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := (volume : Measure ℝ))).ae hμ
      filter_upwards [this] with p hp
      by_cases hpS : p ∈ S
      · have hz : p.2 ∈ Ioc 0 h := ⟨hpS.1, hpS.2.trans hp.2⟩
        rw [hG, indicator_of_mem hpS, indicator_of_mem hz]
      · rw [hG, indicator_of_notMem hpS, norm_zero]
        exact indicator_nonneg (fun _ _ => norm_nonneg _) _
  have hL : ∀ᵐ v ∂μ, ∫ z, G (v, z) = ∫ z in (0 : ℝ)..v, g z := by
    filter_upwards [hμ] with v hv
    rw [intervalIntegral.integral_of_le hv.1, ← integral_indicator measurableSet_Ioc]
    rfl
  have hR : ∀ z, ∫ v, G (v, z) ∂μ = (Ioi 0).indicator (fun z => μ.real (Ici z) * g z) z := by
    intro z
    by_cases hz : 0 < z
    · rw [indicator_of_mem (show z ∈ Ioi 0 from hz)]
      have : (fun v => G (v, z)) = (Ici z).indicator (fun _ => g z) := by
        ext v
        by_cases hv : z ≤ v
        · rw [hG, indicator_of_mem (show (v, z) ∈ S from ⟨hz, hv⟩),
            indicator_of_mem (show v ∈ Ici z from hv)]
        · rw [hG, indicator_of_notMem (show (v, z) ∉ S from fun h => hv h.2),
            indicator_of_notMem (show v ∉ Ici z from hv)]
      rw [this, integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul]
    · rw [indicator_of_notMem (show z ∉ Ioi 0 from hz)]
      have : (fun v => G (v, z)) = fun _ => 0 := by
        ext v
        rw [hG, indicator_of_notMem (show (v, z) ∉ S from fun h => hz h.1)]
      rw [this, integral_zero]
  rw [← integral_congr_ae hL,
    integral_integral_swap (μ := μ) (ν := volume) (f := fun v z => G (v, z)) hGint]
  simp_rw [hR]
  rw [integral_indicator measurableSet_Ioi]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun z hz => ?_
  have hzh : h < z := lt_of_not_ge fun h' => hz.2 ⟨hz.1, h'⟩
  have h0 : μ (Ici z) = 0 :=
    measure_mono_null (t := {v | v ∉ Icc 0 h})
      (fun v (hv : z ≤ v) (hv' : v ∈ Icc 0 h) => absurd (hv'.2.trans_lt hzh) (not_lt.2 hv))
      (ae_iff.1 hμ)
  rw [measureReal_def, h0, ENNReal.toReal_zero, zero_mul]

end MeasureTheory
