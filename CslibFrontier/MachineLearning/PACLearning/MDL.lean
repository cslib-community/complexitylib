/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.SRM
public import Mathlib.InformationTheory.Coding.PrefixFree
import Mathlib.InformationTheory.Coding.Kraft

/-! # The minimum description length bound

A *prefix-free description* of a class `C` assigns each hypothesis `h ∈ C` a binary word `d h` so
that no description of a hypothesis of `C` is a prefix of the description of a different one
[ShalevShwartzBenDavid2014, Section 7.3]. By Kraft's inequality [Kraft1949]
[ShalevShwartzBenDavid2014, Lemma 7.6] the weights
`2^-|d h|` sum to at most `1`, so they form a weighting of `C`, and the SRM bound for the
singletons `{h}` with Hoeffding rates gives the *minimum description length (MDL) bound*
[ShalevShwartzBenDavid2014, Theorem 7.7]: with probability at least `1 - δ`, every `h ∈ C` has

`L_D(h) ≤ L_S(h) + √((|d h| log 2 + log (2 / δ)) / (2 m))`.

The source states the numerator as `|h| + ln (2 / δ)`; the form here is sharper because
`log 2 < 1`. Kraft's inequality for an arbitrary prefix-free set of words is Mathlib's
`InformationTheory.IsPrefixFree.tsum_one_div_card_pow_length_le_one`; this library's Huffman
development (`CslibFrontier.Algorithms.Lean.Huffman.Kraft`) adds the finite converse, which is not
needed here. A class with a prefix-free description is countable, and the hypotheses need
measurable misclassification sets; domain and labels are arbitrary measurable spaces.

## Main definitions

- `IsPrefixFreeDescription C d`: `d` is a prefix-free description of `C`.
- `IsPrefixFreeDescription.weighting`: the Kraft weighting `h ↦ 2^-|d h|` of `C`.

## Main results

- `IsPrefixFreeDescription.injOn`, `.isPrefixFree_image`, `.countable`: a prefix-free description
  is injective on `C`, its image is a prefix-free code, and `C` is countable.
- `IsPrefixFreeDescription.measure_pi_exists_le_abs_sub_le`: the two-sided MDL bound.
- `IsPrefixFreeDescription.mdl_bound`: the MDL bound (Theorem 7.7).

## References

* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- `d` is a *prefix-free description* of the class `C` [ShalevShwartzBenDavid2014,
Section 7.3]: whenever the description of `h ∈ C` is a prefix of the description of `h' ∈ C`,
the two hypotheses are equal. -/
@[expose] def IsPrefixFreeDescription (C : ConceptClass α β) (d : (α → β) → List Bool) : Prop :=
  ∀ h ∈ C, ∀ h' ∈ C, d h <+: d h' → h = h'

namespace IsPrefixFreeDescription

variable {C : ConceptClass α β} {d : (α → β) → List Bool}

/-- A prefix-free description is injective on the class. -/
theorem injOn (hd : IsPrefixFreeDescription C d) : InjOn d C :=
  fun h hh h' hh' heq => hd h hh h' hh' (heq ▸ List.prefix_refl _)

/-- The descriptions of a class form a prefix-free code. -/
theorem isPrefixFree_image (hd : IsPrefixFreeDescription C d) :
    InformationTheory.IsPrefixFree (d '' C) := by
  rintro _ ⟨h, hh, rfl⟩ _ ⟨h', hh', rfl⟩ hpre
  rw [hd h hh h' hh' hpre]

/-- A class with a prefix-free description is countable. -/
theorem countable (hd : IsPrefixFreeDescription C d) : C.Countable :=
  (mapsTo_image d C).countable_of_injOn hd.injOn (Set.to_countable _)

/-- The *Kraft weighting* `h ↦ 2^-|d h|` of a class with a prefix-free description: by Kraft's
inequality [Kraft1949] the weights sum to at most `1`. -/
noncomputable def weighting (hd : IsPrefixFreeDescription C d) : Weighting C where
  toFun h := (1 / 2 : ℝ) ^ (d h).length
  pos _ := by positivity
  summable := by
    have hs := hd.isPrefixFree_image.summable_one_div_card_pow_length (α := Bool)
    simp only [Fintype.card_bool, Nat.cast_ofNat] at hs
    exact hs.comp_injective (i := fun h : C => (⟨d h, h, h.2, rfl⟩ : d '' C))
      fun h h' heq => Subtype.ext (hd.injOn h.2 h'.2 (congrArg Subtype.val heq))
  tsum_le_one := by
    have hs := hd.isPrefixFree_image.summable_one_div_card_pow_length (α := Bool)
    have hle := hd.isPrefixFree_image.tsum_one_div_card_pow_length_le_one (α := Bool)
    simp only [Fintype.card_bool, Nat.cast_ofNat] at hs hle
    refine le_trans ?_ hle
    exact tsum_comp_le_tsum_of_inj hs (fun _ => by positivity)
      (i := fun h : C => (⟨d h, h, h.2, rfl⟩ : d '' C))
      fun h h' heq => Subtype.ext (hd.injOn h.2 h'.2 (congrArg Subtype.val heq))

@[simp] theorem weighting_apply (hd : IsPrefixFreeDescription C d) (h : C) :
    hd.weighting h = (1 / 2 : ℝ) ^ (d h).length := by
  unfold weighting
  rfl

/-- `log (2 / (2^-k δ)) = k log 2 + log (2 / δ)`. -/
private theorem log_two_div_mul (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Real.log (2 / ((1 / 2 : ℝ) ^ k * δ)) = k * Real.log 2 + Real.log (2 / δ) := by
  rw [show 2 / ((1 / 2 : ℝ) ^ k * δ) = 2 ^ k * (2 / δ) by rw [one_div, inv_pow]; field_simp,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]

variable [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- **The MDL bound**, two-sided form: for a class with a prefix-free description `d` whose
hypotheses have measurable misclassification sets, with probability at least `1 - δ` every
`h ∈ C` has `|L_S(h) - L_D(h)| ≤ √((|d h| log 2 + log (2 / δ)) / (2 m))`. -/
theorem measure_pi_exists_le_abs_sub_le (hd : IsPrefixFreeDescription C d)
    (hmeas : ∀ h ∈ C, MeasurableSet {p : α × β | h p.1 ≠ p.2})
    (D : Measure (α × β)) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ C, √(((d h).length * Real.log 2 + Real.log (2 / δ)) / (2 * m)) <
          |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} ≤ ENNReal.ofReal δ := by
  have : Countable C := hd.countable.to_subtype
  refine (measure_mono fun S => ?_).trans (hd.weighting.measure_pi_exists_not_isRepresentative_le
    (H := fun h : C => ({(h : α → β)} : ConceptClass α β))
    (fun h => hasUniformConvergenceRate_singleton (hmeas h h.2)) D (mem_univ D) hm hδ)
  rintro ⟨h, hh, hlt⟩
  refine ⟨⟨h, hh⟩, fun hrep => ?_⟩
  have := hrep h rfl
  rw [weighting_apply, log_two_div_mul _ hδ] at this
  exact (not_le.2 hlt) this

/-- **The MDL bound** [ShalevShwartzBenDavid2014, Theorem 7.7]: for a class with a prefix-free
description `d` whose hypotheses have measurable misclassification sets, with probability at least
`1 - δ` every `h ∈ C` has `L_D(h) ≤ L_S(h) + √((|d h| log 2 + log (2 / δ)) / (2 m))`. -/
theorem mdl_bound (hd : IsPrefixFreeDescription C d)
    (hmeas : ∀ h ∈ C, MeasurableSet {p : α × β | h p.1 ≠ p.2})
    (D : Measure (α × β)) [IsProbabilityMeasure D] {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ h ∈ C, (empiricalMiscount h S : ℝ) / m +
          √(((d h).length * Real.log 2 + Real.log (2 / δ)) / (2 * m)) < (error D h).toReal} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S => ?_).trans (hd.measure_pi_exists_le_abs_sub_le hmeas D hm hδ)
  rintro ⟨h, hh, hlt⟩
  refine ⟨h, hh, lt_of_lt_of_le ?_ (neg_le_abs _)⟩
  linarith

end IsPrefixFreeDescription

end Cslib.MachineLearning.PACLearning
