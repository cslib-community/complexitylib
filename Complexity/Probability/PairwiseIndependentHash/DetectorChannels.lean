/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ColumnDetector
public import Complexity.Probability.PairwiseIndependentHash.RetentionChannel

/-!
# Affine retention channels satisfy the detector interface

The affine retention channels over `𝔽_P` (`Cslib.Probability.affineRetains`) satisfy the channel
interface `Cslib.Probability.RetentionChannels` of the column detectors, with the constants
`c_π = 1`, `C_π = C_pair = 2 ^ H` and `C_var = 4`. Vertices are identified with field elements
through an injective identifier map `ident : V → ZMod P`, and both channels use the affine seed
space; their independence comes from the product of the two seed spaces. So the detector lemma
(`Matrix.le_columnDetector`, `Matrix.lt_card_of_lt_columnDetector`) and the detected stage
(`Matrix.detectedStage_rates`) hold for these channels at rate `f = a ^ H`, where
`1 ≤ P a` and `a ≤ 1` [OpenAI2026LogSpace, (4.8), (4.9)].

## Main results

* `Cslib.Probability.retentionChannels_affineRetains`: the affine channels at rate `a ^ H`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.2 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Cslib.Probability

variable {V : Type*} {P H : ℕ} [Fact P.Prime]

/-- **Affine retention channels satisfy the detector interface.** Let `ident : V → ZMod P` be
injective, `1 ≤ P a` and `a ≤ 1`, and `L = ⌈P a⌉`. Retaining `v` when the affine seed retains
`ident v`, for each of two channels, gives retention channels at rate `f = a ^ H` with retention
probability `π = (L / P) ^ H` and constants `c_π = 1`, `C_π = C_pair = 2 ^ H`, `C_var = 4`. -/
theorem retentionChannels_affineRetains {ident : V → ZMod P} (hident : Function.Injective ident)
    {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) :
    RetentionChannels (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
      (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v)) (a ^ H)
      ((((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H) 1 (2 ^ H) (2 ^ H) 4 := by
  obtain ⟨hL, hlow, hup, hpair, htail⟩ := affineRetains_rates (H := H) hPa ha
  have hdens : ∀ v, (dens {s | affineRetains P H ⌈P * a⌉₊ s (ident v)} : ℝ) =
      (((⌈P * a⌉₊ : ℕ) : ℝ) / P) ^ H := fun v => by
    rw [dens_affineRetains hL]; push_cast; rfl
  refine ⟨hdens, hdens, by rw [one_mul]; exact hlow, hup, fun w y hwy => ?_, fun A hA => ?_⟩
  · exact hpair _ _ (hident.ne hwy)
  · have hcard : #(A.image ident) = #A := card_image_of_injective A hident
    have hfilter : ∀ s, #{x ∈ A | affineRetains P H ⌈P * a⌉₊ s (ident x)} =
        #{y ∈ A.image ident | affineRetains P H ⌈P * a⌉₊ s y} := fun s => by
      rw [filter_image, card_image_of_injective _ hident]
    have := htail (A.image ident) (hA.image ident)
    simp only [hcard, ← hfilter] at this
    exact this

end Cslib.Probability
