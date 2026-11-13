/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Padding
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT

/-!
# Normalizing the output length of a one-way function

Self-delimiting padding using an output-size bound makes the output length depend only on the
input length. Equality of padded images implies equality of the original images, even for a
candidate of a different length. A uniform strict PPT reduction, which passes any advice through
unchanged, therefore preserves one-wayness, uniform or nonuniform.
This supplies the fixed-output-width interface used by the pseudoentropy construction without
assuming that the original function is length-preserving, injective or regular.

## Main definitions

* `Cslib.Crypto.OneWayNormalization.normalize`: pad each image using an input-length bound.

## Main results

* `Cslib.Crypto.InversionHardWithAdvice.normalize`: output normalization preserves hardness of
  inversion with any fixed advice family.
* `Cslib.Crypto.OneWay.normalize`, `Cslib.Crypto.NonuniformOneWay.normalize`: output
  normalization preserves uniform and nonuniform one-wayness.
* `Cslib.Crypto.OneWay.exists_fixedOutputLength`,
  `Cslib.Crypto.NonuniformOneWay.exists_fixedOutputLength`: every (nonuniform) OWF yields one
  with a uniformly polynomial-time output-length function.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definition 1 and Section 4.

Adapted from Crypto/Computational/OneWay/Normalize.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. This is the word-encoding reduction to the write-up's
fixed-output-width setting, using plain polynomial-time certificates and the nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace OneWayNormalization

/-- Normalize a word function using a bound supplied in unary. -/
def normalize (f : List Bool → List Bool) (bound : ℕ → ℕ) (input : List Bool) : List Bool :=
  BitString.padWord (bound input.length) (f input)

/-- Output normalization preserves deterministic polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_normalize {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) {bound : ℕ → ℕ}
    (hbound : ComputableInPolyTime bound encUnary encUnary) :
    ComputableInPolyTime (normalize f bound) encBits encBits := by
  unfold normalize
  fun_prop

/-- Any inverter for the normalized function gives an inverter for the original function.
Only its challenge is padded; the candidate is returned unchanged, at any length. -/
theorem inversion_le (f : List Bool → List Bool) (bound : ℕ → ℕ) (adversary : Inverter) (n : ℕ) :
    Game.succProbability (ProbComp.eval (inversionGame (normalize f bound) adversary n)) ≤
      Game.succProbability (ProbComp.eval (inversionGame f
        (fun n image => adversary n (BitString.padWord (bound n) image)) n)) := by
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [inversionGame, inversionExperiment, ProbComp.eval_bind, BitString.eval_sampleList]
  apply PMF.bind_apply_mono_on_support _ true
  intro input hinput
  have hlen : input.length = n := BitString.length_of_mem_support_uniformList hinput
  simp only [normalize, hlen]
  apply PMF.bind_apply_mono_on_support _ true
  intro candidate _
  simp only [ProbComp.eval_pure, PMF.pure_apply]
  by_cases h : BitString.padWord (bound candidate.length) (f candidate) =
      BitString.padWord (bound n) (f input)
  · simp_all [BitString.word_eq_of_padWord_eq h]
  · simp [h]

end OneWayNormalization

/-- **Normalization relative to fixed advice.** Self-delimiting output padding preserves hardness
of inversion with any fixed advice family: the reduction pads its challenge and passes the advice
through. Uniform one-wayness (`OneWay.normalize`) is the empty-advice case. -/
theorem InversionHardWithAdvice.normalize {f : List Bool → List Bool} {advice : ℕ → List Bool}
    (h : InversionHardWithAdvice f advice) (bound : ℕ → ℕ)
    (hbound : ComputableInPolyTime bound encUnary encUnary) :
    InversionHardWithAdvice (OneWayNormalization.normalize f bound) advice := by
  refine .of_inversion_negligible fun adversary hPPT => ?_
  have hprepare : ComputableInPolyTime
      (fun ((n, word), image) => ((n, word), BitString.padWord (bound n) image))
      (encPair (encPair encUnary encBits) encBits)
      (encPair (encPair encUnary encBits) encBits) := by fun_prop
  exact negligible_of_le (h.inversion_negligible _ (hPPT.preprocess hprepare))
    (OneWayNormalization.inversion_le f bound (fun n image => adversary ((n, advice n), image)))

/-- Self-delimiting output padding preserves one-wayness against uniform strict PPT inverters. -/
theorem OneWay.normalize {f : List Bool → List Bool} (hf : OneWay f) (bound : ℕ → ℕ)
    (hbound : ComputableInPolyTime bound encUnary encUnary) :
    OneWay (OneWayNormalization.normalize f bound) := by
  obtain ⟨hpoly, hhard⟩ := oneWay_iff_inversionHardWithAdvice_nil.mp hf
  exact oneWay_iff_inversionHardWithAdvice_nil.mpr
    ⟨OneWayNormalization.computableInPolyTime_normalize hpoly hbound, hhard.normalize bound hbound⟩

/-- Self-delimiting output padding preserves nonuniform one-wayness. -/
theorem NonuniformOneWay.normalize {f : List Bool → List Bool} (hf : NonuniformOneWay f)
    (bound : ℕ → ℕ) (hbound : ComputableInPolyTime bound encUnary encUnary) :
    NonuniformOneWay (OneWayNormalization.normalize f bound) :=
  ⟨OneWayNormalization.computableInPolyTime_normalize hf.polyTime hbound,
    fun advice hadvice => (hf.secure advice hadvice).normalize bound hbound⟩

/-- The output-size bound used to normalize an efficient function: a polynomial dominating its
output length. -/
private theorem exists_normalizationBound {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) :
    ∃ bound : ℕ → ℕ, ComputableInPolyTime bound encUnary encUnary ∧
      ∀ input, (f input).length ≤ bound input.length := by
  obtain ⟨c, d, hsize⟩ := hf.polyBounded_length.exists_le
  exact ⟨fun n => c * (n + 1) ^ d, by fun_prop, hsize⟩

/-- Every OWF yields an OWF whose output length depends only on the input length.
Both evaluation and this unary output-length function are uniformly polynomial time. -/
theorem OneWay.exists_fixedOutputLength {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), OneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      ComputableInPolyTime length encUnary encUnary := by
  obtain ⟨bound, hbound, hsize⟩ := exists_normalizationBound hf.polyTime
  exact ⟨OneWayNormalization.normalize f bound, fun n => 2 * bound n + 1,
    hf.normalize bound hbound, fun input => BitString.length_padWord (hsize input), by fun_prop⟩

/-- Every nonuniform OWF yields a nonuniform OWF whose output length depends only on the input
length, with a uniformly polynomial-time output-length function. -/
theorem NonuniformOneWay.exists_fixedOutputLength {f : List Bool → List Bool}
    (hf : NonuniformOneWay f) :
    ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), NonuniformOneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      ComputableInPolyTime length encUnary encUnary := by
  obtain ⟨bound, hbound, hsize⟩ := exists_normalizationBound hf.polyTime
  exact ⟨OneWayNormalization.normalize f bound, fun n => 2 * bound n + 1,
    hf.normalize bound hbound, fun input => BitString.length_padWord (hsize input), by fun_prop⟩

end Cslib.Crypto
