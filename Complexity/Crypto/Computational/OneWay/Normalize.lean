/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Padding
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Probability.PMF
import Complexity.Tactic.PPT

/-!
# Normalizing the output length of a one-way function

Self-delimiting padding using an output-size bound makes the output length depend only on the
input length. Equality of padded images implies equality of the original images, even for a
candidate of a different length. A uniform strict PPT reduction therefore preserves one-wayness.
This supplies the fixed-output-width interface used by the pseudoentropy construction without
assuming that the original function is length-preserving, injective or regular.

## Main definitions

* `Cslib.Crypto.OneWayNormalization.normalize`: pad each image using an input-length bound.

## Main results

* `Cslib.Crypto.OneWay.normalize`: output normalization preserves one-wayness.
* `Cslib.Crypto.OneWay.exists_fixedOutputLength`: every OWF yields an OWF with
  a uniformly polynomial-time output-length function.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Definition 1 and Section 4.

Adapted from Crypto/Computational/OneWay/Normalize.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`. This is the word-encoding reduction to the write-up's
fixed-output-width setting, using the shared tidy machine calculus and nonnegative game API.
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
theorem computableTidilyInPolyTime_normalize {f : List Bool → List Bool}
    (hf : ComputableTidilyInPolyTime f encBits encBits) {bound : ℕ → ℕ}
    (hbound : ComputableTidilyInPolyTime bound encUnary encUnary) :
    ComputableTidilyInPolyTime (normalize f bound) encBits encBits := by
  unfold normalize
  fun_prop

/-- Any inverter for the normalized function gives an inverter for the original function.
Only its challenge is padded; the candidate is returned unchanged, at any length. -/
theorem inversion_le (f : List Bool → List Bool) (bound : ℕ → ℕ) (adversary : Inverter) (n : ℕ) :
    Game.succProbability (ProbComp.eval (inversionGame (normalize f bound) adversary n)) ≤
      Game.succProbability (ProbComp.eval (inversionGame f
        (fun n image => adversary n (BitString.padWord (bound n) image)) n)) := by
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [inversionGame, ProbComp.eval_bind, BitString.eval_sampleList]
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

/-- Self-delimiting output padding preserves one-wayness against uniform strict PPT inverters. -/
theorem OneWay.normalize {f : List Bool → List Bool} (hf : OneWay f) (bound : ℕ → ℕ)
    (hbound : ComputableTidilyInPolyTime bound encUnary encUnary) :
    OneWay (OneWayNormalization.normalize f bound) := by
  apply OneWay.of_inversion_negligible
    (.of_tidy <|
      OneWayNormalization.computableTidilyInPolyTime_normalize hf.polyTime.tidy hbound)
  intro adversary hPPT
  have hreduce : IsPPT encBits (fun n image =>
      adversary n (BitString.padWord (bound n) image)) := by ppt
  exact negligible_of_le (hf.inversion_negligible _ hreduce)
    (OneWayNormalization.inversion_le f bound adversary)

/-- Every OWF yields an OWF whose output length depends only on the input length.
Both evaluation and this unary output-length function are uniformly polynomial time. -/
theorem OneWay.exists_fixedOutputLength {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ (g : List Bool → List Bool) (length : ℕ → ℕ), OneWay g ∧
      (∀ input, (g input).length = length input.length) ∧
      ComputableTidilyInPolyTime length encUnary encUnary := by
  obtain ⟨c, d, hsize⟩ := hf.polyTime.polyBounded_length.exists_le
  let bound (n : ℕ) := c * (n + 1) ^ d
  have hbound : ComputableTidilyInPolyTime bound encUnary encUnary := by
    unfold bound
    fun_prop
  refine ⟨OneWayNormalization.normalize f bound, fun n => 2 * bound n + 1,
    hf.normalize bound hbound, ?_, by fun_prop⟩
  intro input
  exact BitString.length_padWord (hsize input)

end Cslib.Crypto
