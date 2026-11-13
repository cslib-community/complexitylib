/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Nonuniform.Basic
public import CslibFrontier.Crypto.Computational.Pseudoentropy.Basic
public import CslibFrontier.Crypto.Computational.PseudorandomGenerator
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Crypto.Computational.GeneratorReindex
import CslibFrontier.Crypto.Computational.Pseudoentropy.ThreeSource.Combined

/-!
# Pseudorandom generators from pseudoentropy pairs

Realize the pair with a deterministic sampler and saved coins, enumerate the entropy grid,
pad and amplify every candidate, then XOR their outputs. Finally extend the resulting family
to every seed length. The density schedule must resolve the pair's gap; no entropy estimate
or chosen successful candidate is supplied to the generator.

## Main results

* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.exists_pseudorandomGenerator`: a samplable
  pseudoentropy pair with an efficiently resolved gap gives a uniform one-bit expanding PRG.
* `Cslib.Crypto.Pseudoentropy.SamplablePair.exists_nonuniformPRG`: a samplable pseudoentropy pair
  whose gap holds against every polynomially bounded advice family gives a nonuniform one-bit
  expanding PRG.

## References

This formalizes [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006],
Section 5 and the final proof of Theorem 1. The matrix extractor used here gives polynomial seed
length without claiming the paper's optimized seed-length exponent.

Adapted from Crypto/Computational/Pseudoentropy/Generator.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter Turing.MultiTapeTM

/-- The extended entropy-grid generator of a samplable pair: it is efficient, stretches every seed
length by one bit, and its fixed-length family is secure relative to every advice family for which
the pair's gap holds. -/
private theorem SamplablePair.exists_generator (pair : SamplablePair) {gap : ℕ → ℝ}
    {densityBound : ℕ → ℕ} (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ (length : ℕ → ℕ) (generator : ℕ → List Bool → List Bool),
      ComputableInPolyTime length encUnary encUnary ∧ (∀ n, n + 1 ≤ length n) ∧
      ComputableInPolyTime (fun a => generator a.1 a.2) (encPair encUnary encBits) encBits ∧
      (∀ n seed, seed.length = length n → (generator n seed).length = length n + 1) ∧
      ∀ advice : ℕ → List Bool, pair.HasGapWithAdvice gap advice →
        IndistinguishableWithAdvice advice
          (fun n => (BitString.uniformList (length n)).map (generator n))
          (fun n => BitString.uniformList (length n + 1)) := by
  have hdensity := hdensity.tidy
  obtain ⟨saved⟩ := pair.exists_seedRealization
  obtain ⟨bound, hbound, hfits⟩ := pair.exists_observationBound
  obtain ⟨common, hcommon, _, hge, hsize⟩ := EntropyGrid.exists_common_seedLength
    (sourceBits := saved.length) (observationBound := bound) (densityBound := densityBound)
    saved.length_isPolyTime hbound (.of_tidy hdensity)
  have htotal := ComputableTidilyInPolyTime.unary_mul.comp
    ((EntropyGrid.isPolyTime_size saved.length_isPolyTime (.of_tidy hdensity)).tidy.prod
      hcommon.tidy)
  refine ⟨fun n => EntropyGrid.size (saved.length n) (densityBound n) * common n,
    fun n => EntropyGrid.combinedGenerate n (saved.length n) (bound n) (densityBound n)
      (common n) (saved.evaluate n), .of_tidy htotal,
    fun n => (hge n).trans (Nat.le_mul_of_pos_left _ (EntropyGrid.size_pos ..)),
    EntropyGrid.isPolyTime_combinedGenerate saved hbound (.of_tidy hdensity) hcommon,
    fun n seed _ => EntropyGrid.length_combinedGenerate .., fun advice hpair => ?_⟩
  exact EntropyGrid.combinedGenerate_indistinguishableWithAdvice hpair saved
    (observationBound := bound) (densityBound := densityBound) (common := common)
    ⟨hbound, .of_tidy hdensity, hcommon, hfits, hsize⟩ hgap

/-- A samplable pseudoentropy pair with an efficiently resolved gap gives a uniform PRG
expanding every seed length by one bit. -/
theorem SamplablePair.HasGap.exists_pseudorandomGenerator {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) {densityBound : ℕ → ℕ}
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ generator : List Bool → List Bool, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨length, generator, hlength, hge, hgenerator, houtput, hsecure⟩ :=
    pair.exists_generator hdensity hgap
  exact ⟨_, GeneratorReindex.pseudorandomGenerator hlength hge hgenerator houtput
    (computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr
      (hsecure _ (hasGap_iff_hasGapWithAdvice_nil.mp hpair)))⟩

/-- A samplable pseudoentropy pair whose gap holds against every polynomially bounded advice
family gives a nonuniform PRG expanding every seed length by one bit. -/
theorem SamplablePair.exists_nonuniformPRG {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : ∀ advice : ℕ → List Bool, PolynomiallyBounded (fun n => (advice n).length) →
      pair.HasGapWithAdvice gap advice)
    {densityBound : ℕ → ℕ}
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ generator : List Bool → List Bool, NonuniformPRG generator (fun n => n + 1) := by
  obtain ⟨length, generator, hlength, hge, hgenerator, houtput, hsecure⟩ :=
    pair.exists_generator hdensity hgap
  exact ⟨_, GeneratorReindex.nonuniformPRG hlength hge hgenerator houtput
    fun advice hadvice => hsecure advice (hpair advice hadvice)⟩

end Cslib.Crypto.Pseudoentropy
