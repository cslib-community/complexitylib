/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.Basic
public import Complexity.Crypto.Computational.PseudorandomGenerator
public import Complexity.Probability.UniformNat
import Complexity.Crypto.Computational.GeneratorReindex
import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Combined

/-!
# Pseudorandom generators from pseudoentropy pairs

Realize the pair with a deterministic sampler and saved coins, enumerate the entropy grid,
pad and amplify every candidate, then XOR their outputs. Finally extend the resulting family
to every seed length. The density schedule must resolve the pair's gap; no entropy estimate
or chosen successful candidate is supplied to the generator.

## Main results

* `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap.exists_pseudorandomGenerator`: a samplable
  pseudoentropy pair with an efficiently resolved gap gives a uniform one-bit expanding PRG.

## References

This formalizes [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006],
Section 5 and the final proof of Theorem 1. The matrix extractor used here gives polynomial seed
length without claiming the paper's optimized seed-length exponent.

Adapted from Crypto/Computational/Pseudoentropy/Generator.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy

open Probability Filter Turing.MultiTapeTM

/-- A samplable pseudoentropy pair with an efficiently resolved gap gives a uniform PRG
expanding every seed length by one bit. -/
theorem SamplablePair.HasGap.exists_pseudorandomGenerator {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) {densityBound : ℕ → ℕ}
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ generator : List Bool → List Bool, PseudorandomGenerator generator (fun n => n + 1) := by
  have hdensity := hdensity.tidy
  obtain ⟨saved⟩ := pair.exists_seedRealization
  obtain ⟨bound, hbound, hfits⟩ := pair.exists_observationBound
  obtain ⟨common, hcommon, _, hge, hsize⟩ := EntropyGrid.exists_common_seedLength
    (sourceBits := saved.length) (observationBound := bound) (densityBound := densityBound)
    saved.length_isPolyTime hbound (.of_tidy hdensity)
  have htotal := ComputableTidilyInPolyTime.unary_mul.comp
    ((EntropyGrid.isPolyTime_size saved.length_isPolyTime (.of_tidy hdensity)).tidy.prod
      hcommon.tidy)
  refine ⟨GeneratorReindex.generate
    (fun n => EntropyGrid.size (saved.length n) (densityBound n) * common n)
    (fun n => EntropyGrid.combinedGenerate n (saved.length n) (bound n) (densityBound n)
      (common n) (saved.evaluate n)), ?_⟩
  refine GeneratorReindex.pseudorandomGenerator (.of_tidy htotal) ?_ (.of_tidy ?_) ?_ ?_
  · intro n
    exact (hge n).trans (Nat.le_mul_of_pos_left _ (EntropyGrid.size_pos ..))
  · exact (EntropyGrid.isPolyTime_combinedGenerate saved
      (observationBound := bound) (densityBound := densityBound) (common := common)
      hbound (.of_tidy hdensity) hcommon).tidy
  · intro n seed _
    exact EntropyGrid.length_combinedGenerate ..
  · exact EntropyGrid.combinedGenerate_indistinguishable hpair saved
      (observationBound := bound) (densityBound := densityBound) (common := common)
      ⟨hbound, .of_tidy hdensity, hcommon, hfits, hsize⟩ hgap

end Cslib.Crypto.Pseudoentropy
