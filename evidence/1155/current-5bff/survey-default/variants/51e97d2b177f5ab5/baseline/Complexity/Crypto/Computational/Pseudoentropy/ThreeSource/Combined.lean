/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorXor
public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Amplification
import Complexity.Tactic.PolyTime

/-!
# Combining the entropy-grid candidates

Run every amplified candidate on a separate seed block and XOR the outputs. The result expands
their total seed length by one bit. The secure choice from the entropy argument proves security;
the program itself never chooses or estimates an entropy.

## Main definitions

* `combinedGenerate`: run and XOR every amplified entropy-grid candidate.

## Main results

* `isPolyTime_combinedGenerate`: one uniform implementation of the complete grid.
* `length_combinedGenerate`: output length is one bit beyond the grid's total seed cost.
* `combinedGenerate_indistinguishable`: security against every efficient test of the full output.

## References

This completes the indexed construction of Thomas Holenstein, *Pseudorandom Generators from
One-Way Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of
Theorem 1, [Holenstein2006].
The security parameter determines the seed length here. Extending this construction to every
input length requires a separate reindexing argument.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability BitString Turing.MultiTapeTM Filter

/-- Use one independent seed block per candidate and XOR the amplified outputs. -/
def combinedGenerate (n sourceBits observationBound densityBound commonBits : ℕ)
    (evaluate : List Bool → List Bool × Bool) (seed : List Bool) : List Bool :=
  GeneratorXor.generate (size sourceBits densityBound) commonBits
    (size sourceBits densityBound * commonBits + 1)
    (fun index => amplifiedGenerate n sourceBits observationBound densityBound commonBits
      index evaluate) seed

/-- The complete grid construction has one uniform polynomial-time implementation. -/
theorem isPolyTime_combinedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hcommon : ComputableInPolyTime common encUnary encUnary) :
    ComputableInPolyTime (fun input =>
      combinedGenerate input.1 (saved.length input.1) (observationBound input.1)
        (densityBound input.1) (common input.1) (saved.evaluate input.1) input.2)
      (encPair encUnary encBits) encBits := by
  have hobservation := hobservation.tidy
  have hdensity := hdensity.tidy
  have hcommon := hcommon.tidy
  refine .of_tidy ?_
  have hlength := saved.length_isPolyTime.tidy
  have hsize := (isPolyTime_size saved.length_isPolyTime (.of_tidy hdensity)).tidy
  have houtput : ComputableTidilyInPolyTime
      (fun n => size (saved.length n) (densityBound n) * common n + 1) encUnary encUnary := by
    fun_prop
  unfold combinedGenerate
  refine (GeneratorXor.isPolyTime_generate (.of_tidy (by polytime)) (.of_tidy (by polytime))
    (.of_tidy (houtput.comp (ComputableTidilyInPolyTime.fst encUnary encBits)))
    (.of_tidy ?_) (.of_tidy (by polytime))).tidy
  have hgenerate := (isPolyTime_amplifiedGenerate saved (.of_tidy hobservation) (.of_tidy
    hdensity) (.of_tidy hcommon)).tidy
  exact hgenerate.comp (g := fun input : ((ℕ × List Bool) × ℕ) × List Bool =>
    ((input.1.1.1, input.1.2), input.2)) (by fun_prop)

/-- The output is one bit longer than the total cost of all the independent seed blocks. -/
theorem length_combinedGenerate (n sourceBits observationBound densityBound commonBits : ℕ)
    (evaluate : List Bool → List Bool × Bool) (seed : List Bool) :
    (combinedGenerate n sourceBits observationBound densityBound commonBits evaluate seed).length =
      size sourceBits densityBound * commonBits + 1 := by
  simp only [combinedGenerate, GeneratorXor.length_generate]

/-- One entropy-valid choice suffices for security of the complete, explicitly computed grid. -/
theorem combinedGenerate_indistinguishable {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (bounds : PaddingBounds saved observationBound densityBound common)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ComputationallyIndistinguishable
      (fun n => (uniformList (size (saved.length n) (densityBound n) * common n)).map
        (combinedGenerate n (saved.length n) (observationBound n) (densityBound n) (common n)
          (saved.evaluate n)))
      (fun n => uniformList (size (saved.length n) (densityBound n) * common n + 1)) := by
  obtain ⟨choose, hchoose, hsecure⟩ := exists_secure_amplified_choice hpair saved bounds hgap
  obtain ⟨hobservationPlain, hdensityPlain, hcommonPlain, _, _⟩ := bounds
  have hobservation := hobservationPlain.tidy
  have hdensity := hdensityPlain.tidy
  have hcommon := hcommonPlain.tidy
  have hlength := saved.length_isPolyTime.tidy
  have hsize := (isPolyTime_size saved.length_isPolyTime (.of_tidy hdensity)).tidy
  unfold combinedGenerate
  refine GeneratorXor.indistinguishable (choose := choose)
    (count := fun n => size (saved.length n) (densityBound n)) (seedBits := common)
    (outputBits := fun n => size (saved.length n) (densityBound n) * common n + 1)
    (generator := fun n index => amplifiedGenerate n (saved.length n) (observationBound n)
      (densityBound n) (common n) index (saved.evaluate n))
    (.of_tidy (by polytime)) (.of_tidy hcommon) (.of_tidy (by polytime)) (.of_tidy ?_) hchoose
      hsecure
  exact (isPolyTime_amplifiedGenerate saved (.of_tidy hobservation) (.of_tidy hdensity) (.of_tidy
    hcommon)).tidy

end Cslib.Crypto.Pseudoentropy.EntropyGrid
