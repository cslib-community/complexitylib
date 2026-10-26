/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorPadding
public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Candidates
import Complexity.Tactic.PPT

/-!
# A common seed length for the entropy grid

One polynomial bounds the input sizes of all entropy-grid entries. Padding to that common
length gives each candidate exactly one bit of stretch and preserves the secure choice against
uniform indexed tests. The common length is increasing and at least the security parameter plus
one, preparing later reindexing by the actual seed length.

## Main definitions

* `PaddingBounds`: shared efficiency and size contract for the padding pipeline.
* `paddedGenerate`: normalize an entropy-grid entry to a common input length.

## Main results

* `exists_common_seedLength`: one increasing efficient schedule bounds every entry's seed length.
* `isPolyTime_paddedGenerate`, `length_paddedGenerate`: efficient evaluation with one-bit stretch.
* `exists_secure_padded_choice`: padding preserves a choice secure against every uniform test.

## References

This supplies the common-length candidate family used before amplification and XOR in
Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability BitString Turing.MultiTapeTM Filter

/-- The entire grid fits one efficient increasing seed-length schedule. -/
theorem exists_common_seedLength {sourceBits observationBound densityBound : ℕ → ℕ}
    (hsource : ComputableInPolyTime sourceBits encUnary encUnary)
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary) :
    ∃ common : ℕ → ℕ, ComputableInPolyTime common encUnary encUnary ∧
      StrictMono common ∧ (∀ n, n + 1 ≤ common n) ∧
      ∀ n index, index < size (sourceBits n) (densityBound n) →
        seedLength n (sourceBits n) (observationBound n) (densityBound n) index ≤ common n := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hsource
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hobservation
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hdensity
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime]
  have hsize := (isPolyTime_size (.of_tidy hsource) (.of_tidy hdensity)).tidy.polynomiallyBounded
  have hseed : ComputableTidilyInPolyTime (fun input => seedLength input.1 (sourceBits input.1)
      (observationBound input.1) (densityBound input.1) input.2)
      (encPair encUnary encUnary) encUnary := by
    apply ComputableInPolyTime.tidy
    apply isPolyTime_seedLength <;> exact .of_tidy (by polytime)
  obtain ⟨c, d, hbound⟩ := hseed.indexed_polynomial_bound
    (f := fun n index => seedLength n (sourceBits n) (observationBound n) (densityBound n) index)
    hsize
  refine ⟨fun n => n + 1 + c * (n + 1) ^ d, by polytime, ?_, fun n => by lia, ?_⟩
  · intro n m hnm
    have hpower := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia : n + 1 ≤ m + 1) d)
    lia
  · intro n index hindex
    exact (hbound n index hindex).trans (by lia)

/-- Efficient observation, entropy-resolution and common seed-length bounds for padding the
entropy grid. The observation bound applies only on support; the seed bound covers every grid
entry. Security assumptions and the entropy gap remain separate. -/
structure PaddingBounds {pair : SamplablePair} (saved : pair.SeedRealization)
    (observationBound densityBound common : ℕ → ℕ) : Prop where
  observation_isPolyTime : ComputableInPolyTime observationBound encUnary encUnary
  density_isPolyTime : ComputableInPolyTime densityBound encUnary encUnary
  common_isPolyTime : ComputableInPolyTime common encUnary encUnary
  observation_fits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
    (pair.encode n observation).length ≤ observationBound n
  seed_fits : ∀ n index, index < size (saved.length n) (densityBound n) →
    seedLength n (saved.length n) (observationBound n) (densityBound n) index ≤ common n

/-- Normalize every grid entry to a chosen common seed length and one bit of stretch. -/
def paddedGenerate (n sourceBits observationBound densityBound commonBits index : ℕ)
    (evaluate : List Bool → List Bool × Bool) (seed : List Bool) : List Bool :=
  GeneratorPadding.generate (seedLength n sourceBits observationBound densityBound index) commonBits
    (generate n sourceBits observationBound densityBound index evaluate) seed

/-- The padded family uses the same saved sampler and ordinary word operations. -/
theorem isPolyTime_paddedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hcommon : ComputableInPolyTime common encUnary encUnary) :
    ComputableInPolyTime (fun input => paddedGenerate input.1.1 (saved.length input.1.1)
      (observationBound input.1.1) (densityBound input.1.1) (common input.1.1) input.1.2
      (saved.evaluate input.1.1) input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits := by
  have hobservation := hobservation.tidy
  have hdensity := hdensity.tidy
  have hcommon := hcommon.tidy
  have hlength := saved.length_isPolyTime.tidy
  have hgenerate := (isPolyTime_generate_of_realization saved (.of_tidy hobservation) (.of_tidy
    hdensity)).tidy
  unfold paddedGenerate
  apply GeneratorPadding.isPolyTime_generate
  · apply isPolyTime_seedLength <;> exact .of_tidy (by fun_prop)
  · exact .of_tidy (by fun_prop)
  · exact .of_tidy (hgenerate.comp (g := fun p : ((ℕ × ℕ) × List Bool) × List Bool =>
      (p.1.1, p.2)) (by fun_prop))
  · exact .of_tidy (by fun_prop)

/-- Correctly sized common inputs give exactly one bit of stretch. -/
theorem length_paddedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    (n observationBound densityBound commonBits index : ℕ)
    (hfits : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ observationBound)
    (hcommon : seedLength n (saved.length n) observationBound densityBound index ≤ commonBits)
    {seed : List Bool} (hseed : seed.length = commonBits) :
    (paddedGenerate n (saved.length n) observationBound densityBound commonBits index
      (saved.evaluate n) seed).length = commonBits + 1 := by
  apply GeneratorPadding.length_generate hcommon _ hseed
  intro seed hseed
  rw [length_generate saved n _ _ _ hfits hseed]
  exact seedLength_lt_outputLength ..

/-- Padding preserves one secure choice against every uniform indexed test. -/
theorem exists_secure_padded_choice {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (bounds : PaddingBounds saved observationBound densityBound common)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ,
      (∀ᶠ n in atTop, choose n < size (saved.length n) (densityBound n)) ∧
      ∀ test : ℕ → ℕ → List Bool → ProbComp Bool,
        IsPPTOn (encPair (encPair encUnary encUnary) encBits)
          encBool (fun input => test input.1.1 input.1.2 input.2) →
        Negligible (fun n => Game.advantage
          (((uniformList (common n)).map (paddedGenerate n (saved.length n) (observationBound n)
            (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformList (common n + 1)).bind
            (fun word => ProbComp.eval (test n (choose n) word)))) := by
  obtain ⟨hobservationPlain, hdensityPlain, hcommonPlain, hfits, hbound⟩ := bounds
  have hobservation := hobservationPlain.tidy
  have hdensity := hdensityPlain.tidy
  have hcommon := hcommonPlain.tidy
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_choice hpair saved (.of_tidy hobservation) (.of_tidy hdensity) hfits hgap
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  have hlength := saved.length_isPolyTime.tidy
  have hseed : ComputableTidilyInPolyTime (fun input => seedLength input.1 (saved.length input.1)
      (observationBound input.1) (densityBound input.1) input.2)
      (encPair encUnary encUnary) encUnary := by
    apply ComputableInPolyTime.tidy
    apply isPolyTime_seedLength <;> exact .of_tidy (by fun_prop)
  let reduction := fun n index => GeneratorPadding.test
    (seedLength n (saved.length n) (observationBound n) (densityBound n) index) (common n)
    (test n index)
  have h := hsecure reduction (by
    dsimp only [reduction]
    apply GeneratorPadding.isPPTOn_test
    · exact .of_tidy (hseed.comp (g := Prod.fst) (by fun_prop))
    · fun_prop
    · exact htest.preprocess (prepare := fun p : ((ℕ × ℕ) × List Bool) × List Bool =>
        (p.1.1, p.2)) (by fun_prop)
    · fun_prop)
  apply h.congr'
  filter_upwards [hchoose] with n hn
  exact (GeneratorPadding.advantage_eq _ _ (hbound n (choose n) hn)
    (seedLength_lt_outputLength n (saved.length n) (observationBound n) (densityBound n)
      (choose n))).symm

end Cslib.Crypto.Pseudoentropy.EntropyGrid
