/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorPadding
public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Candidates
import Complexity.Computability.Probabilistic.PPT.Capture

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
* `exists_secure_padded_choice_withAdvice`, `exists_secure_padded_choice`: padding preserves a
  choice secure against every uniform indexed test, relative to fixed advice and in the uniform
  case.

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
  have hsize := (isPolyTime_size hsource hdensity).tidy.polynomiallyBounded
  have h1 := ComputableInPolyTime.fst encUnary encUnary
  have hseed := (isPolyTime_seedLength h1 (h1.trans hsource) (h1.trans hobservation)
    (h1.trans hdensity) (.snd _ _)).tidy
  obtain ⟨c, d, hbound⟩ := hseed.indexed_polynomial_bound
    (f := fun n index => seedLength n (sourceBits n) (observationBound n) (densityBound n) index)
    hsize
  refine ⟨fun n => n + 1 + c * (n + 1) ^ d,
    (ComputableInPolyTime.id'.unary_add' (.const 1)).unary_add'
      ((ComputableInPolyTime.const c).unary_mul'
        ((ComputableInPolyTime.id'.unary_add' (.const 1)).trans (.unary_pow d))),
    ?_, fun n => by lia, ?_⟩
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
  have hp1 := ComputableInPolyTime.fst (encPair encUnary encUnary) encBits
  have hn := hp1.fst'
  have hgen :=
    ((ComputableInPolyTime.fst (encPair (encPair encUnary encUnary) encBits) encBits).fst'.prod
      (.snd _ _)).trans (isPolyTime_generate_of_realization saved hobservation hdensity)
  exact GeneratorPadding.isPolyTime_generate
    (isPolyTime_seedLength hn (hn.trans saved.length_isPolyTime) (hn.trans hobservation)
      (hn.trans hdensity) hp1.snd')
    (hn.trans hcommon) hgen (.snd _ _)

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

/-- Padding preserves one secure choice relative to fixed advice against every uniform indexed
test. -/
theorem exists_secure_padded_choice_withAdvice {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (bounds : PaddingBounds saved observationBound densityBound common)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ,
      (∀ᶠ n in atTop, choose n < size (saved.length n) (densityBound n)) ∧
      ∀ test : ℕ × List Bool → ℕ → List Bool → ProbComp Bool,
        IsPPTOn (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
          encBool (fun ((a, i), word) => test a i word) →
        Negligible (fun n => Game.advantage
          (((uniformList (common n)).map (paddedGenerate n (saved.length n) (observationBound n)
            (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test (n, advice n) (choose n) word)))
          ((uniformList (common n + 1)).bind
            (fun word => ProbComp.eval (test (n, advice n) (choose n) word)))) := by
  obtain ⟨hobservation, hdensity, hcommon, hfits, hbound⟩ := bounds
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_choice_withAdvice hpair saved hobservation hdensity hfits hgap
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  have hp1 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits
  have hn := hp1.fst'.fst'
  have hadv := htest.preprocess
    ((ComputableInPolyTime.fst (encPair (encPair (encPair encUnary encBits) encUnary) encBits)
      encBits).fst'.prod (.snd _ _))
  let reduction := fun (a : ℕ × List Bool) index => GeneratorPadding.test
    (seedLength a.1 (saved.length a.1) (observationBound a.1) (densityBound a.1) index)
    (common a.1) (test a index)
  have h := hsecure reduction (by
    apply GeneratorPadding.isPPTOn_test
    · exact isPolyTime_seedLength hn (hn.trans saved.length_isPolyTime) (hn.trans hobservation)
        (hn.trans hdensity) hp1.snd'
    · exact hn.trans hcommon
    · exact hadv
    · exact .snd _ _)
  apply h.congr'
  filter_upwards [hchoose] with n hn
  dsimp only [reduction, paddedGenerate]
  exact (GeneratorPadding.advantage_eq _ _ (hbound n (choose n) hn)
    (seedLength_lt_outputLength n (saved.length n) (observationBound n) (densityBound n)
      (choose n))).symm

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
          encBool (fun ((n, i), word) => test n i word) →
        Negligible (fun n => Game.advantage
          (((uniformList (common n)).map (paddedGenerate n (saved.length n) (observationBound n)
            (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformList (common n + 1)).bind
            (fun word => ProbComp.eval (test n (choose n) word)))) := by
  obtain ⟨choose, hchoose, hsecure⟩ := exists_secure_padded_choice_withAdvice
    (SamplablePair.hasGap_iff_hasGapWithAdvice_nil.mp hpair) saved bounds hgap
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  have hp1 := ComputableInPolyTime.fst (encPair (encPair encUnary encBits) encUnary) encBits
  have htest' := htest.preprocess ((hp1.fst'.fst'.prod hp1.snd').prod (.snd _ _))
  exact hsecure (fun a => test a.1) htest'

end Cslib.Crypto.Pseudoentropy.EntropyGrid
