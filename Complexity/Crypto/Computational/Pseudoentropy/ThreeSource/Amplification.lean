/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Padding
public import Complexity.Crypto.Computational.Stretch
import Complexity.Tactic.PolyTime

/-!
# Amplifying the entropy-grid candidates

Each padded candidate is iterated until its output is one bit longer than all the candidates'
independent seeds together. The uniformly randomized stretching reduction preserves the secure
choice, with polynomial loss. This prepares XOR combination without computing that choice.

## Main definitions

* `amplifiedGenerate`: iterate a candidate to cover the full grid's independent seed cost.

## Main results

* `isPolyTime_amplifiedGenerate`: a uniform certificate for the indexed family.
* `length_amplifiedGenerate`: exact output length, one bit beyond the total seed cost.
* `exists_secure_amplified_choice`: amplification preserves the proof-only secure choice.

## References

We follow Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction
for Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1,
[Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability BitString Turing.MultiTapeTM Filter

/-- Amplify one candidate enough to pay for all candidates' independent seeds. -/
def amplifiedGenerate (n sourceBits observationBound densityBound commonBits index : ℕ)
    (evaluate : List Bool → List Bool × Bool) (seed : List Bool) : List Bool :=
  PRGStretch.iterate
    (paddedGenerate n sourceBits observationBound densityBound commonBits index evaluate)
    commonBits (size sourceBits densityBound * commonBits + 1 - commonBits) seed

/-- The entire amplified family is uniformly efficient, including on malformed seed inputs. -/
theorem isPolyTime_amplifiedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hcommon : ComputableInPolyTime common encUnary encUnary) :
    ComputableInPolyTime
      (fun input => amplifiedGenerate input.1.1 (saved.length input.1.1)
        (observationBound input.1.1) (densityBound input.1.1) (common input.1.1) input.1.2
          (saved.evaluate input.1.1) input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits := by
  have hlength := saved.length_isPolyTime
  have hsize := isPolyTime_size hlength hdensity
  have hgenerate := isPolyTime_paddedGenerate saved hobservation hdensity hcommon
  unfold amplifiedGenerate
  apply PRGStretch.polyTime_iterate
  · apply hgenerate.comp (g := fun input : ((ℕ × ℕ) × List Bool) × List Bool =>
      (input.1.1, input.2))
    fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

private theorem length_add_count (sourceBits densityBound commonBits : ℕ) :
    commonBits + (size sourceBits densityBound * commonBits + 1 - commonBits) =
      size sourceBits densityBound * commonBits + 1 := by
  have := Nat.le_mul_of_pos_left commonBits (size_pos sourceBits densityBound)
  lia

/-- Every enumerated candidate outputs one more bit than the total seed cost of the grid. -/
theorem length_amplifiedGenerate {pair : SamplablePair} (saved : pair.SeedRealization)
    (n observationBound densityBound commonBits index : ℕ)
    (hfits : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ observationBound)
    (hcommon : seedLength n (saved.length n) observationBound densityBound index ≤ commonBits)
    {seed : List Bool} (hseed : seed.length = commonBits) :
    (amplifiedGenerate n (saved.length n) observationBound densityBound commonBits index
      (saved.evaluate n) seed).length = size (saved.length n) densityBound * commonBits + 1 := by
  unfold amplifiedGenerate
  rw [PRGStretch.length_iterate_of_le
    (fun _ hs => length_paddedGenerate saved n _ _ _ _ hfits hcommon hs) _ _ hseed.ge, hseed]
  exact length_add_count ..

/-- Amplification preserves one choice secure against every uniform indexed test. -/
theorem exists_secure_amplified_choice {pair : SamplablePair} {gap : ℕ → ℝ}
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
          (((uniformList (common n)).map (amplifiedGenerate n (saved.length n)
            (observationBound n) (densityBound n) (common n) (choose n) (saved.evaluate n))).bind
              (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformList (size (saved.length n) (densityBound n) * common n + 1)).bind
            (fun word => ProbComp.eval (test n (choose n) word)))) := by
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_padded_choice hpair saved bounds hgap
  obtain ⟨hobservationPlain, hdensityPlain, hcommonPlain, _, _⟩ := bounds
  have hobservation := hobservationPlain.tidy
  have hdensity := hdensityPlain.tidy
  have hcommon := hcommonPlain.tidy
  have hlength := saved.length_isPolyTime.tidy
  have hsize := (isPolyTime_size saved.length_isPolyTime hdensityPlain).tidy
  have hcount : ComputableTidilyInPolyTime (fun n =>
      size (saved.length n) (densityBound n) * common n + 1 - common n) encUnary encUnary := by
    polytime
  have h := PRGStretch.indexed_indistinguishable (seedBits := common)
    (generator := fun n index => paddedGenerate n (saved.length n) (observationBound n)
      (densityBound n) (common n) index (saved.evaluate n))
    (count := fun n => size (saved.length n) (densityBound n) * common n + 1 - common n)
    (choose := choose)
    (isPolyTime_paddedGenerate saved (.of_tidy hobservation) (.of_tidy hdensity) (.of_tidy
      hcommon))
    (.of_tidy hcommon) (.of_tidy hcount) hsecure
  refine ⟨choose, hchoose, fun test htest => ?_⟩
  unfold amplifiedGenerate
  simpa only [length_add_count] using h test htest

end Cslib.Crypto.Pseudoentropy.EntropyGrid
