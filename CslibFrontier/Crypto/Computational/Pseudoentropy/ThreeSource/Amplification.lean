/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pseudoentropy.ThreeSource.Padding
public import CslibFrontier.Crypto.Computational.Stretch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.PPT.Capture

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
* `exists_secure_amplified_choice_withAdvice`: amplification preserves the proof-only secure
  choice.

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

private theorem isPolyTime_count {pair : SamplablePair} (saved : pair.SeedRealization)
    {densityBound common : ℕ → ℕ}
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hcommon : ComputableInPolyTime common encUnary encUnary) :
    ComputableInPolyTime
      (fun n => size (saved.length n) (densityBound n) * common n + 1 - common n)
      encUnary encUnary :=
  (((isPolyTime_size saved.length_isPolyTime hdensity).unary_mul' hcommon).unary_add'
    (.const 1)).unary_sub' hcommon

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
  have hn := (ComputableInPolyTime.fst (encPair encUnary encUnary) encBits).trans
    (.fst encUnary encUnary)
  have hgen := (isPolyTime_paddedGenerate saved hobservation hdensity hcommon).comp'
    (((ComputableInPolyTime.fst (encPair (encPair encUnary encUnary) encBits) encBits).trans
      (.fst (encPair encUnary encUnary) encBits)).prod
      (ComputableInPolyTime.snd (encPair (encPair encUnary encUnary) encBits) encBits))
  exact PRGStretch.polyTime_iterate hgen (hcommon.comp' hn)
    ((isPolyTime_count saved hdensity hcommon).comp' hn)
    (ComputableInPolyTime.snd (encPair encUnary encUnary) encBits)

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

private theorem isPolyTime_prepareGen :
    ComputableInPolyTime
      (fun p : (ℕ × (List Bool × ℕ)) × List Bool => ((p.1.1, p.1.2.2), p.2))
      (encPair (encPair encUnary (encPair encBits encUnary)) encBits)
      (encPair (encPair encUnary encUnary) encBits) :=
  let h1 := ComputableInPolyTime.fst (encPair encUnary (encPair encBits encUnary)) encBits
  (h1.fst'.prod h1.snd'.snd').prod (ComputableInPolyTime.snd _ encBits)

/-- Amplification preserves one secure choice relative to fixed advice: the amplified candidate
is indistinguishable from uniform for tests that read both the advice and the candidate index. -/
theorem exists_secure_amplified_choice_withAdvice {pair : SamplablePair} {gap : ℕ → ℝ}
    {advice : ℕ → List Bool} (hpair : pair.HasGapWithAdvice gap advice)
    (saved : pair.SeedRealization)
    {observationBound densityBound common : ℕ → ℕ}
    (bounds : PaddingBounds saved observationBound densityBound common)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ,
      (∀ᶠ n in atTop, choose n < size (saved.length n) (densityBound n)) ∧
      IndistinguishableWithAdvice (fun n => encPair encBits encUnary (advice n, choose n))
        (fun n => (uniformList (common n)).map (amplifiedGenerate n (saved.length n)
          (observationBound n) (densityBound n) (common n) (choose n) (saved.evaluate n)))
        (fun n => uniformList (size (saved.length n) (densityBound n) * common n + 1)) := by
  obtain ⟨choose, hchoose, hsecure⟩ :=
    exists_secure_padded_choice_withAdvice hpair saved bounds hgap
  obtain ⟨hobservationPlain, hdensityPlain, hcommonPlain, _, _⟩ := bounds
  have hgenPlain := isPolyTime_paddedGenerate saved hobservationPlain hdensityPlain hcommonPlain
  have hgen : ComputableInPolyTime
      (fun ((n, (context : List Bool × ℕ)), seed) =>
        paddedGenerate n (saved.length n) (observationBound n)
          (densityBound n) (common n) context.2 (saved.evaluate n) seed)
      (encPair (encPair encUnary (encPair encBits encUnary)) encBits) encBits := by
    refine Eq.mp (congrArg (fun f => ComputableInPolyTime f _ _) (funext fun ⟨⟨_, _⟩, _⟩ => ?_))
      (hgenPlain.comp' isPolyTime_prepareGen)
    rfl
  have h := PRGStretch.indexed_indistinguishable (κ := List Bool × ℕ)
    (encContext := encPair encBits encUnary) (seedBits := common)
    (generator := fun n context => paddedGenerate n (saved.length n) (observationBound n)
      (densityBound n) (common n) context.2 (saved.evaluate n))
    (count := fun n => size (saved.length n) (densityBound n) * common n + 1 - common n)
    (choose := fun n => (advice n, choose n))
    hgen hcommonPlain (isPolyTime_count saved hdensityPlain hcommonPlain)
    (fun adversary hadversary => by
      simpa only [distinguishingGame_eq_bind, PMF.monad_bind_eq_bind] using
        hsecure.negligible_encoded (test := fun ((n, context), word) => adversary n context word)
          hadversary)
  refine ⟨choose, hchoose, IndistinguishableWithAdvice.of_negligible_encoded fun test htest => ?_⟩
  unfold amplifiedGenerate
  refine (h (fun n context word => test ((n, context), word))
    (htest.congr fun ⟨⟨_, _⟩, _⟩ => rfl)).congr' (Eventually.of_forall fun n => ?_)
  simp only [distinguishingGame_eq_bind, PMF.monad_bind_eq_bind]
  rw [length_add_count]

end Cslib.Crypto.Pseudoentropy.EntropyGrid
