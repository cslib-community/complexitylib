/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Pseudoentropy.EntropyGrid
public import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Seeded
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Tactic.PPT

/-!
# Expanding candidates from a pseudoentropy pair

Each entropy-grid entry defines a deterministic polynomial-time expander with its exact seed
length. One entry is secure against every uniform indexed test; its index may vary arbitrarily
with the security parameter. The family is indexed by the whole finite grid and never computes
entropy.

These raw candidates have different seed lengths. `ThreeSource.Padding` gives them a common
seed length and one bit of stretch. Amplification and XOR combination are still needed to turn
them into one generator.

## Main definitions

* `seedLength`, `outputLength`, `generate`: exact lengths and evaluation of one entropy guess.

## Main results

* `isPolyTime_outputLength`: output size is uniformly computable in unary.
* `isPolyTime_generate`, `isPolyTime_generate_of_realization`: candidate evaluation is uniformly
  polynomial time.
* `seedLength_lt_outputLength`, `length_generate`: strict expansion and exact output length.
* `exists_valid_choice`: every sufficiently fine grid eventually contains a valid entry.
* `exists_secure_choice`: a single proof-only choice works for every uniform indexed test.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Section 5, final proof of Theorem 1.
  [Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.EntropyGrid

open Probability BitString Turing.MultiTapeTM Filter PMF

/-- The exact seed length of a candidate, including all three public matrix keys. -/
def seedLength (n sourceBits observationBound densityBound index : ℕ) : ℕ :=
  ThreeSource.seedLength (ExtractionSchedule.count n sourceBits (dyadicSize densityBound - 1))
    sourceBits observationBound (observationBits n sourceBits densityBound index)
    (labelBits n sourceBits densityBound index) (remainingBits n sourceBits densityBound index)

/-- The candidate's output keeps every matrix key and the three digests. -/
def outputLength (n sourceBits observationBound densityBound index : ℕ) : ℕ :=
  ThreeSource.outputLength (ExtractionSchedule.count n sourceBits (dyadicSize densityBound - 1))
    sourceBits observationBound (observationBits n sourceBits densityBound index)
    (labelBits n sourceBits densityBound index) (remainingBits n sourceBits densityBound index)

/-- A candidate is the deterministic three-source extractor at one entropy guess. -/
def generate (n sourceBits observationBound densityBound index : ℕ)
    (evaluate : List Bool → List Bool × Bool) (seed : List Bool) : List Bool :=
  ThreeSource.generate (ExtractionSchedule.count n sourceBits (dyadicSize densityBound - 1))
    sourceBits observationBound (observationBits n sourceBits densityBound index)
    (labelBits n sourceBits densityBound index) (remainingBits n sourceBits densityBound index)
    evaluate seed

section Lengths

variable {α : Type} {input : α ↪ List Bool}
  {n sourceBits observationBound densityBound index : α → ℕ}
  (hn : ComputableInPolyTime n input encUnary)
  (hsource : ComputableInPolyTime sourceBits input encUnary)
  (hobservation : ComputableInPolyTime observationBound input encUnary)
  (hdensity : ComputableInPolyTime densityBound input encUnary)
  (hindex : ComputableInPolyTime index input encUnary)

include hn hsource hobservation hdensity hindex

/-- The exact input size is uniformly available in unary. -/
theorem isPolyTime_seedLength : ComputableInPolyTime
    (fun a => seedLength (n a) (sourceBits a) (observationBound a) (densityBound a) (index a))
    input encUnary := by
  unfold seedLength
  polytime

/-- The exact output size is uniformly available in unary. -/
theorem isPolyTime_outputLength : ComputableInPolyTime
    (fun a => outputLength (n a) (sourceBits a) (observationBound a) (densityBound a) (index a))
    input encUnary := by
  unfold outputLength
  polytime

end Lengths

attribute [program_certificate] isPolyTime_seedLength isPolyTime_outputLength

/-- Candidate evaluation is uniformly polynomial time, with an ordinary captured callback. -/
theorem isPolyTime_generate {α : Type} {input : α ↪ List Bool}
    {n sourceBits observationBound densityBound index : α → ℕ}
    {evaluate : α → List Bool → List Bool × Bool} {seed : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hobservation : ComputableInPolyTime observationBound input encUnary)
    (hdensity : ComputableInPolyTime densityBound input encUnary)
    (hindex : ComputableInPolyTime index input encUnary)
    (hevaluate : ComputableInPolyTime (fun a => evaluate a.1 a.2)
      (encPair input encBits) (encPair encBits encBool))
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime (fun a => generate (n a) (sourceBits a) (observationBound a)
      (densityBound a) (index a) (evaluate a) (seed a)) input encBits := by
  unfold generate
  apply ThreeSource.isPolyTime_generate <;> fun_prop

attribute [program_certificate] isPolyTime_generate

/-- A saved sampler gives one efficient evaluator for the entire indexed family. -/
theorem isPolyTime_generate_of_realization {pair : SamplablePair} (saved : pair.SeedRealization)
    {observationBound densityBound : ℕ → ℕ}
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary) :
    ComputableInPolyTime (fun input => generate input.1.1 (saved.length input.1.1)
      (observationBound input.1.1) (densityBound input.1.1) input.1.2
      (saved.evaluate input.1.1) input.2)
      (encPair (encPair encUnary encUnary) encBits) encBits := by
  have hlength := saved.length_isPolyTime
  have hevaluate := saved.efficient
  apply isPolyTime_generate <;> fun_prop

/-- The advertised lengths give strict expansion for every entry, even an inaccurate guess. -/
theorem seedLength_lt_outputLength (n sourceBits observationBound densityBound index : ℕ) :
    seedLength n sourceBits observationBound densityBound index <
      outputLength n sourceBits observationBound densityBound index :=
  (ThreeSource.seedLength_lt_outputLength_iff ..).mpr (expands n sourceBits densityBound index)

/-- Every correctly sized input has exactly the advertised output length. -/
theorem length_generate {pair : SamplablePair} (saved : pair.SeedRealization)
    (n observationBound densityBound index : ℕ)
    (hbound : ∀ observation ∈ ((pair.joint n).map Prod.fst).support,
      (pair.encode n observation).length ≤ observationBound)
    {seed : List Bool}
    (hseed : seed.length = seedLength n (saved.length n) observationBound densityBound index) :
    (generate n (saved.length n) observationBound densityBound index
      (saved.evaluate n) seed).length =
        outputLength n (saved.length n) observationBound densityBound index :=
  ThreeSource.length_generate _ _ _ _ _ _ _
    (fun _ h => saved.observation_length_le n observationBound hbound h) hseed

/-- Every sufficiently fine grid contains a valid entry, with no entropy estimation required. -/
theorem exists_valid_choice {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization) {densityBound : ℕ → ℕ}
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ, ∀ᶠ n in atTop,
      Valid n (saved.length n) (densityBound n) (choose n)
        (entropy ((pair.joint n).map Prod.fst)) (conditionalEntropy (pair.joint n)) (gap n) := by
  classical
  have hexists : ∀ᶠ n in atTop, ∃ index,
      Valid n (saved.length n) (densityBound n) index
        (entropy ((pair.joint n).map Prod.fst)) (conditionalEntropy (pair.joint n)) (gap n) := by
    filter_upwards [hgap, hpair.eventually_entropy_add_gap_le_one] with n hgap hone
    apply exists_valid n (saved.length n) (densityBound n)
      (entropy_nonneg _) (conditionalEntropy_nonneg _) _ hgap hone
    linarith [saved.entropy_chain_rule n, conditionalEntropy_nonneg (saved.jointWithSeed n)]
  exact ⟨fun n => Classical.epsilon _, hexists.mono (fun _ h => Classical.epsilon_spec h)⟩

/-- A single varying candidate is secure against every uniform indexed test. The choice is
made before the test is quantified and is used only in the proof, never by `generate`. -/
theorem exists_secure_choice {pair : SamplablePair} {gap : ℕ → ℝ}
    (hpair : pair.HasGap gap) (saved : pair.SeedRealization)
    {observationBound densityBound : ℕ → ℕ}
    (hobservation : ComputableInPolyTime observationBound encUnary encUnary)
    (hdensity : ComputableInPolyTime densityBound encUnary encUnary)
    (hfits : ∀ n observation, observation ∈ ((pair.joint n).map Prod.fst).support →
      (pair.encode n observation).length ≤ observationBound n)
    (hgap : ∀ᶠ n in atTop, 4 / (dyadicSize (densityBound n) : ℝ) ≤ gap n) :
    ∃ choose : ℕ → ℕ,
      (∀ᶠ n in atTop, choose n < size (saved.length n) (densityBound n)) ∧
      ∀ test : ℕ → ℕ → List Bool → ProbComp Bool,
        IsPPTOn (encPair (encPair encUnary encUnary) encBits)
          encBool (fun input => test input.1.1 input.1.2 input.2) →
        Negligible (fun n => Game.advantage
          (((uniformList (seedLength n (saved.length n) (observationBound n) (densityBound n)
            (choose n))).map (generate n (saved.length n) (observationBound n) (densityBound n)
              (choose n) (saved.evaluate n))).bind
                (fun word => ProbComp.eval (test n (choose n) word)))
          ((uniformList (outputLength n (saved.length n) (observationBound n) (densityBound n)
            (choose n))).bind (fun word => ProbComp.eval (test n (choose n) word)))) := by
  have hobservation := hobservation.tidy
  have hdensity := hdensity.tidy
  obtain ⟨choose, hvalid⟩ := exists_valid_choice hpair saved hgap
  refine ⟨choose, hvalid.mono (fun _ h => h.index_lt), ?_⟩
  intro test htest
  have hlength := saved.length_isPolyTime.tidy
  have h := hpair.extract_indexed_three saved choose
    (candidates := fun n => size (saved.length n) (densityBound n))
    (inverseSlack := fun n => dyadicSize (densityBound n) - 1)
    (observationBits := fun n i => observationBits n (saved.length n) (densityBound n) i)
    (labelBits := fun n i => labelBits n (saved.length n) (densityBound n) i)
    (remainingBits := fun n i => remainingBits n (saved.length n) (densityBound n) i)
    (numerator := fun n i => numerator (densityBound n) i)
    ⟨by polytime, .of_tidy hobservation, by polytime, by polytime, by polytime, by polytime,
      by polytime, .of_tidy hdensity⟩ hfits (hvalid.mono (fun _ h => h.index_lt))
    (hvalid.mono (fun n h => ⟨numerator_pos _ _, h.numerator_le, h.density_le⟩))
    (hvalid.mono (fun _ h => by simpa only [scale, Nat.cast_mul, Nat.cast_ofNat]
      using h.observation_budget))
    (Eventually.of_forall (fun n => by
      simpa only [scale, Nat.cast_mul, Nat.cast_ofNat] using
        (label_budget n (saved.length n) (densityBound n) (choose n)).le))
    (hvalid.mono (fun _ h => by simpa only [scale, Nat.cast_mul, Nat.cast_ofNat]
      using h.remaining_budget)) test htest
  unfold seedLength outputLength generate
  simp_rw [ThreeSource.eval_generate_of_realization saved _ _ _ _ _ _ (hfits _)]
  simpa only [ProbComp.eval_bind, BitString.eval_sampleList] using h

/-- A linear grid precision suffices for the gap already obtained from a general one-way
function. This is a numerical consequence of rounding the denominator up to a power of two. -/
theorem four_steps_le_owf_gap (n : ℕ) :
    4 / (dyadicSize (16 * (n + 7)) : ℝ) ≤ 1 / (2 * ((n : ℝ) + 7)) := by
  have hD : (0 : ℝ) < dyadicSize (16 * (n + 7)) := by
    exact_mod_cast dyadicSize_pos _
  have hbound : (16 * (n + 7) : ℝ) < dyadicSize (16 * (n + 7)) := by
    exact_mod_cast lt_dyadicSize (16 * (n + 7))
  apply (div_le_div_iff₀ hD (by positivity)).mpr
  nlinarith

end Cslib.Crypto.Pseudoentropy.EntropyGrid
