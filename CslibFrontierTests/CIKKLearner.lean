/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner

/-! Usage checks for the CIKK learner: the class-form theorem specializes to a single target, the
query bound has a closed numeral form, and the closed forms of the parameters evaluate. -/

namespace CslibFrontierTests.CIKKLearner

open Cslib Cslib.Circuits.Boolean Cslib.Crypto.PRG.NisanWigderson Cslib.MachineLearning
  Cslib.MachineLearning.UniformLearning Finset

/-- The direct-product length is nonzero, as the seed distribution of the amplification stage
requires. -/
example (e g : ℕ) : cikkK e g ≠ 0 := NeZero.ne _

/-- **One target.** A test accepting a `2 ^ (ℓ + 1 - g)` fraction of all strings but no output of
the generator of `Amp(f)` gives a learner for `f` with error `2^{-e}` and confidence
`1 - 2^{-h}`. -/
example {n ℓ : ℕ} (e g h : ℕ) (test : BitString (2 ^ ℓ) → Bool) (f : BooleanFunction n)
    (hdense : 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ g * #{y | test y = true})
    (hrej : ∀ z, test (generator (Design.binaryPolynomial (cikkK e g * n + cikkK e g) ℓ)
      (glAmp f (cikkK e g)) z) = false) :
    (cikkLearner n ℓ e g h test).Learns (cikkSeed n ℓ e g h) {f} (1 / 2 ^ e) (1 / 2 ^ h) :=
  learns_cikkLearner e g h hdense fun f' hf' => by
    rw [Set.mem_singleton_iff.1 hf']
    exact hrej

/-- At `ℓ = 2`, `e = 1`, `g = 3` and `h = 1`, the learner makes at most `2 ^ 100` queries. -/
example (n : ℕ) (test : BitString (2 ^ 2) → Bool) :
    (cikkLearner n 2 1 3 1 test).QueriesAtMost (2 ^ 100) := by
  convert queriesAtMost_cikkLearner_two_pow n 2 1 3 1 test using 1

/-- The closed forms of the parameters at `e = 1` and `g = 3`. -/
example : cikkK 1 3 ≤ 2 ^ 20 ∧ cikkMasks 1 3 ≤ 28 ∧ cikkFixed 1 3 ≤ 2 ^ 8 * 79 ∧
    cikkTrials 1 3 ≤ 2 ^ 38 * 5 ∧ cikkRuns 1 3 1 ≤ 2 * 2 ^ 74 ∧
    cikkSamples 1 3 1 ≤ 2 ^ 5 * 79 :=
  ⟨cikkK_le_two_pow 1 3, cikkMasks_le 1 3, cikkFixed_le 1 3, cikkTrials_le 1 3, cikkRuns_le 1 3 1,
    cikkSamples_le 1 3 1⟩

/-- `log₂ k` is at most `2e + g + 15`. -/
example (e g : ℕ) : cikkLogK e g ≤ 2 * e + g + 15 := cikkLogK_le e g

end CslibFrontierTests.CIKKLearner
