/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.ElGamal

/-!
# Fixed-group ElGamal encryption: checked instances

Concrete checks for the typed scheme of `CslibFrontier/Crypto/Computational/ElGamal/Finite.lean`:

* In `ZMod 5` with `g = 1`, ElGamal is correct, and the public key `a • 1` is the secret key `a`
  itself, so an adversary that decrypts with its public key wins the chosen-plaintext experiment
  with certainty. The single-group bound then forces the two DDH advantages of the reduction to
  sum to at least `1`.
* Over a prime-order group family, the bit ElGamal game is the typed chosen-plaintext experiment in
  each group, and the single-group bound applies to the typed adversary `bitAdversary`.
-/

namespace CslibFrontierTests.Crypto.ElGamalFinite

open Cslib Cslib.Probability Cslib.Crypto
open scoped NNReal

example : (elGamal 5 (1 : ZMod 5)).Correct := elGamal_correct 5 1

/-- Challenge `0` against `1`, keep the public key, and decrypt the challenge with it. -/
def unmask : TwoStage (ZMod 5) (MessagePair (ZMod 5)) (ZMod 5 × ZMod 5) Bool (ZMod 5) where
  choose u := pure (⟨0, 1⟩, u)
  guess u ct := pure (decide (ct.2 - u * ct.1 = 1))

/-- In `ZMod 5` with `g = 1`, the unmasking adversary outputs the challenge bit with certainty. -/
theorem eval_cpaExperiment_unmask (b : Bool) :
    ProbComp.eval ((elGamal 5 (1 : ZMod 5)).cpaExperiment (fun _ _ _ => true) unmask b) =
      PMF.pure b := by
  have hconst (c : Bool) : (PMF.uniformOfFintype (ZMod 5)).map (fun _ => c) = PMF.pure c :=
    PMF.map_const _ _
  have h01 : (0 : ZMod 5) ≠ 1 := by decide
  cases b <;> simp [PKE.cpaExperiment, lrExperiment, elGamal, unmask, mul_comm, hconst, h01]

/-- The unmasking adversary has chosen-plaintext advantage `1`. -/
theorem advantage_cpaExperiment_unmask :
    Experiment.advantage ((elGamal 5 (1 : ZMod 5)).cpaExperiment (fun _ _ _ => true) unmask false)
      ((elGamal 5 (1 : ZMod 5)).cpaExperiment (fun _ _ _ => true) unmask true) = 1 := by
  rw [Experiment.advantage, eval_cpaExperiment_unmask, eval_cpaExperiment_unmask]
  simp [Game.advantage, Game.succProbability]

-- In `ZMod 5`, the reduction's two DDH advantages sum to at least the advantage `1`.
example : 1 ≤ ddhAdvantage 5 (1 : ZMod 5) (elGamalToDDH (fun _ _ _ => true) unmask false) +
    ddhAdvantage 5 (1 : ZMod 5) (elGamalToDDH (fun _ _ _ => true) unmask true) :=
  advantage_cpaExperiment_unmask ▸
    advantage_cpaExperiment_elGamal_le (fun c => ⟨c, mul_one c⟩) _ unmask

section Family

variable (F : PrimeOrderGroupFamily)

-- The bit ElGamal game draws a group and runs the typed chosen-plaintext experiment in it.
example (setup : ℕ → PMF F.Desc) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ) :
    F.elGamalCPAGame setup adversary bit n =
      Game.withSetup (setup n) fun d =>
        (elGamal (F.order d) (F.generator d)).cpaExperiment (fun _ _ _ => true)
          (F.bitAdversary adversary n d) bit :=
  rfl

-- In each group, the single-group bound applies to the typed adversary of a bit adversary.
example (adversary : Encryption.Adversary) (n : ℕ) (d : F.Desc) :
    Experiment.advantage
        ((elGamal (F.order d) (F.generator d)).cpaExperiment (fun _ _ _ => true)
          (F.bitAdversary adversary n d) false)
        ((elGamal (F.order d) (F.generator d)).cpaExperiment (fun _ _ _ => true)
          (F.bitAdversary adversary n d) true) ≤
      ddhAdvantage (F.order d) (F.generator d)
          (elGamalToDDH (fun _ _ _ => true) (F.bitAdversary adversary n d) false) +
        ddhAdvantage (F.order d) (F.generator d)
          (elGamalToDDH (fun _ _ _ => true) (F.bitAdversary adversary n d) true) :=
  advantage_cpaExperiment_elGamal_le (F.smul_generator_surjective d) _ _

end Family

end CslibFrontierTests.Crypto.ElGamalFinite
