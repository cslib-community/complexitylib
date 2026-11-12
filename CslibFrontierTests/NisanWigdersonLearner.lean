/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson

/-! The Nisan–Wigderson reconstruction as a membership-query learner, on the design of two
disjoint singletons: a trial at the first position makes no queries, the query bound, and a weak
learner obtained from a dense test that avoids the generator of the constant function `false`. -/

namespace CslibFrontierTests.NisanWigdersonLearner

open Cslib Cslib.Crypto.PRG.NisanWigderson Cslib.MachineLearning.UniformLearning Cslib.Probability
  Finset

/-- The design of two disjoint singletons on two seed bits. -/
def D : Design 2 1 0 2 where
  block := ![{0}, {1}]
  card_block := by decide
  card_inter_le := by decide

/-- A test accepting the strings with a `true` bit. -/
def test (y : Fin 2 → Bool) : Bool := y 0 || y 1

/-- A trial predicting the first output bit reads no value of the target. -/
example (seed : Fin 2 → Bool) (bit : Bool) (pad : Fin 2 → Bool) :
    trialPoints D ⟨0, seed, bit, pad⟩ = [] := by
  simp [trialPoints]

/-- The learner makes at most `m 2 ^ a = 2` queries. -/
example : (nwLearner D (fun y => !test y)).QueriesAtMost 2 :=
  nwLearner_queriesAtMost D _

/-- The test accepts three quarters of all strings and no output of the generator of the constant
function `false`, so the learner built from its negation learns the class `{fun _ => false}` with
error `1 / 2 - 3 / 16` and confidence `3 / 16`. -/
example : (nwLearner D (fun y => !test y)).Learns (PMF.uniformOfFintype (Trial 2 2))
    {fun _ => false} (1 / 2 - 3 / 4 / (2 * 2)) (1 - 3 / 4 / (2 * 2)) := by
  have hcard : #{y : Fin 2 → Bool | test y = true} = 3 := by decide
  have h := nwLearner_learns_of_dens D test (C := {fun _ => false}) (δ := 3 / 4)
    (by rw [Finset.nnratCast_dens, hcard]; simp)
    (by rintro f rfl z; rfl)
  simpa using h

end CslibFrontierTests.NisanWigdersonLearner
