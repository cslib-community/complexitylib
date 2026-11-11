/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.NonadaptiveCircuit.Oracle

/-!
# Tests: non-adaptive learners computed by circuits

A toy learner on `n` bits that queries the target at one point `p`, fixed by the seed, and outputs
the constant hypothesis equal to the answer. Its circuit is a projection onto the answer wire, with
no gates. So it has a circuit with one query and no gates, every hypothesis has at most two gates,
and, on every seed, an oracle circuit with three gates, one of them an oracle gate, computes the
hypothesis.
-/

namespace CslibFrontierTests.NonadaptiveCircuit

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MachineLearning.UniformLearning

variable {n : ℕ}

/-- Query the seed's point `p` and output the constant hypothesis equal to the answer. -/
private def answerLearner : QueryLearner (Fin n) (BitString n) :=
  QueryLearner.ofNonadaptive (fun p => [p]) fun f p _ => f p

private theorem hasCircuit_answerLearner : (answerLearner (n := n)).HasCircuit 1 0 :=
  QueryLearner.hasCircuit_ofNonadaptive
    (fun p g g' h => funext fun _ => h p (List.mem_singleton_self p))
    fun p => ⟨fun _ => p, fun z => z (Fin.castAdd n 0),
      le_of_eq (complexity_wiring (I := interpretation) fun _ => Fin.castAdd n 0),
      fun f x => by simp⟩

/-- Every hypothesis of the toy learner has at most two gates. -/
example (f : BooleanFunction n) (p : BitString n) :
    complexity interpretation (single ((answerLearner p).eval f)) ≤ 2 :=
  hasCircuit_answerLearner.complexity_eval_le f p

/-- A larger size bound also holds. -/
example : (answerLearner (n := n)).HasCircuit 1 5 :=
  hasCircuit_answerLearner.mono (by norm_num)

/-- Padding to three queries keeps the size. -/
example : (answerLearner (n := n)).HasCircuit 3 0 :=
  hasCircuit_answerLearner.pad (by norm_num)

/-- On every seed, an oracle circuit with at most three gates, exactly one of them an oracle gate,
computes the toy learner's hypothesis under every oracle whose slice at `n` is the target. -/
example (p : BitString n) :
    ∃ C : Circuit oracleSignature n 1,
      C.size ≤ 3 ∧ C.program.cost OracleOp.queryWeight = 1 ∧
        C.depthWith OracleOp.queryWeight ≤ 1 ∧
          ∀ (O : Language Bool) (f : BooleanFunction n), O.slice n = f →
            ∀ x, C.eval (oracleInterpretation O) x 0 = (answerLearner p).eval f x := by
  obtain ⟨C, hs, hc, hd, -, hev⟩ := hasCircuit_answerLearner.exists_oracleCircuit p
  exact ⟨C, hs, hc, hd, hev⟩

end CslibFrontierTests.NonadaptiveCircuit
