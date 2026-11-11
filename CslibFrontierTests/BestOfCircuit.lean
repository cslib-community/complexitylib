/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.BestOf.Circuit

/-!
# Tests: best-of-`k` selection by circuits

A toy learner on `n` bits queries the target at the seed's point and outputs the constant
hypothesis equal to the answer; it has a circuit with one query and no gates. Best-of-`3`
selection on `2` sample points then has a circuit with `5` queries and at most `4279` gates, and
so each of its hypotheses has at most `4281` gates. A selection with tied agreement counts returns
the first run.
-/

namespace CslibFrontierTests.BestOfCircuit

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

/-- Best-of-`k` selection of the toy learner on `t` sample points has a circuit with `k + t`
queries. -/
example (k t : ℕ) [NeZero k] :
    (QueryLearner.bestOf (answerLearner (n := n)) k t).HasCircuit (k * 1 + t)
      (k * ((t + 1) * (0 + 469)) + (k - 1) * (8 * (Nat.clog 2 (t + 1) + 1) + 5)) :=
  QueryLearner.hasCircuit_bestOf hasCircuit_answerLearner

/-- With `3` runs and `2` sample points: `5` queries and at most `3 · 3 · 469 + 2 · 29 = 4279`
gates, since `⌈log₂ 3⌉ = 2`. -/
private theorem hasCircuit_bestOf_three_two :
    (QueryLearner.bestOf (answerLearner (n := n)) 3 2).HasCircuit 5 4279 := by
  have h3 : Nat.clog 2 3 = 2 := by
    rw [Nat.clog_of_two_le (by norm_num) (by norm_num), Nat.clog_eq_one le_rfl le_rfl]
  simpa [h3] using QueryLearner.hasCircuit_bestOf (k := 3) (t := 2) hasCircuit_answerLearner

/-- Every hypothesis of that selection has at most `4281` gates. -/
example (f : BooleanFunction n) (s : (Fin 3 → BitString n) × (Fin 2 → BitString n)) :
    complexity interpretation (single ((QueryLearner.bestOf answerLearner 3 2 s).eval f)) ≤
      4281 :=
  hasCircuit_bestOf_three_two.complexity_eval_le f s

/-- Ties go to the first run: among two equal hypotheses, the first is selected. -/
example (g h : BooleanFunction n) (x : Fin 2 → BitString n) :
    QueryLearner.selectBest g ![h, h] x = 0 := by
  have key := QueryLearner.agreeCount_lt_selectBest g ![h, h] x (j := 0)
  generalize QueryLearner.selectBest g ![h, h] x = s at key ⊢
  fin_cases s
  · rfl
  · simp at key

end CslibFrontierTests.BestOfCircuit
