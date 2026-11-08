/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Arithmetic.EvaluationTime
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime
import CslibFrontier.Computability.Probabilistic.Sampling.F4

/-! Uniform arithmetic traces, canonical typed agreement and total malformed-code clients. -/

namespace ComplexityTests.ArithmeticCodeEvaluation

open Cslib Cslib.Circuits Turing.MultiTapeTM

private abbrev F := QuadraticAlgebra (ZMod 2) 1 1
private def theta : F := ⟨0, 1⟩
private abbrev eGate := Circuit.encGate (ArithOp.encoding F4.encoding)

-- One certificate takes the entire varying gate list and input as data.
example : ComputableInPolyTime
    (fun p : List F × List (ArithOp F × List ℕ) =>
      evalCode (arithInterpretation F) 0 p.1 p.2)
    (encPair (encList F4.encoding) (encList eGate)) (encList F4.encoding) :=
  Arithmetic.computableInPolyTime_evalCode (.fst _ _) (.snd _ _)

-- A runtime-length family actually executes all gates, including repeated/shared inputs.
example : ComputableInPolyTime (fun k : ℕ =>
    evalCode (arithInterpretation F) 0 [theta] (List.replicate k (.mul, [0, 0])))
    encUnary (encList F4.encoding) :=
  Arithmetic.computableInPolyTime_evalCode (.const _)
    (ComputableInPolyTime.replicate .id' (.const _))

example (k : ℕ) : evalCode (arithInterpretation F) 0 [theta]
    (List.replicate k (.mul, [0, 0])) = theta :: List.replicate k (theta + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', evalCode_append_singleton, ih]
    have htheta : theta * theta = theta + 1 := by decide
    simp [arithInterpretation, arithInterpretationWith, htheta, List.replicate_succ']

-- The semantic bridge is uniform in the typed program and its input, not a constant circuit.
example {n k : ℕ} (p : Program (arithSignature F) n k) (x : Fin n → F) :
    evalCode (arithInterpretation F) 0 (List.ofFn x) p.code =
      List.ofFn x ++ List.ofFn (p.eval (arithInterpretation F) x) :=
  p.evalCode_code _ _ _

example {n m : ℕ} (c : Circuit (arithSignature F) n m) (x : Fin n → F) (j : Fin m) :
    c.eval (arithInterpretation F) x j =
      (evalCode (arithInterpretation F) 0 (List.ofFn x) c.code.1).getD
        (c.outputs j).toNat 0 :=
  c.eval_eq_getD _ _ _ _

-- Constant, addition and multiplication gates, sharing a previously computed wire.
example : evalCode (arithInterpretation F) 0 [theta]
    [(.mul, [0, 0]), (.add, [1, 0]), (.const theta, []), (.mul, [2, 3])] =
      [theta, theta + 1, 1, theta, theta] := by decide

example : ArithOp.encoding F4.encoding .add ≠ ArithOp.encoding F4.encoding (.const 0) :=
  by decide
example : Program.IsCodeFrom (arithSignature F) 1 0 [(.mul, [0, 0])] := by decide
example : ¬ Program.IsCodeFrom (arithSignature F) 1 0 [(.mul, [0])] := by decide
example : ¬ Program.IsCodeFrom (arithSignature F) 1 0 [(.add, [2 ^ 100, 0])] := by decide

-- A huge binary index reads the default without allocating that many wire slots.
example : evalCode (arithInterpretation F) 0 [theta]
    [(.add, [2 ^ 100, 0])] = [theta, theta] := by decide
example : evalCode (arithInterpretation F) 0 [theta] [(.mul, [0])] = [theta, 0] := by decide
example : evalCode (arithInterpretation F) 0 [theta]
    [(.mul, [0, 0, 2 ^ 100])] = [theta, theta + 1] := by decide
example : evalCode (arithInterpretation F) 0 [] [] = [] := rfl
example : evalCode (arithInterpretation F) 0 [] [(.const theta, [2 ^ 100])] = [theta] := by decide

-- Binary output lookup is charged by its encoding length even beyond the trace.
example : ComputableInPolyTime
    (fun p : (List F × List (ArithOp F × List ℕ)) × ℕ =>
      (evalCode (arithInterpretation F) 0 p.1.1 p.1.2).getD p.2 0)
    (encPair (encPair (encList F4.encoding) (encList eGate)) encNat) F4.encoding :=
  Arithmetic.computableInPolyTime_evalOutput ((ComputableInPolyTime.fst _ _).fst')
    ((ComputableInPolyTime.fst _ _).snd') (.snd _ _)

-- Existing Boolean clients retain the same publicly available generic evaluator and law.
example (x : Fin 1 → Bool) (c : Circuit Boolean.signature 1 1) :
    c.eval Boolean.interpretation x 0 =
      (evalCode Boolean.interpretation false (List.ofFn x) c.code.1).getD
        (c.outputs 0).toNat false := c.eval_eq_getD _ _ _ _

end ComplexityTests.ArithmeticCodeEvaluation
