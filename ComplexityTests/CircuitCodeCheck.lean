/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Encoding.Check
import Complexity.Computability.Circuit.Boolean.Encoding.Certificate
import Complexity.Computability.Probabilistic.Sampling.F4

/-! Generic binary-arity validation and its arithmetic/Boolean consumers. -/

namespace ComplexityTests.CircuitCodeCheck

open Cslib Cslib.Circuits Turing.MultiTapeTM

private abbrev F := QuadraticAlgebra (ZMod 2) 1 1
private abbrev eGate := Circuit.encGate (ArithOp.encoding F4.encoding)

-- The entire runtime gate list, including constants and binary arguments, is charged.
example : ComputableInPolyTime
    (fun p : ℕ × List (ArithOp F × List ℕ) => codeCheck (arithSignature F) p.1 p.2)
    (encPair encUnary (encList eGate)) encBool :=
  Arithmetic.computableInPolyTime_codeCheck (.fst _ _) (.snd _ _)

-- A varying number of repeated multiplication gates remains valid.
example (k : ℕ) : codeCheck (arithSignature F) 1
    (List.replicate k (.mul, [0, 0])) = true := by
  apply codeCheck_eq_true_iff.mpr
  apply Program.isCodeFrom_of_getElem
  intro j hj
  simp [arithSignature]

example : codeCheck (arithSignature F) 1
    [(.mul, [0, 0]), (.add, [1, 0]), (.const 1, []), (.mul, [2, 3])] = true := by decide
example : codeCheck (arithSignature F) 1 [(.mul, [0])] = false := by decide
example : codeCheck (arithSignature F) 1 [(.mul, [0, 0, 0])] = false := by decide
example : codeCheck (arithSignature F) 1 [(.add, [1, 0])] = false := by decide
example : codeCheck (arithSignature F) 1 [(.add, [2 ^ 100, 0])] = false := by decide
example : codeCheck (arithSignature F) 0 [(.const 1, [])] = true := by decide
example : codeCheck (arithSignature F) 0 [] = true := rfl

-- Every canonical typed program passes the same generic checker.
example {σ : Signature} {n k : ℕ} (p : Program σ n k) :
    codeCheck σ n p.code = true := by
  apply codeCheck_eq_true_iff.mpr
  rw [← Program.isSome_ofCode_iff, Program.ofCode_code]
  rfl

-- Operators can themselves be binary arities: no finite carrier or unary-arity assumption.
private abbrev variableArity : Signature where
  Op := ℕ
  Arity := id

example : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × List ℕ) => codeCheck variableArity p.1 p.2)
    (encPair encUnary (encList (Circuit.encGate encNat))) encBool :=
  Circuits.computableInPolyTime_codeCheck (σ := variableArity) (.id') (.fst _ _) (.snd _ _)

example : codeCheck variableArity 0 [(2 ^ 100, [])] = false := by decide
example : codeCheck variableArity 1 [(3, [0, 0, 0])] = true := by decide
example : codeCheck variableArity 1 [(2, [0, 0, 0])] = false := by decide
example : codeCheck variableArity 1 [(2, [0])] = false := by decide
example : codeCheck variableArity 1 [(0, []), (2, [0, 1])] = true := by decide

-- Boolean certificate clients publicly import the moved checker and keep their finite-arity
-- specialization, now without a separate Boolean validity definition.
example : ComputableInPolyTime
    (fun p : ℕ × List (Boolean.Op × List ℕ) => codeCheck Boolean.signature p.1 p.2)
    (encPair encUnary (encList Boolean.encGate)) encBool :=
  Boolean.computableInPolyTime_codeCheck (.fst _ _) (.snd _ _)

end ComplexityTests.CircuitCodeCheck
