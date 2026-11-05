/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the PV statement exploration)

public import ComplexityTests.BoundedArithmetic.Statements

/-! Ordinary imports must retain executable equality for the certificate exploration. -/

open ComplexityTests.BoundedArithmetic Trim

example : FunctionSymbol.s1 ≠ (FunctionSymbol.trim : language.Functions 1) := by decide

example : s1 (.var 0 : language.Term (Fin 1)) ≠ trim (.var 0) := by decide

example : trimS1 = ({ lhs := trim (s1 (.var 0)), rhs := .var 0 } : Equation language 1) :=
  by decide

example : trimS1 ≠ ({ lhs := trim (s1 (.var 0)), rhs := s1 (.var 0) } : Equation language 1) :=
  by decide
