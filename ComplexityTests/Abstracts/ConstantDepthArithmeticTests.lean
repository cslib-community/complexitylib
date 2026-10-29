/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.ConstantDepthArithmeticAbstract

/-! # Concrete clients and non-vacuity checks for the constant-depth arithmetic abstract

Verifies that the public definitions of `ConstantDepthArithmeticAbstract` are the library's
(`SPCircuit.polynomial`, `SPCircuit.productDepth`, `SPCircuit.IsSimple`, `imm`), that
`IMM_{1,1}` is the variable `(0, 0, 0)`, and that the hypotheses of the headline are satisfiable:
the gate-free circuit reading its single input is simple, of product-depth zero, and computes
`IMM_{1,1}` with its one variable in bijection with the input. The headline is instantiated at
`Δ = 2` and `c = 3`.
-/

namespace ComplexityTests.Abstracts.ConstantDepthArithmeticTests

open ComplexityAbstracts.ConstantDepthArithmeticAbstract
open Cslib.Circuits Cslib.Circuits.Arithmetic

variable {K : Type*} {N : ℕ}

example [CommSemiring K] (C : ArithCircuit K N) : polynomial C = SPCircuit.polynomial C :=
  rfl

example (C : ArithCircuit K N) : productDepth C = SPCircuit.productDepth C :=
  rfl

example (C : ArithCircuit K N) : IsSimple C ↔ SPCircuit.IsSimple C :=
  Iff.rfl

example [CommSemiring K] (n d : ℕ) [NeZero n] :
    ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm K n d =
      Cslib.Circuits.Arithmetic.imm K n d :=
  rfl

/-- `IMM_{1,1}` is its single variable. -/
example : ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm ℚ 1 1 =
    MvPolynomial.X (0, 0, 0) := by
  simp [ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm]

/-- The gate-free circuit reading its single input. -/
private def readInput : ArithCircuit ℚ 1 :=
  Circuit.wiring _ fun _ => 0

example : IsSimple readInput := fun g => g.elim0

example : productDepth readInput = 0 :=
  rfl

/-- The bijection between the input and the variable of `IMM_{1,1}`. -/
private def e₁ : Fin 1 ≃ Fin 1 × Fin 1 × Fin 1 where
  toFun _ := (0, 0, 0)
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- It computes `IMM_{1,1}`. -/
example : MvPolynomial.rename e₁ (polynomial readInput) =
    ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm ℚ 1 1 := by
  simp [polynomial, readInput, e₁,
    ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm]

/-- The headline at product-depth two and exponent three. -/
example : ∀ᶠ n in Filter.atTop, ∀ [NeZero n] {N : ℕ}
    (e : Fin N ≃ Fin (Nat.log 2 (Nat.log 2 n)) × Fin n × Fin n) (C : ArithCircuit ℚ N),
    IsSimple C → productDepth C ≤ 2 →
    MvPolynomial.rename e (polynomial C) =
      ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm ℚ n (Nat.log 2 (Nat.log 2 n)) →
    n ^ 3 < C.size :=
  superpolynomial ℚ 2 3

end ComplexityTests.Abstracts.ConstantDepthArithmeticTests
