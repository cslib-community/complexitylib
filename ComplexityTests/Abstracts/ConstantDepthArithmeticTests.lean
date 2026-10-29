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
`IMM_{1,1}` is the variable `(0, 0, 0)`, and that the hypotheses of the headline are satisfiable
at every size: for all `n ≥ 1` and `d`, the circuit of the sum over paths is simple, of
product-depth one, and computes `IMM_{n,d}` with its variables in bijection with the inputs
(`Cslib.Circuits.Arithmetic.SPCircuit.exists_isSimple_imm`); at `n = d = 2` that circuit has `9`
gates on `8` inputs.
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

/-- The hypotheses of the headline are satisfiable at every size: for every `n ≥ 1`, `d` and
product-depth `Δ ≥ 1`, the circuit of the sum over paths is simple, of product-depth at most `Δ`,
and computes `IMM_{n,d}` with its variables in bijection with the inputs. -/
example (K : Type*) [Field K] (n d Δ : ℕ) [NeZero n] (hΔ : 1 ≤ Δ) :
    ∃ (N : ℕ) (e : Fin N ≃ Fin d × Fin n × Fin n) (C : ArithCircuit K N),
      IsSimple C ∧ productDepth C ≤ Δ ∧
        MvPolynomial.rename e (polynomial C) =
          ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm K n d := by
  obtain ⟨C, simple, depth, -, computes⟩ := SPCircuit.exists_isSimple_imm K n d
  exact ⟨_, immVarEquiv n d, C, simple, depth.trans hΔ, computes⟩

/-- At `n = d = 2`, the sum over paths is a simple circuit of `9` gates on `8` inputs computing
`IMM_{2,2}`. -/
example : ∃ C : ArithCircuit ℚ 8, IsSimple C ∧ productDepth C ≤ 1 ∧ C.size = 9 ∧
    MvPolynomial.rename (immVarEquiv 2 2) (polynomial C) =
      ComplexityAbstracts.ConstantDepthArithmeticAbstract.imm ℚ 2 2 := by
  obtain ⟨C, simple, depth, size, computes⟩ := SPCircuit.exists_isSimple_imm ℚ 2 2
  exact ⟨C, simple, depth, size, computes⟩

end ComplexityTests.Abstracts.ConstantDepthArithmeticTests
