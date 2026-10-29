/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Waring.Compilation
import Complexity.Computability.Circuit.Arithmetic.Waring

/-!
# Waring compilation clients

The main client shares a term, emits repeated and earlier outputs, preserves a supplied input,
and contains an unused term gate. A rational sum of two squares represents the squarefree
monomial and exercises both the compiler and the existing Waring term-count theorem.
-/

namespace ComplexityTests.WaringCompilation

open Cslib.Circuits

private def term : Waring.Term ℕ 2 := ⟨3, ![2, 5]⟩

private def source : Circuit (SumOfTerms.signature (Waring.Term ℕ 2)) 1 4 :=
  ⟨(((Program.empty : Program (SumOfTerms.signature (Waring.Term ℕ 2)) 1 0).gate
      ⟨.term term, Fin.elim0⟩).gate ⟨.add, fun _ => .gate 0⟩).gate ⟨.term term, Fin.elim0⟩,
    ![.gate 0, .gate 1, .gate 0, .input 0]⟩

-- Constant costs depend on their symbols, so omitting or conflating constants changes the total.
private def weight : ArithOp ℕ → ℕ
  | .add => 13
  | .mul => 11
  | .const c => c + 7

-- The unused term is still charged, the reused term is compiled only once, and constant weights
-- depend on their symbols.
example :
    (Waring.compile 0 1 source).size = 21 ∧
    (Waring.compile 0 1 source).program.cost ArithOp.mulCost = 8 ∧
    (Waring.compile 0 1 source).program.cost ArithOp.addCost = 5 ∧
    (Waring.compile 0 1 source).program.cost weight = 229 :=
  ⟨by rw [Waring.size_compile]; decide,
    by rw [Waring.mulCost_compile]; decide,
    by rw [Waring.addCost_compile]; decide,
    by rw [Waring.cost_program_compile]; decide⟩

/-- info: ([14283, 28566, 14283, 13], 21, 8, 5, 229) -/
#guard_msgs in
#eval let c := Waring.compile 0 1 source
  (List.ofFn (c.eval (arithInterpretation ℕ) ![7, 11, 13]), c.size,
    c.program.cost ArithOp.mulCost, c.program.cost ArithOp.addCost, c.program.cost weight)

-- The executable example also has a symbolic kernel proof for every semiring input.
example {R : Type*} [Semiring R] (x : Fin 2 → R) (y : Fin 1 → R) :
    (Waring.compile 0 1 source).eval (arithInterpretationWith ℕ Nat.cast) (Fin.append x y) =
      ![term.eval Nat.cast x, term.eval Nat.cast x + term.eval Nat.cast x,
        term.eval Nat.cast x, y 0] := by
  rw [Waring.eval_compile 0 1 Nat.cast (Nat.cast_zero) (Nat.cast_one)]
  ext j
  fin_cases j <;> rfl

-- Degree zero retains the initial zero, named one, scale constant and final multiplication.
private def degreeZero : Waring.Term ℕ 0 := ⟨5, Fin.elim0⟩

-- An incorrect interpretation of the named one invalidates degree-zero semantics.
private def badOne (c : ℕ) : ℕ := if c = 1 then 0 else c

private def degreeOne : Waring.Term ℕ 1 := ⟨3, fun _ => 2⟩

-- Linear forms, degree-zero and degree-one terms, Boolean symbols, and empty programs/wiring.
example (x : ℕ) (y : Fin 2 → ℕ) :
    (Formula.linearForm 0 ![2, 3, 5] ![1, 0, 1]).eval (arithInterpretation ℕ) ![7, 11] = 98 ∧
    (Formula.linearForm (n := 2) 0 ![2, 3, 5] ![1, 0, 1]).toCircuit.program.cost weight = 110 ∧
    (degreeZero.toCircuit 0 1).size = 4 ∧
    (degreeZero.toCircuit 0 1).program.cost ArithOp.mulCost = 1 ∧
    (degreeZero.toCircuit 0 1).program.cost ArithOp.addCost = 0 ∧
    (degreeZero.toCircuit 0 1).eval (arithInterpretation ℕ) Fin.elim0 0 = 5 ∧
    (degreeZero.toCircuit 0 1).eval (arithInterpretationWith ℕ badOne) Fin.elim0 0 = 0 ∧
    degreeZero.eval badOne Fin.elim0 = 5 ∧
    (degreeOne.toCircuit 0 1).size = 6 ∧
    (degreeOne.toCircuit 0 1).program.cost ArithOp.mulCost = 2 ∧
    ((⟨true, fun _ => true⟩ : Waring.Term Bool 1).toCircuit false true).eval
      (arithInterpretationWith Bool (fun b => if b then 1 else 0)) (fun _ => x) 0 = x ∧
    (Waring.compile 0 1
      (Circuit.wiring (SumOfTerms.signature (Waring.Term ℕ 3))
        (Fin.elim0 : Fin 0 → Fin 0))).size = 0 ∧
    (Waring.compile 0 1 (Circuit.id (SumOfTerms.signature (Waring.Term ℕ 0)) 2)).eval
      (arithInterpretation ℕ) y = y := by
  refine ⟨by decide,
    by rw [Formula.cost_toCircuit, Formula.cost_linearForm]; decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by rw [Waring.Term.eval_toCircuit false true _ rfl rfl]; simp [Waring.Term.eval],
    by decide, ?_⟩
  have h := Waring.eval_compile 0 1 id rfl rfl
    (Circuit.id (SumOfTerms.signature (Waring.Term ℕ 0)) 2) Fin.elim0 y
  simpa [Fin.elim0_append, arithInterpretation] using h

private def squarefree : Circuit (SumOfTerms.signature (Waring.Term ℚ 2)) 0 1 :=
  ⟨(((Program.empty : Program (SumOfTerms.signature (Waring.Term ℚ 2)) 0 0).gate
      ⟨.term ⟨1 / 4, ![1, 1]⟩, Fin.elim0⟩).gate
      ⟨.term ⟨-(1 / 4), ![1, -1]⟩, Fin.elim0⟩).gate ⟨.add, fun i => .gate i⟩,
    fun _ => .gate 2⟩

private theorem squarefree_polynomial :
    squarefree.eval (SumOfTerms.interpretation Waring.Term.polynomial) Fin.elim0 0 =
      ∏ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) ℚ) := by
  change (Waring.Term.polynomial ⟨(1 / 4 : ℚ), ![1, 1]⟩ +
    Waring.Term.polynomial ⟨-(1 / 4 : ℚ), ![1, -1]⟩) = _
  norm_num [Waring.Term.polynomial, Fin.sum_univ_two, Fin.prod_univ_two]
  have h : (MvPolynomial.C (1 / 4 : ℚ) : MvPolynomial (Fin 2) ℚ) * 4 = 1 := by
    have h := congrArg (MvPolynomial.C : ℚ → MvPolynomial (Fin 2) ℚ)
      (show (1 / 4 : ℚ) * 4 = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  calc
    _ = ((MvPolynomial.C (1 / 4 : ℚ) : MvPolynomial (Fin 2) ℚ) * 4) *
        (MvPolynomial.X 0 * MvPolynomial.X 1) := by ring
    _ = _ := by rw [h, one_mul]

-- The compiled arithmetic circuit computes the same formal polynomial, and the Waring lower-bound
-- API applies to `squarefree`.
example :
    (Waring.compile 0 1 squarefree).eval
      (arithInterpretationWith ℚ MvPolynomial.C) MvPolynomial.X 0 =
        ∏ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) ℚ) ∧
    2 ≤ squarefree.program.cost SumOfTerms.termCost :=
  ⟨by rw [Waring.polynomial_compile]; exact squarefree_polynomial,
    Waring.choose_le_cost squarefree 1 0 squarefree_polynomial⟩

end ComplexityTests.WaringCompilation
