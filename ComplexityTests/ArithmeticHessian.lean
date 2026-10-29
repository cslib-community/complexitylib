/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Hessian
import Complexity.Computability.Circuit.Pi
import Mathlib.Algebra.Field.ZMod

/-!
# Arithmetic circuits and Hessian lower bounds

The mixed product attains the bound, including in characteristic two. Tests also cover shared
gates, outputs before unused gates, free input/output wiring, zero inputs, scalar multiplication,
and supplied affine inputs. A polynomial vanishing as a function over `ZMod 2` has a nonzero
Hessian, showing why formal-polynomial computation is essential.
-/

namespace ComplexityTests.ArithmeticHessian

open Cslib.Circuits MvPolynomial

private def product (K : Type*) : Circuit (arithSignature K) 2 1 :=
  Circuit.oneGate .mul id

private theorem hessian_product {K : Type*} [Field K] (x : Fin 2 → K) :
    hessian x (X 0 * X 1) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hessian]

private theorem rank_hessian_product {K : Type*} [Field K] (x : Fin 2 → K) :
    (hessian x (X 0 * X 1)).rank = 2 := by
  rw [hessian_product, Matrix.rank_of_isUnit]
  · rfl
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [Matrix.det_fin_two]

-- Formal-polynomial evaluation, value evaluation, and the sharp Hessian multiplication lower bound
-- for the two-variable product over every field (including characteristic two).
example {K : Type*} [Field K] (x : Fin 2 → K) (c : Circuit (arithSignature K) 2 1)
    (hc : c.eval (arithInterpretationWith K MvPolynomial.C) X 0 = X 0 * X 1) :
    (product K).eval (arithInterpretationWith K MvPolynomial.C) X 0 =
        (X 0 * X 1 : MvPolynomial (Fin 2) K) ∧
      MvPolynomial.eval x
        ((product K).eval (arithInterpretationWith K MvPolynomial.C) X 0) =
          (product K).eval (arithInterpretation K) x 0 ∧
      1 ≤ c.program.cost ArithOp.mulCost ∧
      (product (ZMod 2)).program.cost ArithOp.mulCost = 1 ∧
      (hessian (fun _ => (0 : ZMod 2)) (X (0 : Fin 2) * X 1)).rank = 2 :=
  ⟨by simp [product],
    (product K).eval_arithInterpretationWith_mvPolynomial id x 0,
    by simpa [rank_hessian_product] using c.hessian_rank_ceilDiv_two_le id (fun _ => 0) 0 _ hc,
    rfl,
    rank_hessian_product _⟩

-- One product is read twice by an addition. An unused constant follows both output gates.
private def sharedProduct : Circuit (arithSignature ℚ) 2 3 where
  size := 3
  program := (((Program.empty : Program (arithSignature ℚ) 2 0).gate ⟨.mul, Wire.input⟩).gate
    ⟨.add, fun _ => .gate 0⟩).gate ⟨.const 7, Fin.elim0⟩
  outputs := ![.gate 0, .gate 1, .input 0]

example (x : Fin 2 → ℚ) (j : Fin 3) :
    sharedProduct.program.cost ArithOp.mulCost = 1 ∧
      sharedProduct.eval (arithInterpretationWith ℚ MvPolynomial.C) X =
        ![X 0 * X 1, X 0 * X 1 + X 0 * X 1, (X 0 : MvPolynomial (Fin 2) ℚ)] ∧
      (hessian x (sharedProduct.eval (arithInterpretationWith ℚ MvPolynomial.C) X j)).rank ≤ 2 ∧
      (hessian x (sharedProduct.eval (arithInterpretationWith ℚ MvPolynomial.C) X 2)).rank = 0 ∧
      (hessian x ((Circuit.id (arithSignature ℚ) 2).eval
        (arithInterpretationWith ℚ MvPolynomial.C) X 0)).rank ≤ 0 :=
  ⟨rfl,
    by funext k; fin_cases k <;> rfl,
    sharedProduct.hessian_rank_le id x j,
    by change (hessian x (X 0)).rank = 0; simp,
    (Circuit.id (arithSignature ℚ) 2).hessian_rank_le id x 0⟩

-- Constants can be indexed by a different type, and a constant circuit needs no inputs.
private def constantCircuit : Circuit (arithSignature Bool) 0 1 :=
  Circuit.oneGate (.const true) Fin.elim0

-- Scalar multiplication is included in the chosen cost model.
private def scalarProduct : Circuit (arithSignature ℚ) 1 1 where
  size := 2
  program := ((Program.empty : Program (arithSignature ℚ) 1 0).gate ⟨.const 3, Fin.elim0⟩).gate
    ⟨.mul, ![.input 0, .gate 0]⟩
  outputs := fun _ => .gate 1

example (x₁ : Fin 1 → ℚ) (x₂ : Fin 2 → ℚ) :
    constantCircuit.eval
        (arithInterpretationWith Bool (fun b => MvPolynomial.C (if b then (7 : ℚ) else 0))) X 0 =
          MvPolynomial.C 7 ∧
      constantCircuit.program.cost ArithOp.mulCost = 0 ∧
      (hessian (Fin.elim0 : Fin 0 → ℚ) (MvPolynomial.C 7)).rank ⌈/⌉ 2 ≤
        constantCircuit.program.cost ArithOp.mulCost ∧
      scalarProduct.program.cost ArithOp.mulCost = 1 ∧
      scalarProduct.eval (arithInterpretation ℚ) x₁ 0 = x₁ 0 * 3 ∧
      (hessian x₂ ((Program.empty : Program (arithSignature ℚ) 1 0).trace
        (arithInterpretationWith ℚ MvPolynomial.C) (fun _ => X 0 + MvPolynomial.C 3)
          (.input 0))).rank ≤ 0 :=
  ⟨by simp [constantCircuit],
    rfl,
    constantCircuit.hessian_rank_ceilDiv_two_le (fun b => if b then 7 else 0) Fin.elim0 0 _ rfl,
    rfl,
    rfl,
    by apply Program.rank_hessian_trace_le (constant := id); intro i; simp⟩

private noncomputable def vanishingPolynomial : MvPolynomial (Fin 2) (ZMod 2) :=
  (X 0 ^ 2 - X 0) * X 1

example (x : Fin 2 → ZMod 2) :
    MvPolynomial.eval x vanishingPolynomial = 0 ∧
      (hessian x vanishingPolynomial).rank = 2 := by
  refine ⟨?_, ?_⟩
  · have h (a : ZMod 2) : a ^ 2 = a := by revert a; decide
    simp [vanishingPolynomial, h]
  · have h : hessian x vanishingPolynomial = !![0, 1; 1, 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [vanishingPolynomial, hessian, pow_two, ZModModule.add_self, ZModModule.neg_eq_self]
    rw [h, ← hessian_product x]
    exact rank_hessian_product x

end ComplexityTests.ArithmeticHessian
