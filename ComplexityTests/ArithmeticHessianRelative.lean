/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Pairing
import Mathlib.Algebra.Field.ZMod

/-!
# Supplied polynomial inputs and bilinear pairing

A polynomial helper with nonzero Hessian can be exposed for free. Its Hessian must therefore be
removed before applying a multiplication bound. Tests cover copying and reusing such helpers,
raw variables alongside helpers, a genuine multiplication of supplied inputs, and sharp pairing
circuits over arbitrary fields and explicitly in characteristic two.
-/

namespace ComplexityTests.ArithmeticHessianRelative

open Cslib.Circuits MvPolynomial

private noncomputable def helper : MvPolynomial (Fin 2) ℚ := X 0 * X 1

private def reuseHelper : Circuit (arithSignature ℚ) 1 1 := Circuit.oneGate .add ![0, 0]

-- Raw variables and the nonlinear helper are supplied together; both outputs select the helper.
private def helperOutputs : Circuit (arithSignature ℚ) (2 + 1) 2 :=
  Circuit.wiring _ ![2, 2]

-- A nonzero-rank input can be copied or reused with no multiplication; the Hessian residual bound
-- removes the supplied helper's Hessian while still charging subsequent multiplications.
example {K : Type*} [Field K] (point : Fin 2 → ℚ) (j : Fin 2) (pointK : Fin 3 → K)
    (p q : MvPolynomial (Fin 3) K) :
    (hessian (fun _ => (0 : ℚ)) helper).rank = 2 ∧
      (Circuit.id (arithSignature ℚ) 1).program.cost ArithOp.mulCost = 0 ∧
      (∃ a : Fin 1 → ℚ,
        (hessian point helper - ∑ i, a i • hessian point helper).rank ≤ 0) ∧
      (hessian point helper - ∑ _i : Fin 1, (1 : ℚ) • hessian point helper).rank = 0 ∧
      (∃ a : Fin 1 → ℚ,
        (hessian point (helper + helper) - ∑ i, a i • hessian point helper).rank ≤ 0) ∧
      (hessian point (helper + helper) -
        ∑ _i : Fin 1, (2 : ℚ) • hessian point helper).rank = 0 ∧
      (∃ a : Fin 1 → ℚ,
        (hessian point helper - ∑ i, a i • hessian point helper).rank ≤ 0) ∧
      ∃ a : Fin 2 → K,
        (hessian pointK (p * q) - ∑ i, a i • hessian pointK (![p, q] i)).rank ≤ 2 := by
  refine ⟨?_, rfl,
    (Circuit.id (arithSignature ℚ) 1).exists_hessian_residual id point (fun _ => helper) 0
      helper rfl,
    by simp,
    reuseHelper.exists_hessian_residual id point (fun _ => helper) 0 _ rfl,
    by simp [two_smul],
    ?_,
    (Circuit.oneGate (n := 2) (.mul : ArithOp K) id).exists_hessian_residual
      id pointK ![p, q] 0 (p * q) rfl⟩
  · have h : hessian (fun _ => (0 : ℚ)) helper = !![0, 1; 1, 0] := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp [helper, hessian]
    rw [h, Matrix.rank_of_isUnit]
    · rfl
    · rw [Matrix.isUnit_iff_isUnit_det]
      simp [Matrix.det_fin_two]
  · apply helperOutputs.exists_helper_hessian_residual id point (fun _ => helper) j helper
    fin_cases j <;> rfl

-- Two products, one addition and an unused constant. One output predates the other product.
private def pairingCircuit (K : Type*) [Zero K] : Circuit (arithSignature K) (2 + 2) 2 where
  size := 4
  program := ((((Program.empty : Program (arithSignature K) 4 0).gate
    ⟨.mul, ![.input 0, .input 2]⟩).gate ⟨.mul, ![.input 1, .input 3]⟩).gate
      ⟨.add, ![.gate 0, .gate 1]⟩).gate ⟨.const 0, Fin.elim0⟩
  outputs := ![.gate 2, .gate 0]

private theorem pairingCircuit_computes {K : Type*} [Field K] :
    (pairingCircuit K).eval (arithInterpretationWith K MvPolynomial.C)
      (Fin.append (fun i => X (Sum.inl i)) (fun i => X (Sum.inr i))) 0 =
        ∑ i : Fin 2, X (Sum.inl i) * X (Sum.inr i) := by
  change X (Sum.inl (0 : Fin 2)) * X (Sum.inr (0 : Fin 2)) +
    X (Sum.inl (1 : Fin 2)) * X (Sum.inr (1 : Fin 2)) = _
  simp [Fin.sum_univ_two]

-- The empty pairing is the constant zero and has zero multiplication cost.
private def emptyPairing : Circuit (arithSignature ℚ) (0 + 0) 1 :=
  Circuit.oneGate (.const 0) Fin.elim0

example {K : Type*} [Field K] :
    (pairingCircuit K).program.cost ArithOp.mulCost = 2 ∧
      2 ≤ (pairingCircuit K).program.cost ArithOp.mulCost ∧
      2 ≤ (pairingCircuit (ZMod 2)).program.cost ArithOp.mulCost ∧
      emptyPairing.program.cost ArithOp.mulCost = 0 ∧
      0 ≤ emptyPairing.program.cost ArithOp.mulCost :=
  ⟨rfl,
    (pairingCircuit K).pairing_le_mulCost id 0 pairingCircuit_computes,
    (pairingCircuit (ZMod 2)).pairing_le_mulCost id 0 pairingCircuit_computes,
    rfl,
    by apply emptyPairing.pairing_le_mulCost id 0; simp [emptyPairing]⟩

end ComplexityTests.ArithmeticHessianRelative
