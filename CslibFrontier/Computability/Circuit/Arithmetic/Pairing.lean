/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Hessian
import Mathlib.Data.Fintype.Sum

/-!
# Multiplication lower bound for bilinear pairing

The polynomial `∑ i, xᵢ * yᵢ` has a block-swap Hessian of rank `2*n`. Every arithmetic circuit
computing it therefore needs at least `n` multiplications. This holds over every field, including
characteristic two, with arbitrary constant symbols, negative coefficients and cancellation.
Constants, additions and wiring are free. Scalar multiplications are charged.

The two variable blocks are supplied as `Fin.append` of the corresponding formal variables.
The premise is equality of formal polynomials, not agreement of functions over a finite field.

## Main results

* `Cslib.Circuits.Circuit.pairing_le_mulCost`: each paired coordinate requires a multiplication.

## References

* Ported from LowerBound/Fusion/Arithmetic/Interaction/Hessian/Pairing.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

public section

namespace Cslib.Circuits

open MvPolynomial

/-- Computing the formal bilinear pairing requires one multiplication per paired coordinate.
The conclusion bounds multiplication count, so also bounds total gate count. -/
theorem Circuit.pairing_le_mulCost {C K : Type*} [Field K] {n m : ℕ}
    (c : Circuit (arithSignature C) (n + n) m) (constant : C → K) (j : Fin m)
    (hcompute : c.eval (arithInterpretationWith C (MvPolynomial.C ∘ constant))
      (Fin.append (fun i => X (Sum.inl i)) (fun i => X (Sum.inr i))) j =
        ∑ i : Fin n, X (Sum.inl i) * X (Sum.inr i)) :
    n ≤ c.program.cost ArithOp.mulCost := by
  have hinput (i : Fin (n + n)) : hessian (fun _ : Fin n ⊕ Fin n => (0 : K))
      (Fin.append (fun j => X (Sum.inl j)) (fun j => X (Sum.inr j)) i) = 0 := by
    induction i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right, hessian_X]
  have h := c.program.rank_hessian_trace_le constant (fun _ : Fin n ⊕ Fin n => (0 : K))
    (Fin.append (fun i => X (Sum.inl i)) (fun i => X (Sum.inr i)))
    hinput (c.outputs j)
  change (hessian _ (c.eval _ _ j)).rank ≤ _ at h
  rw [hcompute, hessian_sum_X_mul_X, Matrix.rank_submatrix, Matrix.rank_one] at h
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  lia

end Cslib.Circuits
