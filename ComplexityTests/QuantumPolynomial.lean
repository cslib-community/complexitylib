/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.Polynomial
import Complexity.Computability.Circuit.Quantum.Basic

/-! The polynomial method: a one-query algorithm that reads its input bit exactly, so the
hypotheses of the lower bounds are satisfiable by a non-constant function. -/

namespace ComplexityTests.QuantumPolynomial

open Cslib Cslib.Quantum Cslib.BitString Cslib.QueryComplexity

/-- With one query index and a trivial workspace, a basis state is determined by its control bit. -/
def ctrl : Fin 1 × Bool × Unit ≃ Bool :=
  (Equiv.uniqueProd (Bool × Unit) (Fin 1)).trans (Equiv.prodUnique Bool Unit)

/-- The Hadamard gate on the control bit. -/
noncomputable def hadamardCtrl : State 1 Unit →ₗᵢ[ℂ] State 1 Unit :=
  (unitaryEquiv ⟨Gate.hadamardMatrix.submatrix ctrl ctrl,
    Matrix.submatrix_equiv_mem_unitary.mpr Gate.hadamardMatrix_mem_unitaryGroup⟩).toLinearIsometry

/-- The one-query algorithm `H O_x H |0, 0⟩`, which ends in `|0, x₀⟩`. -/
noncomputable def readBit : ℕ → State 1 Unit →ₗᵢ[ℂ] State 1 Unit := fun _ => hadamardCtrl

/-- The initial state `|0, 0, ()⟩`. -/
noncomputable def ψ₀ : State 1 Unit := ket (0, false, ())

theorem norm_ψ₀ : ‖ψ₀‖ = 1 := norm_ket _

/-- The accepting outcome: control bit `1`. -/
def accept : Finset (Fin 1 × Bool × Unit) := {(0, true, ())}

private theorem inv_sqrt_two_mul_self : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- The algorithm accepts with probability exactly `x₀`. -/
theorem measureProb_readBit (x : Fin 1 → Bool) :
    measureProb (run readBit ψ₀ x 1) accept = bitVal ℝ (x 0) := by
  have hamp : (run readBit ψ₀ x 1).ofLp (0, true, ()) = bitVal ℂ (x 0) := by
    simp only [run, readBit, hadamardCtrl, LinearIsometryEquiv.coe_toLinearIsometry,
      unitaryEquiv_apply, Matrix.mulVec, dotProduct, phaseOracle_apply, ψ₀, ket_apply,
      Fintype.sum_prod_type, Fin.sum_univ_one, Fintype.sum_bool, Fintype.univ_unit,
      Finset.sum_singleton, Matrix.submatrix_apply, ctrl, Equiv.trans_apply,
      Equiv.uniqueProd_apply, Equiv.prodUnique_apply, Gate.hadamardMatrix]
    cases x 0
    · simp [bitVal]
    · simp only [Bool.and_self, ↓reduceIte, Complex.ofReal_inv, neg_mul, one_mul, Fin.isValue,
        Prod.mk.injEq, Bool.true_eq_false, and_true, and_false, mul_zero, Bool.and_false,
        Bool.false_eq_true, mul_one, zero_add, mul_neg, neg_neg, Bool.and_true, bitVal]
      linear_combination 2 * inv_sqrt_two_mul_self
  rw [measureProb, accept, Finset.sum_singleton, hamp]
  cases x 0 <;> simp [bitVal]

/-- The algorithm computes the disjunction of one bit exactly. -/
theorem measureProb_readBit_threshold (x : Fin 1 → Bool) :
    measureProb (run readBit ψ₀ x 1) accept = bitVal ℝ (threshold 1 1 x) := by
  rw [measureProb_readBit]
  congr 1
  cases hx : x 0 <;> simp [threshold, weight, hx, Finset.filter_singleton]

-- The exact and bounded-error bounds apply to it.
example : degree (threshold 1 1) ≤ 2 * 1 :=
  degree_le_two_mul readBit ψ₀ 1 accept measureProb_readBit_threshold

example : blockSensitivity (threshold 1 1) ≤ 8 * 1 ^ 2 :=
  blockSensitivity_le_eight_mul_sq readBit ψ₀ 1 accept measureProb_readBit_threshold

example : 1 ≤ 16 * 1 ^ 2 :=
  card_le_sixteen_mul_sq_of_threshold_one_right readBit norm_ψ₀ 1 accept fun x => by
    rw [measureProb_readBit_threshold]
    norm_num

-- With one bit, parity is the bit itself, so the algorithm also computes parity exactly.
example : 1 ≤ 2 * 1 :=
  card_le_two_mul_of_parity readBit ψ₀ 1 accept fun x => by
    rw [measureProb_readBit]
    congr 1
    cases hx : x 0 <;> simp [parity, hx]

-- The acceptance probability of any algorithm is a polynomial of degree at most `2T`.
example (W : Type) [Fintype W] (U : ℕ → State 3 W →ₗᵢ[ℂ] State 3 W) (ψ : State 3 W)
    (S : Finset (Fin 3 × Bool × W)) :
    (fun x => measureProb (run U ψ x 2) S) ∈ lowDegree ℝ (Fin 3) 4 :=
  measureProb_run_mem_lowDegree U ψ 2 S

end ComplexityTests.QuantumPolynomial
