/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters

/-! # Transfer of the matrix multiplication exponent bound

Pattern A: the product predicate and admissible-exponent set are unfolded to their ordinary
circuit/evaluation quantifiers. Only proofs refer to the implementation's exponent definitions.
-/

namespace ComplexityAbstracts.MatrixMultiplicationBridge

open Cslib.Circuits

/-- Split the requested slack between the admissible exponent and its own positive slack. -/
theorem circuits_nine_quarters (K : Type*) [Field K] [CharZero K] (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
        (∀ A B : Matrix (Fin n) (Fin n) K,
          C.eval (arithInterpretation K)
              (Fin.append
                (fun t => A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
                (fun t => B (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) =
            (fun t => (A * B) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) ∧
        (C.size : ℝ) ≤ c * (n : ℝ) ^ ((9 : ℝ) / 4 + γ) := by
  have h := Arithmetic.MatrixMultiplication.admissibleExponent_nine_quarters K
    (τ := 9 / 4 + γ / 2) (by linarith)
  have hsum : (9 : ℝ) / 4 + γ / 2 + γ / 2 = 9 / 4 + γ := by ring
  obtain ⟨c, hc, hC⟩ := h (γ / 2) (by linarith)
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨C, hcorrect, hsize⟩ := hC n hn
  exact ⟨C, hcorrect, hsum ▸ hsize⟩

/-- Transfer the infimum bound over the unfolded admissible-exponent set. -/
theorem exponent_le_nine_quarters (K : Type*) [Field K] [CharZero K] :
    sInf {τ : ℝ | ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
        (∀ A B : Matrix (Fin n) (Fin n) K,
          C.eval (arithInterpretation K)
              (Fin.append
                (fun t => A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)
                (fun t => B (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) =
            (fun t => (A * B) (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2)) ∧
        (C.size : ℝ) ≤ c * (n : ℝ) ^ (τ + ε)} ≤ 9 / 4 :=
  Arithmetic.MatrixMultiplication.omega_le_nine_quarters K

end ComplexityAbstracts.MatrixMultiplicationBridge
