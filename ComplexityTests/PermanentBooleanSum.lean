/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Permanent.BooleanSum
import Complexity.Foundations.Data.Matrix.Permanent
import Mathlib.Algebra.Field.ZMod

/-!
# Single-entry selector elimination clients

The selector in `!![b, X₁; X₂, X₃]` is summed over `b = 0, 1`; it gives `2X₁X₂ + X₃`.
On entries `3,5,7` this is `37`. Both the rational half and the half `2` in `ZMod 3` satisfy
the construction's hypothesis, while no half exists in `ZMod 2`.
-/

namespace ComplexityTests.PermanentBooleanSum

open Cslib Cslib.Circuits Cslib.Circuits.Arithmetic MvPolynomial

private noncomputable def selectorPolynomial (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin (4 + 1)) K :=
  projection ![Sum.inl 4, .inl 1, .inl 2, .inl 3] (genericMatrix K 2).permanent

private theorem selector_map (K : Type*) :
    (fun k : Fin 4 => (Sum.inl
      (if k = finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) then Fin.natAdd 4 (0 : Fin 1)
        else Fin.castAdd 1 k) : Fin 5 ⊕ K)) =
      ![Sum.inl 4, .inl 1, .inl 2, .inl 3] := by
  funext k
  fin_cases k <;> rfl

example : IsProjection (booleanSum 1 (selectorPolynomial ℚ)) (genericMatrix ℚ 3).permanent := by
  have h := isProjection_booleanSum_entry_permanent (K := ℚ) (d := 2) 0 0 (1 / 2)
    (by norm_num)
  rw [selector_map] at h
  exact h

example : IsProjection (booleanSum 1 (selectorPolynomial (ZMod 3)))
    (genericMatrix (ZMod 3) 3).permanent := by
  have h := isProjection_booleanSum_entry_permanent (K := ZMod 3) (d := 2) 0 0 2 (by decide)
  rw [selector_map] at h
  exact h

private theorem selectorPolynomial_eq (K : Type*) [CommSemiring K] :
    selectorPolynomial K = X 4 * X 3 + X 1 * X 2 := by
  unfold selectorPolynomial
  rw [Matrix.permanent_succ_row_zero, Fin.sum_univ_two, Matrix.permanent_succ_row_zero,
    Matrix.permanent_succ_row_zero, Fin.sum_univ_one, Fin.sum_univ_one]
  simp [Matrix.permanent, genericMatrix, finProdFinEquiv]

private theorem booleanSum_selectorPolynomial : booleanSum 1 (selectorPolynomial ℚ) =
    2 * X 1 * X 2 + X 3 := by
  rw [selectorPolynomial_eq, booleanSum,
    ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  have h2 (h : (2 : Fin 5) ≠ Fin.last 4) : Fin.castPred (2 : Fin 5) h = (2 : Fin 4) := rfl
  have h3 (h : (3 : Fin 5) ≠ Fin.last 4) : Fin.castPred (3 : Fin 5) h = (3 : Fin 4) := rfl
  norm_num [booleanAssignment, Fin.append, Fin.addCases, h2, h3]
  ring

example : aeval (![99, 3, 5, 7] : Fin 4 → ℚ)
    (booleanSum 1 (selectorPolynomial ℚ)) = 37 := by
  rw [booleanSum_selectorPolynomial]
  norm_num

example : booleanSum 1 (projection (fun _ : Fin 1 => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ ℚ))
    (genericMatrix ℚ 1).permanent) = 1 := by
  rw [Matrix.permanent_unique, booleanSum,
    ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
  norm_num [genericMatrix, booleanAssignment, Fin.append, Fin.addCases]

example : ¬ ∃ half : ZMod 2, 2 * half = 1 := by
  rintro ⟨half, hhalf⟩
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul] at hhalf
  exact zero_ne_one hhalf

end ComplexityTests.PermanentBooleanSum
