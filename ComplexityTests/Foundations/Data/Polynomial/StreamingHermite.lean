/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.Polynomial.StreamingHermite)

import Complexity.Foundations.Data.Polynomial.StreamingHermite
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases

-- Regression tests intentionally export no declarations.
set_option linter.privateModule false

/-! Concrete finite-field coefficient extraction and recovery with genuinely untruncated local
polynomials. The degree-bound counterexample records the excluded coefficient alias. -/

namespace ComplexityTests.StreamingHermite

noncomputable section

open Finset Polynomial

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The projector can recover a coefficient even when the polynomial degree exceeds `q - 1`,
as long as it stays below the next congruent degree. -/
example (a : ZMod 7) :
    (∑ u : (ZMod 7)ˣ, (u : ZMod 7) ^ 4 * (a * (u : ZMod 7) ^ 2 + (u : ZMod 7) ^ 7)) =
      -a := by
  have hdeg : (C a * X ^ 2 + X ^ 7 : (ZMod 7)[X]).natDegree <
      2 + (Fintype.card (ZMod 7) - 1) := by
    refine (natDegree_add_le _ _).trans_lt ?_
    rw [natDegree_X_pow, ZMod.card]
    exact (max_le ((natDegree_C_mul_X_pow_le a 2).trans (by decide : 2 ≤ 7))
      (le_refl 7)).trans_lt (by decide)
  have h := FiniteField.sum_units_pow_mul_eval (i := 2) (by decide) hdeg
  simpa using h

/-- At the first excluded degree, the constant-coefficient projector aliases `X ^ 6` to `1`
over the nonzero elements of `ZMod 7`. -/
example :
    (∑ u : (ZMod 7)ˣ, (u : ZMod 7) ^ 6 * (X ^ 6 : (ZMod 7)[X]).eval (u : ZMod 7)) ≠
      -(X ^ 6 : (ZMod 7)[X]).coeff 0 := by
  simp only [eval_pow, eval_X, ← pow_add]
  rw [FiniteField.sum_pow_units]
  norm_num

private abbrev node : Fin 2 → ZMod 7 := ![1, 2]

private abbrev mult : Fin 2 → ℕ := ![1, 2]

private abbrev target : (ZMod 7)[X] := X ^ 2 + C 3

/-- The added high-order term does not belong to the required Taylor jet, but it remains in
the polynomial passed to the recovery formula. -/
private def localPoly (i : Fin 2) : (ZMod 7)[X] :=
  taylor (node i) target + X ^ (mult i + 2)

/-- Recover `H(0) = 3` from two nodes with multiplicities `1,2`. Both local polynomials contain
extra nonzero terms above the prescribed Taylor order. -/
example : (3 : ZMod 7) = ∑ i : Fin 2, ∑ u : (ZMod 7)ˣ,
    hermiteEvalKernel univ node mult 0 i (u : ZMod 7) * (localPoly i).eval (u : ZMod 7) := by
  have hnodes : ((univ : Finset (Fin 2)) : Set (Fin 2)).Pairwise
      fun i j => IsUnit (node i - node j) := by
    intro i _ j _ hij
    apply isUnit_iff_ne_zero.mpr
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide
  have htarget : target.degree < ↑(∑ i : Fin 2, mult i) := by
    rw [show target.degree = 2 by unfold target; compute_degree!]
    decide
  have hjet (i : Fin 2) (_ : i ∈ (univ : Finset (Fin 2))) (j : ℕ) (hj : j < mult i) :
      (localPoly i).coeff j = (taylor (node i) target).coeff j := by
    simp [localPoly, coeff_X_pow, show j ≠ mult i + 2 by omega]
  have hdegree (i : Fin 2) (_ : i ∈ (univ : Finset (Fin 2))) :
      (localPoly i).natDegree < Fintype.card (ZMod 7) - 1 := by
    refine (natDegree_add_le _ _).trans_lt ?_
    rw [natDegree_taylor, natDegree_X_pow, ZMod.card,
      show target.natDegree = 2 by unfold target; compute_degree!]
    fin_cases i <;> decide
  have h := eval_eq_sum_hermiteEvalKernel_mul_eval hnodes
    (fun i _ => by fin_cases i <;> decide) htarget localPoly hjet hdegree 0
  rw [show target.eval 0 = 3 by simp [target]] at h
  exact h

end

end ComplexityTests.StreamingHermite
