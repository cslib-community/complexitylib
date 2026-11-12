/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.ROABP

/-!
# Read-once oblivious branching programs

The width-one program with layers `(X)` read in the order `1, 0` computes `X 1 * X 0`: it is a
program of degree one in some order, and its coefficient at the monomial `x₀ x₁` is the entry
of the product of the two coefficient matrices `(1)`.
-/

public section

namespace CslibFrontierTests.ROABP

open Cslib.Circuits.Arithmetic MvPolynomial

/-- The layers `(X)`. -/
noncomputable def layers : Fin 2 → Matrix (Fin 1) (Fin 1) (Polynomial ℚ) :=
  fun _ => Matrix.of fun _ _ => Polynomial.X

theorem roabpProd_layers : roabpProd layers [1, 0] 0 0 = (X 1 * X 0 : MvPolynomial (Fin 2) ℚ) := by
  simp [roabpProd, layers, Matrix.mul_apply]

/-- `X 1 * X 0` is computed by a width-one program of degree one in the order `1, 0`. -/
theorem isROABP_X_mul_X : IsROABP 1 1 (X 1 * X 0 : MvPolynomial (Fin 2) ℚ) :=
  ⟨[1, 0], layers, 0, 0, by decide, fun _ _ _ => by simp [layers], roabpProd_layers.symm⟩

/-- The coefficient of `x₀ x₁` is the entry of the product of the coefficient matrices. -/
example : (roabpProd layers [1, 0] 0 0).coeff (Finsupp.single 0 1 + Finsupp.single 1 1) =
    ([1, 0].map fun i => layerCoeff layers i
      ((Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) i)).prod 0 0 :=
  coeff_roabpProd layers (by decide) _ (fun i hi => absurd (by fin_cases i <;> simp) hi) 0 0

end CslibFrontierTests.ROABP
