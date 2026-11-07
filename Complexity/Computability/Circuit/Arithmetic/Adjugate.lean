/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Arithmetic.Gradient
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Complexity.Foundations.LinearAlgebra.Matrix.Derivation

/-!
# Adjugate circuits from determinant circuits

The partial derivative of the generic determinant along the entry `(a, b)` is the cofactor
`adjugate (genericMatrix K n) b a` (`Cslib.Circuits.Arithmetic.pderiv_det_genericMatrix`). This
follows from Laplace expansion along row `a`: the cofactors of row `a` do not involve the
variables of that row. Reverse-mode differentiation [BaurStrassen1983] therefore turns a circuit
with `s` gates computing the determinant into one with at most `5 s + 2` gates and three times the
multiplications computing all `n²` entries of the adjugate
(`Cslib.Circuits.Arithmetic.exists_circuit_adjugate_of_det`). With Bird's division-free
determinant circuits this gives adjugate circuits with at most `15 n⁴ + 22` gates over every
commutative ring (`Cslib.Circuits.Arithmetic.exists_circuit_adjugate`).

Over a field, the inverse of a matrix is its adjugate divided by its determinant. Baur and
Strassen draw from this that inverting a matrix is no harder than computing its determinant, up to
a constant factor. The circuits here have no division gate, so only the adjugate is formalized.

## Main results

* `Cslib.Circuits.Arithmetic.pderiv_det_genericMatrix`: `∂ det / ∂ x_{a b} = adj_{b a}`.
* `Cslib.Circuits.Arithmetic.exists_circuit_adjugate_of_det`: the adjugate costs at most five
  times the determinant, plus two gates.
* `Cslib.Circuits.Arithmetic.exists_circuit_adjugate`: polynomial-size adjugate circuits.

## References

* [W. Baur and V. Strassen, *The complexity of partial derivatives*][BaurStrassen1983]
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- The partial derivative of the generic determinant along the variable of entry `(a, b)` is the
cofactor `adjugate (genericMatrix K n) b a`. -/
theorem pderiv_det_genericMatrix (a b : Fin n) :
    pderiv (finProdFinEquiv (a, b)) (genericMatrix K n).det =
      adjugate (genericMatrix K n) b a := by
  classical
  have hentry : ∀ k l, (k, l) ≠ (a, b) →
      pderiv (finProdFinEquiv (a, b)) (genericMatrix K n k l) = 0 := fun k l h => by
    rw [genericMatrix, of_apply, pderiv_X, Pi.single_apply,
      ite_eq_right fun h' => h (finProdFinEquiv.injective h')]
  rw [derivation_det_eq_sum_adjugate _ _ a fun k hk l =>
      hentry k l fun h => hk (congrArg Prod.fst h),
    Finset.sum_eq_single b (fun l _ hl => by
      rw [hentry a l fun h => hl (congrArg Prod.snd h), smul_zero])
      (fun h => absurd (Finset.mem_univ b) h),
    genericMatrix, of_apply, pderiv_X_self, smul_eq_mul, mul_one]

/-- **Adjugates from determinants** [BaurStrassen1983]: if a circuit with `s` gates computes the
generic `n × n` determinant, then a circuit with at most `5 s + 2` gates and three times the
multiplications computes every entry of the adjugate; output `n * a + b` is entry `(a, b)`. -/
theorem exists_circuit_adjugate_of_det {m : ℕ} (c : Circuit (arithSignature K) (n * n) m)
    (j : Fin m) (hc : c.polynomial j = (genericMatrix K n).det) :
    ∃ d : Circuit (arithSignature K) (n * n) (n * n), d.size ≤ 5 * c.size + 2 ∧
      d.program.cost ArithOp.mulCost = 3 * c.program.cost ArithOp.mulCost ∧
      ∀ a b, d.polynomial (finProdFinEquiv (a, b)) = adjugate (genericMatrix K n) a b := by
  obtain ⟨e, hsize, hmul, -, he⟩ := c.exists_gradient j
  refine ⟨⟨e.program, fun k => e.outputs (finProdFinEquiv
      ((finProdFinEquiv.symm k).2, (finProdFinEquiv.symm k).1)).succ⟩, hsize, hmul,
    fun a b => ?_⟩
  have h := he (finProdFinEquiv (b, a))
  rw [hc, pderiv_det_genericMatrix] at h
  simpa only [Circuit.polynomial, Circuit.eval, Function.comp_apply, Equiv.symm_apply_apply]
    using h

/-- The adjugate of the generic `n × n` matrix has circuits with at most `15 n⁴ + 22` gates over
every commutative ring. -/
theorem exists_circuit_adjugate (n : ℕ) :
    ∃ d : Circuit (arithSignature K) (n * n) (n * n), d.size ≤ 15 * n ^ 4 + 22 ∧
      ∀ a b, d.polynomial (finProdFinEquiv (a, b)) = adjugate (genericMatrix K n) a b := by
  obtain ⟨c, hc, hsize⟩ := exists_circuit_det (K := K) n
  obtain ⟨d, hd, -, hadj⟩ := exists_circuit_adjugate_of_det c 0 hc
  exact ⟨d, by omega, hadj⟩

end Cslib.Circuits.Arithmetic
