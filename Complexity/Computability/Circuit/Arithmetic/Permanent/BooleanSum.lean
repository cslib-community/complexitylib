/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Permanent.Formula
public import Complexity.Computability.Circuit.Arithmetic.VNP
import Complexity.Foundations.Data.Matrix.Permanent.BooleanSum

/-!
# Eliminate a selector occurring in one permanent entry

If `K` has a scalar `half` with `2 * half = 1`, a Boolean selector placed in one entry of the
`d × d` generic permanent can be summed out as a projection of the `(d + 1) × (d + 1)` generic
permanent. All other entries remain independent variables, in the existing row-major layout.
The selector is the final variable, following the `d * d` ordinary inputs, so the summation
uses the existing `booleanSum`.

[Orzel et al., Claim 13, p. 47:10][OrzelSrinivasanTavenasYehudayoff2025] allows a nonzero scalar
multiplier in projections and therefore states zero extra dimension. The library's
`IsProjection` permits only substitutions: the factor `2` is represented by a separate scalar
block, costing one extra matrix dimension. The explicit half hypothesis is essential to this
construction; it holds over fields of characteristic other than two. Membership in VNP and
formula simulation have their separately proved, more general ring/semiring scopes.

The selector occurs exactly once in this result. The two-entry gadget, repeated-selector
elimination, the conversion of VP-based VNP witnesses to formulas, and full VNP-hardness remain
separate obligations. Only nonuniform projection existence and dimension are certified.

## Main results

* `Cslib.Circuits.Arithmetic.isProjection_booleanSum_entry_permanent`: one extra dimension
  eliminates a selector in one entry, when `2` has a half.

## References

* [I. Orzel et al.][OrzelSrinivasanTavenasYehudayoff2025], *The Algebraic Cost of a Boolean Sum*,
  §3.3, Claim 13
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {d : ℕ}

private def entryAssignment (i j : Fin d) (b : K) : Fin (d * d) → Fin (d * d) ⊕ K :=
  fun k => if k = finProdFinEquiv (i, j) then .inr b else .inl k

private def selectorAssignment (i j : Fin d) : Fin (d * d) → Fin (d * d + 1) ⊕ K :=
  fun k => .inl (if k = finProdFinEquiv (i, j) then Fin.natAdd (d * d) 0 else Fin.castAdd 1 k)

private theorem projection_permanent_entry (i j : Fin d) (b : K) :
    projection (entryAssignment i j b) (genericMatrix K d).permanent =
      ((genericMatrix K d).updateRow i
        (Function.update (genericMatrix K d i) j (C b))).permanent := by
  rw [AlgHom.map_permanent]
  congr 1
  apply Matrix.ext
  intro r c
  by_cases hr : r = i <;> by_cases hc : c = j <;>
    simp [genericMatrix, entryAssignment, Matrix.updateRow_apply, hr, hc]

private theorem booleanSum_permanent_entry (i j : Fin d) :
    booleanSum 1 (projection (selectorAssignment (K := K) i j) (genericMatrix K d).permanent) =
      projection (entryAssignment i j 0) (genericMatrix K d).permanent +
        projection (entryAssignment i j 1) (genericMatrix K d).permanent := by
  rw [booleanSum, ← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]
  simp_rw [projection_projection]
  congr 1 <;> congr 2 <;> funext k <;>
    by_cases hk : k = finProdFinEquiv (i, j) <;>
    simp [selectorAssignment, entryAssignment, booleanAssignment, hk]

/-- A selector occurring in one matrix entry can be summed out using a permanent with one
extra dimension, under the explicit half-of-two hypothesis. The selector is the last variable;
the ordinary inputs retain the existing row-major order. -/
theorem isProjection_booleanSum_entry_permanent (i j : Fin d) (half : K)
    (hhalf : 2 * half = 1) :
    IsProjection
      (booleanSum 1 (projection
        (fun k : Fin (d * d) => Sum.inl
          (if k = finProdFinEquiv (i, j) then Fin.natAdd (d * d) 0 else Fin.castAdd 1 k))
        (genericMatrix K d).permanent))
      (genericMatrix K (d + 1)).permanent := by
  change IsProjection
    (booleanSum 1 (projection (selectorAssignment (K := K) i j) (genericMatrix K d).permanent)) _
  rw [booleanSum_permanent_entry, projection_permanent_entry, projection_permanent_entry]
  simp only [map_zero, map_one]
  have hh : (2 : MvPolynomial (Fin (d * d)) K) * C half = 1 := by
    rw [← map_ofNat C 2, ← map_mul, hhalf, map_one]
  rw [Matrix.permanent_updateRow_update_zero_add_one _ i j (C half) hh]
  have hp : IsProjection
      (((genericMatrix K d).updateRow i
        (Function.update (genericMatrix K d i) j (C half))).permanent)
      (genericMatrix K d).permanent :=
    ⟨entryAssignment i j half, projection_permanent_entry i j half⟩
  have hc : IsProjection (2 : MvPolynomial (Fin (d * d)) K) (genericMatrix K 1).permanent := by
    refine ⟨fun _ => .inr 2, ?_⟩
    rw [Matrix.permanent_unique]
    simp only [genericMatrix, Matrix.of_apply, projection_X, Sum.elim_inr]
    exact map_ofNat C 2
  simpa only [mul_comm (2 : MvPolynomial (Fin (d * d)) K)] using hp.permanent_mul hc

end Cslib.Circuits.Arithmetic
