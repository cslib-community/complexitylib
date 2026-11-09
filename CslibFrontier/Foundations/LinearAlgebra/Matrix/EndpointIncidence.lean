/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Incidence matrices with indexed endpoint pairs

The two endpoints of each column contribute separately. In characteristic two a loop
therefore gives a zero column, while different column indices retain parallel occurrences.
No simple-graph edge-count convention is used.

## Main definitions

* `Matrix.endpointIncidence`: the matrix of two indexed endpoint contributions.

## Main results

* `Matrix.rank_endpointIncidence_add_one`: rank of a connected endpoint system.
* `Matrix.range_transpose_eq_ker_of_euler`: exactness from finite Euler counts.
-/

public section

namespace Matrix

variable {V E F : Type*} [Fintype V] [DecidableEq V]

/-- The characteristic-two incidence matrix of indexed endpoint pairs. Both ends contribute,
so a loop contributes twice and cancels. Parallel occurrences retain their column indices. -/
@[expose] def endpointIncidence (u v : E → V) : Matrix V E (ZMod 2) :=
  fun a e => (if a = u e then 1 else 0) + if a = v e then 1 else 0

/-- The transpose incidence map computes endpoint differences over the two-element field. -/
theorem endpointIncidence_transpose_mulVec (u v : E → V) (s : V → ZMod 2) (e : E) :
    (endpointIncidence u v).transpose.mulVec s e = s (u e) + s (v e) := by
  simp [endpointIncidence, mulVec, dotProduct, add_mul, Finset.sum_add_distrib]

/-- The kernel of the transpose incidence map consists exactly of endpoint-constant functions. -/
theorem mem_ker_endpointIncidence_transpose (u v : E → V) (s : V → ZMod 2) :
    s ∈ (endpointIncidence u v).transpose.mulVecLin.ker ↔ ∀ e, s (u e) = s (v e) := by
  rw [LinearMap.mem_ker, funext_iff]
  simp only [mulVecLin_apply, endpointIncidence_transpose_mulVec, Pi.zero_apply,
    CharTwo.add_eq_zero]

/-- In a connected endpoint system, constants give the whole transpose incidence kernel.
The hypothesis states ordinary endpoint connectivity in its invariant-function form. -/
noncomputable def endpointIncidenceKernelEquiv (u v : E → V) (root : V)
    (hconn : ∀ s : V → ZMod 2, (∀ e, s (u e) = s (v e)) → ∀ a b, s a = s b) :
    ZMod 2 ≃ₗ[ZMod 2] (endpointIncidence u v).transpose.mulVecLin.ker where
  toFun c := ⟨fun _ => c, (mem_ker_endpointIncidence_transpose u v _).mpr (fun _ => rfl)⟩
  invFun s := s.val root
  left_inv _ := rfl
  right_inv s := Subtype.ext (funext fun a =>
    hconn s.val ((mem_ker_endpointIncidence_transpose u v s.val).mp s.property) root a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Fintype E] [Fintype F]

/-- A connected indexed incidence matrix has rank one less than its number of vertices.
This counts endpoint names and indexed columns separately. -/
theorem rank_endpointIncidence_add_one (u v : E → V) (root : V)
    (hconn : ∀ s : V → ZMod 2, (∀ e, s (u e) = s (v e)) → ∀ a b, s a = s b) :
    (endpointIncidence u v).rank + 1 = Fintype.card V := by
  have hk : Module.finrank (ZMod 2) (endpointIncidence u v).transpose.mulVecLin.ker = 1 := by
    rw [← (endpointIncidenceKernelEquiv u v root hconn).finrank_eq]
    exact Module.finrank_self _
  have h := (endpointIncidence u v).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (endpointIncidence u v).transpose.rank +
    Module.finrank (ZMod 2) (endpointIncidence u v).transpose.mulVecLin.ker = _ at h
  simpa only [rank_transpose, hk, Module.finrank_pi, Module.finrank_self, mul_one] using h

omit [DecidableEq V] in
/-- A zero matrix product and the connected Euler dimension equation force exactness.
This finite-dimensional argument discharges the cycle/cut-space dimension step without a
spanning-tree, cotree, or lifting certificate. -/
theorem range_transpose_eq_ker_of_euler (B : Matrix V E (ZMod 2))
    (D : Matrix F E (ZMod 2)) (hzero : D * B.transpose = 0)
    (hB : B.rank + 1 = Fintype.card V) (hD : D.rank + 1 = Fintype.card F)
    (hEuler : Fintype.card V + Fintype.card F = Fintype.card E + 2) :
    LinearMap.range B.transpose.mulVecLin = LinearMap.ker D.mulVecLin := by
  have hle : LinearMap.range B.transpose.mulVecLin ≤ LinearMap.ker D.mulVecLin := by
    rintro _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    change D.mulVec (B.transpose.mulVec s) = 0
    rw [mulVec_mulVec, hzero, zero_mulVec]
  apply Submodule.eq_of_le_of_finrank_eq (K := ZMod 2) hle
  have hnull := D.mulVecLin.finrank_range_add_finrank_ker
  change D.rank + Module.finrank (ZMod 2) D.mulVecLin.ker = _ at hnull
  simp only [Module.finrank_pi] at hnull
  rw [← rank, rank_transpose]
  omega

end Matrix
