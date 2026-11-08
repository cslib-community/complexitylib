/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Expander.Basic
import CslibFrontier.Foundations.Combinatorics.Expander.SimpleGraph
import CslibFrontier.Foundations.Combinatorics.Expander.Spectrum

/-!
# Expander Rayleigh quotient, adjacency matrix, and spectrum tests

Concrete instances for the Rayleigh-quotient characterization of
`spectralExpansion`, the `SimpleGraph.adjMatrix` walk bridge, and the eigenvalue characterizations
of `spectralExpansion` and `secondEigenvalue`.
-/

namespace ComplexityTests.Expander

open Cslib Finset
open scoped BigOperators

/-- The 4-cycle as a simple 2-regular rotation map. -/
private def cycleFour : RotationMap (Fin 4) Bool where
  rot p := if p.2 then (p.1 + 1, false) else (p.1 - 1, true)
  rot_involutive := by
    unfold Function.Involutive
    decide

private theorem isSimple_cycleFour : cycleFour.IsSimple :=
  ⟨by decide, by decide⟩

-- The walk operator of the 4-cycle agrees with its adjacency matrix scaled by `1 / 2`.
example (f : Fin 4 → ℝ) :
    cycleFour.walk f = (2 : ℝ)⁻¹ • (cycleFour.toSimpleGraph.adjMatrix ℝ).mulVec f := by
  simpa using isSimple_cycleFour.walk_eq_smul_adjMatrix_mulVec f

example (f : Fin 4 → ℝ) (v : Fin 4) :
    cycleFour.walk f v = (cycleFour.toSimpleGraph.adjMatrix ℝ).mulVec f v / 2 := by
  simpa using isSimple_cycleFour.walk_apply_eq_adjMatrix_mulVec_div f v

/-- The complete graph with self-loops on `Fin 4`. -/
private def completeFour : RotationMap (Fin 4) (Fin 4) where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

-- The Rayleigh quotient characterization bounds `spectralExpansion` on the complete graph.
private theorem spectralExpansion_completeFour : completeFour.spectralExpansion = 0 := by
  refine le_antisymm ?_ completeFour.spectralExpansion_nonneg
  refine completeFour.spectralExpansion_le_of_abs_expect_mul_walk_le le_rfl
    fun f hf ↦ ?_
  simp [RotationMap.walk_apply, RotationMap.neighbor, completeFour, hf]

example {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D) :
    G.spectralExpansion =
      ⨆ f : {f : V → ℝ // 𝔼 v, f v = 0 ∧ f ≠ 0}, |𝔼 v, f.1 v * G.walk f.1 v| / 𝔼 v, f.1 v ^ 2 :=
  G.spectralExpansion_eq_ciSup

example {V D : Type*} [Fintype V] [Fintype D] (G : RotationMap V D) :
    G.spectralExpansion = ‖G.orthogonalWalk.toContinuousLinearMap‖ :=
  G.spectralExpansion_eq_norm_orthogonalWalk

-- On `Fin 4`, `EuclideanSpace ℝ (Fin 4)` has dimension 4; the top eigenvalue of `walkEuclidean`
-- on the complete graph is `1` and the second eigenvalue is `0`.
private theorem finrank_fin4 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
  simp [finrank_euclideanSpace]

example :
    completeFour.isSymmetric_walkEuclidean.eigenvalues finrank_fin4 ⟨0, by decide⟩ = 1 :=
  completeFour.walkEuclidean_eigenvalues_zero finrank_fin4 (by decide)

example :
    completeFour.isSymmetric_walkEuclidean.eigenvalues finrank_fin4 ⟨1, by decide⟩ = 0 := by
  rw [← completeFour.secondEigenvalue_eq_walkEuclidean_eigenvalues_one
    finrank_fin4 (by decide)]
  have h := completeFour.abs_secondEigenvalue_le_spectralExpansion
  rw [spectralExpansion_completeFour, abs_nonpos_iff] at h
  exact h

end ComplexityTests.Expander
