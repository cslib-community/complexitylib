/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Expander.Hitting
import CslibFrontier.Foundations.Combinatorics.Expander.Mixing

/-!
# Expander-walk hitting tests

The complete two-vertex rotation has spectral parameter zero. Singleton sets at successive
vertices therefore satisfy the independent-sampling bound `2⁻⁽ᵗ⁺¹⁾`, including when the target
singleton alternates with time. A one-step calculation attains the bound, and the complement
corollary controls avoidance of a fixed singleton. Empty vertices and full target sets exercise
the boundary conventions.
-/

namespace ComplexityTests.ExpanderHitting

open Cslib Finset
open scoped BigOperators

private def completeTwo : RotationMap (Fin 2) (Fin 2) where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

private theorem spectralExpansion_completeTwo : completeTwo.spectralExpansion = 0 := by
  apply le_antisymm ?_ completeTwo.spectralExpansion_nonneg
  apply RotationMap.spectralExpansion_le le_rfl
  intro f hf
  simp [RotationMap.walk_apply, RotationMap.neighbor, completeTwo, hf]

-- The density hypotheses are discharged for arbitrary, possibly varying singleton targets.
example (b : ℕ → Fin 2) (t : ℕ) :
    (dens {p : Fin 2 × (Fin t → Fin 2) |
      ∀ i ≤ t, completeTwo.walkAt p i = b i} : ℝ) ≤ (1 / 2 : ℝ) ^ (t + 1) := by
  have h := completeTwo.dens_filter_forall_walkAt_mem_le
    (B := fun i => {b i}) (μ := 1 / 2) (by intro i; norm_num [nnratCast_dens]) t
  simpa [spectralExpansion_completeTwo, pow_succ'] using h

-- An actual walk event meets the bound: its four seeds have one successful pair.
example : (dens {p : Fin 2 × (Fin 1 → Fin 2) |
    ∀ i : Fin 2, completeTwo.walkAt p i = 0} : ℝ) = 1 / 4 := by
  have hcard : #{p : Fin 2 × (Fin 1 → Fin 2) |
      ∀ i : Fin 2, completeTwo.walkAt p i = 0} = 1 := by decide
  rw [nnratCast_dens, hcard]
  norm_num

example (t : ℕ) :
    (dens {p : Fin 2 × (Fin t → Fin 2) |
      ∀ i ≤ t, completeTwo.walkAt p i ≠ 0} : ℝ) ≤ (1 / 2 : ℝ) ^ (t + 1) := by
  have h := completeTwo.dens_filter_forall_walkAt_notMem_le ({0} : Finset (Fin 2)) t
  norm_num [spectralExpansion_completeTwo, nnratCast_dens, pow_succ'] at h ⊢
  exact h

example (t : ℕ) :
    (dens {p : Fin 2 × (Fin t → Fin 2) |
      ∀ i ≤ t, completeTwo.walkAt p i ∈ (univ : Finset (Fin 2))} : ℝ) ≤ 1 := by
  have h := completeTwo.dens_filter_forall_walkAt_mem_le_pow
    (B := fun _ => univ) (μ := 1) (fun _ => by simp) le_rfl t
  convert h using 1
  norm_num

private def emptyVertices : RotationMap (Fin 0) Unit where
  rot := id
  rot_involutive := fun _ => rfl

example (t : ℕ) :
    (dens {p : Fin 0 × (Fin t → Unit) |
      ∀ i ≤ t, emptyVertices.walkAt p i ∈ (∅ : Finset (Fin 0))} : ℝ) ≤ 0 := by
  have h := emptyVertices.dens_filter_forall_walkAt_mem_le
    (B := fun _ => ∅) (μ := 0) (fun _ => by simp) t
  convert h using 1
  norm_num

-- Centering in the mixing bound does not need an inhabitant of the vertex type.
example (t : ℕ) (f g : Fin 0 → ℝ) :
    (𝔼 v, f v * (emptyVertices.walk ^ t) g v - (𝔼 v, f v) * 𝔼 v, g v) ^ 2 ≤ 0 := by
  convert emptyVertices.sq_expect_mul_walk_pow_sub_le t f g using 1
  simp

-- A nonconstant score has zero centered correlation after a positive complete-graph walk.
example (t : ℕ) :
    let f : Fin 2 → ℝ := fun v => if v = 0 then 1 else 0
    (𝔼 v, f v * (completeTwo.walk ^ (t + 1)) f v - (𝔼 v, f v) * 𝔼 v, f v) ^ 2 ≤ 0 := by
  dsimp only
  simpa [spectralExpansion_completeTwo] using completeTwo.sq_expect_mul_walk_pow_sub_le
    (t + 1) (fun v => if v = 0 then 1 else 0) (fun v => if v = 0 then 1 else 0)

end ComplexityTests.ExpanderHitting
