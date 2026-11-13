/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Foundations.Combinatorics.Expander.HittingProduct

set_option linter.privateModule false

open Cslib Finset
open scoped BigOperators

private def completeTwo : RotationMap (Fin 2) (Fin 2) where
  rot := Prod.swap
  rot_involutive := Prod.swap_swap

private theorem expansion_zero : completeTwo.spectralExpansion = 0 := by
  apply le_antisymm ?_ completeTwo.spectralExpansion_nonneg
  apply RotationMap.spectralExpansion_le le_rfl
  intro f hf
  simp [RotationMap.walk_apply, RotationMap.neighbor, completeTwo, hf]

-- One vertex (zero edges): the initial density factor must remain.
open Classical in
example : (dens {p : Fin 2 × (Fin 0 → Fin 2) |
    ∀ i ≤ 0, completeTwo.walkAt p i ∈ ({0} : Finset (Fin 2))} : ℝ) ^ 2 ≤ 1 / 2 := by
  simpa [nnratCast_dens] using
    completeTwo.sq_dens_filter_forall_walkAt_mem_le_product (fun _ => {0}) 0

-- Unequal densities: singleton, full set, singleton.
open Classical in
example : let B : ℕ → Finset (Fin 2) := fun i => if i = 1 then univ else {0}
    (dens {p : Fin 2 × (Fin 2 → Fin 2) |
      ∀ i ≤ 2, completeTwo.walkAt p i ∈ B i} : ℝ) ^ 2 ≤ 1 / 4 := by
  dsimp only
  have h := completeTwo.sq_dens_filter_forall_walkAt_mem_le_product
    (fun i => if i = 1 then univ else {0}) 2
  norm_num [expansion_zero, prod_range_succ, nnratCast_dens] at h ⊢
  convert h using 1
  apply congrArg (fun n : ℕ => ((n : ℝ) / 8) ^ 2)
  apply congrArg Finset.card
  ext p
  simp

open Classical in
example : (dens {p : Fin 2 × (Fin 2 → Fin 2) |
    ∀ i : Fin 3, completeTwo.walkAt p i ∈
      (if i.val = 1 then univ else {0})} : ℝ) = 1 / 4 := by
  have hc : #{p : Fin 2 × (Fin 2 → Fin 2) |
      ∀ i : Fin 3, completeTwo.walkAt p i ∈
        (if i.val = 1 then univ else {0})} = 2 := by decide
  rw [nnratCast_dens, hc]
  norm_num

open Classical in
example (t : ℕ) : (dens {p : Fin 2 × (Fin t → Fin 2) |
    ∀ i ≤ t, completeTwo.walkAt p i ∈ (∅ : Finset (Fin 2))} : ℝ) ≤ 0 := by
  simpa using completeTwo.dens_filter_forall_walkAt_mem_le_product (fun _ => ∅) t

open Classical in
example (t : ℕ) : (dens {p : Fin 2 × (Fin t → Fin 2) |
    ∀ i ≤ t, completeTwo.walkAt p i ∈ (univ : Finset (Fin 2))} : ℝ) ≤ 1 := by
  have h := completeTwo.dens_filter_forall_walkAt_mem_le_sqrt_pow
    univ t (η := 0) expansion_zero.le
  norm_num [expansion_zero] at h ⊢

private def singletonGraph : RotationMap Unit Unit where
  rot := id
  rot_involutive := fun _ => rfl

-- An inhabited one-vertex graph exercises the native model without a nontriviality hypothesis.
open Classical in
example : (𝔼 v, (if v ∈ (univ : Finset Unit) then singletonGraph.walk (fun _ => 1) v else 0) ^ 2) ≤
    (1 + singletonGraph.spectralExpansion ^ 2) := by
  simpa using singletonGraph.expect_mask_walk_sq_le univ (fun _ => 1)

-- Explicit source-parameter transport, with the real half-length exponent.
open Classical in
example (t : ℕ) : (dens {p : Fin 2 × (Fin t → Fin 2) |
    ∀ i ≤ t, completeTwo.walkAt p i ∈ ({0} : Finset (Fin 2))} : ℝ) ≤
      (1 / 2 : ℝ) ^ (((t + 1 : ℕ) : ℝ) / 2) := by
  simpa [nnratCast_dens] using
    completeTwo.dens_filter_forall_walkAt_mem_le_rpow_of_spectralExpansion_le
      {0} t 0 2 (by simp [expansion_zero])
