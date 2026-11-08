/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.UniformDiagonalization
import Complexity.Computability.Complexity.Problems.BoundedHalting

/-! Uniform diagonalization: the sides of the stages, the marked union on concrete words, `P`
meeting the hypotheses, a class that is not closed under finite variations, and the theorem applied
to bounded halting and its complement, which are decidable and outside `P`. -/

namespace ComplexityTests.UniformDiagonalization

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### The construction -/

/-- Even stages diagonalize against the first family and odd ones against the second. -/
example : UniformDiagonalization.side 0 = true ∧ UniformDiagonalization.side 1 = false ∧
    UniformDiagonalization.side 4 = true :=
  ⟨rfl, rfl, rfl⟩

/-- The construction starts at stage `0` and advances at most one stage per length. -/
example (dA dF : Bool → Universal.Desc) (n : ℕ) :
    UniformDiagonalization.stage dA dF 0 = 0 ∧ UniformDiagonalization.stage dA dF n ≤ n :=
  ⟨UniformDiagonalization.stage_zero dA dF, UniformDiagonalization.stage_le_self dA dF n⟩

/-! ### The marked union -/

/-- `false :: x` is in the marked union exactly when `x` is in the first set, and `true :: x`
exactly when `x` is in the second. -/
example : [false, true] ∈ markedUnion {[true]} ∅ ∧ [true, true] ∉ markedUnion {[true]} ∅ ∧
    [] ∉ markedUnion {[true]} Set.univ := by
  refine ⟨cons_mem_markedUnion.mpr rfl, fun h => ?_, fun ⟨x, h⟩ => ?_⟩
  · simpa using cons_mem_markedUnion.mp h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-! ### The hypotheses -/

/-- `P` meets both hypotheses on classes. -/
example : RecursivelyPresentable encBits (P encBits) ∧ ClosedUnderFiniteVariation (P encBits) :=
  ⟨recursivelyPresentable_P, closedUnderFiniteVariation_P encBits⟩

/-- The class containing only the empty set is not closed under finite variations. -/
example : ¬ ClosedUnderFiniteVariation ({∅} : Set (Set (List Bool))) := fun h => by
  have hmem := h (L := ∅) (L' := {[]}) rfl (by simp)
  exact Set.singleton_ne_empty _ hmem

/-! ### Bounded halting -/

/-- Bounded halting is decidable: it is in `E`. -/
theorem isDecidable_boundedHalting : IsDecidable BoundedHalting encBits := by
  obtain ⟨k, c₁, c₂, s, h⟩ := Set.mem_iUnion.mp BoundedHalting.mem_E
  exact ⟨_, _, h⟩

/-- **The theorem is not vacuous**: mixing bounded halting with its complement along a problem in
`P` gives a decidable problem outside `P` that reduces to their marked union. -/
example : ∃ G ∈ P encBits, G.ite BoundedHalting BoundedHaltingᶜ ∉ P encBits ∧
    IsDecidable (G.ite BoundedHalting BoundedHaltingᶜ) encBits ∧
    PolyTimeReducible encBits encBits (G.ite BoundedHalting BoundedHaltingᶜ)
      (markedUnion BoundedHalting BoundedHaltingᶜ) := by
  have hc : BoundedHaltingᶜ ∉ P encBits := fun h =>
    BoundedHalting.notMem_P (by simpa using compl_mem_P h)
  obtain ⟨G, hG, h₁, -⟩ := exists_mem_P_ite_notMem_P recursivelyPresentable_P
    (closedUnderFiniteVariation_P encBits) isDecidable_boundedHalting
    isDecidable_boundedHalting.compl BoundedHalting.notMem_P hc
  exact ⟨G, hG, h₁, isDecidable_ite hG isDecidable_boundedHalting isDecidable_boundedHalting.compl,
    polyTimeReducible_ite_markedUnion hG⟩

end ComplexityTests.UniformDiagonalization
