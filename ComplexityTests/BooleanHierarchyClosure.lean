/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Complexity.Classes.BooleanHierarchy.Closure

/-! Regression tests for Boolean-hierarchy closure and its level bounds. -/

open Cslib.Complexity

-- The generic intersection/difference bounds do not require the base class to contain ∅.
example :
    (∅ : Set Bool) ∩ ∅ ∈ differenceHierarchy ∅ (0 * 0) ∧
    (∅ : Set Bool) \ ∅ ∈ differenceHierarchy ∅ (0 * (0 + 1)) :=
  ⟨inter_mem_differenceHierarchy (by simp) (by simp) rfl rfl,
    diff_mem_differenceHierarchy (by simp) (by simp) rfl rfl⟩

-- All sets form a concrete non-vacuous base lattice; its first level contains any language.
example (A B : Set Bool) :
    A ∩ B ∈ differenceHierarchy Set.univ (1 * 1) ∧
    A \ B ∈ differenceHierarchy Set.univ (1 * (1 + 1)) ∧
    A ∪ B ∈ differenceHierarchy Set.univ ((1 + 1) * (1 + 1) + 1) :=
  ⟨inter_mem_differenceHierarchy (by simp) (by simp) (by simp) (by simp),
    diff_mem_differenceHierarchy (by simp) (by simp) (by simp) (by simp),
    union_mem_differenceHierarchy (by simp) (by simp) (by simp) (by simp) (by simp)⟩

-- NP languages occur at level one, so `inter_mem_BH` and `diff_mem_BH` compose without unfolding
-- the hierarchy.
example {α : Type} {enc : α ↪ List Bool} {A B C : Set α}
    (hA : A ∈ NP enc) (hB : B ∈ NP enc) (hC : C ∈ NP enc) :
    A ∩ B ∈ BH enc 1 ∧ (A ∩ B) \ C ∈ BH enc 2 :=
  let hAB : A ∩ B ∈ BH enc 1 :=
    inter_mem_BH (n := 1) (m := 1) (BH_one.symm ▸ hA) (BH_one.symm ▸ hB)
  ⟨hAB, diff_mem_BH (n := 1) (m := 1) hAB (BH_one.symm ▸ hC)⟩
