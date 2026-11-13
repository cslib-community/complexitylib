/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Fagin.Ordered
import Mathlib.ModelTheory.Graph

/-!
# Tests for ordered Fagin definability

An edge from `0` to `max` is an ordered query. Swapping the two input vertices changes its
truth even though the underlying input structures are isomorphic. The ordered API admits it.
-/

namespace CslibFrontierTests.OrderedFagin

open FirstOrder Language Structure Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Cslib.Complexity Turing.MultiTapeTM

/-- A two-vertex input relation consisting of just one directed edge. -/
def oneEdge (forward : Bool) : Ordered.Structure Language.graph where
  size := 2
  size_ge_two := le_refl _
  input.RelMap
    | .adj, xs => if forward then xs 0 = 0 ∧ xs 1 = 1 else xs 0 = 1 ∧ xs 1 = 0

/-- The ordered sentence asking for an edge from zero to the last vertex. -/
def edgeZeroMax : (language Language.graph).Sentence :=
  Relations.boundedFormula (L := language Language.graph) (Sum.inl adj)
    ![zero Language.graph, max Language.graph]

/-- The order-sensitive query defined by this sentence. -/
def edgeZeroMaxQuery : Query Language.graph := {M | edgeZeroMax.Realize M}

example : oneEdge true ∈ edgeZeroMaxQuery := by
  change (0 : Fin 2) = 0 ∧ (1 : Fin 2) = 1
  exact ⟨rfl, rfl⟩

example : oneEdge false ∉ edgeZeroMaxQuery := by
  change ¬ ((0 : Fin 2) = 1 ∧ (1 : Fin 2) = 0)
  decide

example : ESODefinable edgeZeroMaxQuery :=
  (show Ordered.Definable edgeZeroMaxQuery from ⟨edgeZeroMax, fun _ => Iff.rfl⟩).esoDefinable

/-- The input structures are isomorphic by exchanging their two elements. -/
def swapInputs : oneEdge true ≃[Language.graph] oneEdge false where
  toEquiv := Equiv.swap (0 : Fin 2) (1 : Fin 2)
  map_fun' f := isEmptyElim f
  map_rel' := by
    intro n r xs
    cases r
    change Fin 2 → Fin 2 at xs
    change ((Equiv.swap (0 : Fin 2) 1) (xs 0) = 1 ∧
      (Equiv.swap (0 : Fin 2) 1) (xs 1) = 0) ↔ xs 0 = (0 : Fin 2) ∧ xs 1 = (1 : Fin 2)
    simp [Equiv.swap_apply_eq_iff]

/-- A concrete finite vocabulary, including the exact binary relation arity. -/
def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

/-- This concrete order-sensitive query satisfies the recovered theorem's NP premise. -/
theorem edgeZeroMax_mem_NP : edgeZeroMaxQuery.encodedLanguage graphVocabulary ∈ NP encStructure :=
  Definable.encodedLanguage_mem_NP graphVocabulary ⟨edgeZeroMax, fun _ => Iff.rfl⟩

example : ESODefinable edgeZeroMaxQuery :=
  ESODefinable.of_encodedLanguage_mem_NP graphVocabulary edgeZeroMax_mem_NP

example : encode graphVocabulary (oneEdge true) ∈
    edgeZeroMaxQuery.encodedLanguage graphVocabulary :=
  (mem_encodedLanguage_encode _ _ _).mpr ⟨rfl, rfl⟩

example : encode graphVocabulary (oneEdge false) ∉
    edgeZeroMaxQuery.encodedLanguage graphVocabulary := by
  rw [mem_encodedLanguage_encode]
  change ¬ ((0 : Fin 2) = 1 ∧ (1 : Fin 2) = 0)
  decide

example : (0, [ [] ]) ∉ edgeZeroMaxQuery.encodedLanguage graphVocabulary :=
  Query.not_mem_encodedLanguage_of_lt_two _ _ (by decide)

example : (1, [ [true] ]) ∉ edgeZeroMaxQuery.encodedLanguage graphVocabulary :=
  Query.not_mem_encodedLanguage_of_lt_two _ _ (by decide)

example : (2, []) ∉ edgeZeroMaxQuery.encodedLanguage graphVocabulary :=
  Query.not_mem_encodedLanguage_of_not_wellFormed _ _ (by decide)

example : (2, [ [true] ]) ∉ edgeZeroMaxQuery.encodedLanguage graphVocabulary :=
  Query.not_mem_encodedLanguage_of_not_wellFormed _ _ (by decide)

end CslibFrontierTests.OrderedFagin
