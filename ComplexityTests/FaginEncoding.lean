/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.FirstOrder.Encoding
import Complexity.Logics.SecondOrder.Coloring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Tests: encodings of finite relational structures

The vocabulary of graphs has one binary symbol, and a vocabulary with a single nullary symbol
exercises the degenerate arities. The tests check that concrete inputs decode to the intended
structures, that well-formedness is decided as specified (including the empty structure and
nullary relations), that malformed inputs are outside every query language, and that the query
language of colorability contains the encoding of an edge for two colors but not for one.
-/

namespace ComplexityTests.FaginEncoding

open FirstOrder Language Structure CategoryTheory Cslib.Logic

/-- The vocabulary of graphs: the single binary symbol `adj`. -/
def graphVocabulary : Vocabulary Language.graph where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨2, adj⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun ⟨_, .adj⟩ => rfl }

@[simp]
theorem graphVocabulary_count : graphVocabulary.count = 1 :=
  rfl

@[simp]
theorem graphVocabulary_symbol (i : Fin graphVocabulary.count) :
    graphVocabulary.symbol i = ⟨2, adj⟩ :=
  rfl

/-- The language with a single nullary relation symbol. -/
def nullaryLanguage : Language :=
  ⟨fun _ => Empty, fun | 0 => Unit | _ + 1 => Empty⟩

instance : nullaryLanguage.IsRelational := fun _ => inferInstanceAs (IsEmpty Empty)

/-- The nullary symbol. -/
abbrev nullarySymbol : nullaryLanguage.Relations 0 := ()

/-- The vocabulary with the single nullary symbol. -/
def nullaryVocabulary : Vocabulary nullaryLanguage where
  count := 1
  symbol :=
    { toFun := fun _ => ⟨0, ()⟩
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun
        | ⟨0, ()⟩ => rfl
        | ⟨_ + 1, r⟩ => r.elim }

/-! ### Well-formedness -/

/-- The edge: two vertices, adjacent both ways, no loops. -/
def edge : EncodedStructure := (2, [ [false, true, true, false] ])

example : graphVocabulary.WellFormed edge := by decide +kernel
example : graphVocabulary.checkShape edge = true := by decide +kernel

/-- The empty graph has an empty adjacency table. -/
example : graphVocabulary.WellFormed (0, [ [] ]) := by decide +kernel

/-- A missing table, a surplus table, and a table of the wrong length are malformed. -/
example : ¬ graphVocabulary.WellFormed (2, []) := by decide +kernel
example : ¬ graphVocabulary.WellFormed (2, [ [false, true, true, false], [] ]) := by decide +kernel
example : ¬ graphVocabulary.WellFormed (2, [ [false, true, true] ]) := by decide +kernel
example : ¬ graphVocabulary.WellFormed (0, []) := by decide +kernel

/-- A nullary relation has a one-bit table, even on the empty structure. -/
example : nullaryVocabulary.WellFormed (0, [ [true] ]) := by decide +kernel
example : nullaryVocabulary.WellFormed (3, [ [false] ]) := by decide +kernel
example : ¬ nullaryVocabulary.WellFormed (0, [ [] ]) := by decide +kernel
example : ¬ nullaryVocabulary.WellFormed (3, [ [false, false] ]) := by decide +kernel

/-! ### Decoding -/

/-- The nullary relation holds in the decoded structure exactly when its bit is set. -/
example : (nullaryVocabulary.decode (0, [ [true] ])).RelMap nullarySymbol ![] := by
  rw [Vocabulary.relMap_decode]
  decide +kernel

example : ¬ (nullaryVocabulary.decode (3, [ [false] ])).RelMap nullarySymbol ![] := by
  rw [Vocabulary.relMap_decode]
  decide +kernel

/-- The edge decodes to the complete graph on two vertices. -/
theorem relMap_decode_edge (x y : Fin 2) :
    (graphVocabulary.decode edge).RelMap adj ![x, y] ↔ x ≠ y := by
  rw [Vocabulary.relMap_decode]
  fin_cases x <;> fin_cases y <;> decide +kernel

/-- Malformed inputs are never in a query language. -/
example (K : Set (Bundled Language.graph.Structure)) :
    (2, [ [false, true, true] ]) ∉ graphVocabulary.queryLanguage K :=
  fun h => absurd h.1 (by decide +kernel)

/-! ### Encoding -/

/-- Adjacency in the complete graph on two vertices. -/
theorem relMap_top_structure (x : Fin 2 → Fin 2) :
    (⊤ : SimpleGraph (Fin 2)).structure.RelMap adj x ↔ x 0 ≠ x 1 :=
  Iff.rfl

/-- The encoding of the complete graph on two vertices, numbered by itself, is the edge. -/
example : @Vocabulary.encode _ graphVocabulary (Fin 2) (⊤ : SimpleGraph (Fin 2)).structure 2
    (Equiv.refl _) = edge := by
  refine Prod.ext rfl (List.ext_getElem (by simp [Vocabulary.encode, edge]) fun i hi hi' => ?_)
  obtain rfl : i = 0 := by simpa [edge] using hi'
  simp only [Vocabulary.encode, List.getElem_ofFn, Vocabulary.relTable, graphVocabulary_symbol,
    Equiv.refl_symm, Equiv.coe_refl, Function.id_comp]
  refine List.ext_getElem (by simp [edge]) fun j hj hj' => ?_
  have hj4 : j < 4 := by simpa [edge] using hj'
  simp only [List.getElem_ofFn]
  interval_cases j <;> simp only [edge, relMap_top_structure, List.getElem_cons_zero,
    List.getElem_cons_succ, decide_eq_true_eq, decide_eq_false_iff_not] <;> decide +kernel +revert

/-- For a class closed under isomorphism, membership of an encoding is membership of the
structure: the encodings of the complete graph on two vertices along both numberings are in the
query language of two-colorability. -/
example (e : Fin 2 ≃ Fin 2) :
    (letI := (⊤ : SimpleGraph (Fin 2)).structure; graphVocabulary.encode (Fin 2) e) ∈
      graphVocabulary.queryLanguage
        {M | ∃ f : M → Fin 2, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} := by
  let _ := (⊤ : SimpleGraph (Fin 2)).structure
  rw [Vocabulary.mem_queryLanguage_encode (Cslib.Logic.ESO.Definable.colorable 2).isoClosed]
  exact ⟨id, fun x y h => h.ne⟩

/-! ### Colorability -/

/-- The edge is two-colorable: it belongs to the query language of two-colorability. -/
example : edge ∈ graphVocabulary.queryLanguage {M | ∃ f : M → Fin 2,
    ∀ x y, RelMap adj ![x, y] → f x ≠ f y} :=
  ⟨by decide +kernel, id, fun x y h => (relMap_decode_edge x y).1 h⟩

/-- The edge is not one-colorable. -/
example : edge ∉ graphVocabulary.queryLanguage {M | ∃ f : M → Fin 1,
    ∀ x y, RelMap adj ![x, y] → f x ≠ f y} := by
  intro h
  obtain ⟨f, hf⟩ := h.2
  exact hf (0 : Fin 2) (1 : Fin 2) ((relMap_decode_edge 0 1).2 (by decide)) (Subsingleton.elim _ _)

end ComplexityTests.FaginEncoding
