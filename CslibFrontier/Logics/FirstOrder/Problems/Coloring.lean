/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Interpretation.Tagged
public import Mathlib.ModelTheory.Graph

/-!
# Colorability of graph structures

A structure for Mathlib's language of graphs `FirstOrder.Language.graph` is a directed graph,
possibly with loops. It is `n`-colorable (`graph.Colorable`) when its vertices can be colored with
`n` colors so that the two ends of every edge have different colors; a loop makes it uncolorable,
and on simple graphs this is `SimpleGraph.Colorable`. The classes `graph.ThreeColorable` of
three-colorable graph structures (3COL, loops allowed) and `graph.SimpleThreeColorable` of
three-colorable simple graphs (classical 3COL) are closed under isomorphism and invariant
under disjoint copies. Their existential second-order definability is in
`CslibFrontier.Logics.SecondOrder.Coloring`, and the machine-level problem, on graphs encoded as
lists
of vertices and edges, is `Cslib.Complexity.ThreeColoring`.

## Main definitions

* `Cslib.Logic.FO.graph.Colorable`: `n`-colorability of a graph structure.
* `Cslib.Logic.FO.graph.ThreeColorable`, `Cslib.Logic.FO.graph.SimpleThreeColorable`: the classes
  of three-colorable graph structures and of three-colorable simple graphs.

## Main results

* `Cslib.Logic.FO.graph.isoClosed_ThreeColorable`,
  `Cslib.Logic.FO.graph.copyInvariant_ThreeColorable` and their simple-graph versions.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
-/

@[expose] public section

universe w

namespace Cslib.Logic.FO.graph

open FirstOrder Language Structure CategoryTheory

/-- A graph structure is **`n`-colorable** when its vertices can be colored with `n` colors so
that the two ends of every edge have different colors. -/
def Colorable (n : ℕ) (M : Type*) [Language.graph.Structure M] : Prop :=
  ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y

/-- **3COL**: the class of three-colorable graph structures, loops allowed. -/
def ThreeColorable : Set (Bundled.{w} Language.graph.Structure) :=
  {M | Colorable 3 M}

/-- **Classical 3COL**: the class of three-colorable simple graphs. -/
def SimpleThreeColorable : Set (Bundled.{w} Language.graph.Structure) :=
  {M | M ⊨ Theory.simpleGraph ∧ Colorable 3 M}

variable {J M N : Type*} [Language.graph.Structure M] [Language.graph.Structure N] {n : ℕ}

/-- Colorability is invariant under isomorphism. -/
theorem Colorable.of_equiv (e : M ≃[Language.graph] N) (h : Colorable n M) : Colorable n N := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun y => f (e.symm y), fun x y hxy => hf _ _ ?_⟩
  rwa [← relMap_pair_equiv e, e.apply_symm_apply, e.apply_symm_apply]

/-- 3COL is closed under isomorphism. -/
theorem isoClosed_ThreeColorable : IsoClosed ThreeColorable.{w} :=
  IsoClosed.of_forall_imp fun _ _ _ e => Colorable.of_equiv e

/-- Classical 3COL is closed under isomorphism. -/
theorem isoClosed_SimpleThreeColorable : IsoClosed SimpleThreeColorable.{w} :=
  IsoClosed.of_forall_imp fun _ _ _ e h =>
    ⟨by have := h.1; exact StrongHomClass.theory_model (T := Theory.simpleGraph) e,
      Colorable.of_equiv e h.2⟩

/-- The empty graph is colorable. -/
theorem colorable_of_isEmpty [IsEmpty M] : Colorable n M :=
  ⟨isEmptyElim, fun x => isEmptyElim x⟩

/-- A positive number of disjoint copies of a graph is `n`-colorable exactly when the graph is. -/
theorem colorable_copies_iff [Nonempty J] : Colorable n (Copies J M) ↔ Colorable n M := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨j₀⟩ := ‹Nonempty J›
    exact ⟨fun x => f ⟨j₀, x⟩,
      fun x y h => hf _ _ ((Copies.relMap_copies_two adj _ _).2 ⟨rfl, h⟩)⟩
  · rintro ⟨f, hf⟩
    exact ⟨fun x => f x.val, fun x y h => hf _ _ ((Copies.relMap_copies_two adj _ _).1 h).2⟩

/-- A positive number of disjoint copies of a graph is a simple graph exactly when the graph is. -/
theorem simpleGraph_copies_iff [Nonempty J] :
    Copies J M ⊨ Theory.simpleGraph ↔ M ⊨ Theory.simpleGraph := by
  simp only [Theory.simpleGraph_model_iff, Copies.relMap_copies_two]
  constructor
  · rintro ⟨⟨hirr⟩, ⟨hsymm⟩⟩
    obtain ⟨j₀⟩ := ‹Nonempty J›
    exact ⟨⟨fun x h => hirr ⟨j₀, x⟩ ⟨rfl, h⟩⟩,
      ⟨fun x y h => (hsymm ⟨j₀, x⟩ ⟨j₀, y⟩ ⟨rfl, h⟩).2⟩⟩
  · rintro ⟨⟨hirr⟩, ⟨hsymm⟩⟩
    exact ⟨⟨fun x h => hirr x.val h.2⟩, ⟨fun x y h => ⟨h.1.symm, hsymm _ _ h.2⟩⟩⟩

/-- 3COL is invariant under copies. -/
theorem copyInvariant_ThreeColorable : CopyInvariant ThreeColorable.{w} :=
  fun _ _ _ _ _ _ => colorable_copies_iff

/-- Classical 3COL is invariant under copies. -/
theorem copyInvariant_SimpleThreeColorable : CopyInvariant SimpleThreeColorable.{w} :=
  fun _ _ _ _ _ _ => and_congr simpleGraph_copies_iff colorable_copies_iff

end Cslib.Logic.FO.graph
