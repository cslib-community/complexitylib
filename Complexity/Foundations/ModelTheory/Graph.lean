/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/ModelTheory/Graph.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.ModelTheory.Graph

/-!
# Isomorphic graphs satisfy the same sentences

A simple graph `G` on `V` is a structure of Mathlib's language of graphs `FirstOrder.Language.graph`
through `SimpleGraph.structure`. A graph isomorphism `G ≃g H` is then an equivalence of
`Language.graph`-structures, so `G` and `H` satisfy the same first-order sentences
(`SimpleGraph.Iso.realize_sentence_iff`).

## Main results

* `SimpleGraph.Iso.realize_sentence_iff`: isomorphic simple graphs satisfy the same sentences of
  the language of graphs.
-/

public section

namespace SimpleGraph.Iso

open FirstOrder Language

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Isomorphic simple graphs satisfy the same sentences of the language of graphs. -/
theorem realize_sentence_iff (e : G ≃g H) (φ : Language.graph.Sentence) :
    (letI := G.structure; V ⊨ φ) ↔ (letI := H.structure; W ⊨ φ) := by
  let := G.structure
  let := H.structure
  let f : V ≃[Language.graph] W :=
    { toEquiv := e.toEquiv
      map_fun' := fun f => isEmptyElim f
      map_rel' := fun {n} R x => by
        match n, R with
        | 2, .adj => exact e.map_adj_iff }
  exact StrongHomClass.realize_sentence f φ

end SimpleGraph.Iso
