/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Rishik Pavani
-/

module
-- upstream: candidate (Mathlib, `Mathlib/ModelTheory/Graph.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.ModelTheory.Graph

/-!
# Graph maps as maps of `Language.graph`-structures

A simple graph `G` on `V` is a structure of Mathlib's language of graphs `FirstOrder.Language.graph`
through `SimpleGraph.structure`. This file translates between the graph maps of
`Mathlib/Combinatorics/SimpleGraph/Maps.lean` and the maps of `Language.graph`-structures: a graph
isomorphism `G ≃g H` is exactly an equivalence `V ≃[Language.graph] W` of the structures
`G.structure` and `H.structure`, and an induced embedding `G ↪g H` is exactly an embedding
`V ↪[Language.graph] W`. Isomorphisms therefore transfer the realization of every first-order
formula, and isomorphic graphs satisfy the same sentences.

## Main definitions

* `SimpleGraph.Iso.toLanguageEquiv`, `SimpleGraph.Iso.ofLanguageEquiv`: a graph isomorphism as an
  equivalence of `Language.graph`-structures, and back.
* `SimpleGraph.Embedding.toLanguageEmbedding`, `SimpleGraph.Embedding.ofLanguageEmbedding`: an
  induced graph embedding as an embedding of `Language.graph`-structures, and back.

## Main results

* `SimpleGraph.Iso.realize_boundedFormula_iff`, `SimpleGraph.Iso.realize_formula_iff`: a graph
  isomorphism transfers the realization of formulas along the isomorphism.
* `SimpleGraph.Iso.realize_sentence_iff`: isomorphic simple graphs satisfy the same sentences of
  the language of graphs.
-/

public section

namespace SimpleGraph

open FirstOrder Language

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

namespace Embedding

/-- An induced embedding of simple graphs is an embedding of the `Language.graph`-structures. -/
def toLanguageEmbedding (f : G ↪g H) :
    @Language.Embedding Language.graph V W G.structure H.structure :=
  letI := G.structure
  letI := H.structure
  { toEmbedding := f.toEmbedding
    map_fun' := fun g => isEmptyElim g
    map_rel' := fun {n} R x => by
      match n, R with
      | 2, .adj => exact f.map_adj_iff }

/-- An embedding of the `Language.graph`-structures of two simple graphs is an induced embedding
of the graphs. -/
def ofLanguageEmbedding (f : @Language.Embedding Language.graph V W G.structure H.structure) :
    G ↪g H where
  toEmbedding := @Language.Embedding.toEmbedding _ _ _ G.structure H.structure f
  map_rel_iff' {a b} := by
    let := G.structure
    let := H.structure
    exact f.map_rel adj ![a, b]

@[simp]
theorem coe_toLanguageEmbedding (f : G ↪g H) :
    (letI := G.structure; letI := H.structure; ⇑f.toLanguageEmbedding) = ⇑f := by
  funext; rfl

@[simp]
theorem coe_ofLanguageEmbedding
    (f : @Language.Embedding Language.graph V W G.structure H.structure) :
    ⇑(ofLanguageEmbedding f) = (letI := G.structure; letI := H.structure; ⇑f) := by
  funext; rfl

@[simp]
theorem ofLanguageEmbedding_toLanguageEmbedding (f : G ↪g H) :
    ofLanguageEmbedding f.toLanguageEmbedding = f := by
  ext; rfl

@[simp]
theorem toLanguageEmbedding_ofLanguageEmbedding
    (f : @Language.Embedding Language.graph V W G.structure H.structure) :
    (ofLanguageEmbedding f).toLanguageEmbedding = f := by
  let := G.structure
  let := H.structure
  ext; rfl

end Embedding

namespace Iso

/-- A graph isomorphism is an equivalence of the `Language.graph`-structures. -/
def toLanguageEquiv (e : G ≃g H) : @Language.Equiv Language.graph V W G.structure H.structure :=
  letI := G.structure
  letI := H.structure
  { toEquiv := e.toEquiv
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      match n, R with
      | 2, .adj => exact e.map_adj_iff }

/-- An equivalence of the `Language.graph`-structures of two simple graphs is a graph
isomorphism. -/
def ofLanguageEquiv (f : @Language.Equiv Language.graph V W G.structure H.structure) :
    G ≃g H where
  toEquiv := @Language.Equiv.toEquiv _ _ _ G.structure H.structure f
  map_rel_iff' {a b} := by
    let := G.structure
    let := H.structure
    exact f.map_rel adj ![a, b]

@[simp]
theorem coe_toLanguageEquiv (e : G ≃g H) :
    (letI := G.structure; letI := H.structure; ⇑e.toLanguageEquiv) = ⇑e := by
  funext; rfl

@[simp]
theorem coe_ofLanguageEquiv (f : @Language.Equiv Language.graph V W G.structure H.structure) :
    ⇑(ofLanguageEquiv f) = (letI := G.structure; letI := H.structure; ⇑f) := by
  funext; rfl

@[simp]
theorem ofLanguageEquiv_toLanguageEquiv (e : G ≃g H) : ofLanguageEquiv e.toLanguageEquiv = e := by
  ext; rfl

@[simp]
theorem toLanguageEquiv_ofLanguageEquiv
    (f : @Language.Equiv Language.graph V W G.structure H.structure) :
    (ofLanguageEquiv f).toLanguageEquiv = f := by
  let := G.structure
  let := H.structure
  ext; rfl

/-- A graph isomorphism transfers the realization of bounded formulas of the language of graphs:
`φ` holds in `H` at the image under `e` of an assignment exactly when it holds in `G` at the
assignment. -/
theorem realize_boundedFormula_iff (e : G ≃g H) {α : Type*} {n : ℕ}
    (φ : Language.graph.BoundedFormula α n) (v : α → V) (xs : Fin n → V) :
    (letI := H.structure; φ.Realize (e ∘ v) (e ∘ xs)) ↔
      (letI := G.structure; φ.Realize v xs) :=
  letI := G.structure
  letI := H.structure
  StrongHomClass.realize_boundedFormula e.toLanguageEquiv φ

/-- A graph isomorphism transfers the realization of formulas of the language of graphs: `φ`
holds in `H` at the image under `e` of an assignment exactly when it holds in `G` at the
assignment. -/
theorem realize_formula_iff (e : G ≃g H) {α : Type*} (φ : Language.graph.Formula α)
    (v : α → V) :
    (letI := H.structure; φ.Realize (e ∘ v)) ↔ (letI := G.structure; φ.Realize v) :=
  letI := G.structure
  letI := H.structure
  StrongHomClass.realize_formula e.toLanguageEquiv φ

/-- Isomorphic simple graphs satisfy the same sentences of the language of graphs. -/
theorem realize_sentence_iff (e : G ≃g H) (φ : Language.graph.Sentence) :
    (letI := G.structure; V ⊨ φ) ↔ (letI := H.structure; W ⊨ φ) :=
  letI := G.structure
  letI := H.structure
  StrongHomClass.realize_sentence e.toLanguageEquiv φ

end Iso

end SimpleGraph
