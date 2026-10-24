/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Problems.Coloring
public import Complexity.Logics.SecondOrder.Existential
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.ModelTheory.Graph

/-!
# Colorability is existential second-order definable

A structure for Mathlib's language of graphs `FirstOrder.Language.graph` is a directed graph,
possibly with loops. It is `n`-colorable (`Cslib.Logic.FO.graph.Colorable`) when its vertices can
be colored with `n` colors so that the two ends of every edge have different colors. This is
expressed by the existential second-order sentence
`∃ C₀ … Cₙ₋₁, (∀ x, C₀ x ∨ ⋯ ∨ Cₙ₋₁ x) ∧ ∀ x y, E x y → ¬ (C₀ x ∧ C₀ y) ∧ ⋯ ∧ ¬ (Cₙ₋₁ x ∧ Cₙ₋₁ y)`
with one unary relation variable for each color [Fagin, Section 1, Example 1][Fagin1974],
[Immerman, Section 7.1][Immerman1999]. On the structure of a simple graph it says that the graph
is `n`-colorable in the sense of `SimpleGraph.Colorable`; in particular bipartiteness (`n = 2`) and
three-colorability (`n = 3`) are existential second-order definable.

## Main definitions

* `Cslib.Logic.ESO.Sentence.color`, `Cslib.Logic.ESO.Sentence.edge`,
  `Cslib.Logic.ESO.Sentence.colorableMatrix`: the color and edge relation symbols and the
  first-order matrix of the colorability sentence.
* `Cslib.Logic.ESO.Sentence.colorable`: the existential second-order sentence saying that a graph
  is `n`-colorable.

## Main results

* `Cslib.Logic.ESO.Sentence.realize_colorable_iff`: its semantics on directed graphs.
* `Cslib.Logic.ESO.Sentence.realize_colorable_structure_iff`: its semantics on simple graphs.
* `Cslib.Logic.ESO.Definable.colorable`: the class of `n`-colorable finite directed graphs is
  existential second-order definable.
* `Cslib.Logic.FO.Definable.simpleGraph`, `Cslib.Logic.ESO.Definable.colorable_simpleGraph`: the
  class of finite simple graphs is first-order definable, and the class of `n`-colorable ones is
  existential second-order definable.
* `Cslib.Logic.FO.graph.definable_ThreeColorable`,
  `Cslib.Logic.FO.graph.definable_SimpleThreeColorable`: the classes 3COL and classical 3COL of
  `Complexity.Logics.FirstOrder.Problems.Coloring` are existential second-order definable.

## References

* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe w

open FirstOrder Language Structure CategoryTheory BoundedFormula

/-- The class of finite simple graphs, the models of `FirstOrder.Language.Theory.simpleGraph`, is
first-order definable. -/
theorem Cslib.Logic.FO.Definable.simpleGraph :
    FO.Definable {M : Bundled.{w} Language.graph.Structure | M ⊨ Theory.simpleGraph} :=
  ⟨adj.irreflexive ⊓ adj.symmetric, fun _ _ => by simp [Theory.simpleGraph]⟩

namespace Cslib.Logic.ESO

namespace Sentence

/-- The relation symbol of the color `c`, a unary relation variable. -/
abbrev color {n : ℕ} (c : Fin n) :
    (Language.graph.sum (varLanguage fun _ : Fin n => 1)).Relations 1 :=
  Sum.inr ⟨c, rfl⟩

/-- The edge relation symbol, among the symbols of the colorability sentence. -/
abbrev edge (n : ℕ) : (Language.graph.sum (varLanguage fun _ : Fin n => 1)).Relations 2 :=
  Sum.inl adj

/-- The first-order part of the colorability sentence: every vertex has one of the colors, and
no edge joins two vertices of the same color. -/
noncomputable def colorableMatrix (n : ℕ) :
    (Language.graph.sum (varLanguage fun _ : Fin n => 1)).Sentence :=
  ∀' (BoundedFormula.iSup fun c => (color c).boundedFormula₁ &0) ⊓
    ∀' ∀' ((edge n).boundedFormula₂ &0 &1 ⟹
      BoundedFormula.iInf fun c => ∼((color c).boundedFormula₁ &0 ⊓ (color c).boundedFormula₁ &1))

/-- **Colorability**: the existential second-order sentence saying that every vertex has one of
`n` colors and that no edge joins two vertices of the same color. -/
noncomputable def colorable (n : ℕ) : Sentence Language.graph :=
  ⟨Fin n, fun _ => 1, colorableMatrix n⟩

variable {n : ℕ} {M : Type w} [Language.graph.Structure M]

private theorem relMap_edge (R : Fin n → Set (Fin 1 → M)) (x : Fin 2 → M) :
    @RelMap _ M (@sumStructure _ _ M _ (varLanguage.structure R)) 2 (edge n) x ↔ RelMap adj x :=
  Iff.rfl

private theorem relMap_color (R : Fin n → Set (Fin 1 → M)) (c : Fin n) (x : Fin 1 → M) :
    @RelMap _ M (@sumStructure _ _ M _ (varLanguage.structure R)) 1 (color c) x ↔ x ∈ R c :=
  Iff.rfl

/-- The first-order part of the colorability sentence holds of unary relations `R c` when they
cover the vertices and no edge has both ends in the same `R c`. -/
private theorem realize_colorableMatrix (R : Fin n → Set (Fin 1 → M)) :
    (letI := varLanguage.structure (arity := fun _ : Fin n => 1) R; M ⊨ colorableMatrix n) ↔
      (∀ x, ∃ c, ![x] ∈ R c) ∧ ∀ x y, RelMap adj ![x, y] → ∀ c, ![x] ∈ R c → ![y] ∉ R c := by
  simp [colorableMatrix, FirstOrder.Language.Sentence.Realize, Formula.Realize, relMap_edge,
    relMap_color, Fin.snoc]

/-- A directed graph satisfies the colorability sentence exactly when it has a coloring with `n`
colors in which the two ends of every edge have different colors. -/
theorem realize_colorable_iff :
    (colorable n).Realize M ↔ ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y := by
  change (∃ R : Fin n → Set (Fin 1 → M),
    letI := varLanguage.structure (arity := fun _ : Fin n => 1) R; M ⊨ colorableMatrix n) ↔ _
  simp only [realize_colorableMatrix]
  constructor
  · rintro ⟨R, hcover, hproper⟩
    choose f hf using hcover
    refine ⟨f, fun x y hxy hfxy => hproper x y hxy (f x) (hf x) ?_⟩
    rw [hfxy]
    exact hf y
  · rintro ⟨f, hf⟩
    exact ⟨fun c => {v | f (v 0) = c}, fun x => ⟨f x, rfl⟩,
      fun x y hxy _ hx hy => hf x y hxy (hx.trans hy.symm)⟩

/-- A simple graph satisfies the colorability sentence exactly when it is `n`-colorable. -/
theorem realize_colorable_structure_iff {V : Type w} (G : SimpleGraph V) :
    (letI := G.structure; (colorable n).Realize V) ↔ G.Colorable n := by
  let _ := G.structure
  rw [realize_colorable_iff]
  refine ⟨fun ⟨f, hf⟩ => ⟨.mk f fun h => hf _ _ h⟩, fun ⟨C⟩ => ⟨C, fun x y h => C.valid h⟩⟩

end Sentence

/-- **Colorability is existential second-order definable**: the class of finite directed graphs
that are `n`-colorable is a generalized spectrum [Fagin, Section 1, Example 1][Fagin1974]. -/
theorem Definable.colorable (n : ℕ) :
    Definable {M : Bundled.{w} Language.graph.Structure |
      ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} :=
  ⟨.colorable n, fun _ _ => Sentence.realize_colorable_iff.symm⟩

/-- **Colorability of simple graphs is existential second-order definable**: the class of finite
simple graphs that are `n`-colorable, such as the bipartite (`n = 2`) or three-colorable (`n = 3`)
ones, is the intersection of a first-order definable class with an existential second-order
definable one. -/
theorem Definable.colorable_simpleGraph (n : ℕ) :
    Definable {M : Bundled.{w} Language.graph.Structure |
      M ⊨ Theory.simpleGraph ∧ ∃ f : M → Fin n, ∀ x y, RelMap adj ![x, y] → f x ≠ f y} :=
  (Definable.of_fo FO.Definable.simpleGraph).inter (Definable.colorable n)

end Cslib.Logic.ESO

namespace Cslib.Logic.FO.graph

/-- **3COL is existential second-order definable.** -/
theorem definable_ThreeColorable : ESO.Definable ThreeColorable.{w} :=
  ESO.Definable.colorable 3

/-- **Classical 3COL is existential second-order definable.** -/
theorem definable_SimpleThreeColorable : ESO.Definable SimpleThreeColorable.{w} :=
  ESO.Definable.colorable_simpleGraph 3

end Cslib.Logic.FO.graph
