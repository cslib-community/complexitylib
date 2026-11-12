/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

/-!
# Cubic graphs with a proper 3-edge-colouring

A simple `3`-regular graph with a proper `3`-edge-colouring is determined by its three colour
classes, which are perfect matchings: `M.mate c v` is the other end of the edge of colour `c` at
`v` (`Cslib.CubicEdgeColoring`). The structure records exactly this: each `M.mate c` is a
fixed-point-free involution, and the three partners of a vertex are distinct. Its graph
`M.toSimpleGraph` is `3`-regular (`CubicEdgeColoring.isRegularOfDegree`), and colouring each edge
by its class (`CubicEdgeColoring.edgeLabeling`) is proper: the edges at a vertex have distinct
colours (`CubicEdgeColoring.edgeLabeling_injective`).

For an assignment `x : V → Bool`, read as the set of vertices where it is true, the induced
subgraph `G_x` *contains colour `c`* when some edge of colour `c` has both ends in `x`
(`CubicEdgeColoring.HasColor`, characterised through the graph and the labelling by
`CubicEdgeColoring.hasColor_iff`). The function `f_G` of
[ArenasBroadrickLiewVanDenBroeck2026, Section 5.1] is true exactly when `G_x` contains at least
one edge and at most two colours (`CubicEdgeColoring.someButNotAllColors`).

A graph is a **balanced-cut `γ`-edge expander** (`Cslib.IsBalancedCutExpander`) when every cut
into two parts of at least `|V| / 3` vertices each is crossed by at least `γ |V|` edges
[ArenasBroadrickLiewVanDenBroeck2026, Section 5.2].

## Main definitions

* `Cslib.CubicEdgeColoring`: a cubic graph with a proper `3`-edge-colouring, by colour classes.
* `Cslib.CubicEdgeColoring.toSimpleGraph`, `Cslib.CubicEdgeColoring.edgeLabeling`: its graph
  and colouring.
* `Cslib.CubicEdgeColoring.HasColor`, `Cslib.CubicEdgeColoring.someButNotAllColors`: colours of
  induced subgraphs and the function `f_G`.
* `Cslib.CubicEdgeColoring.IsIndep`: assignments that are independent sets.
* `Cslib.IsBalancedCutExpander`: expansion across balanced cuts.

## Main results

* `Cslib.CubicEdgeColoring.isRegularOfDegree`: the graph is `3`-regular.
* `Cslib.CubicEdgeColoring.edgeLabeling_injective`: the colouring is proper.
* `Cslib.CubicEdgeColoring.hasColor_iff`: `HasColor` through the graph and its colouring.
* `Cslib.CubicEdgeColoring.card_interedges`: the edges crossing a cut, counted by colour.

## References

* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib

open Finset

/-- A simple cubic graph with a proper `3`-edge-colouring, given by its colour classes:
`mate c v` is the other end of the edge of colour `c` at `v`. -/
structure CubicEdgeColoring (V : Type*) where
  /-- The other end of the edge of colour `c` at `v`. -/
  mate : Fin 3 → V → V
  /-- Each colour class is a matching. -/
  mate_mate : ∀ c v, mate c (mate c v) = v
  /-- There are no loops. -/
  mate_ne : ∀ c v, mate c v ≠ v
  /-- The three edges at a vertex go to distinct vertices: there are no parallel edges. -/
  mate_injective : ∀ v, Function.Injective fun c => mate c v

namespace CubicEdgeColoring

variable {V : Type*} (M : CubicEdgeColoring V)

/-- The simple graph of a cubic edge colouring: `u` and `v` are adjacent when they are joined
by an edge of some colour. -/
def toSimpleGraph : SimpleGraph V where
  Adj u v := ∃ c, M.mate c u = v
  symm := ⟨fun u _ ⟨c, h⟩ => ⟨c, h ▸ M.mate_mate c u⟩⟩
  loopless := ⟨fun u ⟨c, h⟩ => M.mate_ne c u h⟩

theorem toSimpleGraph_adj {u v : V} : M.toSimpleGraph.Adj u v ↔ ∃ c, M.mate c u = v :=
  Iff.rfl

theorem mate_eq_iff {c : Fin 3} {u v : V} : M.mate c u = v ↔ M.mate c v = u :=
  ⟨fun h => h ▸ M.mate_mate c u, fun h => h ▸ M.mate_mate c v⟩

/-- The colour of an edge is determined by its ends. -/
theorem color_unique {c c' : Fin 3} {u v : V} (h : M.mate c u = v) (h' : M.mate c' u = v) :
    c = c' :=
  M.mate_injective u (h.trans h'.symm)

instance [DecidableEq V] : DecidableRel M.toSimpleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (∃ c, M.mate c u = v))

/-- The neighbours of `v` are its three partners. -/
theorem neighborFinset_eq [Fintype V] [DecidableEq V] (v : V) :
    M.toSimpleGraph.neighborFinset v = univ.image fun c => M.mate c v := by
  ext u
  simp [toSimpleGraph_adj]

/-- **The graph is `3`-regular.** -/
theorem isRegularOfDegree [Fintype V] [DecidableEq V] : M.toSimpleGraph.IsRegularOfDegree 3 :=
  fun v => by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
      card_image_of_injective _ (M.mate_injective v)]
    rfl

/-- The colour of the edge between adjacent vertices. -/
noncomputable def color {u v : V} (h : M.toSimpleGraph.Adj u v) : Fin 3 :=
  h.choose

theorem mate_color {u v : V} (h : M.toSimpleGraph.Adj u v) : M.mate (M.color h) u = v :=
  h.choose_spec

theorem color_eq_iff {u v : V} (h : M.toSimpleGraph.Adj u v) {c : Fin 3} :
    M.color h = c ↔ M.mate c u = v :=
  ⟨fun hc => hc ▸ M.mate_color h, fun hc => M.color_unique (M.mate_color h) hc⟩

/-- The edge colouring of the graph by colour classes. -/
noncomputable def edgeLabeling : M.toSimpleGraph.EdgeLabeling (Fin 3) :=
  SimpleGraph.EdgeLabeling.mk (fun _ _ h => M.color h) fun _ _ h =>
    (M.color_eq_iff _).mpr (M.mate_eq_iff.mp (M.mate_color h))

theorem edgeLabeling_get {u v : V} (h : M.toSimpleGraph.Adj u v) :
    M.edgeLabeling.get u v h = M.color h :=
  rfl

/-- **The colouring is proper**: distinct edges at a vertex have distinct colours. -/
theorem edgeLabeling_injective {v u w : V} (hu : M.toSimpleGraph.Adj v u)
    (hw : M.toSimpleGraph.Adj v w) (h : M.edgeLabeling.get v u hu = M.edgeLabeling.get v w hw) :
    u = w := by
  rw [edgeLabeling_get, edgeLabeling_get] at h
  rw [← M.mate_color hu, ← M.mate_color hw, h]

/-! ### Colours of induced subgraphs and the function `f_G` -/

/-- The subgraph induced by the vertices where `x` is true contains an edge of colour `c`. -/
def HasColor (x : V → Bool) (c : Fin 3) : Prop :=
  ∃ v, x v = true ∧ x (M.mate c v) = true

instance [Fintype V] (x : V → Bool) (c : Fin 3) : Decidable (M.HasColor x c) :=
  inferInstanceAs (Decidable (∃ v, x v = true ∧ x (M.mate c v) = true))

/-- `HasColor` through the graph and its edge colouring. -/
theorem hasColor_iff (x : V → Bool) (c : Fin 3) :
    M.HasColor x c ↔ ∃ u v, ∃ h : M.toSimpleGraph.Adj u v,
      x u = true ∧ x v = true ∧ M.edgeLabeling.get u v h = c := by
  constructor
  · rintro ⟨v, hv, hm⟩
    exact ⟨v, _, ⟨c, rfl⟩, hv, hm, (M.color_eq_iff _).mpr rfl⟩
  · rintro ⟨u, v, h, hu, hv, hc⟩
    rw [edgeLabeling_get, color_eq_iff] at hc
    exact ⟨u, hu, hc ▸ hv⟩

/-- The function `f_G` of [ArenasBroadrickLiewVanDenBroeck2026, Section 5.1]: the subgraph
induced by `x` contains at least one edge and at most two colours. -/
def someButNotAllColors [Fintype V] (x : V → Bool) : Bool :=
  decide ((∃ c, M.HasColor x c) ∧ ∃ c, ¬M.HasColor x c)

/-- An assignment is an *independent set* when it contains no edge. -/
def IsIndep (x : V → Bool) : Prop :=
  ∀ c v, ¬(x v = true ∧ x (M.mate c v) = true)

instance [Fintype V] (x : V → Bool) : Decidable (M.IsIndep x) :=
  inferInstanceAs (Decidable (∀ c v, ¬(x v = true ∧ x (M.mate c v) = true)))

/-- Independent sets contain no colour, so `f_G` is false on them. -/
theorem someButNotAllColors_of_isIndep [Fintype V] {x : V → Bool} (hx : M.IsIndep x) :
    M.someButNotAllColors x = false := by
  simp only [someButNotAllColors, decide_eq_false_iff_not, not_and, not_exists, not_not]
  rintro ⟨c, v, hv⟩
  exact absurd hv (hx c v)

/-! ### Crossing edges -/

/-- **Crossing edges by colour.** The edges from `A` to its complement are counted by their ends
in `A` and their colours. -/
theorem card_interedges [Fintype V] [DecidableEq V] (A : Finset V) :
    (M.toSimpleGraph.interedges A Aᶜ).card =
      ∑ c, (A.filter fun u => M.mate c u ∉ A).card := by
  rw [← card_sigma]
  symm
  refine card_bij (fun p _ => (p.2, M.mate p.1 p.2)) ?_ ?_ ?_
  · rintro ⟨c, u⟩ hp
    simp only [mem_sigma, mem_univ, mem_filter, true_and] at hp
    exact M.toSimpleGraph.mem_interedges_iff.mpr ⟨hp.1, mem_compl.mpr hp.2, c, rfl⟩
  · rintro ⟨c, u⟩ - ⟨c', u'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [M.mate_injective u h]
  · rintro ⟨a, b⟩ he
    obtain ⟨ha, hb, c, hc⟩ := M.toSimpleGraph.mem_interedges_iff.mp he
    dsimp only at ha hb hc
    subst hc
    exact ⟨⟨c, a⟩, by simpa using ⟨ha, mem_compl.mp hb⟩, rfl⟩

end CubicEdgeColoring

/-- A graph is a **balanced-cut `γ`-edge expander** when every cut `(A, Aᶜ)` with both sides of
at least `|V| / 3` vertices is crossed by at least `γ |V|` edges. -/
def IsBalancedCutExpander {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (γ : ℝ) : Prop :=
  ∀ A : Finset V, Fintype.card V ≤ 3 * A.card → Fintype.card V ≤ 3 * Aᶜ.card →
    γ * Fintype.card V ≤ (G.interedges A Aᶜ).card

end Cslib
