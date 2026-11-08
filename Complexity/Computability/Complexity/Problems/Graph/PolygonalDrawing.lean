/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem
public import Complexity.Foundations.Geometry.Polygonal.Route

/-!
# Polygonal drawings of listed multigraphs

Each listed edge occurrence has its own finite polygonal route in the real plane `ℂ`.
Both ends of a loop remain distinct route parameters. Repeated declarations of the same
natural number name the same point; only distinct declared names must have distinct points.
There is no constraint on undeclared names and no degree bound.

Embedding is expressed entirely by actual real segment intersections and route parameters.
It excludes self-intersections, visits to unrelated vertices and intersections of different
edge interiors. It does not contain a rotation, numerical genus or a drawing provider.

## Main definitions

* `Cslib.Complexity.Graph.PolygonalDrawing`: coordinates and finite edge routes.
* `Cslib.Complexity.Graph.PolygonalDrawing.IsEmbedding`: genuine nonintersection conditions.
-/

public section

namespace Cslib.Complexity.Graph

/-- An actual finite polygonal drawing of the existing indexed listed graph. The endpoint
equations hold even before requiring the endpoints to be among the declared names. -/
structure PolygonalDrawing (G : Graph) where
  /-- The point of each vertex name; undeclared names have no geometric restrictions. -/
  vertex : ℕ → ℂ
  /-- One route per listed edge occurrence, without identifying equal edge pairs. -/
  route : Fin G.2.length → Polygonal.Route
  /-- The two route ends are the corresponding named graph endpoints. -/
  endpoint_eq : ∀ e b, (route e).endpoint b = vertex (Dart.vertex (e, b))

namespace PolygonalDrawing

variable {G : Graph} (D : PolygonalDrawing G)

/-- An actual outgoing end-segment vector, with both germs retained at a loop. -/
@[expose] def germ (d : Dart G) : ℂ := (D.route d.1).germ d.2

/-- The actual direction of an outgoing segment in the oriented real plane. -/
@[expose] noncomputable def direction (d : Dart G) : Real.Angle := (D.germ d).arg

/-- Geometric embedding of the indexed multigraph. Every intersection below is tested at
arbitrary real parameters of actual straight segments. Endpoint closure of an individual
loop is permitted by `simple`; different edge routes may meet only at common named ends. -/
structure IsEmbedding : Prop where
  /-- Distinct declared names, including isolates, have distinct points. -/
  vertices_injective : Set.InjOn D.vertex {v | v ∈ G.1}
  /-- Each route is simple except for its intended loop closure. -/
  simple : ∀ e, (D.route e).IsSimple
  /-- A declared vertex on an edge route must occur at the corresponding original end. -/
  vertex_contacts : ∀ e (i : Fin (D.route e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
    ∀ v ∈ G.1, (D.route e).eval i t = D.vertex v →
      ∃ b, (D.route e).AtEnd i t b ∧ Dart.vertex (e, b) = v
  /-- Different indexed edge occurrences intersect only at common original endpoints. -/
  edge_contacts : ∀ e f, e ≠ f → ∀ (i : Fin (D.route e).segments)
    (j : Fin (D.route f).segments) (s t : ℝ), s ∈ Set.Icc 0 1 → t ∈ Set.Icc 0 1 →
    (D.route e).eval i s = (D.route f).eval j t →
      ∃ b c, (D.route e).AtEnd i s b ∧ (D.route f).AtEnd j t c ∧
        Dart.vertex (e, b) = Dart.vertex (f, c)

/-- A geometric embedding has nonzero outgoing end segments. -/
theorem IsEmbedding.germ_ne_zero {D : PolygonalDrawing G} (hD : D.IsEmbedding) (d : Dart G) :
    D.germ d ≠ 0 := (hD.simple d.1).germ_ne_zero d.2

/-- Declared isolated vertices are separated just like all other distinct declared names. -/
theorem IsEmbedding.vertex_ne {D : PolygonalDrawing G} (hD : D.IsEmbedding)
    {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) (huv : u ≠ v) :
    D.vertex u ≠ D.vertex v := fun h => huv (hD.vertices_injective hu hv h)

end PolygonalDrawing
end Cslib.Complexity.Graph
