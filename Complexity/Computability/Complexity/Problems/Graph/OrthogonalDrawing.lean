/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Complexity.Foundations.Geometry.Orthogonal.Simple

/-!
# Supplied planar orthogonal drawings of finite incidence graphs

Drawing data are a finite list of integer vertex positions and a finite list of polygonal
routes. Positions follow the declared vertex list and routes follow the edge list, including
parallel edge occurrences. All geometric conditions refer to complete real segment supports.
The drawing predicate uses loopless graphs with distinct declared vertex labels.

Edge orientation in the input list is immaterial: an incidence route may be listed in either
direction. Its endpoints must be the actual incident vertices. Routes are simple, orthogonal,
avoid nonincident vertices, and meet other routes only at shared incident vertices.

## Main definitions

* `Cslib.Complexity.Graph.OrthogonalDrawing`: finite position and route data.
* `Cslib.Complexity.Graph.drawingPosition`: the displayed point of a declared vertex.
* `Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing`: the geometric embedding certificate.
* `Cslib.Complexity.Graph.drawingFits`: bounds on all listed integer coordinates.
* `Cslib.Complexity.Graph.drawingWireLength`, `Cslib.Complexity.Graph.drawingSegmentCount`:
  explicit geometric output costs.

## References

These are the ordinary finite drawing conditions, expressed using Mathlib real segments and
the existing listed graph representation.
-/

@[expose] public section

namespace Cslib.Complexity.Graph

open Orthogonal

/-- Vertex positions and edge routes, in their graph-list orders. No graph data are duplicated.
-/
abbrev OrthogonalDrawing : Type := List Point × List Route

/-- Displayed position of a declared vertex, using its first position in the vertex list. -/
def drawingPosition (G : Graph) (d : OrthogonalDrawing) (v : ℕ) : Point :=
  d.1.getD (G.1.idxOf v) (0, 0)

/-- A supplied planar orthogonal embedding of the loopless listed graph. Parallel listed edges
have distinct simple routes; all contacts are tested in the real plane. -/
structure IsPlanarOrthogonalDrawing (G : Graph) (d : OrthogonalDrawing) : Prop where
  /-- Exactly one position per declared vertex. -/
  vertexCount : d.1.length = G.1.length
  /-- Exactly one route per listed edge occurrence. -/
  edgeCount : d.2.length = G.2.length
  /-- Labels describe distinct vertices. -/
  labelsNodup : G.1.Nodup
  /-- Distinct declared vertices have distinct positions. -/
  positionsNodup : d.1.Nodup
  /-- Both endpoints of every edge are declared. -/
  endpointsDeclared : ∀ e ∈ G.2, e.1 ∈ G.1 ∧ e.2 ∈ G.1
  /-- This interface concerns loopless graphs. -/
  loopless : ∀ e ∈ G.2, e.1 ≠ e.2
  /-- Route endpoints are the incident vertices, in either order. -/
  endpoints : ∀ i (hi : i < G.2.length),
    let r := d.2.getD i []
    let a := drawingPosition G d G.2[i].1
    let b := drawingPosition G d G.2[i].2
    (r.head? = some a ∧ r.getLast? = some b) ∨
      (r.head? = some b ∧ r.getLast? = some a)
  /-- Every segment is nondegenerate and axis aligned. -/
  orthogonal : ∀ i < G.2.length, IsOrthogonal (d.2.getD i [])
  /-- Every route has no retracing, repeated points, or self-crossing. -/
  simple : ∀ i < G.2.length, IsSimple (d.2.getD i [])
  /-- A route visits only its incident graph vertices. -/
  avoidsVertices : ∀ i (hi : i < G.2.length), ∀ v ∈ G.1,
    realPoint (drawingPosition G d v) ∈ support (d.2.getD i []) →
      v = G.2[i].1 ∨ v = G.2[i].2
  /-- Distinct routes intersect only at common graph endpoints. -/
  contacts : ∀ i (hi : i < G.2.length), ∀ j (hj : j < G.2.length), i ≠ j →
    ∀ p ∈ support (d.2.getD i []), p ∈ support (d.2.getD j []) →
      ∃ v ∈ G.1, (v = G.2[i].1 ∨ v = G.2[i].2) ∧
        (v = G.2[j].1 ∨ v = G.2[j].2) ∧ p = realPoint (drawingPosition G d v)

/-- Every listed position and route point lies in the nonnegative integer rectangle. -/
def drawingFits (d : OrthogonalDrawing) (width height : ℕ) : Prop :=
  (∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width ∧ 0 ≤ p.2 ∧ p.2 ≤ height) ∧
    ∀ r ∈ d.2, ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ width ∧ 0 ≤ p.2 ∧ p.2 ≤ height

/-- A larger rectangle preserves bounds on every displayed vertex and route point. -/
theorem drawingFits_mono {d : OrthogonalDrawing} {w h w' h' : ℕ}
    (hd : drawingFits d w h) (hw : w ≤ w') (hh : h ≤ h') : drawingFits d w' h' := by
  have hw' : (w : ℤ) ≤ w' := by exact_mod_cast hw
  have hh' : (h : ℤ) ≤ h' := by exact_mod_cast hh
  constructor
  · intro p hp
    have hb := hd.1 p hp
    exact ⟨hb.1, hb.2.1.trans hw', hb.2.2.1, hb.2.2.2.trans hh'⟩
  · intro r hr p hp
    have hb := hd.2 r hr p hp
    exact ⟨hb.1, hb.2.1.trans hw', hb.2.2.1, hb.2.2.2.trans hh'⟩

/-- The sum of Manhattan lengths of all incidence routes. -/
def drawingWireLength (d : OrthogonalDrawing) : ℕ := (d.2.map wireLength).sum

/-- The number of consecutive segments in all incidence routes. -/
def drawingSegmentCount (d : OrthogonalDrawing) : ℕ :=
  (d.2.map fun r => r.consecutivePairs.length).sum

end Cslib.Complexity.Graph
