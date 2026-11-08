/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import all Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Dual

/-!
# Boolean cycles as boundaries of face colors

Vertex parity counts actual indexed darts: a loop contributes twice. Face boundaries take
the exclusive or of the colors of the two actual incident face orbits. On a componentwise
numerically genus-zero rotation, the vertex-even labels are exactly these boundaries.

This is an original finite reconstruction, obtained by applying the existing face-even
lifting theorem to the actual indexed dual. It includes sparse and duplicate vertex
declarations, parallel occurrences, loops, points, disconnected graphs and the empty graph.
It asserts no geometric realization, Jordan theorem or Hanani–Tutte theorem.

## Main definitions

* `Cslib.Complexity.Graph.vertexParity`: actual dart-incidence parity.
* `Cslib.Complexity.Graph.RotationSystem.faceBoundary`: boundary of actual face colors.

## Main results

* `Cslib.Complexity.Graph.RotationSystem.vertexEven_iff_exists_faceColors`: cycle exactness.
-/

public section

namespace Cslib.Complexity.Graph

open Classical in
/-- Sum of edge bits over actual dart incidences at a natural-number vertex. Both ends of a
loop occur, so their contributions cancel. Undeclared names with no darts have zero parity. -/
@[expose] noncomputable def vertexParity (G : Graph) (x : Fin G.2.length → Bool)
    (v : ℕ) : Bool :=
  ∑ d : Dart G, if d.vertex = v then x d.1 else 0

/-- Every vertex has even incidence parity, counting both indexed ends of every loop. -/
@[expose] def VertexEven (G : Graph) (x : Fin G.2.length → Bool) : Prop :=
  ∀ v, G.vertexParity x v = false

namespace RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- The boundary of face colors labels each edge by the exclusive or of its two incident
actual face orbits. A bridge incident twice to one face consequently receives `false`. -/
@[expose] def faceBoundary (q : r.Face → Bool) : Fin G.2.length → Bool :=
  fun i => q (Quotient.mk _ (i, false)) ^^ q (Quotient.mk _ (i, true))

/-- Either end reads the same face boundary. -/
theorem faceBoundary_dart (q : r.Face → Bool) (d : Dart G) :
    r.faceBoundary q d.1 =
      (q (Quotient.mk _ d) ^^ q (Quotient.mk _ d.reverse)) := by
  rcases d with ⟨i, b⟩
  cases b
  · rfl
  · exact Bool.xor_comm _ _

/-- The canonical face/dual-vertex equivalence sends a dart's face to its actual face ID. -/
@[simp] theorem faceDualVertexEquiv_mk (d : Dart G) :
    (r.faceDualVertexEquiv (Quotient.mk _ d)).val = r.faceId d := by
  rfl

/-- Dual-face parity is original vertex parity, with the reversal required by the actual
dual face successor. No Euler or endpoint declaration assumption is needed. -/
theorem dual_faceParity_eq_vertexParity (x : Fin G.2.length → Bool) (d : Dart G) :
    r.dualRotation.faceParity (fun i => x (Fin.cast r.dualGraph_length i))
        (Quotient.mk _ (r.dualDartEquiv d)) = G.vertexParity x d.reverse.vertex := by
  classical
  rw [r.dualRotation.faceParity_mk, parityOn_eq_sum, Finset.sum_filter]
  rw [← Equiv.sum_comp r.dualDartEquiv]
  simp only [r.dual_sameFace_iff]
  change (∑ e : Dart G, if d.reverse.vertex = e.reverse.vertex then x e.1 else 0) = _
  have hs := Equiv.sum_comp (Dart.reversal G)
    (fun e : Dart G => if d.reverse.vertex = e.reverse.vertex then x e.1 else 0)
  change (∑ e : Dart G,
    if d.reverse.vertex = e.reverse.reverse.vertex then x e.1 else 0) = _ at hs
  rw [← hs]
  simp only [Dart.reverse_reverse, vertexParity, eq_comm]

/-- Vertex-even labels are precisely face-even labels on the actual indexed dual. -/
theorem vertexEven_iff_dual_faceEven (x : Fin G.2.length → Bool) :
    G.VertexEven x ↔
      r.dualRotation.FaceEven (fun i => x (Fin.cast r.dualGraph_length i)) := by
  rw [r.dualRotation.faceEven_iff_dart]
  constructor
  · intro h a
    obtain ⟨d, rfl⟩ := r.dualDartEquiv.surjective a
    rw [r.dual_faceParity_eq_vertexParity]
    exact h _
  · intro h v
    by_cases hv : ∃ d : Dart G, d.vertex = v
    · obtain ⟨d, rfl⟩ := hv
      simpa only [r.dual_faceParity_eq_vertexParity, Dart.reverse_reverse] using
        h (r.dualDartEquiv d.reverse)
    · classical
      simp only [vertexParity]
      apply Finset.sum_eq_zero
      intro d _
      exact ite_eq_right (fun hd => hv ⟨d, hd⟩)

/-- A face boundary becomes the ordinary endpoint gradient on the actual indexed dual. -/
theorem dual_edgeGradient_faceColors (q : r.Face → Bool) :
    ∃ spin : ℕ → Bool, r.dualGraph.edgeGradient spin =
      fun i => r.faceBoundary q (Fin.cast r.dualGraph_length i) := by
  classical
  let spin (v : ℕ) := if hv : v ∈ r.dualGraph.1 then
    q (r.faceDualVertexEquiv.symm ⟨v, hv⟩) else false
  have hs (d : Dart G) : spin (r.faceId d) = q (Quotient.mk _ d) := by
    have hv : r.faceId d ∈ r.dualGraph.1 := by
      simpa only [r.vertex_dualDartEquiv] using r.dual_vertex_mem (r.dualDartEquiv d)
    dsimp only [spin]
    rw [dite_eq_left hv]
    congr 1
    apply r.faceDualVertexEquiv.injective
    simp only [Equiv.apply_symm_apply]
    exact Subtype.ext (r.faceDualVertexEquiv_mk d).symm
  refine ⟨spin, funext fun i => ?_⟩
  let j := Fin.cast r.dualGraph_length i
  have hd := r.dualGraph.edgeGradient_dart spin (r.dualDartEquiv (j, false))
  change r.dualGraph.edgeGradient spin i = _ at hd ⊢
  rw [hd, ← r.dualDartEquiv_reverse, r.vertex_dualDartEquiv,
    r.vertex_dualDartEquiv, hs, hs]
  rfl

/-- Every face boundary has even incidence parity, with no genus or endpoint assumptions. -/
theorem vertexEven_faceBoundary (q : r.Face → Bool) : G.VertexEven (r.faceBoundary q) := by
  rw [r.vertexEven_iff_dual_faceEven]
  obtain ⟨spin, hs⟩ := r.dual_edgeGradient_faceColors q
  rw [← hs]
  exact r.dualRotation.faceEven_edgeGradient spin

/-- Under declared endpoints and componentwise numerical genus zero, every vertex-even
Boolean edge label is a boundary of actual face colors, and conversely. The quantifiers
include arbitrary disconnected supports, loops, parallels, sparse names, duplicate declared
vertices, isolated points and empty graphs. This is finite map mathematics, not a geometric
planarity or Hanani–Tutte statement. -/
theorem vertexEven_iff_exists_faceColors
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) (hgenus : r.NumericalGenusZero)
    (x : Fin G.2.length → Bool) :
    G.VertexEven x ↔ ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  constructor
  · intro hx
    obtain ⟨spin, hs⟩ := (r.dualRotation.faceEven_iff_exists_vertexSpins
      r.dualGraph_endpoints_declared ((r.numericalGenusZero_dual_iff hG).mpr hgenus)
      (fun i => x (Fin.cast r.dualGraph_length i))).mp
        ((r.vertexEven_iff_dual_faceEven x).mp hx)
    refine ⟨fun f => spin (r.faceDualVertexEquiv f).val, funext fun i => ?_⟩
    have he := congrFun hs (r.dualDartEquiv (i, false)).1
    rw [r.dualGraph.edgeGradient_dart spin (r.dualDartEquiv (i, false)),
      ← r.dualDartEquiv_reverse, r.vertex_dualDartEquiv,
      r.vertex_dualDartEquiv] at he
    simp only [faceBoundary, r.faceDualVertexEquiv_mk]
    exact he
  · rintro ⟨q, rfl⟩
    exact r.vertexEven_faceBoundary q

end RotationSystem
end Cslib.Complexity.Graph
