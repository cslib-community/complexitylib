/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Basic
public import Complexity.Computability.PCP.DegreeReduction
public import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.ProdSigma

/-!
# Enumerating half-edges and vertex clouds

Degree reduction replaces a vertex by its incident half-edges. The executable enumeration uses
edge indices and Boolean endpoint tags, including both ends of a loop and every parallel edge.
`cloudEquiv` proves that this enumeration is exactly the cloud in the existing mathematical
degree-reduction construction. Its inverse is list search, not a choice of a finite enumeration.

## Main definitions

* `Cslib.PCP.Encoded.Graph.halfEdges`: the ordered half-edges of an edge list.
* `Cslib.PCP.Encoded.Graph.endpoint`: read the endpoint of a numbered half-edge.
* `Cslib.PCP.Encoded.Graph.cloud`: enumerate the half-edges incident to a vertex.
* `Cslib.PCP.Encoded.Graph.cloudEquiv`: identify this enumeration with the mathematical cloud.

## Main results

* `Cslib.PCP.Encoded.Graph.mem_cloud_iff`: the enumeration includes exactly incident half-edges.
* `Cslib.PCP.Encoded.Graph.nodup_cloud`: each half-edge occurs once.
* `Cslib.PCP.Encoded.Graph.isPolyTime_cloud`: enumeration, scanning and endpoint lookup are
  uniformly polynomial-time in the encoded graph and vertex.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM

variable {C α Input : Type} {input : Input ↪ List Bool} {enc : C ↪ List Bool}

/-- The ordered half-edges: first and second endpoint of every edge, retaining multiplicities
of the edges. The two ends of a loop remain distinct half-edges. -/
def halfEdges (g : Graph C) : List (ℕ × Bool) :=
  (List.range g.edges.length).product [false, true]

/-- Read the first endpoint for `false` and the second endpoint for `true`.
Out-of-range edge indices return vertex zero. -/
def endpoint (fallback : C) (g : Graph C) (p : ℕ × Bool) : ℕ :=
  let e := g.edgeAt fallback p.1
  if p.2 then e.dst else e.src

/-- Enumerate the half-edges incident to a vertex in edge-list order. -/
def cloud (fallback : C) (g : Graph C) (vertex : ℕ) : List (ℕ × Bool) :=
  g.halfEdges.filter fun p => g.endpoint fallback p == vertex

/-- Enumerating both ends of every edge is polynomial-time. -/
@[fun_prop]
theorem isPolyTime_halfEdges {graph : Input → Graph C}
    (hgraph : ComputableInPolyTime graph input (encoding enc)) :
    ComputableInPolyTime (fun x => (graph x).halfEdges)
      input (encList (encPair encUnary encBool)) := by
  have hrange : ComputableInPolyTime (fun x => List.range (graph x).edges.length)
      input (encList encUnary) :=
    ComputableInPolyTime.range.comp
      ((ComputableInPolyTime.length_list (Edge.encoding enc)).comp (isPolyTime_edges hgraph))
  unfold halfEdges List.product
  exact ComputableInPolyTime.flatMapWithInput hrange
    (ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.const (encIn := encPair input encUnary) [false, true])
      (((ComputableInPolyTime.snd input encUnary).comp
        (ComputableInPolyTime.fst (encPair input encUnary) encBool)).prod
        (ComputableInPolyTime.snd (encPair input encUnary) encBool)))

/-- Endpoint lookup is uniform in the graph and the half-edge. -/
@[fun_prop]
theorem isPolyTime_endpoint {graph : Input → Graph C} {halfEdge : Input → ℕ × Bool}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hhalfEdge : ComputableInPolyTime halfEdge input (encPair encUnary encBool))
    (fallback : C) :
    ComputableInPolyTime (fun x => (graph x).endpoint fallback (halfEdge x))
      input encUnary := by
  have hedge := isPolyTime_edgeAt hgraph hhalfEdge.fst' fallback
  unfold endpoint
  exact hhalfEdge.snd'.ite (Edge.isPolyTime_dst hedge) (Edge.isPolyTime_src hedge)

/-- Cloud enumeration charges each endpoint lookup and the entire filtered output. -/
@[fun_prop]
theorem isPolyTime_cloud {graph : Input → Graph C} {vertex : Input → ℕ}
    (hgraph : ComputableInPolyTime graph input (encoding enc))
    (hvertex : ComputableInPolyTime vertex input encUnary) (fallback : C) :
    ComputableInPolyTime (fun x => (graph x).cloud fallback (vertex x))
      input (encList (encPair encUnary encBool)) := by
  unfold cloud
  exact ComputableInPolyTime.filterWithInput (isPolyTime_halfEdges hgraph)
    ((isPolyTime_endpoint
      (hgraph.comp (ComputableInPolyTime.fst input (encPair encUnary encBool)))
      (ComputableInPolyTime.snd input (encPair encUnary encBool)) fallback).beq
      (hvertex.comp (ComputableInPolyTime.fst input (encPair encUnary encBool))))

/-- Every edge contributes exactly two half-edges. -/
@[simp]
theorem length_halfEdges (g : Graph C) : g.halfEdges.length = 2 * g.edges.length := by
  change ((List.range g.edges.length) ×ˢ [false, true]).length = _
  simp [List.length_product, mul_comm]

/-- A numbered half-edge exists exactly when its edge index exists. -/
@[simp]
theorem mem_halfEdges_iff (g : Graph C) (p : ℕ × Bool) :
    p ∈ g.halfEdges ↔ p.1 < g.edges.length := by
  cases p with | mk i b => cases b <;> simp [halfEdges]

/-- Both ends of every edge have distinct names, even for loops and parallel edges. -/
theorem nodup_halfEdges (g : Graph C) : g.halfEdges.Nodup :=
  List.nodup_range.product (by decide)

/-- Half-edge positions retain the original edge order, with its two ends adjacent. -/
def halfEdgesEnumeration (g : Graph C) :
    List.Enumeration g.halfEdges (fun p : Fin g.edges.length × Bool => (p.1.val, p.2)) :=
  (List.Enumeration.range g.edges.length).prod
    (List.Enumeration.ofNodup [false, true] (by decide) (by intro b; cases b <;> simp))

/-- Cloud membership means that the edge exists and the selected endpoint is the vertex. -/
@[simp]
theorem mem_cloud_iff (g : Graph C) (fallback : C) (vertex : ℕ) (p : ℕ × Bool) :
    p ∈ g.cloud fallback vertex ↔
      p.1 < g.edges.length ∧ g.endpoint fallback p = vertex := by
  simp [cloud]

/-- A cloud has no repeated half-edge. -/
theorem nodup_cloud (g : Graph C) (fallback : C) (vertex : ℕ) :
    (g.cloud fallback vertex).Nodup :=
  (g.nodup_halfEdges).filter _

/-- Every cloud has at most two half-edges per original edge. -/
theorem length_cloud_le (g : Graph C) (fallback : C) (vertex : ℕ) :
    (g.cloud fallback vertex).length ≤ 2 * g.edges.length := by
  exact (List.length_filter_le _ _).trans_eq (g.length_halfEdges)

/-- Endpoint lookup agrees with the mathematical graph on existing edges. -/
theorem endpoint_eq (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (p : Fin g.edges.length × Bool) :
    g.endpoint fallback (p.1.val, p.2) = (g.toGraph eval).endpoint p := by
  rcases p with ⟨i, b⟩
  cases b <;> simp [endpoint, edgeAt, toGraph, ConstraintGraph.endpoint]

/-- The computed cloud list is precisely the mathematical cloud, with an explicit inverse
which searches the ordered half-edge list. -/
def cloudEquiv (g : Graph C) (eval : C → α → α → Bool) (fallback : C) (vertex : ℕ) :
    Fin (g.cloud fallback vertex).length ≃ (g.toGraph eval).Cloud vertex :=
  (List.Nodup.getEquiv _ (g.nodup_cloud fallback vertex)).trans
    { toFun := fun p =>
        ⟨(⟨p.val.1, (g.mem_cloud_iff fallback vertex p.val).mp p.property |>.1⟩, p.val.2),
          by
            rw [← g.endpoint_eq eval fallback]
            exact ((g.mem_cloud_iff fallback vertex p.val).mp p.property).2⟩
      invFun := fun p =>
        ⟨(p.val.1.val, p.val.2), (g.mem_cloud_iff fallback vertex _).mpr
          ⟨p.val.1.isLt, (g.endpoint_eq eval fallback p.val).trans p.property⟩⟩
      left_inv := fun p => Subtype.ext rfl
      right_inv := fun p => Subtype.ext (Prod.ext (Fin.ext rfl) rfl) }

/-- The forward cloud identification reads the selected list entry. -/
theorem cloudEquiv_apply (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (vertex : ℕ) (i : Fin (g.cloud fallback vertex).length) :
    ((g.cloudEquiv eval fallback vertex i).val.1.val,
      (g.cloudEquiv eval fallback vertex i).val.2) = (g.cloud fallback vertex).get i :=
  rfl

/-- The inverse cloud identification is the ordinary index-of operation. -/
theorem cloudEquiv_symm_apply (g : Graph C) (eval : C → α → α → Bool) (fallback : C)
    (vertex : ℕ) (p : (g.toGraph eval).Cloud vertex) :
    ((g.cloudEquiv eval fallback vertex).symm p).val =
      (g.cloud fallback vertex).idxOf (p.val.1.val, p.val.2) :=
  rfl

end Cslib.PCP.Encoded.Graph
