/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.OrthogonalLayout
public import Complexity.Foundations.Geometry.Orthogonal.Endpoint
import Mathlib.Data.List.GetD

/-!
# Canonical unit paths and their local occupancy

The finite path list uses the canonical incidence ports and the explicit linear per-route wire
budget. Correctness statements refer to the existing graph's edge occurrences by their indices.

## Main definitions

* `Cslib.Complexity.Graph.unitPaths`: canonical finite unit paths in edge-list order.
* `Cslib.Complexity.Graph.unitPath`: indexed access, with the empty path outside the edge range.

## Main results

* `Cslib.Complexity.Graph.unitPath_endpoints`, `.unitPath_nodup`, `.unitPath_unit`:
  endpoint, uniqueness and unit-adjacency certificates.
* `Cslib.Complexity.Graph.unitPath_first_neighbor`, `.unitPath_last_neighbor`: exact canonical
  port neighbors at both ends, with `.endpointNeighbor_ne` for different incident edges.
* `Cslib.Complexity.Graph.unitPath_support`, `.unitPath_bounds`: continuous support and grid bounds.
* `Cslib.Complexity.Graph.unitPath_declared_center_iff`: no nonincident source-center contacts.
* `Cslib.Complexity.Graph.unitPath_contact`, `.unitPath_atMostTwo`: actual crossing classification
  and at most two paths at nonvertex points.
* `Cslib.Complexity.Graph.unitPath_crossing_neighbors`: opposite horizontal/vertical unit neighbors.
* `Cslib.Complexity.Graph.BridgeStemCrossing.not_listed`: crossings avoid all original bends.
* `Cslib.Complexity.Graph.unitPath_neighbor_lengths`, `.unitPath_neighbors_distinct`: the two
  distinct unit neighbors at every ordinary nonvertex occupied cell.
-/

@[expose] public section

namespace Cslib.Complexity.Graph

open Orthogonal

/-- Canonical unit paths, with the checked linear per-edge wire budget. -/
def unitPaths (G : Graph) : List Route :=
  (G.orthogonalRoutes G.canonicalPorts).map
    (subdivideWithin (80 * G.1.length + 10 * G.2.length))

/-- Access one finite canonical unit path, defaulting to the empty path outside the edge range. -/
def unitPath (G : Graph) (i : ℕ) : Route := G.unitPaths.getD i []

/-- One unit path is emitted for every listed edge occurrence. -/
@[simp] theorem unitPaths_length (G : Graph) : G.unitPaths.length = G.2.length := by
  simp [unitPaths]

private theorem canonical_orthogonal (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    IsOrthogonal ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)) :=
  orthogonalRoutes_orthogonal G G.canonicalPorts hi (hG _ (List.getElem_mem hi)).1
    (hG _ (List.getElem_mem hi)).2 (hloop _ (List.getElem_mem hi))

/-- The budgeted compiler produces the full subdivision at every existing edge. -/
theorem unitPath_eq_subdivide (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    G.unitPath i = subdivide ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)) := by
  have hwire : wireLength ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)) ≤
      80 * G.1.length + 10 * G.2.length := by
    rw [getElem_orthogonalRoutes]
    exact Layout.route_wireLength_le hi
      (List.idxOf_lt_length_iff.2 (hG _ (List.getElem_mem hi)).1)
      (List.idxOf_lt_length_iff.2 (hG _ (List.getElem_mem hi)).2) _ _
  unfold unitPath
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [unitPaths, List.getElem_map]
  exact subdivideWithin_eq_of_wireLength_le (canonical_orthogonal G hG hloop hi) hwire

/-- Canonical unit paths preserve both original indexed edge endpoints. -/
theorem unitPath_endpoints (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    (G.unitPath i).head? = some (Layout.center (G.1.idxOf (G.edgeEndpoint i false))) ∧
      (G.unitPath i).getLast? = some (Layout.center (G.1.idxOf (G.edgeEndpoint i true))) := by
  rw [unitPath_eq_subdivide G hG hloop hi, subdivide_head,
    subdivide_last (canonical_orthogonal G hG hloop hi),
    getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi]
  exact ⟨rfl, rfl⟩

/-- Canonical unit paths never repeat a listed lattice point. -/
theorem unitPath_nodup (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    (G.unitPath i).Nodup := by
  rw [unitPath_eq_subdivide G hG hloop hi]
  exact subdivide_nodup (canonical_orthogonal G hG hloop hi)
    (orthogonalRoutes_simple G G.canonicalPorts hi (hG _ (List.getElem_mem hi)).1
      (hG _ (List.getElem_mem hi)).2 (hloop _ (List.getElem_mem hi)))

/-- The first unit neighbor is the source center plus its actual canonical port direction. -/
theorem unitPath_first_neighbor (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    (d : Point) :
    (G.unitPath i).getD 1 d = Layout.center (G.1.idxOf (G.edgeEndpoint i false)) +
      Layout.portStep (portAt G.canonicalPorts i false) := by
  have hf : segmentWalk (Layout.center (G.1.idxOf (G.edgeEndpoint i false)))
      (Layout.elbow (G.1.idxOf (G.edgeEndpoint i false))
        (portAt G.canonicalPorts i false)) <:+: G.unitPath i := by
    rw [unitPath_eq_subdivide G hG hloop hi]
    apply segmentWalk_infix_subdivide (canonical_orthogonal G hG hloop hi)
      (e := (Layout.center (G.1.idxOf (G.edgeEndpoint i false)),
        Layout.elbow (G.1.idxOf (G.edgeEndpoint i false)) (portAt G.canonicalPorts i false)))
    rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi]
    simp [Layout.route, List.consecutivePairs]
  rw [Layout.fanWalk] at hf
  have hp : [_ , _] <:+: [Layout.center (G.1.idxOf (G.edgeEndpoint i false)),
      Layout.center (G.1.idxOf (G.edgeEndpoint i false)) +
        Layout.portStep (portAt G.canonicalPorts i false),
      Layout.elbow (G.1.idxOf (G.edgeEndpoint i false))
        (portAt G.canonicalPorts i false)] := ⟨[], [_], rfl⟩
  exact (infix_head_pair_getD (unitPath_nodup G hG hloop hi)
    (hp.trans hf) (unitPath_endpoints G hG hloop hi).1 d).2

/-- The penultimate unit point is the target center plus its canonical port direction. -/
theorem unitPath_last_neighbor (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    (d : Point) :
    (G.unitPath i).getD ((G.unitPath i).length - 2) d =
      Layout.center (G.1.idxOf (G.edgeEndpoint i true)) +
        Layout.portStep (portAt G.canonicalPorts i true) := by
  have hf : segmentWalk (Layout.elbow (G.1.idxOf (G.edgeEndpoint i true))
        (portAt G.canonicalPorts i true))
      (Layout.center (G.1.idxOf (G.edgeEndpoint i true))) <:+: G.unitPath i := by
    rw [unitPath_eq_subdivide G hG hloop hi]
    apply segmentWalk_infix_subdivide (canonical_orthogonal G hG hloop hi)
      (e := (Layout.elbow (G.1.idxOf (G.edgeEndpoint i true)) (portAt G.canonicalPorts i true),
        Layout.center (G.1.idxOf (G.edgeEndpoint i true))))
    rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi]
    simp [Layout.route, List.consecutivePairs]
  rw [Layout.returnFanWalk] at hf
  have hp : [_ , _] <:+: [Layout.elbow (G.1.idxOf (G.edgeEndpoint i true))
      (portAt G.canonicalPorts i true),
      Layout.center (G.1.idxOf (G.edgeEndpoint i true)) +
        Layout.portStep (portAt G.canonicalPorts i true),
      Layout.center (G.1.idxOf (G.edgeEndpoint i true))] := ⟨[_], [], rfl⟩
  exact (infix_last_pair_getD (unitPath_nodup G hG hloop hi)
    (hp.trans hf) (unitPath_endpoints G hG hloop hi).2 d).2

/-- The immediate unit neighbor at a chosen end of an indexed canonical path. -/
def endpointNeighbor (G : Graph) (i : ℕ) (side : Bool) : Point :=
  let r := G.unitPath i
  if side then r.getD (r.length - 2) (0, 0) else r.getD 1 (0, 0)

/-- Side-indexed exact endpoint-neighbor formula. -/
theorem endpointNeighbor_eq (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    (side : Bool) :
    G.endpointNeighbor i side = Layout.center (G.1.idxOf (G.edgeEndpoint i side)) +
      Layout.portStep (portAt G.canonicalPorts i side) := by
  cases side
  · exact unitPath_first_neighbor G hG hloop hi (0, 0)
  · exact unitPath_last_neighbor G hG hloop hi (0, 0)

/-- Different edge occurrences at the same source center use different unit neighbors. -/
theorem endpointNeighbor_ne (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) (left right : Bool)
    (hc : G.1.idxOf (G.edgeEndpoint i left) = G.1.idxOf (G.edgeEndpoint j right)) :
    G.endpointNeighbor i left ≠ G.endpointNeighbor j right := by
  intro h
  rw [endpointNeighbor_eq G hG hloop hi, endpointNeighbor_eq G hG hloop hj, hc] at h
  have hp := Layout.portStep_injective (add_left_cancel h)
  exact canonical_index_port_ne G hG hdeg hi hj hij left right (Prod.ext hc hp)

/-- Every consecutive pair in a canonical unit path is exactly one Manhattan unit apart. -/
theorem unitPath_unit (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    {e : Point × Point} (he : e ∈ (G.unitPath i).consecutivePairs) : length e.1 e.2 = 1 := by
  rw [unitPath_eq_subdivide G hG hloop hi] at he
  exact subdivide_unit (canonical_orthogonal G hG hloop hi) he

/-- Unit paths retain the whole continuous real support of their original polygonal routes. -/
theorem unitPath_support (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    support (G.unitPath i) =
      support ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)) := by
  rw [unitPath_eq_subdivide G hG hloop hi,
    support_subdivide (canonical_orthogonal G hG hloop hi)]

/-- An integer point lies on a unit path exactly when it lies on the original real route. -/
theorem mem_unitPath_iff_support (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) (p : Point) :
    p ∈ G.unitPath i ↔
      realPoint p ∈ support ((G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi)) := by
  rw [mem_iff_realPoint_mem_support (fun _ he => unitPath_unit G hG hloop hi he),
    unitPath_support G hG hloop hi]

/-- Every listed unit point lies in the original explicit linear rectangle. -/
theorem unitPath_bounds (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    {p : Point} (hp : p ∈ G.unitPath i) :
    0 ≤ p.1 ∧ p.1 ≤ 8 * (G.1.length : ℤ) ∧
      0 ≤ p.2 ∧ p.2 ≤ 8 * (G.1.length : ℤ) + 2 * G.2.length := by
  have hp' := (mem_unitPath_iff_support G hG hloop hi p).1 hp
  apply point_bounds_of_mem_support (canonical_orthogonal G hG hloop hi) _ hp'
  intro q hq
  rw [getElem_orthogonalRoutes G G.canonicalPorts hi] at hq
  exact Layout.route_bounds hi (List.idxOf_lt_length_iff.2 (hG _ (List.getElem_mem hi)).1)
    (List.idxOf_lt_length_iff.2 (hG _ (List.getElem_mem hi)).2) _ _ hq

/-- Every canonical edge path is nonempty. -/
theorem unitPath_ne_nil (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length) :
    G.unitPath i ≠ [] := by
  intro h
  have he := (unitPath_endpoints G hG hloop hi).1
  rw [h] at he
  cases he

/-- A source grid center lies on a canonical unit path exactly when its position index is one
of that graph edge's two endpoint indices. -/
theorem unitPath_center_iff (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i w : ℕ}
    (hi : i < G.2.length) (hw : w < G.1.length) :
    Layout.center w ∈ G.unitPath i ↔ w = G.1.idxOf G.2[i].1 ∨ w = G.1.idxOf G.2[i].2 := by
  have hu := (hG _ (List.getElem_mem hi)).1
  have hv := (hG _ (List.getElem_mem hi)).2
  have hne : G.1.idxOf G.2[i].1 ≠ G.1.idxOf G.2[i].2 :=
    fun h => hloop _ (List.getElem_mem hi) ((List.idxOf_inj hu).1 h)
  rw [mem_unitPath_iff_support G hG hloop hi, getElem_orthogonalRoutes G G.canonicalPorts hi]
  exact Layout.center_mem_support_iff (List.idxOf_lt_length_iff.2 hu)
    (List.idxOf_lt_length_iff.2 hv) hw hne _ _

/-- No source vertex center lies on a nonincident path, stated using the graph's actual labels. -/
theorem unitPath_declared_center_iff (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i v : ℕ}
    (hi : i < G.2.length) (hv : v ∈ G.1) :
    Layout.center (G.1.idxOf v) ∈ G.unitPath i ↔ v = G.2[i].1 ∨ v = G.2[i].2 := by
  rw [unitPath_center_iff G hG hloop hi (List.idxOf_lt_length_iff.2 hv)]
  simp only [List.idxOf_inj hv]

/-- An occupied point away from source centers has a genuine predecessor and successor at
every occurrence index. Together with `unitPath_nodup`, that occurrence index is unique. -/
theorem unitPath_interior_index (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i k : ℕ} (hi : i < G.2.length)
    (hk : k < (G.unitPath i).length) {p : Point} (heq : (G.unitPath i)[k] = p)
    (hcenter : p ∉ G.orthogonalPositions) : 0 < k ∧ k + 1 < (G.unitPath i).length := by
  have hcenters (side : Bool) : Layout.center (G.1.idxOf (G.edgeEndpoint i side)) ∈
      G.orthogonalPositions :=
    List.mem_map.2 ⟨_, List.mem_range.2
      (List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hi side)), rfl⟩
  have he := unitPath_endpoints G hG hloop hi
  constructor
  · by_contra h
    have hk0 : k = 0 := by omega
    subst k
    have hh : (G.unitPath i).head? = some p := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, heq]
    apply hcenter
    rw [← Option.some.inj (he.1.symm.trans hh)]
    exact hcenters false
  · by_contra h
    have hkl : k = (G.unitPath i).length - 1 := by omega
    have hh : (G.unitPath i).getLast? = some p := by
      rw [List.getLast?_eq_getElem?, ← hkl, List.getElem?_eq_getElem hk, heq]
    apply hcenter
    rw [← Option.some.inj (he.2.symm.trans hh)]
    exact hcenters true

private theorem pair_mem_at {r : Route} {k : ℕ} (hk : k + 1 < r.length) :
    (r[k], r[k + 1]) ∈ r.consecutivePairs := by
  have hlen : k < r.consecutivePairs.length := by
    simp only [List.consecutivePairs, List.length_zip, List.length_tail]
    omega
  have hm : r.consecutivePairs[k] ∈ r.consecutivePairs := List.getElem_mem hlen
  simpa only [List.consecutivePairs, List.getElem_zip, List.getElem_tail] using hm

/-- The two actual predecessor/successor lookups at a nonvertex cell are unit neighbors. -/
theorem unitPath_neighbor_lengths (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i k : ℕ} (hi : i < G.2.length)
    (hk : k < (G.unitPath i).length) {p : Point} (heq : (G.unitPath i)[k] = p)
    (hcenter : p ∉ G.orthogonalPositions) :
    length ((G.unitPath i).getD (k - 1) p) p = 1 ∧
      length p ((G.unitPath i).getD (k + 1) p) = 1 := by
  obtain ⟨h0, hlast⟩ := unitPath_interior_index G hG hloop hi hk heq hcenter
  have hprev : k - 1 < (G.unitPath i).length := by omega
  rw [List.getD_eq_getElem _ _ hprev, List.getD_eq_getElem _ _ hlast]
  constructor
  · have hpair := pair_mem_at (r := G.unitPath i) (k := k - 1) (by omega)
    have h := unitPath_unit G hG hloop hi hpair
    simpa only [Nat.sub_add_cancel (show 1 ≤ k by omega), heq] using h
  · have h := unitPath_unit G hG hloop hi (pair_mem_at hlast)
    simpa only [heq] using h

/-- A nonvertex cell's predecessor and successor are distinct, so its two ports differ. -/
theorem unitPath_neighbors_distinct (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i k : ℕ} (hi : i < G.2.length)
    (hk : k < (G.unitPath i).length) {p : Point} (heq : (G.unitPath i)[k] = p)
    (hcenter : p ∉ G.orthogonalPositions) :
    (G.unitPath i).getD (k - 1) p ≠ (G.unitPath i).getD (k + 1) p := by
  obtain ⟨h0, hlast⟩ := unitPath_interior_index G hG hloop hi hk heq hcenter
  rw [List.getD_eq_getElem _ _ (show k - 1 < (G.unitPath i).length by omega),
    List.getD_eq_getElem _ _ hlast]
  intro h
  have hindex := (unitPath_nodup G hG hloop hi).getElem_inj_iff.1 h
  omega

/-- Nonvertex occupied cells are neither end of a canonical path. -/
theorem unitPath_not_endpoints (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i : ℕ} (hi : i < G.2.length)
    {p : Point} (hcenter : p ∉ G.orthogonalPositions) :
    (G.unitPath i).head? ≠ some p ∧ (G.unitPath i).getLast? ≠ some p := by
  have hcenters (side : Bool) : Layout.center (G.1.idxOf (G.edgeEndpoint i side)) ∈
      G.orthogonalPositions :=
    List.mem_map.2 ⟨_, List.mem_range.2
      (List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hi side)), rfl⟩
  have he := unitPath_endpoints G hG hloop hi
  constructor
  · intro hp
    apply hcenter
    rw [← Option.some.inj (he.1.symm.trans hp)]
    exact hcenters false
  · intro hp
    apply hcenter
    rw [← Option.some.inj (he.2.symm.trans hp)]
    exact hcenters true

/-- The vertical column assigned to one canonical graph incidence. -/
def pathColumn (G : Graph) (i : ℕ) (side : Bool) : ℤ :=
  Layout.column (G.1.idxOf (G.edgeEndpoint i side)) (portAt G.canonicalPorts i side)

/-- A genuine strict transverse crossing of edge `i`'s bridge with one stem of edge `j`.
The geometry is the canonical construction, not an assumed drawing witness. -/
def BridgeStemCrossing (G : Graph) (i j : ℕ) (side : Bool) (p : Point) : Prop :=
  Transverse (G.pathColumn i false, Layout.track G.1.length i)
    (G.pathColumn i true, Layout.track G.1.length i)
    (Layout.elbow (G.1.idxOf (G.edgeEndpoint j side)) (portAt G.canonicalPorts j side))
    (G.pathColumn j side, Layout.track G.1.length j) (realPoint p)

/-- A canonical crossing lies at its exact integer stem column and bridge row. -/
theorem BridgeStemCrossing.point {G : Graph} {i j : ℕ} {side : Bool} {p : Point}
    (hc : G.BridgeStemCrossing i j side p) :
    p = (G.pathColumn j side, Layout.track G.1.length i) :=
  realPoint_injective (Layout.bridge_stem_crossing_point hc)

/-- The crossing lies strictly between the bridge's two port columns. -/
theorem BridgeStemCrossing.horizontal {G : Graph} {i j : ℕ} {side : Bool} {p : Point}
    (hc : G.BridgeStemCrossing i j side p) :
    min (G.pathColumn i false) (G.pathColumn i true) < p.1 ∧
      p.1 < max (G.pathColumn i false) (G.pathColumn i true) := by
  have hp := hc.point
  rcases hc with ⟨_, _, _, hlo, hhi, _⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · simpa only [hp, pathColumn, Layout.elbow] using And.intro hlo hhi
  · simp only [pathColumn, Layout.elbow, min_self, max_self] at hlo hhi
    omega

/-- The crossing lies strictly above the stem's elbow and below its top endpoint. -/
theorem BridgeStemCrossing.vertical {G : Graph}
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1) {i j : ℕ}
    (hj : j < G.2.length) {side : Bool} {p : Point} (hc : G.BridgeStemCrossing i j side p) :
    (Layout.elbow (G.1.idxOf (G.edgeEndpoint j side)) (portAt G.canonicalPorts j side)).2 < p.2 ∧
      p.2 < Layout.track G.1.length j := by
  have hp := hc.point
  have htop := Layout.elbow_below_track (e := j)
    (List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hj side))
    (portAt G.canonicalPorts j side)
  rcases hc with ⟨_, _, _, _, _, hlo, hhi⟩ | ⟨_, _, _, hlo, hhi, _⟩
  · rw [hp]
    change _ < Layout.track G.1.length i ∧ _
    omega
  · simp only [pathColumn, Layout.elbow, min_self, max_self] at hlo hhi
    omega

/-- Actual contact of two distinct canonical unit paths is a vertex center or a strict
bridge/stem crossing, in one of the two orientations. -/
theorem unitPath_contact (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p : Point}
    (hp : p ∈ G.unitPath i) (hq : p ∈ G.unitPath j) :
    p ∈ G.orthogonalPositions ∨
      (∃ side, G.BridgeStemCrossing i j side p) ∨
        ∃ side, G.BridgeStemCrossing j i side p := by
  have hindex (k : ℕ) (hk : k < G.2.length) (side : Bool) :
      G.1.idxOf (G.edgeEndpoint k side) < G.1.length :=
    List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hk side)
  have hp' := (mem_unitPath_iff_support G hG hloop hi p).1 hp
  have hq' := (mem_unitPath_iff_support G hG hloop hj p).1 hq
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi] at hp'
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hj] at hq'
  have hc := Layout.route_contact (hindex i hi false) (hindex i hi true)
    (hindex j hj false) (hindex j hj true) hij
    (canonical_index_port_ne G hG hdeg hi hj hij false false)
    (canonical_index_port_ne G hG hdeg hi hj hij false true)
    (canonical_index_port_ne G hG hdeg hi hj hij true false)
    (canonical_index_port_ne G hG hdeg hi hj hij true true) hp' hq'
  rcases hc with ⟨w, hw, _, heq⟩ | h | h | h | h
  · apply Or.inl
    have hw' : w < G.1.length := by
      rcases hw with rfl | rfl
      · exact hindex i hi false
      · exact hindex i hi true
    exact List.mem_map.2 ⟨w, List.mem_range.2 hw', (realPoint_injective heq).symm⟩
  · exact Or.inr (Or.inl ⟨false, h⟩)
  · exact Or.inr (Or.inl ⟨true, h⟩)
  · exact Or.inr (Or.inr ⟨false, h⟩)
  · exact Or.inr (Or.inr ⟨true, h⟩)

/-- Unique canonical tracks and incidence columns admit at most the named two paths through
their intersection, independently of whether that intersection is actually occupied. -/
theorem unitPath_on_column_track (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j k : ℕ}
    (hj : j < G.2.length) (hk : k < G.2.length) (side : Bool) :
    (G.pathColumn j side, Layout.track G.1.length i) ∈ G.unitPath k → k = i ∨ k = j := by
  intro hp
  have hp' := (mem_unitPath_iff_support G hG hloop hk _).1 hp
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hk, Layout.support_route] at hp'
  have hfan (b : Bool) (hf : realPoint (G.pathColumn j side, Layout.track G.1.length i) ∈
      Layout.fan (G.1.idxOf (G.edgeEndpoint k b)) (portAt G.canonicalPorts k b)) : False := by
    have hb := (Layout.fan_bounds hf).2.2.2
    have hw : (G.1.idxOf (G.edgeEndpoint k b) : ℝ) + 1 ≤ G.1.length := by
      exact_mod_cast List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hk b)
    have hi0 : (0 : ℝ) ≤ i := by positivity
    change (Layout.track G.1.length i : ℝ) ≤ _ at hb
    simp only [Layout.track] at hb
    push_cast at hb
    linarith
  have hstem (b : Bool) (hs : realPoint (G.pathColumn j side, Layout.track G.1.length i) ∈
      Layout.stem G.1.length k (G.1.idxOf (G.edgeEndpoint k b))
        (portAt G.canonicalPorts k b)) : k = i ∨ k = j := by
    by_cases hkj : k = j
    · exact Or.inr hkj
    · have hx := (Layout.mem_stem.1 hs).1
      change (G.pathColumn j side : ℝ) = (G.pathColumn k b : ℝ) at hx
      have hx' : G.pathColumn j side = G.pathColumn k b := by exact_mod_cast hx
      unfold pathColumn at hx'
      have heq := Layout.column_injective hx'
      exact False.elim (canonical_index_port_ne G hG hdeg hj hk (Ne.symm hkj) side b
        (Prod.ext heq.1 heq.2))
  simp only [Set.mem_union] at hp'
  rcases hp' with (((hp' | hp') | hp') | hp') | hp'
  · exact False.elim (hfan false hp')
  · exact hstem false hp'
  · have hy := (Layout.mem_bridge.1 hp').1
    change (Layout.track G.1.length i : ℝ) = (Layout.track G.1.length k : ℝ) at hy
    have hy' : Layout.track G.1.length i = Layout.track G.1.length k := by exact_mod_cast hy
    simp only [Layout.track] at hy'
    exact Or.inl (by omega)
  · exact hstem true hp'
  · exact False.elim (hfan true hp')

/-- Outside declared vertex centers, any two distinct occupied paths exclude every third path. -/
theorem unitPath_atMostTwo (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j k : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hk : k < G.2.length) (hij : i ≠ j)
    {p : Point} (hcenter : p ∉ G.orthogonalPositions)
    (hp : p ∈ G.unitPath i) (hq : p ∈ G.unitPath j) (hr : p ∈ G.unitPath k) : k = i ∨ k = j := by
  rcases unitPath_contact G hG hloop hdeg hi hj hij hp hq with h | ⟨side, hc⟩ | ⟨side, hc⟩
  · exact False.elim (hcenter h)
  · rw [hc.point] at hr
    exact unitPath_on_column_track G hG hloop hdeg hj hk side hr
  · rw [hc.point] at hr
    exact (unitPath_on_column_track G hG hloop hdeg hi hk side hr).symm

/-- Every nonvertex shared point belongs to the original finite quadratic candidate cover. -/
theorem unitPath_shared_mem_crossingCandidates (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p : Point}
    (hcenter : p ∉ G.orthogonalPositions) (hp : p ∈ G.unitPath i) (hq : p ∈ G.unitPath j) :
    p ∈ G.crossingCandidates G.canonicalPorts := by
  rcases unitPath_contact G hG hloop hdeg hi hj hij hp hq with h | ⟨side, hc⟩ | ⟨side, hc⟩
  · exact False.elim (hcenter h)
  · rw [hc.point]
    exact mem_crossingCandidates G G.canonicalPorts hi hj side
  · rw [hc.point]
    exact mem_crossingCandidates G G.canonicalPorts hj hi side

/-- Every strict canonical crossing avoids every original source vertex center. -/
theorem BridgeStemCrossing.not_vertex_center {G : Graph} {i j : ℕ} {side : Bool} {p : Point}
    (hc : G.BridgeStemCrossing i j side p) : p ∉ G.orthogonalPositions := by
  intro h
  obtain ⟨w, hw, heq⟩ := List.mem_map.1 h
  rw [List.mem_range] at hw
  have hy := congrArg Prod.snd (heq.trans hc.point)
  simp only [Layout.center, Layout.track] at hy
  omega

private theorem listed_on_upper_track {n e f u v : ℕ} (hu : u < n) (hv : v < n)
    (s t : Fin 3) {p : Point} (hp : p ∈ Layout.route n f u v s t)
    (hy : p.2 = Layout.track n e) :
    p = (Layout.column u s, Layout.track n f) ∨ p = (Layout.column v t, Layout.track n f) := by
  have hcu : (Layout.center u).2 < Layout.track n e := by
    simp only [Layout.center, Layout.track]
    omega
  have hcv : (Layout.center v).2 < Layout.track n e := by
    simp only [Layout.center, Layout.track]
    omega
  have heu := Layout.elbow_below_track (e := e) hu s
  have hev := Layout.elbow_below_track (e := e) hv t
  simp only [Layout.route, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; omega
  · exfalso; omega
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso; omega
  · exfalso; omega

/-- A crossing is not any listed point of either original polygonal route, including its
elbows and upper endpoints. Thus no crossing occurs at a bend. -/
theorem BridgeStemCrossing.not_listed {G : Graph}
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) {side : Bool} {p : Point}
    (hc : G.BridgeStemCrossing i j side p) :
    p ∉ (G.orthogonalRoutes G.canonicalPorts)[i]'(by simpa using hi) ∧
      p ∉ (G.orthogonalRoutes G.canonicalPorts)[j]'(by simpa using hj) := by
  have hindex (k : ℕ) (hk : k < G.2.length) (b : Bool) :
      G.1.idxOf (G.edgeEndpoint k b) < G.1.length :=
    List.idxOf_lt_length_iff.2 (edgeEndpoint_mem G hG hk b)
  have hrow : p.2 = Layout.track G.1.length i := congrArg Prod.snd hc.point
  have hx := hc.horizontal
  have hy := hc.vertical hG hj
  constructor
  · intro hp
    rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi] at hp
    have htop := listed_on_upper_track (hindex i hi false) (hindex i hi true) _ _ hp hrow
    rcases htop with heq | heq
    · have heq' : p.1 = G.pathColumn i false := congrArg Prod.fst heq
      omega
    · have heq' : p.1 = G.pathColumn i true := congrArg Prod.fst heq
      omega
  · intro hp
    rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hj] at hp
    have htop := listed_on_upper_track (hindex j hj false) (hindex j hj true) _ _ hp hrow
    rcases htop with heq | heq <;>
      have heq' : p.2 = Layout.track G.1.length j := congrArg Prod.snd heq <;> omega

/-- A strict crossing produces actual consecutive opposite horizontal/vertical unit neighbors
on its two paths. Both the positions and their traversal order come from the canonical data. -/
theorem BridgeStemCrossing.neighbors {G : Graph}
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) {side : Bool} {p : Point}
    (hc : G.BridgeStemCrossing i j side p) :
    StraightThrough (G.unitPath i) p (1, 0) ∧ StraightThrough (G.unitPath j) p (0, 1) := by
  have hri := canonical_orthogonal G hG hloop hi
  have hrj := canonical_orthogonal G hG hloop hj
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi] at hri
  rw [getElem_orthogonalRoutes_endpoint G G.canonicalPorts hj] at hrj
  have hp := hc.point
  have hpx : p.1 = G.pathColumn j side := congrArg Prod.fst hp
  have hpy : p.2 = Layout.track G.1.length i := congrArg Prod.snd hp
  have hx := hc.horizontal
  have hy := hc.vertical hG hj
  constructor
  · rw [unitPath_eq_subdivide G hG hloop hi,
      getElem_orthogonalRoutes_endpoint G G.canonicalPorts hi]
    apply subdivide_horizontal hri
      (e := ((G.pathColumn i false, Layout.track G.1.length i),
        (G.pathColumn i true, Layout.track G.1.length i)))
    · simp [Layout.route, List.consecutivePairs, pathColumn]
    · rfl
    · exact hpy
    · exact hx
  · rw [unitPath_eq_subdivide G hG hloop hj,
      getElem_orthogonalRoutes_endpoint G G.canonicalPorts hj]
    cases side
    · apply subdivide_vertical hrj
        (e := (Layout.elbow (G.1.idxOf (G.edgeEndpoint j false))
          (portAt G.canonicalPorts j false), (G.pathColumn j false, Layout.track G.1.length j)))
      · simp [Layout.route, List.consecutivePairs, pathColumn]
      · rfl
      · exact hpx
      · change min (Layout.elbow (G.1.idxOf (G.edgeEndpoint j false))
          (portAt G.canonicalPorts j false)).2 (Layout.track G.1.length j) < p.2 ∧
          p.2 < max (Layout.elbow (G.1.idxOf (G.edgeEndpoint j false))
            (portAt G.canonicalPorts j false)).2 (Layout.track G.1.length j)
        omega
    · apply subdivide_vertical hrj
        (e := ((G.pathColumn j true, Layout.track G.1.length j),
          Layout.elbow (G.1.idxOf (G.edgeEndpoint j true)) (portAt G.canonicalPorts j true)))
      · simp [Layout.route, List.consecutivePairs, pathColumn]
      · rfl
      · exact hpx
      · change min (Layout.track G.1.length j) (Layout.elbow
          (G.1.idxOf (G.edgeEndpoint j true)) (portAt G.canonicalPorts j true)).2 < p.2 ∧
          p.2 < max (Layout.track G.1.length j) (Layout.elbow
            (G.1.idxOf (G.edgeEndpoint j true)) (portAt G.canonicalPorts j true)).2
        omega

/-- Every actual nonvertex contact has one horizontally straight path and one vertically
straight path, with opposite immediate unit neighbors. -/
theorem unitPath_crossing_neighbors (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hloop : ∀ edge ∈ G.2, edge.1 ≠ edge.2)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) {p : Point}
    (hcenter : p ∉ G.orthogonalPositions) (hp : p ∈ G.unitPath i) (hq : p ∈ G.unitPath j) :
    (StraightThrough (G.unitPath i) p (1, 0) ∧ StraightThrough (G.unitPath j) p (0, 1)) ∨
      (StraightThrough (G.unitPath i) p (0, 1) ∧ StraightThrough (G.unitPath j) p (1, 0)) := by
  rcases unitPath_contact G hG hloop hdeg hi hj hij hp hq with h | ⟨side, hc⟩ | ⟨side, hc⟩
  · exact False.elim (hcenter h)
  · exact Or.inl (hc.neighbors hG hloop hi hj)
  · exact Or.inr (hc.neighbors hG hloop hj hi).symm

end Cslib.Complexity.Graph
