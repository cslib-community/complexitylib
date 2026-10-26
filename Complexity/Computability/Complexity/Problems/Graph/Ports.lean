/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
import Batteries.Data.List.Lemmas
import Mathlib.Data.List.GetD

/-!
# Canonical three-way ports for finite graph incidences

Each listed edge contributes its two endpoint occurrences in order. An incidence is assigned the
number of preceding equal vertex labels, reduced modulo three. When every vertex occurs at most
three times, reduction does nothing and every incidence of that vertex gets a distinct port.
Parallel listed edges remain distinct; a loop contributes two incidences.

## Main definitions

* `Cslib.Complexity.Graph.incidenceVertices`: finite list of endpoint occurrences.
* `Cslib.Complexity.Graph.incidencePort`: canonical three-way port of an occurrence.
* `Cslib.Complexity.Graph.canonicalPorts`: finite edge-indexed port table.

## Main results

* `Cslib.Complexity.Graph.incidencePort_injective`: equal vertex/port pairs identify incidences
  whenever endpoint occurrence counts are at most three.
-/

@[expose] public section

namespace Cslib.Complexity.Graph

/-- Endpoints of all listed edges, counting edge occurrences rather than simple-graph degree. -/
def incidenceVertices (G : Graph) : List ℕ := G.2.flatMap fun e => [e.1, e.2]

/-- Number of endpoint occurrences is twice the edge-list length. -/
@[simp] theorem incidenceVertices_length (G : Graph) :
    G.incidenceVertices.length = 2 * G.2.length := by
  simp [incidenceVertices, List.length_flatMap, List.map_const', Nat.mul_comm]

/-- The even endpoint occurrence is the first endpoint of the corresponding listed edge. -/
theorem getD_incidenceVertices_even (G : Graph) (i : ℕ) :
    G.incidenceVertices.getD (2 * i) 0 = (G.2.getD i (0, 0)).1 := by
  rcases G with ⟨V, E⟩
  induction E generalizing i with
  | nil => simp [incidenceVertices]
  | cons e E ih =>
    cases i with
    | zero => simp [incidenceVertices]
    | succ i =>
      simpa only [incidenceVertices, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_succ, List.getD_cons_succ, Nat.add_succ_sub_one, Nat.add_zero] using ih i

/-- The odd endpoint occurrence is the second endpoint of the corresponding listed edge. -/
theorem getD_incidenceVertices_odd (G : Graph) (i : ℕ) :
    G.incidenceVertices.getD (2 * i + 1) 0 = (G.2.getD i (0, 0)).2 := by
  rcases G with ⟨V, E⟩
  induction E generalizing i with
  | nil => simp [incidenceVertices]
  | cons e E ih =>
    cases i with
    | zero => simp [incidenceVertices]
    | succ i =>
      simpa only [incidenceVertices, List.flatMap_cons, List.cons_append, List.nil_append,
        Nat.mul_succ, Nat.add_assoc, List.getD_cons_succ] using ih i

/-- Executable port assignment; under the degree hypothesis the remainder is the rank itself. -/
def incidencePort (G : Graph) (k : ℕ) : Fin 3 :=
  ⟨((G.incidenceVertices.take k).count (G.incidenceVertices.getD k 0)) % 3,
    Nat.mod_lt _ (by decide)⟩

/-- The edge-indexed finite table of canonical port pairs. -/
def canonicalPorts (G : Graph) : List (Fin 3 × Fin 3) :=
  (List.range G.2.length).map fun i => (G.incidencePort (2 * i), G.incidencePort (2 * i + 1))

/-- One canonical port pair per listed edge. -/
@[simp] theorem canonicalPorts_length (G : Graph) : G.canonicalPorts.length = G.2.length := by
  simp [canonicalPorts]

/-- Reading the canonical table at an existing edge returns its two incidence ports. -/
theorem getD_canonicalPorts (G : Graph) {i : ℕ} (hi : i < G.2.length) :
    G.canonicalPorts.getD i (0, 0) = (G.incidencePort (2 * i), G.incidencePort (2 * i + 1)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [canonicalPorts]

/-- For graphs with at most three incidences per vertex, no remainder reduction occurs. -/
theorem incidencePort_val (G : Graph)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {k : ℕ}
    (hk : k < G.incidenceVertices.length) :
    (G.incidencePort k : ℕ) = (G.incidenceVertices.take k).count G.incidenceVertices[k] := by
  have h : (G.incidenceVertices.take k).count G.incidenceVertices[k] <
      G.incidenceVertices.count G.incidenceVertices[k] := by
    rw [← List.countBefore_eq_count_take]
    exact List.countBefore_lt_count_getElem
  have htotal := hdeg G.incidenceVertices[k]
  simp only [incidencePort, List.getD_eq_getElem _ _ hk]
  exact Nat.mod_eq_of_lt (by omega)

/-- Equal vertex labels and canonical ports identify endpoint occurrences when all incidence
counts are at most three. -/
theorem incidencePort_injective (G : Graph)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.incidenceVertices.length) (hj : j < G.incidenceVertices.length)
    (hv : G.incidenceVertices[i] = G.incidenceVertices[j])
    (hp : G.incidencePort i = G.incidencePort j) : i = j := by
  have h := congrArg Fin.val hp
  rw [incidencePort_val G hdeg hi, incidencePort_val G hdeg hj] at h
  simp only [← List.countBefore_eq_count_take] at h
  calc i = G.incidenceVertices.idxOfNth G.incidenceVertices[i]
        (G.incidenceVertices.countBefore G.incidenceVertices[i] i) :=
      List.idxOfNth_countBefore_getElem.symm
    _ = G.incidenceVertices.idxOfNth G.incidenceVertices[j]
        (G.incidenceVertices.countBefore G.incidenceVertices[j] j) := by rw [h, hv]
    _ = j := List.idxOfNth_countBefore_getElem

/-- Endpoint label of a listed edge occurrence; `false` means first, `true` second. -/
def edgeEndpoint (G : Graph) (i : ℕ) (side : Bool) : ℕ :=
  if side then (G.2.getD i (0, 0)).2 else (G.2.getD i (0, 0)).1

/-- The endpoint occurrence index agrees with the finite flattened endpoint list. -/
theorem getD_incidenceVertices_endpoint (G : Graph) (i : ℕ) (side : Bool) :
    G.incidenceVertices.getD (2 * i + side.toNat) 0 = G.edgeEndpoint i side := by
  cases side
  · exact getD_incidenceVertices_even G i
  · exact getD_incidenceVertices_odd G i

/-- A listed endpoint occurrence lies in the endpoint list's index range. -/
theorem endpoint_index_lt (G : Graph) {i : ℕ} (hi : i < G.2.length) (side : Bool) :
    2 * i + side.toNat < G.incidenceVertices.length := by
  rw [incidenceVertices_length]
  cases side <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega

/-- Vertex and canonical port determine both the edge occurrence and which end it is. -/
theorem endpoint_port_injective (G : Graph)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (left right : Bool)
    (hv : G.edgeEndpoint i left = G.edgeEndpoint j right)
    (hp : G.incidencePort (2 * i + left.toNat) = G.incidencePort (2 * j + right.toNat)) :
    i = j ∧ left = right := by
  have hi' := endpoint_index_lt G hi left
  have hj' := endpoint_index_lt G hj right
  have hv' : G.incidenceVertices[2 * i + left.toNat] =
      G.incidenceVertices[2 * j + right.toNat] := by
    rw [← List.getD_eq_getElem _ 0 hi', ← List.getD_eq_getElem _ 0 hj',
      getD_incidenceVertices_endpoint, getD_incidenceVertices_endpoint]
    exact hv
  have h := incidencePort_injective G hdeg hi' hj' hv' hp
  cases left <;> cases right <;> simp only [Bool.toNat_false, Bool.toNat_true] at h ⊢ <;>
    constructor <;> first | omega | trivial

/-- Reading a finite port table at one end of an edge occurrence. -/
def portAt (ports : List (Fin 3 × Fin 3)) (i : ℕ) (side : Bool) : Fin 3 :=
  if side then (ports.getD i (0, 0)).2 else (ports.getD i (0, 0)).1

/-- The canonical table reads the corresponding incidence's occurrence-rank port. -/
theorem portAt_canonicalPorts (G : Graph) {i : ℕ} (hi : i < G.2.length) (side : Bool) :
    portAt G.canonicalPorts i side = G.incidencePort (2 * i + side.toNat) := by
  rw [portAt, getD_canonicalPorts G hi]
  cases side <;> rfl

/-- Every indexed endpoint of a graph with declared endpoints is declared. -/
theorem edgeEndpoint_mem (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1) {i : ℕ}
    (hi : i < G.2.length) (side : Bool) : G.edgeEndpoint i side ∈ G.1 := by
  have hmem : G.2.getD i (0, 0) ∈ G.2 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  cases side
  · exact (hG _ hmem).1
  · exact (hG _ hmem).2

/-- Canonical vertex-position/port pairs are distinct at every pair of different listed edges. -/
theorem canonical_index_port_ne (G : Graph)
    (hG : ∀ edge ∈ G.2, edge.1 ∈ G.1 ∧ edge.2 ∈ G.1)
    (hdeg : ∀ v, G.incidenceVertices.count v ≤ 3) {i j : ℕ}
    (hi : i < G.2.length) (hj : j < G.2.length) (hij : i ≠ j) (left right : Bool) :
    (G.1.idxOf (G.edgeEndpoint i left), portAt G.canonicalPorts i left) ≠
      (G.1.idxOf (G.edgeEndpoint j right), portAt G.canonicalPorts j right) := by
  intro h
  have hv := (List.idxOf_inj (edgeEndpoint_mem G hG hi left)).1 (congrArg Prod.fst h)
  have hp := congrArg Prod.snd h
  rw [portAt_canonicalPorts G hi, portAt_canonicalPorts G hj] at hp
  exact hij (endpoint_port_injective G hdeg hi hj left right hv hp).1

end Cslib.Complexity.Graph
