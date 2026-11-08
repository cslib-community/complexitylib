/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained
public import Complexity.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Diam
import Complexity.Foundations.Data.Nat.LogRpow
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.GetD

/-!
# Orthogonal vectors hardness of diameter two versus three

Roditty and Vassilevska Williams [RodittyVassilevskaWilliams2013] (Section 4, Theorem 9) showed
that a procedure distinguishing graphs of diameter two from graphs of diameter three within time
`m ^ (2 - ε)` on `m` edges solves CNF-SAT on `n` variables within time `2 ^ (n (1 - ε / 2))` times
a polynomial. Their graph has a vertex for each partial assignment of either half of the variables,
a vertex for each clause, and two hubs; the clause vertices and the hubs form a clique. This module
formalizes the orthogonal vectors form of that construction, factoring it through the split-and-list
reduction of Williams [Williams2005]: partial assignments become vectors and clauses become
coordinates. The clique on the coordinates is replaced by edges from both hubs to every coordinate,
and two padding vertices are added.

From lists `A` and `B` of `N` vectors of dimension `d`, the graph `Cslib.Complexity.OV.toDiameter`
has a vertex for each vector, a vertex for each coordinate, two hubs `0` and `1`, and two
non-adjacent padding vertices `2` and `3`. The hub `0` is adjacent to the vectors of `A`, the hub
`1` to those of `B`, the two hubs to each other and to every coordinate and padding vertex, and a
vector to the coordinates where it holds `true`. Every vertex is adjacent to a hub, so the
diameter is at most three. Two vectors of the same list share a hub, and a vector of `A` and one of
`B` are at distance two exactly when they share a coordinate holding `true`, that is when they are
not orthogonal. So the graph has diameter three when the instance has an orthogonal pair, and
diameter two otherwise (`Cslib.Complexity.OV.ediam_toDiameter`); the padding vertices keep the
diameter at two on instances with no vectors.

The graph has `O(N d)` vertices and edges. Its vertex list and its edge list are each written by
one pass over the encoded instance, a finite automaton with two counters
(`Cslib.Complexity.OV.parseRun`), the coordinate and the number of the current vector, streaming
the outputs of each bit. The counters take `O(log L)` bits on an encoded instance of length `L`, so
the two streams, paired, compute the reduction within time `L (log L) ^ D`
(`Cslib.Complexity.OV.exists_computableInO_toDiameter`). Then a procedure
separating diameter two from diameter three within time `L ^ (2 - ε)`, on graphs encoded in length
`L`, decides `OV` within time `N ^ (2 - ε')` times a polynomial in the dimension
(`Cslib.Complexity.DecidableInTimeO.decidableInTimeO_OV_of_diameter`), which the orthogonal
vectors hypothesis excludes (`Cslib.Complexity.not_decidableInTimeO_diameter_of_OVH`).

The lower bound is stated in the length `L` of the encoded graph. A time bound in the number
`n + m` of listed vertices and edges alone would be vacuous: vertex labels are unbounded, and a
machine whose time is bounded in `n + m` cannot read long labels, so it cannot tell a four-cycle
from a path whose last edge leaves the declared vertices. The size form therefore charges the input
length as well, with the bound `(n + m) ^ (2 - ε) + L`
(`Cslib.Complexity.not_decidableInTimeO_diameter_size_of_OVH`). On the graphs of the reduction,
labels take `O(log (N d))` bits, so `L` and `n + m` differ by a logarithmic factor.

The graphs of the reduction have `Θ(N d)` edges for an unrestricted dimension `d`, so this is
Theorem 9 for general `m`. The statement for sparse graphs in the introduction of
[RodittyVassilevskaWilliams2013] is not covered: it needs dimension `c log N`, that is the
low-dimension form of the orthogonal vectors hypothesis, which this library does not state.

**The hypothesis is unresolved.** This library neither proves nor refutes `OVH`; it refutes
`SETH` (`Cslib.Complexity.CountingNativeEndpoint.not_SETH`), so the hardness from `SETH`, through
`Cslib.Complexity.OVH_of_SETH`, holds vacuously. The transfer from a fast diameter procedure to a
fast `OV` decider is unconditional.

## Main definitions

* `Cslib.Complexity.OV.toDiameter`: the graph of an orthogonal vectors instance.
* `Cslib.Complexity.OV.parseRun`: one pass over an encoded instance, emitting outputs for each bit
  and each vector.

## Main results

* `Cslib.Complexity.OV.ediam_toDiameter`: the diameter of `toDiameter p` is three if `p ∈ OV`, and
  two otherwise.
* `Cslib.Complexity.OV.exists_computableInO_toDiameter`: the reduction runs within time
  `L (log L) ^ D`.
* `Cslib.Complexity.DecidableInTimeO.decidableInTimeO_OV_of_diameter`: separating diameter two
  from three within time `L ^ (2 - ε)` decides `OV` within time `N ^ (2 - min ε 1 / 2) (d + 1) ^ 2`.
* `Cslib.Complexity.not_decidableInTimeO_diameter_of_OVH`,
  `Cslib.Complexity.not_decidableInTimeO_diameter_size_of_OVH`: under `OVH`, diameter two is not
  separated from diameter three within time `L ^ (2 - ε)`, nor within `(n + m) ^ (2 - ε) + L`.

## References

* [L. Roditty, V. Vassilevska Williams, *Fast approximation algorithms for the diameter and radius
  of sparse graphs*][RodittyVassilevskaWilliams2013]
* [R. Williams, *A new algorithm for optimal 2-constraint satisfaction and its
  implications*][Williams2005]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace OV

/-! ### Outputs of the bits and vectors of a list -/

/-- The concatenated outputs `f i b` of the bits `b` of a vector, numbered from `i`. -/
def bitsOut {β : Type} (f : ℕ → Bool → List β) : ℕ → List Bool → List β
  | _, [] => []
  | i, b :: v => f i b ++ bitsOut f (i + 1) v

/-- The concatenated outputs of the vectors of a list, numbered from `k`: for the vector `v`
numbered `k`, the outputs `f k i b` of its bits followed by `g k`. -/
def vecsOut {β : Type} (f : ℕ → ℕ → Bool → List β) (g : ℕ → List β) :
    ℕ → List (List Bool) → List β
  | _, [] => []
  | k, v :: vs => bitsOut (f k) 0 v ++ g k ++ vecsOut f g (k + 1) vs

/-- Membership in the outputs of the bits of a vector. -/
theorem mem_bitsOut {β : Type} {f : ℕ → Bool → List β} {i : ℕ} {v : List Bool} {x : β} :
    x ∈ bitsOut f i v ↔ ∃ j, ∃ h : j < v.length, x ∈ f (i + j) v[j] := by
  induction v generalizing i with
  | nil => simp [bitsOut]
  | cons b v ih =>
    simp only [bitsOut, List.mem_append, ih, List.length_cons]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · exact ⟨j + 1, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h⟩
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · exact Or.inl (by simpa using h)
      · exact Or.inr ⟨j, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h⟩

/-- Membership in the outputs of the vectors of a list. -/
theorem mem_vecsOut {β : Type} {f : ℕ → ℕ → Bool → List β} {g : ℕ → List β} {k : ℕ}
    {vs : List (List Bool)} {x : β} :
    x ∈ vecsOut f g k vs ↔ ∃ j, ∃ h : j < vs.length,
      (∃ i, ∃ hi : i < vs[j].length, x ∈ f (k + j) i vs[j][i]) ∨ x ∈ g (k + j) := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    simp only [vecsOut, List.mem_append, ih, mem_bitsOut, List.length_cons, Nat.zero_add]
    constructor
    · rintro ((⟨i, hi, h⟩ | h) | ⟨j, hj, h⟩)
      · exact ⟨0, by omega, Or.inl ⟨i, by simpa using hi, by simpa using h⟩⟩
      · exact ⟨0, by omega, Or.inr (by simpa using h)⟩
      · exact ⟨j + 1, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h⟩
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · rcases h with ⟨i, hi, h⟩ | h
        · exact Or.inl (Or.inl ⟨i, by simpa using hi, by simpa using h⟩)
        · exact Or.inl (Or.inr (by simpa using h))
      · exact Or.inr ⟨j, by omega, by simpa [Nat.add_assoc, Nat.add_comm 1 j] using h⟩

/-! ### The graph -/

namespace Diameter

/-- The vertex of the coordinate `i`. -/
def coordVertex (i : ℕ) : ℕ := 2 * i + 4

/-- The vertex of the vector numbered `k`; the vectors of both lists are numbered consecutively. -/
def vecVertex (k : ℕ) : ℕ := 2 * k + 5

/-- The hub of a list: `0` for the first list, `1` for the second. -/
def sideVertex (b : Bool) : ℕ := if b then 1 else 0

/-- The vertices listed for the bit of coordinate `i` of a vector: the coordinate vertex. -/
def bitVertices (_k i : ℕ) (_b : Bool) : List ℕ := [coordVertex i]

/-- The vertices listed after the vector numbered `k`: the vector vertex. -/
def endVertices (_b : Bool) (k : ℕ) : List ℕ := [vecVertex k]

/-- The edges listed for the bit `b` of coordinate `i` of the vector numbered `k`: the coordinate
is adjacent to both hubs, and to the vector when `b` is `true`. -/
def bitEdges (k i : ℕ) (b : Bool) : List (ℕ × ℕ) :=
  (0, coordVertex i) :: (1, coordVertex i) :: if b then [(coordVertex i, vecVertex k)] else []

/-- The edge listed after the vector numbered `k` of a list: from the hub of the list. -/
def endEdges (b : Bool) (k : ℕ) : List (ℕ × ℕ) := [(sideVertex b, vecVertex k)]

/-- The hubs `0` and `1` and the padding vertices `2` and `3`. -/
def constVertices : List ℕ := [0, 1, 2, 3]

/-- The hubs are adjacent to each other and to both padding vertices. -/
def constEdges : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]

end Diameter

open Diameter

/-- **The graph of an orthogonal vectors instance**, the orthogonal vectors form of the graph of
Theorem 9 of [RodittyVassilevskaWilliams2013]: a vertex for
each vector and each coordinate, the hubs `0` and `1` and the padding vertices `2` and `3`. The hub
`0` is adjacent to the vectors of the first list, the hub `1` to those of the second, both hubs to
each other, to the coordinates and to the padding vertices, and a vector to the coordinates where it
holds `true`. -/
def toDiameter (p : List (List Bool) × List (List Bool)) : Graph :=
  (vecsOut bitVertices (endVertices false) 0 p.1 ++
      vecsOut bitVertices (endVertices true) p.1.length p.2 ++ constVertices,
    vecsOut bitEdges (endEdges false) 0 p.1 ++
      vecsOut bitEdges (endEdges true) p.1.length p.2 ++ constEdges)

/-! ### Vertices and edges of the gadget -/

section Gadget

variable {p : List (List Bool) × List (List Bool)}

/-- The vertices of the gadget: four constants, coordinates, and vectors. -/
theorem mem_vertices_toDiameter {v : ℕ} (hv : v ∈ (toDiameter p).1) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨
      (∃ i, v = coordVertex i ∧ (0, coordVertex i) ∈ (toDiameter p).2 ∧
        (1, coordVertex i) ∈ (toDiameter p).2) ∨
      (∃ k < p.1.length, v = vecVertex k) ∨
      (∃ j < p.2.length, v = vecVertex (p.1.length + j)) := by
  simp only [toDiameter, List.mem_append, mem_vecsOut, bitVertices, endVertices, constVertices,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with ((⟨j, hj, ⟨i, hi, rfl⟩ | rfl⟩ | ⟨j, hj, ⟨i, hi, rfl⟩ | rfl⟩) | h)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, ?_, ?_⟩)))) <;>
      simp only [toDiameter, List.mem_append, mem_vecsOut] <;>
      exact Or.inl (Or.inl ⟨j, hj, Or.inl ⟨i, hi, by simp [bitEdges]⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, by simp⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl, ?_, ?_⟩)))) <;>
      simp only [toDiameter, List.mem_append, mem_vecsOut] <;>
      exact Or.inl (Or.inr ⟨j, hj, Or.inl ⟨i, hi, by simp [bitEdges]⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, rfl⟩)))))
  · omega

/-- The edges of the gadget. -/
theorem mem_edges_toDiameter {e : ℕ × ℕ} (he : e ∈ (toDiameter p).2) :
    e ∈ constEdges ∨ (∃ i, e = (0, coordVertex i) ∨ e = (1, coordVertex i)) ∨
      (∃ k < p.1.length, e = (0, vecVertex k)) ∨
      (∃ j < p.2.length, e = (1, vecVertex (p.1.length + j))) ∨
      (∃ k, ∃ hk : k < p.1.length, ∃ i, ∃ hi : i < p.1[k].length,
        p.1[k][i] = true ∧ e = (coordVertex i, vecVertex k)) ∨
      (∃ j, ∃ hj : j < p.2.length, ∃ i, ∃ hi : i < p.2[j].length,
        p.2[j][i] = true ∧ e = (coordVertex i, vecVertex (p.1.length + j))) := by
  simp only [toDiameter, List.mem_append, mem_vecsOut, Nat.zero_add] at he
  rcases he with ((⟨k, hk, ⟨i, hi, h⟩ | h⟩ | ⟨j, hj, ⟨i, hi, h⟩ | h⟩) | h)
  · simp only [bitEdges, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inr (Or.inl ⟨i, Or.inl rfl⟩)
    · exact Or.inr (Or.inl ⟨i, Or.inr rfl⟩)
    · split_ifs at h with hb
      · rw [List.mem_singleton] at h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, hk, i, hi, hb, h⟩))))
      · exact absurd h List.not_mem_nil
  · simp only [endEdges, sideVertex, List.mem_singleton] at h
    exact Or.inr (Or.inr (Or.inl ⟨k, hk, h⟩))
  · simp only [bitEdges, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact Or.inr (Or.inl ⟨i, Or.inl rfl⟩)
    · exact Or.inr (Or.inl ⟨i, Or.inr rfl⟩)
    · split_ifs at h with hb
      · rw [List.mem_singleton] at h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨j, hj, i, hi, hb, h⟩))))
      · exact absurd h List.not_mem_nil
  · simp only [endEdges, sideVertex, List.mem_singleton] at h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, hj, h⟩)))
  · exact Or.inl h

/-- An edge starts at a hub or at a coordinate. -/
theorem fst_mem_edges_toDiameter {a b : ℕ} (h : (a, b) ∈ (toDiameter p).2) :
    a = 0 ∨ a = 1 ∨ ∃ i, a = coordVertex i := by
  rcases mem_edges_toDiameter h with h | ⟨i, h | h⟩ | ⟨k, -, h⟩ | ⟨j, -, h⟩ |
    ⟨k, -, i, -, -, h⟩ | ⟨j, -, i, -, -, h⟩
  · simp only [constEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
    omega
  all_goals
    rw [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr ⟨_, rfl⟩)

/-- The neighbours of a vector of the first list: the hub `0` and its coordinates. -/
theorem eq_of_mem_edges_toDiameter_vec₁ {w k : ℕ} (hk : k < p.1.length)
    (h : (w, vecVertex k) ∈ (toDiameter p).2 ∨ (vecVertex k, w) ∈ (toDiameter p).2) :
    w = 0 ∨ ∃ i, ∃ hi : i < p.1[k].length, p.1[k][i] = true ∧ w = coordVertex i := by
  rcases h with h | h
  · rcases mem_edges_toDiameter h with h | ⟨i, h | h⟩ | ⟨k', hk', h⟩ | ⟨j, hj, h⟩ |
      ⟨k', hk', i, hi, hb, h⟩ | ⟨j, hj, i, hi, hb, h⟩
    · simp only [constEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        vecVertex] at h
      omega
    all_goals
      rw [Prod.mk.injEq] at h
      obtain ⟨rfl, he⟩ := h
      simp only [vecVertex, coordVertex] at he
    · omega
    · omega
    · exact Or.inl rfl
    · omega
    · obtain rfl : k' = k := by omega
      exact Or.inr ⟨i, hi, hb, rfl⟩
    · omega
  · rcases fst_mem_edges_toDiameter h with h | h | ⟨i, h⟩ <;>
      simp only [vecVertex, coordVertex] at h <;> omega

/-- The neighbours of a vector of the second list: the hub `1` and its coordinates. -/
theorem eq_of_mem_edges_toDiameter_vec₂ {w j : ℕ} (hj : j < p.2.length)
    (h : (w, vecVertex (p.1.length + j)) ∈ (toDiameter p).2 ∨
      (vecVertex (p.1.length + j), w) ∈ (toDiameter p).2) :
    w = 1 ∨ ∃ i, ∃ hi : i < p.2[j].length, p.2[j][i] = true ∧ w = coordVertex i := by
  rcases h with h | h
  · rcases mem_edges_toDiameter h with h | ⟨i, h | h⟩ | ⟨k', hk', h⟩ | ⟨j', hj', h⟩ |
      ⟨k', hk', i, hi, hb, h⟩ | ⟨j', hj', i, hi, hb, h⟩
    · simp only [constEdges, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false,
        vecVertex] at h
      omega
    all_goals
      rw [Prod.mk.injEq] at h
      obtain ⟨rfl, he⟩ := h
      simp only [vecVertex, coordVertex] at he
    · omega
    · omega
    · omega
    · exact Or.inl rfl
    · omega
    · obtain rfl : j' = j := by omega
      exact Or.inr ⟨i, hi, hb, rfl⟩
  · rcases fst_mem_edges_toDiameter h with h | h | ⟨i, h⟩ <;>
      simp only [vecVertex, coordVertex] at h <;> omega

/-- The constant vertices are vertices of the gadget. -/
theorem const_mem_toDiameter {v : ℕ} (hv : v ∈ constVertices) : v ∈ (toDiameter p).1 :=
  List.mem_append_right _ hv

/-- The constant edges are edges of the gadget. -/
theorem const_mem_edges_toDiameter {e : ℕ × ℕ} (he : e ∈ constEdges) : e ∈ (toDiameter p).2 :=
  List.mem_append_right _ he

/-- The hub `0` is adjacent to the vectors of the first list. -/
theorem vec_mem_edges_toDiameter₁ {k : ℕ} (hk : k < p.1.length) :
    (0, vecVertex k) ∈ (toDiameter p).2 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inl ⟨k, hk, Or.inr (by simp [endEdges, sideVertex])⟩)

/-- The hub `1` is adjacent to the vectors of the second list. -/
theorem vec_mem_edges_toDiameter₂ {j : ℕ} (hj : j < p.2.length) :
    (1, vecVertex (p.1.length + j)) ∈ (toDiameter p).2 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inr ⟨j, hj, Or.inr (by simp [endEdges, sideVertex])⟩)

/-- A vector of the first list is adjacent to the coordinates where it holds `true`. -/
theorem coord_mem_edges_toDiameter₁ {k i : ℕ} (hk : k < p.1.length) (hi : i < p.1[k].length)
    (hb : p.1[k][i] = true) : (coordVertex i, vecVertex k) ∈ (toDiameter p).2 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inl ⟨k, hk, Or.inl ⟨i, hi, by simp [bitEdges, hb]⟩⟩)

/-- A vector of the second list is adjacent to the coordinates where it holds `true`. -/
theorem coord_mem_edges_toDiameter₂ {j i : ℕ} (hj : j < p.2.length) (hi : i < p.2[j].length)
    (hb : p.2[j][i] = true) :
    (coordVertex i, vecVertex (p.1.length + j)) ∈ (toDiameter p).2 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inr ⟨j, hj, Or.inl ⟨i, hi, by simp [bitEdges, hb]⟩⟩)

/-- The coordinates of the vectors of the first list are vertices of the gadget. -/
theorem coord_mem_toDiameter₁ {k i : ℕ} (hk : k < p.1.length) (hi : i < p.1[k].length) :
    coordVertex i ∈ (toDiameter p).1 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inl ⟨k, hk, Or.inl ⟨i, hi, by simp [bitVertices]⟩⟩)

/-- The vectors of the first list are vertices of the gadget. -/
theorem vec_mem_toDiameter₁ {k : ℕ} (hk : k < p.1.length) : vecVertex k ∈ (toDiameter p).1 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inl ⟨k, hk, Or.inr (by simp [endVertices])⟩)

/-- The vectors of the second list are vertices of the gadget. -/
theorem vec_mem_toDiameter₂ {j : ℕ} (hj : j < p.2.length) :
    vecVertex (p.1.length + j) ∈ (toDiameter p).1 := by
  simp only [toDiameter, List.mem_append, mem_vecsOut]
  exact Or.inl (Or.inr ⟨j, hj, Or.inr (by simp [endVertices])⟩)

/-! ### Distances in the gadget -/

/-- Two vertices joined by an edge, or equal, are at distance at most one. -/
private theorem edist_le_one_of {u v : {v // v ∈ (toDiameter p).1}}
    (h : u.1 = v.1 ∨ (u.1, v.1) ∈ (toDiameter p).2 ∨ (v.1, u.1) ∈ (toDiameter p).2) :
    (toDiameter p).induced.edist u v ≤ 1 := by
  rw [SimpleGraph.edist_le_one_iff_adj_or_eq]
  by_cases huv : u.1 = v.1
  · exact Or.inr (Subtype.ext huv)
  · refine Or.inl (Graph.toSimpleGraph_adj.mpr ⟨huv, ?_⟩)
    rcases h with h | h | h
    · exact absurd h huv
    · exact Or.inl h
    · exact Or.inr h

/-- Two vertices with a common neighbour are at distance at most two. -/
private theorem edist_le_two_of {u v w : {v // v ∈ (toDiameter p).1}}
    (hu : (toDiameter p).induced.edist u w ≤ 1) (hv : (toDiameter p).induced.edist w v ≤ 1) :
    (toDiameter p).induced.edist u v ≤ 2 :=
  (SimpleGraph.edist_triangle).trans (by
    calc _ ≤ (1 : ℕ∞) + 1 := add_le_add hu hv
      _ = 2 := one_add_one_eq_two)

/-- Two vertices joined by a path of three edges are at distance at most three. -/
private theorem edist_le_three_of {u v w x : {v // v ∈ (toDiameter p).1}}
    (hu : (toDiameter p).induced.edist u w ≤ 1) (hw : (toDiameter p).induced.edist w x ≤ 1)
    (hv : (toDiameter p).induced.edist x v ≤ 1) :
    (toDiameter p).induced.edist u v ≤ 3 :=
  (SimpleGraph.edist_triangle).trans (by
    calc _ ≤ (toDiameter p).induced.edist u w + (toDiameter p).induced.edist w x +
          (toDiameter p).induced.edist x v :=
          add_le_add_left SimpleGraph.edist_triangle _
      _ ≤ (1 : ℕ∞) + 1 + 1 := add_le_add (add_le_add hu hw) hv
      _ = 3 := by norm_num)

/-- The hub `0` of the first list, a vertex of the gadget. -/
def toDiameterHub₀ (p : List (List Bool) × List (List Bool)) : {v // v ∈ (toDiameter p).1} :=
  ⟨0, const_mem_toDiameter (by simp [constVertices])⟩

/-- The hub `1` of the second list, a vertex of the gadget. -/
def toDiameterHub₁ (p : List (List Bool) × List (List Bool)) : {v // v ∈ (toDiameter p).1} :=
  ⟨1, const_mem_toDiameter (by simp [constVertices])⟩

/-- **The vertices of the gadget**: every vertex is a neighbour of both hubs `0` and `1`, or a
vector of the first list, adjacent to `0`, or a vector of the second list, adjacent to `1`. -/
theorem classify_toDiameter (u : {v // v ∈ (toDiameter p).1}) :
    ((toDiameter p).induced.edist (toDiameterHub₀ p) u ≤ 1 ∧
        (toDiameter p).induced.edist (toDiameterHub₁ p) u ≤ 1) ∨
      (∃ k < p.1.length, u.1 = vecVertex k ∧
        (toDiameter p).induced.edist (toDiameterHub₀ p) u ≤ 1) ∨
      (∃ j < p.2.length, u.1 = vecVertex (p.1.length + j) ∧
        (toDiameter p).induced.edist (toDiameterHub₁ p) u ≤ 1) := by
  have hc {a b : ℕ} (h : (a, b) ∈ constEdges) : (a, b) ∈ (toDiameter p).2 :=
    const_mem_edges_toDiameter h
  obtain ⟨v, hv⟩ := u
  rcases mem_vertices_toDiameter hv with rfl | rfl | rfl | rfl | ⟨i, rfl, h₀, h₁⟩ |
    ⟨k, hk, rfl⟩ | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨edist_le_one_of (Or.inl rfl),
      edist_le_one_of (Or.inr (Or.inr (hc (by simp [constEdges, toDiameterHub₁]))))⟩
  · exact Or.inl ⟨edist_le_one_of (Or.inr (Or.inl (hc (by simp [constEdges, toDiameterHub₀])))),
      edist_le_one_of (Or.inl rfl)⟩
  · exact Or.inl ⟨edist_le_one_of (Or.inr (Or.inl (hc (by simp [constEdges, toDiameterHub₀])))),
      edist_le_one_of (Or.inr (Or.inl (hc (by simp [constEdges, toDiameterHub₁]))))⟩
  · exact Or.inl ⟨edist_le_one_of (Or.inr (Or.inl (hc (by simp [constEdges, toDiameterHub₀])))),
      edist_le_one_of (Or.inr (Or.inl (hc (by simp [constEdges, toDiameterHub₁]))))⟩
  · exact Or.inl ⟨edist_le_one_of (Or.inr (Or.inl h₀)), edist_le_one_of (Or.inr (Or.inl h₁))⟩
  · exact Or.inr (Or.inl ⟨k, hk, rfl,
      edist_le_one_of (Or.inr (Or.inl (vec_mem_edges_toDiameter₁ hk)))⟩)
  · exact Or.inr (Or.inr ⟨j, hj, rfl,
      edist_le_one_of (Or.inr (Or.inl (vec_mem_edges_toDiameter₂ hj)))⟩)

/-- Non-orthogonal vectors share a coordinate holding `true` in both. -/
theorem exists_getElem_of_not_orthogonal {a b : List Bool} (h : ¬OV.Orthogonal a b) :
    ∃ i, ∃ ha : i < a.length, ∃ hb : i < b.length, a[i] = true ∧ b[i] = true := by
  simp only [OV.Orthogonal, not_forall, not_or, Bool.not_eq_false] at h
  obtain ⟨i, ha, hb⟩ := h
  have hia : i < a.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hc)] at ha
    exact Bool.false_ne_true ha
  have hib : i < b.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hc)] at hb
    exact Bool.false_ne_true hb
  refine ⟨i, hia, hib, ?_, ?_⟩
  · rwa [List.getD_eq_getElem _ _ hia] at ha
  · rwa [List.getD_eq_getElem _ _ hib] at hb

/-- **Diameter at most three**: through the hubs `0` and `1`. -/
theorem edist_toDiameter_le_three (u v : {v // v ∈ (toDiameter p).1}) :
    (toDiameter p).induced.edist u v ≤ 3 := by
  have h01 : (toDiameter p).induced.edist (toDiameterHub₀ p) (toDiameterHub₁ p) ≤ 1 :=
    edist_le_one_of (Or.inr (Or.inl (const_mem_edges_toDiameter
      (by simp [constEdges, toDiameterHub₀, toDiameterHub₁]))))
  have near (u : {v // v ∈ (toDiameter p).1}) :
      (toDiameter p).induced.edist u (toDiameterHub₀ p) ≤ 1 ∨
      (toDiameter p).induced.edist u (toDiameterHub₁ p) ≤ 1 := by
    rcases classify_toDiameter u with ⟨h, -⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
    · exact Or.inl (SimpleGraph.edist_comm.trans_le h)
    · exact Or.inl (SimpleGraph.edist_comm.trans_le h)
    · exact Or.inr (SimpleGraph.edist_comm.trans_le h)
  rcases near u with hu | hu <;> rcases near v with hv | hv
  · exact (edist_le_two_of hu (SimpleGraph.edist_comm.trans_le hv)).trans (by norm_num)
  · exact edist_le_three_of hu h01 (SimpleGraph.edist_comm.trans_le hv)
  · exact edist_le_three_of hu (SimpleGraph.edist_comm.trans_le h01)
      (SimpleGraph.edist_comm.trans_le hv)
  · exact (edist_le_two_of hu (SimpleGraph.edist_comm.trans_le hv)).trans (by norm_num)

/-- **Diameter at most two without an orthogonal pair**: a vector of each list share a coordinate
holding `true` in both, and all other pairs of vertices share a hub. -/
theorem edist_toDiameter_le_two (hp : p ∉ OV) (u v : {v // v ∈ (toDiameter p).1}) :
    (toDiameter p).induced.edist u v ≤ 2 := by
  have cross {u v : {v // v ∈ (toDiameter p).1}} {k j : ℕ} (hk : k < p.1.length)
      (hj : j < p.2.length) (hu : u.1 = vecVertex k) (hv : v.1 = vecVertex (p.1.length + j)) :
      (toDiameter p).induced.edist u v ≤ 2 := by
    have hno : ¬OV.Orthogonal p.1[k] p.2[j] := fun h =>
      hp ⟨_, List.getElem_mem hk, _, List.getElem_mem hj, h⟩
    obtain ⟨i, hia, hib, ha, hb⟩ := exists_getElem_of_not_orthogonal hno
    exact edist_le_two_of (w := ⟨coordVertex i, coord_mem_toDiameter₁ hk hia⟩)
      (edist_le_one_of (Or.inr (Or.inr (hu ▸ coord_mem_edges_toDiameter₁ hk hia ha))))
      (edist_le_one_of (Or.inr (Or.inl (hv ▸ coord_mem_edges_toDiameter₂ hj hib hb))))
  rcases classify_toDiameter u with ⟨hu₀, hu₁⟩ | ⟨k, hk, hu, hu₀⟩ | ⟨j, hj, hu, hu₁⟩ <;>
    rcases classify_toDiameter v with ⟨hv₀, hv₁⟩ | ⟨k', hk', hv, hv₀⟩ | ⟨j', hj', hv, hv₁⟩
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₀) hv₀
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₀) hv₀
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₁) hv₁
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₀) hv₀
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₀) hv₀
  · exact cross hk hj' hu hv
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₁) hv₁
  · exact SimpleGraph.edist_comm.trans_le (cross hk' hj hv hu)
  · exact edist_le_two_of (SimpleGraph.edist_comm.trans_le hu₁) hv₁

/-- **An orthogonal pair is at distance more than two.** -/
theorem two_lt_edist_toDiameter {k j : ℕ} (hk : k < p.1.length) (hj : j < p.2.length)
    (h : OV.Orthogonal p.1[k] p.2[j]) :
    2 < (toDiameter p).induced.edist ⟨vecVertex k, vec_mem_toDiameter₁ hk⟩
      ⟨vecVertex (p.1.length + j), vec_mem_toDiameter₂ hj⟩ := by
  rw [SimpleGraph.two_lt_edist_iff]
  refine ⟨fun he => ?_, fun he => ?_, ?_⟩
  · have := congrArg Subtype.val he
    simp only [vecVertex] at this
    omega
  · obtain ⟨-, he⟩ := Graph.toSimpleGraph_adj.mp he
    have he' : (vecVertex (p.1.length + j), vecVertex k) ∈ (toDiameter p).2 ∨
        (vecVertex k, vecVertex (p.1.length + j)) ∈ (toDiameter p).2 := he.symm
    rcases eq_of_mem_edges_toDiameter_vec₁ hk he' with he | ⟨i, -, -, he⟩ <;>
      simp only [vecVertex, coordVertex] at he <;> omega
  · refine Set.eq_empty_of_forall_notMem fun w hw => ?_
    rw [SimpleGraph.mem_commonNeighbors] at hw
    obtain ⟨-, hu⟩ := Graph.toSimpleGraph_adj.mp hw.1
    obtain ⟨-, hv⟩ := Graph.toSimpleGraph_adj.mp hw.2
    have hu' : (w.1, vecVertex k) ∈ (toDiameter p).2 ∨ (vecVertex k, w.1) ∈ (toDiameter p).2 :=
      hu.symm
    have hv' : (w.1, vecVertex (p.1.length + j)) ∈ (toDiameter p).2 ∨
        (vecVertex (p.1.length + j), w.1) ∈ (toDiameter p).2 := hv.symm
    rcases eq_of_mem_edges_toDiameter_vec₁ hk hu' with hu | ⟨i, hia, ha, hu⟩ <;>
      rcases eq_of_mem_edges_toDiameter_vec₂ hj hv' with hv | ⟨i', hib, hb, hv⟩
    · omega
    · simp only [coordVertex] at hv
      omega
    · simp only [coordVertex] at hu
      omega
    · obtain rfl : i = i' := by simp only [coordVertex] at hu hv; omega
      rcases h i with h | h
      · rw [List.getD_eq_getElem _ _ hia] at h
        exact Bool.false_ne_true (h.symm.trans ha)
      · rw [List.getD_eq_getElem _ _ hib] at h
        exact Bool.false_ne_true (h.symm.trans hb)

/-- The constant vertices `2` and `3` are not adjacent. -/
theorem one_lt_edist_toDiameter_two_three :
    1 < (toDiameter p).induced.edist ⟨2, const_mem_toDiameter (by simp [constVertices])⟩
      ⟨3, const_mem_toDiameter (by simp [constVertices])⟩ := by
  refine lt_of_not_ge fun h => ?_
  rcases SimpleGraph.edist_le_one_iff_adj_or_eq.mp h with he | he
  · obtain ⟨-, he⟩ := Graph.toSimpleGraph_adj.mp he
    have he' : ((2 : ℕ), (3 : ℕ)) ∈ (toDiameter p).2 ∨ ((3 : ℕ), (2 : ℕ)) ∈ (toDiameter p).2 := he
    rcases he' with he | he <;> rcases fst_mem_edges_toDiameter he with h | h | ⟨i, h⟩ <;>
      first | omega | (simp only [coordVertex] at h; omega)
  · have := congrArg Subtype.val he
    simp only at this
    omega

/-- **Correctness of the reduction from orthogonal vectors to diameter**: the gadget has diameter
three on instances with an orthogonal pair, and diameter two otherwise. -/
theorem ediam_toDiameter (p : List (List Bool) × List (List Bool)) :
    (toDiameter p).induced.ediam = if p ∈ OV then 3 else 2 := by
  split_ifs with hp
  · obtain ⟨a, ha, b, hb, h⟩ := hp
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
    refine le_antisymm (SimpleGraph.ediam_le_of_edist_le edist_toDiameter_le_three) ?_
    exact (Order.add_one_le_of_lt (two_lt_edist_toDiameter hk hj h)).trans
      SimpleGraph.edist_le_ediam
  · exact le_antisymm (SimpleGraph.ediam_le_of_edist_le (edist_toDiameter_le_two hp))
      ((Order.add_one_le_of_lt one_lt_edist_toDiameter_two_three).trans SimpleGraph.edist_le_ediam)

end Gadget

/-! ### One pass over an encoded instance -/

/-- The state of the parser of an encoded instance `encOV (A, B)`: whether it reads `B`, whether
it reads the marker of a bit of the outer frame of `A` (or the first bit of `encOV`), whether the
bit it reads is a frame marker, the coordinate of the current bit, and the number of the current
vector. -/
abbrev ParseState : Type := (((Bool × Bool) × Bool) × ℕ) × ℕ

/-- The encoding of the parser state. -/
abbrev encParseState : ParseState ↪ List Bool :=
  encPair (encPair (encPair (encPair encBool encBool) encBool) encNat) encNat

/-- A round of the parser, reading one bit. In the first list each bit `c` of the inner frames
comes as `[true, c]` in the outer frame, and the first unmarked bit ends the first list. In the
inner frames, a marker `true` announces a bit of the vector and `false` ends the vector. -/
def parseStep (p : ParseState × Bool) : ParseState :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then
    if p.2 then ((((false, true), p.1.1.1.2), p.1.1.2), p.1.2)
    else ((((true, false), false), p.1.1.2), p.1.2)
  else if p.1.1.1.2 then ((((p.1.1.1.1.1, false), false), p.1.1.2 + 1), p.1.2)
  else if p.2 then ((((p.1.1.1.1.1, false), true), p.1.1.2), p.1.2)
  else ((((p.1.1.1.1.1, false), false), 0), p.1.2 + 1)

/-- The output of a round of the parser: `f k i b` for the bit `b` of coordinate `i` of the vector
numbered `k`, and `g s k` at the end of the vector numbered `k` of the list `s`. -/
def parseEmit {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β)
    (p : ParseState × Bool) : List β :=
  if !p.1.1.1.1.1 && !p.1.1.1.1.2 then []
  else if p.1.1.1.2 then f p.1.2 p.1.1.2 p.2
  else if p.2 then []
  else g p.1.1.1.1.1 p.1.2

/-- **One pass of the parser** over a list of bits, from a state. -/
def parseRun {β : Type} (f : ℕ → ℕ → Bool → List β) (g : Bool → ℕ → List β) :
    ParseState → List Bool → List β
  | _, [] => []
  | s, b :: l => parseEmit f g (s, b) ++ parseRun f g (parseStep (s, b)) l

section Stream

variable {β : Type} {f : ℕ → ℕ → Bool → List β} {g : Bool → ℕ → List β}

/-- The streamed output of the parser rounds is the encoded output of the pass. -/
theorem streamEmit_eq_parseRun {enc : β ↪ List Bool} (s : ParseState) (l : List Bool) :
    streamEmit parseStep (fun p => encList enc (parseEmit f g p)) s l =
      encList enc (parseRun f g s l) := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => rw [streamEmit, ih, parseRun, encList_append]

/-- In the second phase, a frame `[true, b₁, …, true, bₙ, false]` is one vector. -/
theorem parseRun_frame_snd (i k : ℕ) (v : List Bool) (rest : List Bool) :
    parseRun f g ((((true, false), false), i), k) (frame v ++ rest) =
      bitsOut (f k) i v ++ g true k ++ parseRun f g ((((true, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [frame_nil, parseRun, parseEmit, parseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.cons_append, parseRun, parseEmit, parseStep, bitsOut]
    simp [ih, List.append_assoc]

/-- In the second phase, the frames of a list of vectors. -/
theorem parseRun_frames_snd (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    parseRun f g ((((true, false), false), 0), k) (vs.flatMap frame ++ rest) =
      vecsOut f (g true) k vs ++
        parseRun f g ((((true, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.append_assoc, parseRun_frame_snd, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- In the first phase, the outer frame marks each bit `c` of the inner frames as `[true, c]`. -/
theorem parseRun_frame_fst (i k : ℕ) (v : List Bool) (rest : List Bool) :
    parseRun f g ((((false, false), false), i), k)
        ((frame v).flatMap (fun b => [true, b]) ++ rest) =
      bitsOut (f k) i v ++ g false k ++
        parseRun f g ((((false, false), false), 0), k + 1) rest := by
  induction v generalizing i with
  | nil => simp [parseRun, parseEmit, parseStep, bitsOut]
  | cons b v ih =>
    simp only [frame_cons, List.flatMap_cons, List.cons_append, List.nil_append]
    cases b <;> simp [parseRun, parseEmit, parseStep, bitsOut, ih, List.append_assoc]

/-- In the first phase, the outer frame of the inner frames of a list of vectors. -/
theorem parseRun_frames_fst (k : ℕ) (vs : List (List Bool)) (rest : List Bool) :
    parseRun f g ((((false, false), false), 0), k)
        ((vs.flatMap frame).flatMap (fun b => [true, b]) ++ rest) =
      vecsOut f (g false) k vs ++
        parseRun f g ((((false, false), false), 0), k + vs.length) rest := by
  induction vs generalizing k with
  | nil => simp [vecsOut]
  | cons v vs ih =>
    rw [List.flatMap_cons, List.flatMap_append, List.append_assoc, parseRun_frame_fst, ih]
    simp [vecsOut, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 vs.length]

/-- **The parser on an encoded instance**: it emits the outputs of the first list, then those of
the second, numbering the vectors of both lists consecutively. -/
theorem parseRun_encOV (p : List (List Bool) × List (List Bool)) :
    parseRun f g ((((false, false), false), 0), 0) (encOV p) =
      vecsOut f (g false) 0 p.1 ++ vecsOut f (g true) p.1.length p.2 := by
  have hl (l : List (List Bool)) : encList encBits l = l.flatMap frame := rfl
  have e : encOV p = (p.1.flatMap frame).flatMap (fun b => [true, b]) ++
      (false :: p.2.flatMap frame ++ []) := by
    simp only [encOV, encPair_apply, frame, hl, List.append_nil, List.append_assoc,
      List.singleton_append]
  have h₁ : parseStep (((((false, false), false), 0), 0 + p.1.length), false) =
      ((((true, false), false), 0), p.1.length) := by simp [parseStep]
  have h₂ : parseEmit f g (((((false, false), false), 0), 0 + p.1.length), false) = [] := by
    simp [parseEmit]
  rw [e, parseRun_frames_fst, List.cons_append, parseRun, h₁, h₂, List.nil_append,
    parseRun_frames_snd]
  simp [parseRun]

end Stream

/-! ### The size of the parser state -/

/-- A round increases the coordinate plus the vector number by at most one. -/
private theorem parseStep_le (s : ParseState) (b : Bool) :
    (parseStep (s, b)).1.2 + (parseStep (s, b)).2 ≤ s.1.2 + s.2 + 1 := by
  unfold parseStep
  split_ifs <;> simp only <;> omega

/-- The coordinate plus the vector number grow by at most the number of rounds. -/
private theorem foldl_parseStep_le (s : ParseState) (l : List Bool) :
    (l.foldl (fun s b => parseStep (s, b)) s).1.2 + (l.foldl (fun s b => parseStep (s, b)) s).2 ≤
      s.1.2 + s.2 + l.length := by
  induction l generalizing s with
  | nil => simp
  | cons b l ih =>
    have := ih (parseStep (s, b))
    have := parseStep_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- The length of an encoded parser state. -/
private theorem length_encParseState (s : ParseState) :
    (encParseState s).length = 43 + 2 * Nat.size s.1.2 + Nat.size s.2 := by
  simp only [length_encPair, encBool_apply, encNat_apply, Nat.size_eq_bits_len,
    List.length_singleton]
  omega

/-- The parser state after `j` bits holds numbers at most `j`. -/
private theorem length_encParseState_streamState_le (x : List Bool) (j : ℕ) :
    (encParseState (streamState ((((false, false), false), 0), 0) parseStep x j)).length ≤
      43 + 3 * Nat.size x.length := by
  have h₁ : (streamState ((((false, false), false), 0), 0) parseStep x j).1.2 +
      (streamState ((((false, false), false), 0), 0) parseStep x j).2 ≤ x.length := by
    have := foldl_parseStep_le ((((false, false), false), 0), 0) (x.take j)
    simp only [List.length_take, Nat.zero_add] at this
    exact this.trans (min_le_right _ _)
  have h₂ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) parseStep x j).1.2 ≤ x.length by omega)
  have h₃ := Nat.size_le_size (show
    (streamState ((((false, false), false), 0), 0) parseStep x j).2 ≤ x.length by omega)
  rw [length_encParseState]
  omega

open ComputableInPolyTime in
/-- A round of the parser is computable in polynomial time. -/
theorem computableInPolyTime_parseStep :
    ComputableInPolyTime parseStep (encPair encParseState encBool) encParseState := by
  unfold parseStep
  fun_prop

open ComputableInPolyTime in
/-- The output of a round of the parser is computable in polynomial time when its outputs are. -/
theorem computableInPolyTime_parseEmit {β : Type} {enc : β ↪ List Bool} {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β}
    (hf : ComputableInPolyTime (fun p : ParseState × Bool => f p.1.2 p.1.1.2 p.2)
      (encPair encParseState encBool) (encList enc))
    (hg : ComputableInPolyTime (fun p : ParseState × Bool => g p.1.1.1.1.1 p.1.2)
      (encPair encParseState encBool) (encList enc)) :
    ComputableInPolyTime (parseEmit f g) (encPair encParseState encBool) (encList enc) := by
  have hnil : ComputableInPolyTime (fun _ : ParseState × Bool => ([] : List β))
      (encPair encParseState encBool) (encList enc) := by fun_prop
  have hc₁ : ComputableInPolyTime (fun p : ParseState × Bool => !p.1.1.1.1.1 && !p.1.1.1.1.2)
      (encPair encParseState encBool) encBool := by fun_prop
  have hc₂ : ComputableInPolyTime (fun p : ParseState × Bool => p.1.1.1.2)
      (encPair encParseState encBool) encBool := by fun_prop
  have hc₃ : ComputableInPolyTime (fun p : ParseState × Bool => p.2)
      (encPair encParseState encBool) encBool := by fun_prop
  exact ite' hc₁ hnil (ite' hc₂ hf (ite' hc₃ hnil hg))

open ComputableInPolyTime in
/-- **One pass of the parser** over an encoded instance runs within time `L (log L) ^ D` on inputs
of length `L`, when its outputs are computable in polynomial time. -/
theorem computableInO_parseRun {β : Type} {enc : β ↪ List Bool} {f : ℕ → ℕ → Bool → List β}
    {g : Bool → ℕ → List β} (fin : List β)
    (hfg : ComputableInPolyTime (parseEmit f g) (encPair encParseState encBool) (encList enc)) :
    ∃ D, ComputableInO
      (fun x : List Bool => parseRun f g ((((false, false), false), 0), 0) x ++ fin)
      encBits (encList enc) (fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D)
      fun x => (x.length + 1) * (Nat.size x.length + 1) ^ D := by
  obtain ⟨dN, _, hN_deg⟩ := computableInPolyTime_parseStep.exists_degree
  obtain ⟨tN, sN, ⟨cN, htN⟩, ⟨cN', hsN⟩, hN⟩ := Internal.NormalForm.degree hN_deg
  obtain ⟨dE, _, hE_deg⟩ := hfg.exists_degree
  obtain ⟨tE, sE, ⟨cE, htE⟩, ⟨cE', hsE⟩, hE⟩ := Internal.NormalForm.degree hE_deg
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const (α := List Bool) (encIn := encBits)
    (encOut := encParseState) ((((false, false), false), 0), 0)
  obtain ⟨cF, hF⟩ := computableInTimeAndSpace_of_const (α := ParseState) (encIn := encParseState)
    (encOut := encList enc) fin
  let reader : InputReader Bool Unit := ⟨(), fun _ b => (none, some b)⟩
  have hI' : ComputableTidilyInTimeAndSpace (fun _ : List Bool => ((((false, false), false), 0), 0))
      encBits encParseState (fun _ => 2 * cI + 2) (fun _ => 0) := hI.computableTidilyInTimeAndSpace
  have hF' : ComputableTidilyInTimeAndSpace (fun _ : ParseState => fin) encParseState (encList enc)
      (fun _ => 2 * cF + 2) (fun _ => 0) := hF.computableTidilyInTimeAndSpace
  -- the rounds take time polylogarithmic in the input length
  have hpow (x : List Bool) (d : ℕ) (hd : d ≤ dN + dE + 1) :
      (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤
        89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    calc (2 * (43 + 3 * Nat.size x.length) + 3) ^ d ≤ (89 * (Nat.size x.length + 1)) ^ d :=
          Nat.pow_le_pow_left (by omega) d
      _ = 89 ^ d * (Nat.size x.length + 1) ^ d := Nat.mul_pow _ _ _
      _ ≤ 89 ^ d * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) hd)
  have hround (x : List Bool) (j : ℕ) (hj : j < x.length) (c₁ c₂ : ℕ)
      (u₁ u₂ : ParseState × Bool → ℕ)
      (h₁ : ∀ a, u₁ a ≤ c₁ * ((encPair encParseState encBool a).length + 1) ^ dN)
      (h₂ : ∀ a, u₂ a ≤ c₂ * ((encPair encParseState encBool a).length + 1) ^ dE) :
      u₁ (streamState ((((false, false), false), 0), 0) parseStep x j, x[j]) +
        u₂ (streamState ((((false, false), false), 0), 0) parseStep x j, x[j]) ≤
      c₁ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
        c₂ * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE := by
    have hs : (encParseState
        (streamState ((((false, false), false), 0), 0) parseStep x j, x[j]).1).length ≤
        43 + 3 * Nat.size x.length := length_encParseState_streamState_le x j
    have e : (encPair encParseState encBool
        (streamState ((((false, false), false), 0), 0) parseStep x j, x[j])).length + 1 ≤
        2 * (43 + 3 * Nat.size x.length) + 3 := by
      rw [length_encPair, encBool_apply, List.length_singleton]
      omega
    exact Nat.add_le_add ((h₁ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
      ((h₂ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e _)))
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.streamFold reader (fun b => [b])
    (fun _ => List.cons_ne_nil _ _) (fun a rest => by simp [reader, InputReader.read])
    (encA := encBool) (fun x => x) (fun x => by simp) hI' hN hE hF'
    (g := fun x : List Bool => parseRun f g ((((false, false), false), 0), 0) x ++ fin)
    (fun x => by rw [encList_append, streamEmit_eq_parseRun])
    (tMax := fun x => cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (sMax := fun x => cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE)
    (lMax := fun x => 43 + 3 * Nat.size x.length)
    (fun x j hj => hround x j hj cN cE tN tE htN htE)
    (fun x j hj => hround x j hj cN' cE' sN sE hsN hsE)
    (fun x j _ => length_encParseState_streamState_le x j)
    (fun x j hj => by rw [encBool_apply, List.length_singleton]; omega)
  set M := cN * 89 ^ dN + cE * 89 ^ dE + cN' * 89 ^ dN + cE' * 89 ^ dE
  have key (L Y t l a b : ℕ) (hY : 1 ≤ Y) (ht : t ≤ M * Y) (hl : l ≤ 43 * Y) :
      a + b + L + L * (t + l + 1) + l + 1 ≤ (a + b + M + 100) * ((L + 1) * Y + 1) := by
    nlinarith [Nat.mul_le_mul_left L ht, Nat.mul_le_mul_left L hl, Nat.mul_le_mul_left L hY]
  have hY (x : List Bool) : 1 ≤ (Nat.size x.length + 1) ^ (dN + dE + 1) :=
    Nat.one_le_pow _ _ (by omega)
  have hl (x : List Bool) : 43 + 3 * Nat.size x.length ≤
      43 * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have := Nat.le_self_pow (show dN + dE + 1 ≠ 0 by omega) (Nat.size x.length + 1)
    omega
  have ht (x : List Bool) : cN * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  have hs (x : List Bool) : cN' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dN +
      cE' * (2 * (43 + 3 * Nat.size x.length) + 3) ^ dE ≤
      M * (Nat.size x.length + 1) ^ (dN + dE + 1) := by
    have h₁ := Nat.mul_le_mul_left cN' (hpow x dN (by omega))
    have h₂ := Nat.mul_le_mul_left cE' (hpow x dE (by omega))
    simp only [M, Nat.add_mul, Nat.mul_assoc] at h₁ h₂ ⊢
    omega
  refine ⟨dN + dE + 1, ComputableInO.of_bounds h.computableInTimeAndSpace
    (c * (2 * cI + 2 + (2 * cF + 2) + M + 100)) (fun x => ?_) (fun x => ?_)
    (fun x => (h.computableInTimeAndSpace.length_le x).trans ?_)⟩
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [encBits_apply]
    exact key _ _ _ _ _ _ (hY x) (ht x) (hl x)
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have h₁ := hs x
    have h₂ := hl x
    have h₃ := hY x
    have h₄ : (Nat.size x.length + 1) ^ (dN + dE + 1) ≤
        (x.length + 1) * (Nat.size x.length + 1) ^ (dN + dE + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    nlinarith
  · rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [encBits_apply]
    exact key _ _ _ _ _ _ (hY x) (ht x) (hl x)

open ComputableInPolyTime in
/-- **The reduction from orthogonal vectors to diameter runs in quasi-linear time**: within time
`L (log L) ^ D` on instances encoded in length `L`. -/
theorem exists_computableInO_toDiameter : ∃ D, ComputableInO toDiameter encOV encGraph
    (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D)
    (fun p => ((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D) := by
  have hV : ComputableInPolyTime (parseEmit bitVertices endVertices) (encPair encParseState encBool)
      (encList encNat) :=
    computableInPolyTime_parseEmit (by unfold bitVertices coordVertex; fun_prop)
      (by unfold endVertices vecVertex; fun_prop)
  have hE : ComputableInPolyTime (parseEmit bitEdges endEdges) (encPair encParseState encBool)
      (encList (encPair encNat encNat)) :=
    computableInPolyTime_parseEmit (by unfold bitEdges coordVertex vecVertex; fun_prop)
      (by unfold endEdges sideVertex vecVertex; fun_prop)
  obtain ⟨D₁, h₁⟩ := computableInO_parseRun constVertices hV
  obtain ⟨D₂, h₂⟩ := computableInO_parseRun constEdges hE
  have h := ((h₁.prod h₂).of_encIn_eq (encD := encOV) (fun p => encOV p) (fun _ => rfl)).of_enc_eq
    (g := toDiameter)
    (encC := encGraph) (fun p => by
      simp only [Function.comp_apply, toDiameter, parseRun_encOV]
      rfl)
  refine ⟨D₁ + D₂, h.mono 2 (fun p => ?_) (fun p => ?_)⟩ <;>
  · simp only [Function.comp_apply]
    have a₁ := Nat.mul_le_mul_left ((encOV p).length + 1)
      (Nat.pow_le_pow_right (Nat.add_pos_right (Nat.size (encOV p).length) Nat.one_pos)
        (Nat.le_add_right D₁ D₂))
    have a₂ := Nat.mul_le_mul_left ((encOV p).length + 1)
      (Nat.pow_le_pow_right (Nat.add_pos_right (Nat.size (encOV p).length) Nat.one_pos)
        (Nat.le_add_left D₂ D₁))
    omega

/-- The encoded length of an instance of `N` vectors of dimension `d` is `O(N d)`. -/
theorem length_encOV_le (p : List (List Bool) × List (List Bool)) :
    (encOV p).length + 1 ≤ 4 * (p.1.length + p.2.length) * (OV.dim p + 1) + 2 := by
  have hl (l : List (List Bool)) (hd : ∀ v ∈ l, v.length ≤ OV.dim p) :
      (encList encBits l).length ≤ l.length * (2 * OV.dim p + 1) := by
    rw [length_encList]
    calc (l.map fun a => 2 * (encBits a).length + 1).sum
        ≤ (l.map fun _ => 2 * OV.dim p + 1).sum :=
          List.sum_le_sum fun a ha => by
            have := hd a ha
            rw [encBits_apply]
            omega
      _ = l.length * (2 * OV.dim p + 1) := by simp
  have h₁ := hl p.1 fun v hv => le_listMax (f := List.length) (List.mem_append_left _ hv)
  have h₂ := hl p.2 fun v hv => le_listMax (f := List.length) (List.mem_append_right _ hv)
  rw [encOV, length_encPair]
  nlinarith

end OV

open OV

/-! ### The conditional lower bound -/

/-- **Separating diameter two from three decides orthogonal vectors**, the orthogonal vectors form
of Theorem 9 of [RodittyVassilevskaWilliams2013]: a procedure accepting the graphs of diameter at
most two and rejecting those of diameter three, within time `L ^ (2 - ε)` on graphs encoded in
length `L`, decides `OV` within time `N ^ (2 - min ε 1 / 2) (d + 1) ^ 2` on `N` vectors of
dimension `d`. -/
theorem DecidableInTimeO.decidableInTimeO_OV_of_diameter {ε : ℝ} (hε : 0 < ε) {S : Set Graph}
    (hS₂ : ∀ G : Graph, G.induced.ediam ≤ 2 → G ∈ S)
    (hS₃ : ∀ G : Graph, G.induced.ediam = 3 → G ∉ S)
    (hS : DecidableInTimeO S encGraph fun G => ((encGraph G).length : ℝ) ^ (2 - ε)) :
    DecidableInTimeO OV encOV fun p =>
      ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - min ε 1 / 2) * (OV.dim p + 1) ^ 2 := by
  obtain ⟨g, t, c, hg, hgS, ht⟩ := hS.exists_computableInO
  obtain ⟨D, hred⟩ := exists_computableInO_toDiameter
  obtain ⟨cR, hcR⟩ := hred.length_le
  set ε₀ := min ε 1 with hε₀_def
  have hε₀ : 0 < ε₀ := lt_min hε one_pos
  have hε₁ : ε₀ ≤ 1 := min_le_right ε 1
  have hεε : ε₀ ≤ ε := min_le_left ε 1
  obtain ⟨K, hK, hKb⟩ := Nat.exists_size_add_one_pow_le_mul_rpow D (ε := ε₀ / 4) (by positivity)
  have hdec := (hg.comp hred).not'
  set r : ℝ := 2 - ε₀ / 2 with hr
  -- the time of the composed decider, in terms of `X = L + 1`
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set C₁ : ℝ := cR * (K + 1) + 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := by
    have : (0 : ℝ) ≤ cR * (K + 1) := by positivity
    linarith
  have hbound (p : List (List Bool) × List (List Bool)) :
      ((((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D + t (toDiameter p) : ℕ) : ℝ) ≤
        (K + c * C₁ ^ 2) * (((encOV p).length : ℝ) + 1) ^ r + c := by
    set X : ℝ := ((encOV p).length : ℝ) + 1 with hX
    have hX1 : 1 ≤ X := by linarith [(Nat.cast_nonneg (encOV p).length : (0 : ℝ) ≤ _)]
    have hX0 : 0 < X := by linarith
    have hT : (((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D : ℕ) ≤
        K * X ^ (1 + ε₀ / 4) := by
      push_cast
      rw [Real.rpow_add hX0, Real.rpow_one]
      have := hKb (encOV p).length
      push_cast at this
      calc X * ((Nat.size (encOV p).length : ℝ) + 1) ^ D ≤ X * (K * X ^ (ε₀ / 4)) :=
            mul_le_mul_of_nonneg_left this hX0.le
        _ = K * (X * X ^ (ε₀ / 4)) := by ring
    -- the reduced instance has encoded length `O(X ^ (1 + δ))`
    have hLG : ((encGraph (toDiameter p)).length : ℝ) + 1 ≤ C₁ * X ^ (1 + ε₀ / 4) := by
      have h' : ((encGraph (toDiameter p)).length : ℝ) ≤
          cR * ((((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D : ℕ) + 1) := by
        exact_mod_cast hcR p
      have hXp : 1 ≤ X ^ (1 + ε₀ / 4) := Real.one_le_rpow hX1 (by positivity)
      have hcR0 : (0 : ℝ) ≤ cR := Nat.cast_nonneg cR
      have := mul_le_mul_of_nonneg_left hT hcR0
      nlinarith
    have hpowLG : ((encGraph (toDiameter p)).length : ℝ) ^ (2 - ε) ≤
        (((encGraph (toDiameter p)).length : ℝ) + 1) ^ (2 - ε₀) := by
      rcases Nat.eq_zero_or_pos (encGraph (toDiameter p)).length with h0 | h0
      · rw [h0, Nat.cast_zero, zero_add, Real.one_rpow]
        by_cases h2 : 2 - ε = 0
        · rw [h2, Real.rpow_zero]
        · rw [Real.zero_rpow h2]
          exact zero_le_one
      · have h1 : (1 : ℝ) ≤ (encGraph (toDiameter p)).length := by exact_mod_cast h0
        calc ((encGraph (toDiameter p)).length : ℝ) ^ (2 - ε)
            ≤ ((encGraph (toDiameter p)).length : ℝ) ^ (2 - ε₀) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ ≤ (((encGraph (toDiameter p)).length : ℝ) + 1) ^ (2 - ε₀) :=
              Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hLGr : (((encGraph (toDiameter p)).length : ℝ) + 1) ^ (2 - ε₀) ≤ C₁ ^ 2 * X ^ r := by
      calc (((encGraph (toDiameter p)).length : ℝ) + 1) ^ (2 - ε₀)
          ≤ (C₁ * X ^ (1 + ε₀ / 4)) ^ (2 - ε₀) :=
            Real.rpow_le_rpow (by positivity) hLG (by linarith)
        _ = C₁ ^ (2 - ε₀) * X ^ ((1 + ε₀ / 4) * (2 - ε₀)) := by
            rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_mul hX0.le]
        _ ≤ C₁ ^ (2 : ℝ) * X ^ r := by
            refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le hC₁1 (by linarith))
              (Real.rpow_le_rpow_of_exponent_le hX1 ?_) (by positivity) (by positivity)
            nlinarith
        _ = C₁ ^ 2 * X ^ r := by rw [Real.rpow_two]
    have htLG : (t (toDiameter p) : ℝ) ≤ c * (C₁ ^ 2 * X ^ r) + c :=
      (ht _).trans (by nlinarith [hpowLG.trans hLGr])
    have hXr : X ^ (1 + ε₀ / 4) ≤ X ^ r := Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    push_cast
    push_cast at hT
    nlinarith
  -- in terms of the number `N` of vectors and the dimension `d`
  set C₂ : ℝ := K + c * C₁ ^ 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hfinal (p : List (List Bool) × List (List Bool)) :
      ((((encOV p).length + 1) * (Nat.size (encOV p).length + 1) ^ D + t (toDiameter p) : ℕ) : ℝ) ≤
        (40 * C₂ + c) * ((((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
          ((OV.dim p : ℝ) + 1) ^ 2)) + (40 * C₂ + c) := by
    set X : ℝ := ((encOV p).length : ℝ) + 1 with hX
    have hX1 : 1 ≤ X := by linarith [(Nat.cast_nonneg (encOV p).length : (0 : ℝ) ≤ _)]
    have hlen := length_encOV_le p
    have hlen' : X ≤ 4 * ((p.1.length + p.2.length : ℕ) : ℝ) * ((OV.dim p : ℝ) + 1) + 2 := by
      have : (((encOV p).length + 1 : ℕ) : ℝ) ≤
          ((4 * (p.1.length + p.2.length) * (OV.dim p + 1) + 2 : ℕ) : ℝ) := by exact_mod_cast hlen
      push_cast at this
      push_cast
      linarith
    set Y : ℝ := ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) * ((OV.dim p : ℝ) + 1) ^ 2
    have hY0 : 0 ≤ Y := by positivity
    have hXr : X ^ r ≤ 36 * Y + 4 := by
      rcases Nat.eq_zero_or_pos (p.1.length + p.2.length) with hN | hN
      · rw [hN, Nat.cast_zero, mul_zero, zero_mul, zero_add] at hlen'
        calc X ^ r ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow (by linarith) hlen' (by linarith) |>.trans
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
          _ = 4 := by norm_num
          _ ≤ 36 * Y + 4 := by linarith
      · have hN1 : (1 : ℝ) ≤ ((p.1.length + p.2.length : ℕ) : ℝ) := by exact_mod_cast hN
        have hd1 : (1 : ℝ) ≤ (OV.dim p : ℝ) + 1 := by
          linarith [(Nat.cast_nonneg (OV.dim p) : (0 : ℝ) ≤ _)]
        have hX6 : X ≤ 6 * (((p.1.length + p.2.length : ℕ) : ℝ) * ((OV.dim p : ℝ) + 1)) := by
          nlinarith
        calc X ^ r ≤ (6 * (((p.1.length + p.2.length : ℕ) : ℝ) * ((OV.dim p : ℝ) + 1))) ^ r :=
              Real.rpow_le_rpow (by linarith) hX6 (by linarith)
          _ = 6 ^ r * (((p.1.length + p.2.length : ℕ) : ℝ) ^ r * ((OV.dim p : ℝ) + 1) ^ r) := by
              rw [Real.mul_rpow (by norm_num) (by positivity),
                Real.mul_rpow (by positivity) (by positivity)]
          _ ≤ 36 * Y := by
              have h6 : (6 : ℝ) ^ r ≤ 36 :=
                (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)).trans
                  (by norm_num : (6 : ℝ) ^ (2 : ℝ) ≤ 36)
              have hd : ((OV.dim p : ℝ) + 1) ^ r ≤ ((OV.dim p : ℝ) + 1) ^ 2 := by
                rw [← Real.rpow_two]
                exact Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
              have hNr : (0 : ℝ) ≤ ((p.1.length + p.2.length : ℕ) : ℝ) ^ r := by positivity
              calc 6 ^ r * (((p.1.length + p.2.length : ℕ) : ℝ) ^ r * ((OV.dim p : ℝ) + 1) ^ r)
                  ≤ 36 * (((p.1.length + p.2.length : ℕ) : ℝ) ^ r * ((OV.dim p : ℝ) + 1) ^ 2) :=
                    mul_le_mul h6 (mul_le_mul_of_nonneg_left hd hNr) (by positivity)
                      (by norm_num)
                _ = 36 * Y := rfl
          _ ≤ 36 * Y + 4 := by linarith
    have := hbound p
    nlinarith
  refine (DecidableInTimeO.of_computableInO hdec (fun p => ?_) (fun p => hfinal p)).mono
    (⌈40 * C₂ + c⌉₊) (fun p => ?_) (fun p => by positivity)
  · simp only [Function.comp_apply]
    by_cases hp : p ∈ OV
    · have h := ediam_toDiameter p
      simp only [hp, ↓reduceIte] at h
      have := (hgS (toDiameter p)).not.mp (hS₃ _ h)
      simp [hp, this]
    · have h := ediam_toDiameter p
      simp only [hp, ↓reduceIte] at h
      have := (hgS (toDiameter p)).mp (hS₂ _ h.le)
      simp [hp, this]
  · have hC : (40 * C₂ + c) ≤ (⌈40 * C₂ + c⌉₊ : ℝ) := Nat.le_ceil _
    have hY0 : (0 : ℝ) ≤ ((p.1.length + p.2.length : ℕ) : ℝ) ^ (2 - ε₀ / 2) *
        ((OV.dim p : ℝ) + 1) ^ 2 := by positivity
    nlinarith

/-- **Orthogonal vectors hardness of diameter two versus three** [RodittyVassilevskaWilliams2013]:
under the orthogonal vectors hypothesis, for every `ε > 0`, no procedure accepting the graphs of
diameter at most two and rejecting those of diameter three runs within time `L ^ (2 - ε)` on
graphs encoded in length `L`. -/
theorem not_decidableInTimeO_diameter_of_OVH (hOVH : OVH) {ε : ℝ} (hε : 0 < ε)
    {S : Set Graph} (hS₂ : ∀ G : Graph, G.induced.ediam ≤ 2 → G ∈ S)
    (hS₃ : ∀ G : Graph, G.induced.ediam = 3 → G ∉ S) :
    ¬DecidableInTimeO S encGraph fun G => ((encGraph G).length : ℝ) ^ (2 - ε) := fun hS =>
  hOVH _ (half_pos (lt_min hε one_pos)) 2 (hS.decidableInTimeO_OV_of_diameter hε hS₂ hS₃)

/-- **Orthogonal vectors hardness of diameter two versus three, in the size of the graph**: under
the orthogonal vectors hypothesis, for every `ε > 0`, no procedure accepting the graphs of diameter
at most two and rejecting those of diameter three runs within time `(n + m) ^ (2 - ε) + L` on
graphs listing `n` vertices and `m` edges, encoded in length `L`. The term `L` lets the procedure
read its input: without it the statement would hold without the hypothesis, since a time bound in
`n + m` alone does not allow reading long vertex labels. -/
theorem not_decidableInTimeO_diameter_size_of_OVH (hOVH : OVH) {ε : ℝ} (hε : 0 < ε)
    {S : Set Graph} (hS₂ : ∀ G : Graph, G.induced.ediam ≤ 2 → G ∈ S)
    (hS₃ : ∀ G : Graph, G.induced.ediam = 3 → G ∉ S) :
    ¬DecidableInTimeO S encGraph fun G =>
      ((G.1.length + G.2.length : ℕ) : ℝ) ^ (2 - ε) + (encGraph G).length := by
  intro hS
  refine not_decidableInTimeO_diameter_of_OVH hOVH (lt_min hε one_pos) hS₂ hS₃
    (hS.mono 2 (fun G => ?_) (fun G => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hle : ((G.1.length + G.2.length : ℕ) : ℝ) ≤ (encGraph G).length := by
    exact_mod_cast G.length_vertices_add_length_edges_le_encGraph
  have hL : (1 : ℝ) ≤ (encGraph G).length := by
    have : 0 < (encGraph G).length := by
      rw [encGraph, length_encPair]
      omega
    exact_mod_cast this
  have hpos : (0 : ℝ) ≤ ((encGraph G).length : ℝ) ^ (2 - min ε 1) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  -- the size term
  have hA : ((G.1.length + G.2.length : ℕ) : ℝ) ^ (2 - ε) ≤
      ((encGraph G).length : ℝ) ^ (2 - min ε 1) + 1 := by
    rcases Nat.eq_zero_or_pos (G.1.length + G.2.length) with h0 | h0
    · rw [h0, Nat.cast_zero]
      have h₁ : (0 : ℝ) ^ (2 - ε) ≤ 1 := by
        by_cases h2 : 2 - ε = 0
        · rw [h2, Real.rpow_zero]
        · rw [Real.zero_rpow h2]
          exact zero_le_one
      linarith
    · have h1 : (1 : ℝ) ≤ ((G.1.length + G.2.length : ℕ) : ℝ) := by exact_mod_cast h0
      have h₁ : ((G.1.length + G.2.length : ℕ) : ℝ) ^ (2 - ε) ≤
          ((encGraph G).length : ℝ) ^ (2 - min ε 1) :=
        (Real.rpow_le_rpow_of_exponent_le h1 (by linarith [min_le_left ε 1])).trans
          (Real.rpow_le_rpow (by linarith) hle (by linarith [min_le_right ε 1]))
      linarith
  -- the length term
  have hB : ((encGraph G).length : ℝ) ≤ ((encGraph G).length : ℝ) ^ (2 - min ε 1) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL
      (show (1 : ℝ) ≤ 2 - min ε 1 by linarith [min_le_right ε 1])
    rwa [Real.rpow_one] at h
  simp only [Nat.cast_ofNat]
  linarith

/-- **Diameter at most two is not decidable in subquadratic time under the orthogonal vectors
hypothesis**, for graphs encoded in length `L`. -/
theorem not_decidableInTimeO_ediam_le_two_of_OVH (hOVH : OVH) {ε : ℝ} (hε : 0 < ε) :
    ¬DecidableInTimeO {G : Graph | G.induced.ediam ≤ 2} encGraph
      fun G => ((encGraph G).length : ℝ) ^ (2 - ε) :=
  not_decidableInTimeO_diameter_of_OVH hOVH hε (fun _ h => h) fun G h hG => by
    have h₂ : G.induced.ediam ≤ 2 := hG
    rw [h] at h₂
    exact absurd h₂ (by decide)

end Cslib.Complexity
