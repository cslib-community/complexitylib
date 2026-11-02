/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.AdjacencyList.Spec
public import Complexity.DataStructure.Memory.Frame
public import Complexity.DataStructure.Memory.Triple

/-!
# Adjacency arrays over the memory oracle

The read-only adjacency-list interface `AdjacencyList.spec n` is implemented over
`Memory.spec w` by compressed adjacency arrays: a field `offsets` whose cell `u` holds the start
of the list of `u` in the edge array, so that the out-degree of `u` is the difference of two
consecutive offsets, and a field `edges` holding each edge as two cells, its target and its
weight. This is the layout in which a word RAM receives a graph as input. A degree query reads
two offsets, and an edge query reads an offset and the edge's two cells (`amortized`).

The interface never changes its state, so a refinement represents one graph `adj`: its invariant
says that the arrays hold `adj` (`Holds`), and its abstraction function is constant. The methods
write nothing (`ops_triple`), and the invariant reads only the two fields, so the arrays are
framed by their fields and share memory with other structures (`framed`).

## Main definitions

* `Layout`, `Layout.footprint`, `Layout.Valid`: the two fields, their cells, and the length of the
  offset field.
* `degree`, `edge`, `ops`, `methods`: the queries as memory programs.
* `Holds`, `Inv`: the arrays hold a graph, and the implementation invariant.
* `refinement`, `framed`: the arrays as a refinement of the interface for the graph they hold,
  framed by their fields.

## Main results

* `ops_triple`: each query returns the specified answer within three memory units, and writes
  nothing.
* `amortized`: every query costs at most three memory units.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 22.1][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.AdjacencyList.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory

/-- Adjacency arrays: the offset of each vertex's list, and the edges, two cells each. -/
structure Layout where
  /-- Cell `u` holds the position of the first edge out of `u`; cell `n` the number of edges. -/
  offsets : Block
  /-- Edge `j` occupies cells `2 j` (its target) and `2 j + 1` (its weight). -/
  edges : Block

namespace Layout

/-- The cells of both fields. -/
def footprint (L : Layout) : Finset ℕ := L.offsets.footprint ∪ L.edges.footprint

/-- The offset field of a graph on `n` vertices has `n + 1` cells. -/
structure Valid (L : Layout) (n : ℕ) : Prop where
  /-- One offset per vertex, and the end of the last list. -/
  offsets_length : L.offsets.length = n + 1

end Layout

variable {n : ℕ} (L : Layout)

/-- The out-degree of `u`: the difference of two consecutive offsets. -/
def degree (u : Fin n) : Prog ℕ := do
  let a ← L.offsets.get u
  let b ← L.offsets.get (u + 1)
  pure (b - a)

/-- The `i`-th edge out of `u`: its target and weight, from the edge at the offset of `u` plus
`i`. A target that is not a vertex cannot occur for an admissible query; the answer is then the
spec's placeholder `(u, 0)`. -/
def edge (u : Fin n) (i : ℕ) : Prog (Fin n × ℕ) := do
  let a ← L.offsets.get u
  let t ← L.edges.get (2 * (a + i))
  let c ← L.edges.get (2 * (a + i) + 1)
  pure (if h : t < n then (⟨t, h⟩, c) else (u, 0))

/-- The queries as memory programs. -/
def ops : (o : AdjacencyList.Op n) → Prog o.Result
  | .degree u => degree L u
  | .edge u i => edge L u i

/-- The queries as methods of `AdjacencyList.spec n` over `Memory.spec w`. -/
abbrev methods (w : ℕ) : Methods (AdjacencyList.spec n) (Memory.spec w) := ops L

/-- The memory `m` holds the graph `adj` in the layout: consecutive offsets differ by the
out-degrees, the edges out of `u` follow its offset in order, and every list ends within the edge
field. -/
structure Holds (adj : AdjacencyList.State n) (m : ℕ → ℕ) : Prop where
  /-- The list of `u` ends where the list of `u + 1` starts. -/
  offset_succ : ∀ u : Fin n,
    m (L.offsets.base + (u + 1)) = m (L.offsets.base + u) + (adj u).length
  /-- Every list ends within the edge field. -/
  end_le : ∀ u : Fin n, 2 * m (L.offsets.base + (u + 1)) ≤ L.edges.length
  /-- The target of each edge. -/
  target : ∀ (u : Fin n) (i : ℕ) (hi : i < (adj u).length),
    m (L.edges.base + 2 * (m (L.offsets.base + u) + i)) = (adj u)[i].1
  /-- The weight of each edge. -/
  weight : ∀ (u : Fin n) (i : ℕ) (hi : i < (adj u).length),
    m (L.edges.base + (2 * (m (L.offsets.base + u) + i) + 1)) = (adj u)[i].2

/-- The implementation invariant for the graph `adj`: both fields are allocated and hold it. -/
structure Inv (adj : AdjacencyList.State n) (s : Memory.State) : Prop where
  /-- The offset field is allocated. -/
  offsets_allocated : L.offsets.Allocated s
  /-- The edge field is allocated. -/
  edges_allocated : L.edges.Allocated s
  /-- The fields hold the graph. -/
  holds : Holds L adj s.mem

variable {L} {w : ℕ} {adj : AdjacencyList.State n}

/-- The cells an edge query reads lie in the edge field. -/
theorem Holds.edge_lt {m : ℕ → ℕ} (h : Holds L adj m) (u : Fin n) {i : ℕ}
    (hi : i < (adj u).length) : 2 * (m (L.offsets.base + u) + i) + 1 < L.edges.length := by
  have h₁ := h.offset_succ u
  have h₂ := h.end_le u
  omega

/-- **Each query returns the specified answer** within three memory units, and writes nothing. -/
theorem ops_triple (hL : L.Valid n) {s : Memory.State} (hs : Inv L adj s)
    (o : AdjacencyList.Op n) (hv : AdjacencyList.valid adj o) :
    Triple w s (ops L o) 3 fun r s' => AdjacencyList.step adj o = (adj, r) ∧ s' = s := by
  have hoff : ∀ j ≤ n, L.offsets.base + j < s.frontier := fun j hj =>
    hs.offsets_allocated.lt_frontier (by rw [hL.offsets_length]; omega)
  cases o with
  | degree u =>
    refine Triple.read_bind (hoff u u.isLt.le) <| Triple.read_bind (hoff (u + 1) u.isLt) <|
      Triple.pure ⟨?_, rfl⟩
    rw [AdjacencyList.step_degree, hs.holds.offset_succ u]
    simp
  | edge u i =>
    have hlt := hs.holds.edge_lt u hv
    refine Triple.read_bind (hoff u u.isLt.le) <|
      Triple.read_bind (hs.edges_allocated.lt_frontier (by omega)) <|
      Triple.read_bind (hs.edges_allocated.lt_frontier hlt) <| Triple.pure ⟨?_, rfl⟩
    rw [AdjacencyList.step_edge _ _ hv, hs.holds.target u i hv, hs.holds.weight u i hv]
    simp

/-- The run of a query, by `ops_triple`. -/
theorem ops_run (hL : L.Valid n) {s : Memory.State} (hs : Inv L adj s) (o : AdjacencyList.Op n)
    (hv : AdjacencyList.valid adj o) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ops L o)) ∧
      (Memory.spec w).totalCost charge s ((Memory.spec w).clientHistory s (ops L o)) ≤ 3 ∧
      AdjacencyList.step adj o = (adj, (Memory.spec w).clientResult s (ops L o)) ∧
        (Memory.spec w).clientState s (ops L o) = s :=
  triple_iff.mp (ops_triple hL hs o hv)

variable (adj) in
/-- The adjacency arrays implement the interface for the graph `adj` they hold. -/
def refinement (hL : L.Valid n) : Refinement (AdjacencyList.spec n) (Memory.spec w) :=
  Refinement.ofFn (methods L w) (Inv L adj) (fun _ => adj)
    (fun o hs hv => (ops_run hL hs o hv).1)
    (fun o hs hv => by
      obtain ⟨-, -, hstep, hs'⟩ := ops_run hL hs o hv
      exact ⟨hstep, (congrArg (Inv L adj) hs').mpr hs⟩)

/-- The fields are allocated. -/
theorem Inv.lt_frontier {s : Memory.State} (hs : Inv L adj s) {a : ℕ} (ha : a ∈ L.footprint) :
    a < s.frontier := by
  have h₁ := hs.offsets_allocated
  have h₂ := hs.edges_allocated
  simp only [Layout.footprint, Finset.mem_union, Block.mem_footprint, Block.Owns] at ha
  unfold Block.Allocated at h₁ h₂
  omega

/-- The invariant reads only the two fields and survives a growing frontier. -/
theorem Inv.congr (hL : L.Valid n) {s s' : Memory.State} (hs : Inv L adj s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier) :
    Inv L adj s' := by
  have hoff : ∀ j ≤ n, s'.mem (L.offsets.base + j) = s.mem (L.offsets.base + j) := fun j hj =>
    h _ (Finset.mem_union_left _ (Block.mem_footprint.mpr
      (Block.owns_add (by rw [hL.offsets_length]; omega))))
  have hedge : ∀ j < L.edges.length, s'.mem (L.edges.base + j) = s.mem (L.edges.base + j) :=
    fun j hj => h _ (Finset.mem_union_right _ (Block.mem_footprint.mpr (Block.owns_add hj)))
  have H := hs.holds
  refine ⟨hs.offsets_allocated.mono hf, hs.edges_allocated.mono hf, ⟨fun u => ?_, fun u => ?_,
    fun u i hi => ?_, fun u i hi => ?_⟩⟩
  · rw [hoff _ u.isLt, hoff _ u.isLt.le]
    exact H.offset_succ u
  · rw [hoff _ u.isLt]
    exact H.end_le u
  · have := H.edge_lt u hi
    rw [hoff _ u.isLt.le, hedge _ (by omega)]
    exact H.target u i hi
  · have := H.edge_lt u hi
    rw [hoff _ u.isLt.le, hedge _ this]
    exact H.weight u i hi

variable (adj) in
/-- The adjacency arrays, framed by their two fields. -/
def framed (hL : L.Valid n) : Memory.Framed (AdjacencyList.spec n) w :=
  .ofStatic (refinement adj hL) L.footprint (fun hs ha => Inv.lt_frontier hs ha)
    (fun hs h hf => ⟨hs.congr hL h hf, rfl⟩)
    (fun o hs hv b _ _ => by
      obtain ⟨-, -, -, hs'⟩ := ops_run (w := w) hL hs o hv
      change ((Memory.spec w).clientState _ (ops L o)).mem b = _
      rw [hs'])

/-- The footprint of the arrays is their two fields. -/
@[simp] theorem framed_footprint (hL : L.Valid n) (s : Memory.State) :
    (framed (w := w) adj hL).footprint s = L.footprint := rfl

/-- **Every query costs at most three memory units.** -/
theorem amortized (hL : L.Valid n) :
    (framed (w := w) adj hL).Amortized charge (fun _ _ => 3) fun _ => 0 :=
  Refinement.Amortized.ofFn fun {_} o hs hv => by
    obtain ⟨-, hc, -⟩ := ops_run (w := w) hL hs o hv
    exact Nat.add_le_add_right hc 0

end Cslib.DataStructure.AdjacencyList.Memory
