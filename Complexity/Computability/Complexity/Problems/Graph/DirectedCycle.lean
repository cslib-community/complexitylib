/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Complexity.Foundations.Relation.Acyclic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith

/-!
# Directed cycles

A graph, given by a list of vertices and a list of edges, is read as a directed graph through its
arcs `(u, v) ∈ G.2` between declared vertices (`Cslib.Complexity.Graph.DirAdj`), as for the
directed Hamiltonian problems. A *directed cycle* (`Cslib.Complexity.Graph.IsDirCycle`) is a
nonempty list of distinct declared vertices whose consecutive vertices, read cyclically
(`Cycle.Chain`), are joined by arcs; a vertex with a self-loop is a cycle of length one, and two
vertices with arcs both ways form a cycle of length two. A graph is *acyclic*
(`Cslib.Complexity.Graph.IsDirAcyclic`) when it has no directed cycle.

The feedback set problems remove vertices (`Cslib.Complexity.Graph.deleteVerts`) or arcs
(`Cslib.Complexity.Graph.deleteArcs`) so as to leave an acyclic graph. Removing vertices leaves an
acyclic graph exactly when every directed cycle passes through a removed vertex
(`Cslib.Complexity.Graph.isDirAcyclic_deleteVerts_iff`).

Through `Relation.acyclic_iff_forall_nodup_not_cycle_chain`, a graph is acyclic exactly when its
adjacency relation is `Relation.Acyclic`, and through `Relation.acyclic_iff_exists_rank`,
exactly when its declared vertices can be numbered below their number so that every arc increases
the number (`Cslib.Complexity.Graph.isDirAcyclic_iff_exists_rank`): a topological numbering. Such
numberings, listed along the vertex list, are the `NP` certificates of the feedback set problems;
their encodings are quadratic in the encoding of the graph
(`Cslib.Complexity.Graph.length_encList_map_le`).

## Main definitions

* `Cslib.Complexity.Graph.DirAdj`, `Cslib.Complexity.Graph.IsDirCycle`,
  `Cslib.Complexity.Graph.IsDirAcyclic`.
* `Cslib.Complexity.Graph.deleteVerts`, `Cslib.Complexity.Graph.deleteArcs`.

## Main results

* `Cslib.Complexity.Graph.isDirCycle_iff`: directed cycles as closed chains of the arc relation.
* `Cslib.Complexity.Graph.isDirAcyclic_iff_acyclic`: acyclicity of the adjacency relation.
* `Cslib.Complexity.Graph.isDirAcyclic_iff_exists_rank`,
  `Cslib.Complexity.Graph.exists_rank_of_isDirAcyclic`,
  `Cslib.Complexity.Graph.isDirAcyclic_of_rank`: acyclicity through topological numberings.
* `Cslib.Complexity.Graph.isDirAcyclic_deleteVerts_iff`: removed vertices meet every cycle.
* `Cslib.Complexity.Graph.length_encList_map_le`: the size of a listed numbering.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

namespace Graph

/-- The arc relation of a directed graph: an arc `(u, v) ∈ G.2` between declared vertices. -/
def DirAdj (G : Graph) (u v : ℕ) : Prop := u ∈ G.1 ∧ v ∈ G.1 ∧ (u, v) ∈ G.2

/-- `c` is a directed cycle of `G`: a nonempty list of distinct declared vertices whose
consecutive vertices, read cyclically, are joined by arcs. A vertex with a self-loop is a cycle of
length one. -/
def IsDirCycle (G : Graph) (c : List ℕ) : Prop :=
  c ≠ [] ∧ c.Nodup ∧ (∀ v ∈ c, v ∈ G.1) ∧ (c : Cycle ℕ).Chain fun u v => (u, v) ∈ G.2

/-- `G` is acyclic: it has no directed cycle. -/
def IsDirAcyclic (G : Graph) : Prop := ∀ c, ¬G.IsDirCycle c

/-- Remove the vertices of `R`: the remaining vertices are those not in `R`, and the arcs are
kept, so that arcs at removed vertices join no declared vertices. -/
def deleteVerts (G : Graph) (R : Finset ℕ) : Graph := (G.1.filter fun v => v ∉ R, G.2)

/-- Remove the arcs of `S`, keeping the vertices. -/
def deleteArcs (G : Graph) (S : Finset (ℕ × ℕ)) : Graph := (G.1, G.2.filter fun e => e ∉ S)

@[simp]
theorem mem_deleteVerts_fst {G : Graph} {R : Finset ℕ} {v : ℕ} :
    v ∈ (G.deleteVerts R).1 ↔ v ∈ G.1 ∧ v ∉ R := by
  simp [deleteVerts]

@[simp]
theorem deleteVerts_snd (G : Graph) (R : Finset ℕ) : (G.deleteVerts R).2 = G.2 := rfl

@[simp]
theorem deleteArcs_fst (G : Graph) (S : Finset (ℕ × ℕ)) : (G.deleteArcs S).1 = G.1 := rfl

@[simp]
theorem mem_deleteArcs_snd {G : Graph} {S : Finset (ℕ × ℕ)} {e : ℕ × ℕ} :
    e ∈ (G.deleteArcs S).2 ↔ e ∈ G.2 ∧ e ∉ S := by
  simp [deleteArcs]

theorem dirAdj_deleteVerts {G : Graph} {R : Finset ℕ} {u v : ℕ} :
    (G.deleteVerts R).DirAdj u v ↔ G.DirAdj u v ∧ u ∉ R ∧ v ∉ R := by
  simp only [DirAdj, mem_deleteVerts_fst, deleteVerts_snd]
  tauto

theorem dirAdj_deleteArcs {G : Graph} {S : Finset (ℕ × ℕ)} {u v : ℕ} :
    (G.deleteArcs S).DirAdj u v ↔ G.DirAdj u v ∧ (u, v) ∉ S := by
  simp only [DirAdj, deleteArcs_fst, mem_deleteArcs_snd]
  tauto

/-- Directed cycles are the nonempty lists without repetitions that are closed chains of the arc
relation between declared vertices. -/
theorem isDirCycle_iff {G : Graph} {c : List ℕ} :
    G.IsDirCycle c ↔ c ≠ [] ∧ c.Nodup ∧ (c : Cycle ℕ).Chain G.DirAdj := by
  constructor
  · rintro ⟨hne, hnd, hV, hch⟩
    obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨hne, hnd, ?_⟩
    rw [Cycle.chain_coe_cons] at hch ⊢
    rw [List.IsChain.iff_mem] at hch
    refine hch.imp fun u v ⟨hu, hv, huv⟩ => ⟨hV u ?_, hV v ?_, huv⟩
    · simp only [List.mem_cons, List.mem_append] at hu ⊢
      tauto
    · simp only [List.mem_cons, List.mem_append] at hv ⊢
      tauto
  · rintro ⟨hne, hnd, hch⟩
    refine ⟨hne, hnd, fun v hv => ?_, hch.imp fun _ _ h => h.2.2⟩
    obtain ⟨w, hvw, -⟩ := Relation.TransGen.head'_iff.1 (Relation.transGen_of_cycle_chain hch hv)
    exact hvw.1

/-- **Acyclicity through walks**: a graph is acyclic exactly when its adjacency relation is
acyclic (`Relation.Acyclic`), that is, when no vertex reaches itself by a nonempty walk along arcs
between declared vertices. -/
theorem isDirAcyclic_iff_acyclic {G : Graph} : G.IsDirAcyclic ↔ Relation.Acyclic G.DirAdj := by
  rw [Relation.acyclic_iff_forall_nodup_not_cycle_chain]
  simp only [IsDirAcyclic, isDirCycle_iff, not_and]

/-- An acyclic graph has a topological numbering: its declared vertices get numbers below the
number of distinct declared vertices, and every arc between declared vertices increases the
number. -/
theorem exists_rank_of_isDirAcyclic {G : Graph} (h : G.IsDirAcyclic) :
    ∃ f : ℕ → ℕ, (∀ v ∈ G.1, f v < G.1.toFinset.card) ∧ ∀ u v, G.DirAdj u v → f u < f v := by
  obtain ⟨f, hlt, hf⟩ := (isDirAcyclic_iff_acyclic.1 h).exists_rank G.1.toFinset
    (fun _ _ h => ⟨List.mem_toFinset.2 h.1, List.mem_toFinset.2 h.2.1⟩)
  exact ⟨f, fun v hv => hlt v (List.mem_toFinset.2 hv), hf⟩

/-- A numbering that every arc between declared vertices increases shows that a graph is
acyclic. -/
theorem isDirAcyclic_of_rank {G : Graph} {f : ℕ → ℕ} (hf : ∀ u v, G.DirAdj u v → f u < f v) :
    G.IsDirAcyclic :=
  isDirAcyclic_iff_acyclic.2 (Relation.acyclic_of_rank hf)

/-- **Acyclicity through topological numberings.** -/
theorem isDirAcyclic_iff_exists_rank {G : Graph} :
    G.IsDirAcyclic ↔
      ∃ f : ℕ → ℕ, (∀ v ∈ G.1, f v < G.1.toFinset.card) ∧ ∀ u v, G.DirAdj u v → f u < f v :=
  ⟨exists_rank_of_isDirAcyclic, fun ⟨_, _, hf⟩ => isDirAcyclic_of_rank hf⟩

/-- **Feedback vertex sets meet every cycle**: removing the vertices of `R` leaves an acyclic
graph exactly when every directed cycle passes through a vertex of `R`. -/
theorem isDirAcyclic_deleteVerts_iff {G : Graph} {R : Finset ℕ} :
    (G.deleteVerts R).IsDirAcyclic ↔ ∀ c, G.IsDirCycle c → ∃ v ∈ c, v ∈ R := by
  constructor
  · intro h c hc
    by_contra hR
    push Not at hR
    obtain ⟨hne, hnd, hV, hch⟩ := hc
    exact h c ⟨hne, hnd, fun v hv => mem_deleteVerts_fst.2 ⟨hV v hv, hR v hv⟩, hch⟩
  · rintro h c ⟨hne, hnd, hV, hch⟩
    obtain ⟨v, hv, hvR⟩ := h c ⟨hne, hnd, fun v hv => (mem_deleteVerts_fst.1 (hV v hv)).1, hch⟩
    exact (mem_deleteVerts_fst.1 (hV v hv)).2 hvR

/-! ### Listed numberings -/

/-- A numbering below `m` listed along the vertex list of an instance whose encoding has length
`n ≥ m` has an encoding of length at most `2 n ^ 2 + n`. -/
theorem length_encList_map_le {G : Graph} {f : ℕ → ℕ} {n : ℕ} (hG : G.1.length ≤ n)
    (hf : ∀ v ∈ G.1, f v ≤ n) : (encList encNat (G.1.map f)).length ≤ 2 * n ^ 2 + n := by
  have hentry : ∀ a ∈ G.1.map f, (encNat a).length ≤ n := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    exact (length_encNat_le_self _).trans (hf v hv)
  have h := length_encList_le encNat _ hentry
  rw [List.length_map] at h
  nlinarith

end Graph

end Cslib.Complexity
