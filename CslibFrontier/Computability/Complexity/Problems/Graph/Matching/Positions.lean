/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Matching
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.GetD

/-!
# Edge positions in framed graphs

`Graph.edgeList` enumerates the edges of the existing `Graph.induced`, discarding loops,
undeclared endpoints and repeated edges in either orientation. `positions` and `ofPositions`
relate edge positions to Mathlib subgraphs. The latter is spanning, so incomplete matchings
must restrict its vertex set to their covered vertices.

These declarations and proofs were extracted from `Graph.PerfectMatching` for constructive
matching algorithms, preserving the original public names and normalization conventions.
`cover_positions` now also applies at each covered vertex of an incomplete matching.
`exists_getD_edgeList_of_adj` supplies a valid edge position directly from adjacency,
so coverage, edge-cardinality and legacy counting proofs share the same orientation witness.
-/

public section

namespace Cslib.Complexity.Graph

variable {G : Graph}

/-- The edges of `G.induced`, each listed once: the edges of `G` between distinct declared
vertices, with repetitions in either orientation erased. -/
@[expose] def edgeList (G : Graph) : List (ℕ × ℕ) :=
  (G.2.filter fun e => decide (e.1 ≠ e.2) && decide (e.1 ∈ G.1) && decide (e.2 ∈ G.1)).eraseDupsBy
    fun a b => decide (a = b) || decide (a = (b.2, b.1))

/-- Whether the vertex `v` is an end of the edge `e`. -/
@[expose] def incident (e : ℕ × ℕ) (v : ℕ) : Bool := decide (e.1 = v) || decide (e.2 = v)

/-! ### The edge list -/

/-- An entry of the edge list joins two distinct declared vertices by an edge of `G`. -/
theorem of_mem_edgeList {e : ℕ × ℕ} (he : e ∈ G.edgeList) :
    e ∈ G.2 ∧ e.1 ≠ e.2 ∧ e.1 ∈ G.1 ∧ e.2 ∈ G.1 := by
  have := List.mem_filter.mp ((List.eraseDupsBy_sublist _).subset he)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1, this.2.1.1, this.2.1.2, this.2.2⟩

/-- Each edge of `G.induced` is in the edge list in one of its orientations. -/
theorem exists_mem_edgeList {u v : {v // v ∈ G.1}} (h : G.induced.Adj u v) :
    (u.1, v.1) ∈ G.edgeList ∨ (v.1, u.1) ∈ G.edgeList := by
  rw [induced_adj, toSimpleGraph_adj] at h
  obtain ⟨hne, huv⟩ := h
  have key : ∀ e ∈ G.2, e.1 ≠ e.2 → e.1 ∈ G.1 → e.2 ∈ G.1 → e ∈ G.edgeList ∨ e.swap ∈ G.edgeList :=
    fun e he h1 h2 h3 => by
      have hmem : e ∈ G.2.filter fun e =>
          decide (e.1 ≠ e.2) && decide (e.1 ∈ G.1) && decide (e.2 ∈ G.1) :=
        List.mem_filter.mpr ⟨he, by simp [h1, h2, h3]⟩
      obtain ⟨b, hb, rfl | hab⟩ := List.exists_mem_eraseDupsBy (r := fun a b =>
        decide (a = b) || decide (a = (b.2, b.1))) hmem
      · exact Or.inl hb
      · have hab : e = b ∨ e = (b.2, b.1) := by simpa using hab
        rcases hab with rfl | rfl
        · exact Or.inl hb
        · exact Or.inr hb
  rcases huv with huv | hvu
  · exact key _ huv hne u.2 v.2
  · rcases key _ hvu (fun h => hne h.symm) v.2 u.2 with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- No entry of the edge list repeats an earlier entry, in either orientation. -/
theorem pairwise_edgeList (G : Graph) : G.edgeList.Pairwise fun a b => b ≠ a ∧ b ≠ a.swap := by
  refine (List.pairwise_eraseDupsBy (r := fun a b => decide (a = b) || decide (a = (b.2, b.1)))
    _).imp fun h => ?_
  simpa [Prod.swap] using h

/-- Distinct positions of the edge list hold distinct edges, in either orientation. -/
theorem eq_of_getD_edgeList {i j : ℕ} (hi : i < G.edgeList.length) (hj : j < G.edgeList.length)
    (h : G.edgeList.getD i (0, 0) = G.edgeList.getD j (0, 0) ∨
      G.edgeList.getD i (0, 0) = (G.edgeList.getD j (0, 0)).swap) : i = j := by
  have hp := List.pairwise_iff_getElem.mp (pairwise_edgeList G)
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h
  by_contra hij
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · obtain ⟨h1, h2⟩ := hp i j hi hj hlt
    rcases h with h | h
    · exact h1 h.symm
    · exact h2 (by rw [h, Prod.swap_swap])
  · obtain ⟨h1, h2⟩ := hp j i hj hi hlt
    rcases h with h | h
    · exact h1 h
    · exact h2 h

/-- An entry of the edge list, read at a position below its length. -/
theorem getD_edgeList_mem {i : ℕ} (hi : i < G.edgeList.length) :
    G.edgeList.getD i (0, 0) ∈ G.edgeList := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- The position of an entry of the edge list. -/
theorem exists_getD_edgeList {e : ℕ × ℕ} (he : e ∈ G.edgeList) :
    ∃ i < G.edgeList.length, G.edgeList.getD i (0, 0) = e := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  exact ⟨i, hi, List.getD_eq_getElem _ _ hi⟩

/-- Every actual adjacency has a retained edge position, in one of its two orientations. -/
theorem exists_getD_edgeList_of_adj {u v : {v // v ∈ G.1}} (h : G.induced.Adj u v) :
    ∃ i < G.edgeList.length, G.edgeList.getD i (0, 0) = (u.val, v.val) ∨
      G.edgeList.getD i (0, 0) = (v.val, u.val) := by
  rcases exists_mem_edgeList h with he | he
  · obtain ⟨i, hi, hie⟩ := exists_getD_edgeList he
    exact ⟨i, hi, Or.inl hie⟩
  · obtain ⟨i, hi, hie⟩ := exists_getD_edgeList he
    exact ⟨i, hi, Or.inr hie⟩

/-- The adjacency of a subgraph of `G.induced`, read on natural numbers. -/
@[expose] def AdjNat (M : G.induced.Subgraph) (u w : ℕ) : Prop :=
  ∃ (hu : u ∈ G.1) (hw : w ∈ G.1), M.Adj ⟨u, hu⟩ ⟨w, hw⟩

/-- The positions of the edges of a subgraph. -/
noncomputable def positions (M : G.induced.Subgraph) : Finset ℕ := by
  classical
  exact (Finset.range G.edgeList.length).filter fun i =>
    AdjNat M (G.edgeList.getD i (0, 0)).1 (G.edgeList.getD i (0, 0)).2

/-- Position membership is original subgraph adjacency at a valid normalized edge. -/
theorem mem_positions {M : G.induced.Subgraph} {i : ℕ} :
    i ∈ positions M ↔ i < G.edgeList.length ∧
      AdjNat M (G.edgeList.getD i (0, 0)).1 (G.edgeList.getD i (0, 0)).2 := by
  classical
  simp only [positions, Finset.mem_filter, Finset.mem_range]

/-- The subgraph spanned by the edges at a set of positions. -/
@[expose] def ofPositions (G : Graph) (S : Finset ℕ) : G.induced.Subgraph where
  verts := Set.univ
  Adj u w := G.induced.Adj u w ∧
    ∃ i ∈ S, G.edgeList.getD i (0, 0) = (u.1, w.1) ∨ G.edgeList.getD i (0, 0) = (w.1, u.1)
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm := ⟨fun _ _ ⟨h, i, hi, he⟩ => ⟨h.symm, i, hi, he.symm⟩⟩

/-- The other end of an edge at a vertex `v`. -/
theorem exists_other_end {e : ℕ × ℕ} {v : ℕ} (hv : incident e v = true) :
    ∃ w, e = (v, w) ∨ e = (w, v) := by
  simp only [incident, Bool.or_eq_true, decide_eq_true_eq] at hv
  rcases hv with rfl | rfl
  · exact ⟨e.2, Or.inl rfl⟩
  · exact ⟨e.1, Or.inr rfl⟩

/-- Exactly one selected incident edge at every declared vertex gives a perfect matching. -/
theorem isPerfectMatching_ofPositions {S : Finset ℕ} (hS : ∀ i ∈ S, i < G.edgeList.length)
    (hcov : ∀ v ∈ G.1, ∃! i, i < G.edgeList.length ∧
      incident (G.edgeList.getD i (0, 0)) v = true ∧ i ∈ S) :
    (ofPositions G S).IsPerfectMatching := by
  refine SimpleGraph.Subgraph.isPerfectMatching_iff.mpr fun u => ?_
  obtain ⟨i, ⟨hi, hinc, hiS⟩, huniq⟩ := hcov u.1 u.2
  have hmem := getD_edgeList_mem hi
  obtain ⟨hG, hne, h1, h2⟩ := of_mem_edgeList hmem
  obtain ⟨w, hw⟩ := exists_other_end hinc
  have hw' : w ∈ G.1 := by rcases hw with hw | hw <;> rw [hw] at h1 h2 <;> assumption
  have hadj : G.induced.Adj u ⟨w, hw'⟩ := by
    rw [induced_adj, toSimpleGraph_adj]
    rcases hw with hw | hw <;> rw [hw] at hG hne
    · exact ⟨hne, Or.inl hG⟩
    · exact ⟨Ne.symm hne, Or.inr hG⟩
  refine ⟨⟨w, hw'⟩, ⟨hadj, i, hiS, hw⟩, fun w' ⟨_, i', hi'S, hw'e⟩ => ?_⟩
  have hi' := hS i' hi'S
  have hinc' : incident (G.edgeList.getD i' (0, 0)) u = true := by
    rcases hw'e with h | h <;> rw [h] <;> simp [incident]
  have := huniq i' ⟨hi', hinc', hi'S⟩
  subst this
  refine Subtype.ext (?_ : (w' : ℕ) = w)
  rcases hw with hw | hw <;> rcases hw'e with h | h <;> rw [hw] at h hne <;>
    simp only [Prod.mk.injEq] at h hne <;> omega

/-- A covered vertex of any matching has exactly one incident original edge position. -/
theorem cover_positions {M : G.induced.Subgraph} (hM : M.IsMatching) :
    ∀ (v : ℕ) (hv : v ∈ G.1), (⟨v, hv⟩ : {v // v ∈ G.1}) ∈ M.verts → ∃! i, i < G.edgeList.length ∧
      incident (G.edgeList.getD i (0, 0)) v = true ∧ i ∈ positions M := by
  intro v hv hvM
  obtain ⟨w, hvw, hwuniq⟩ := hM hvM
  -- the edge `vw` sits at a position of the edge list
  obtain ⟨i, hi, he⟩ := exists_getD_edgeList_of_adj (M.adj_sub hvw)
  refine ⟨i, ⟨hi, by rcases he with h | h <;> rw [h] <;> simp [incident],
    mem_positions.mpr ⟨hi, ?_⟩⟩,
    fun j ⟨hj, hinc, hjS⟩ => ?_⟩
  · rcases he with h | h <;> rw [h]
    · exact ⟨hv, w.2, hvw⟩
    · exact ⟨w.2, hv, hvw.symm⟩
  · obtain ⟨-, hu, hw, hadj⟩ := mem_positions.mp hjS
    have hmem := getD_edgeList_mem hj
    obtain ⟨w', hw'⟩ := exists_other_end hinc
    -- the edge at `j` joins `v` to the partner `w` of `v`
    have hpartner : w' = w.1 := by
      rcases hw' with h | h <;> simp only [h] at hu hw hadj
      · exact congrArg Subtype.val (hwuniq ⟨w', hw⟩ hadj)
      · exact congrArg Subtype.val (hwuniq ⟨w', hu⟩ hadj.symm)
    subst hpartner
    refine eq_of_getD_edgeList hj hi ?_
    rcases hw' with h | h <;> rcases he with h' | h' <;> rw [h, h'] <;> simp

end Cslib.Complexity.Graph
