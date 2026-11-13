/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Dijkstra.HeapStatement
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# Dijkstra's algorithm: the adjacency-list input words

This file reads the input words `Cslib.Algorithms.Dijkstra.ListInstance.encode` of an
adjacency-list instance back from the initial memory of a word RAM: `n`, the source, the offsets
of the adjacency lists and the targets and weights of the edges each sit at the address used by
the original linked memory client and the retained word-RAM priority-queue interface. Memory past
the input is `0`.

## Main definitions

* `Cslib.Algorithms.Dijkstra.ListInstance.dbase`: the first address past the input.

## Main results

* `Cslib.Algorithms.Dijkstra.ListInstance.encode_length`: the input has `n + 2 m + 3` words.
* `Cslib.Algorithms.Dijkstra.ListInstance.init_offset`,
  `Cslib.Algorithms.Dijkstra.ListInstance.init_target`,
  `Cslib.Algorithms.Dijkstra.ListInstance.init_weight`: the input words in the initial memory.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Dijkstra.ListInstance

open Cslib.WordRAM

variable (G : ListInstance) {r : ℕ}

/-- The first address past the input words: the base of the distance words. -/
def dbase : ℕ := G.n + 2 * G.m + 4

/-- The edges of all lists, in order. -/
private def edges : List (Fin G.n × ℕ) := (List.finRange G.n).flatMap G.adj

/-- The offset of `u` is the number of edges out of the vertices below `u`. -/
private theorem offset_eq_length (u : ℕ) :
    G.offset u = (((List.finRange G.n).take u).flatMap G.adj).length := by
  simp [offset, List.length_flatMap]

/-- The edge list has `m` edges. -/
private theorem length_edges : G.edges.length = G.m := by
  simp [edges, m, List.length_flatMap, ← Fin.sum_univ_def]

private theorem edges_eq_append (u : Fin G.n) :
    G.edges = ((List.finRange G.n).take u).flatMap G.adj ++
      (G.adj u ++ ((List.finRange G.n).drop (u + 1)).flatMap G.adj) := by
  have hu : (u : ℕ) < (List.finRange G.n).length := by simp
  conv_lhs => rw [edges, ← List.take_append_drop u (List.finRange G.n),
    List.drop_eq_getElem_cons hu]
  simp [List.flatMap_append]

private theorem offset_add_lt_length_edges (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    G.offset u + i < G.edges.length := by
  rw [G.edges_eq_append u, List.length_append, List.length_append, ← offset_eq_length]
  omega

/-- Edge `offset u + i` of the edge list is edge `i` out of `u`. -/
private theorem edges_getElem (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    G.edges[G.offset u + i]'(G.offset_add_lt_length_edges u hi) = (G.adj u)[i] := by
  simp only [G.edges_eq_append u, G.offset_eq_length u,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_append_left hi]

/-- Word `2 j + k` of the edge words, for `k < 2`, is word `k` of edge `j`. -/
private theorem getD_flatMap_pairs (l : List (Fin G.n × ℕ)) (j : ℕ) (hj : j < l.length) :
    (l.flatMap fun e => [(e.1 : ℕ), e.2]).getD (2 * j) 0 = l[j].1 ∧
      (l.flatMap fun e => [(e.1 : ℕ), e.2]).getD (2 * j + 1) 0 = l[j].2 := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simp
    | succ j =>
      have h := ih j (by simpa using hj)
      rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 1 + 2 by ring]
      simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.getD_cons_succ,
        List.getElem_cons_succ] using h

/-- The edge words are the edge list, two words per edge. -/
private theorem edgeWords_eq : ((List.finRange G.n).flatMap fun u =>
    (G.adj u).flatMap fun e => [(e.1 : ℕ), e.2]) =
    G.edges.flatMap fun e => [(e.1 : ℕ), e.2] := by
  rw [edges, List.flatMap_assoc]

/-- Word `k + n + 3` of the input is word `k` of the edge words. -/
private theorem encode_getD_edge (k : ℕ) :
    G.encode.getD (k + G.n + 3) 0 =
      (G.edges.flatMap fun e => [(e.1 : ℕ), e.2]).getD k 0 := by
  rw [encode, show k + G.n + 3 = (k + G.n + 1) + 1 + 1 by ring,
    List.getD_cons_succ, List.getD_cons_succ, edgeWords_eq,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The input has `n + 2 m + 3` words. -/
theorem encode_length : G.encode.length = G.n + 2 * G.m + 3 := by
  have h : ∀ l : List (Fin G.n × ℕ),
      (l.flatMap fun e => [(e.1 : ℕ), e.2]).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.length_cons, ih]
      ring
  simp only [encode, edgeWords_eq, List.length_cons, List.length_append, List.length_map,
    List.length_range, h, length_edges, Nat.add_right_cancel_iff]
  ring

/-- The offset of `u + 1` is the offset of `u` plus the length of the list of `u`. -/
theorem offset_succ {u : ℕ} (hu : u < G.n) :
    G.offset (u + 1) = G.offset u + (G.adj ⟨u, hu⟩).length := by
  have hl : u < (List.finRange G.n).length := by simpa using hu
  simp [offset, List.take_add_one, List.getElem?_eq_getElem hl]

/-- The offset of `n` is the number of edges. -/
theorem offset_n : G.offset G.n = G.m := by
  rw [offset, List.take_of_length_le (by simp), ← Fin.sum_univ_def]
  rfl

/-- The offsets grow. -/
theorem offset_mono {u v : ℕ} (h : u ≤ v) : G.offset u ≤ G.offset v :=
  ((List.take_sublist_take_left h).map _).sum_le_sum fun _ _ => Nat.zero_le _

/-- Address `1` initially holds `n`. -/
theorem init_n : (Data.init G.encode : Data r).mem 1 = G.n := rfl

/-- Address `2` initially holds the source. -/
theorem init_source : (Data.init G.encode : Data r).mem 2 = G.source := rfl

/-- Address `u + 3` initially holds the offset of `u`, for `u ≤ n`. -/
theorem init_offset {u : ℕ} (hu : u ≤ G.n) :
    (Data.init G.encode : Data r).mem (u + 3) = G.offset u := by
  rw [Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by simp; omega), List.getD_map_range _ _ (Nat.lt_succ_of_le hu)]

/-- The target of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 4`. -/
theorem init_target (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 4) = ((G.adj u)[i].1 : ℕ) := by
  rw [show 2 * (G.offset u + i) + G.n + 4 = 2 * (G.offset u + i) + G.n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge,
    (G.getD_flatMap_pairs _ _ (G.offset_add_lt_length_edges u hi)).1, G.edges_getElem u hi]

/-- The weight of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 5`. -/
theorem init_weight (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 5) = (G.adj u)[i].2 := by
  rw [show 2 * (G.offset u + i) + G.n + 5 = (2 * (G.offset u + i) + 1) + G.n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge,
    (G.getD_flatMap_pairs _ _ (G.offset_add_lt_length_edges u hi)).2, G.edges_getElem u hi]

/-- Memory past the input is initially `0`. -/
theorem init_past {a : ℕ} (ha : G.dbase ≤ a) : (Data.init G.encode : Data r).mem a = 0 := by
  have hz : a ≠ 0 := by unfold dbase at ha; omega
  have hl : G.encode.length ≤ a - 1 := by rw [encode_length]; unfold dbase at ha; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
  rw [Data.init_mem_succ, List.getD_eq_default _ _ (by simpa using hl)]

/-- The original adjacency-list input fits whenever the advertised Dijkstra word envelope fits. -/
theorem inputFits_encode (G : ListInstance) {w : ℕ}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    InputFits w G.encode := by
  refine ⟨?_, ?_⟩
  · rw [G.encode_length]
    exact hw_in.of_le (by nlinarith)
  · intro x hx
    simp only [ListInstance.encode, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap, List.mem_finRange, true_and] at hx
    rcases hx with rfl | rfl | ⟨⟨i, hi, rfl⟩ | ⟨u, ⟨v, c⟩, he, hx⟩⟩
    · exact hw_in.of_le (by nlinarith)
    · have := G.source.isLt
      exact hw_in.of_le (by nlinarith)
    · have hle : G.offset i ≤ G.m := G.offset_n ▸ G.offset_mono (by omega)
      exact hw_in.of_le (by nlinarith)
    · simp only [List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have := v.isLt
        exact hw_in.of_le (by nlinarith)
      · have hc := G.le_maxWeight he
        exact hw_in.of_le (by nlinarith)

end Cslib.Algorithms.Dijkstra.ListInstance

end
