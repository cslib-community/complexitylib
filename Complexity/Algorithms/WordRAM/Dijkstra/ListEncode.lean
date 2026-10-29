/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.HeapStatement
public import Complexity.Algorithms.WordRAM.Dijkstra.Invariant
import Mathlib.Algebra.BigOperators.Fin

/-!
# Dijkstra's algorithm: the adjacency-list input words and edge-scan relaxation

This file reads the input words `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.encode` of an
adjacency-list instance back from the initial memory of a word RAM: `n`, the source, the offsets
of the adjacency lists and the targets and weights of the edges each sit at the address that
`Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode` (and its binary-heap instantiation
`Cslib.Algorithms.WordRAM.Dijkstra.heapDijkstra`) reads them from, and memory past the input is
`0`.

It also defines the effect of scanning the edges out of a vertex on one distance word
(`Cslib.Algorithms.WordRAM.Dijkstra.edgesWord`), and shows that it is the relaxation of the
weight-matrix instance (`Cslib.Algorithms.WordRAM.Dijkstra.decode_edgesWord`): the scan of all
parallel edges to a vertex has the effect of the lightest one.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.dbase`: the first address past the input.
* `Cslib.Algorithms.WordRAM.Dijkstra.edgeWord`, `Cslib.Algorithms.WordRAM.Dijkstra.edgesWord`:
  the relaxation of a distance word through one edge, and through a list of edges.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.encode_length`: the input has `n + 2 m + 3`
  words.
* `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_offset`,
  `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_target`,
  `Cslib.Algorithms.WordRAM.Dijkstra.ListInstance.init_weight`: the input words in the initial
  memory.
* `Cslib.Algorithms.WordRAM.Dijkstra.decode_edgesWord`: the scan of the edges out of a vertex
  relaxes the tentative distances.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM

namespace ListInstance

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

/-- Edge `offset u + i` of the edge list is edge `i` out of `u`. -/
private theorem edges_getElem (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    G.edges[G.offset u + i]? = some (G.adj u)[i] := by
  have hu : (u : ℕ) < (List.finRange G.n).length := by simp
  have hs : List.finRange G.n = (List.finRange G.n).take u ++
      (u :: (List.finRange G.n).drop (u + 1)) := by
    conv_lhs => rw [← List.take_append_drop u (List.finRange G.n)]
    rw [List.drop_eq_getElem_cons hu]
    simp
  rw [edges, hs, List.flatMap_append, List.flatMap_cons, offset_eq_length,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

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
      simpa [List.getD_eq_getElem?_getD] using h

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
    List.getD_cons_succ, List.getD_cons_succ, edgeWords_eq, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp), List.getD_eq_getElem?_getD]
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
    List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [Nat.lt_succ_of_le hu]

/-- The target of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 4`. -/
theorem init_target (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 4) = ((G.adj u)[i].1 : ℕ) := by
  rw [show 2 * (G.offset u + i) + G.n + 4 = 2 * (G.offset u + i) + G.n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge]
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp (G.edges_getElem u hi)
  rw [(G.getD_flatMap_pairs _ _ hl).1, he]

/-- The weight of edge `i` out of `u` is initially at address `2 (offset u + i) + n + 5`. -/
theorem init_weight (u : Fin G.n) {i : ℕ} (hi : i < (G.adj u).length) :
    (Data.init G.encode : Data r).mem (2 * (G.offset u + i) + G.n + 5) = (G.adj u)[i].2 := by
  rw [show 2 * (G.offset u + i) + G.n + 5 = (2 * (G.offset u + i) + 1) + G.n + 3 + 1 by ring,
    Data.init_mem_succ, encode_getD_edge]
  obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp (G.edges_getElem u hi)
  rw [(G.getD_flatMap_pairs _ _ hl).2, he]

/-- Memory past the input is initially `0`. -/
theorem init_past {a : ℕ} (ha : G.dbase ≤ a) : (Data.init G.encode : Data r).mem a = 0 := by
  have hz : a ≠ 0 := by unfold dbase at ha; omega
  have hl : G.encode.length ≤ a - 1 := by rw [encode_length]; unfold dbase at ha; omega
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hl)]

/-- Every edge weight is at most the largest weight. -/
theorem le_maxWeight {u : Fin G.n} {e : Fin G.n × ℕ} (he : e ∈ G.adj u) : e.2 ≤ G.maxWeight := by
  have h1 : e.2 ≤ ((G.adj u).map Prod.snd).foldr max 0 :=
    List.le_max_of_le (List.mem_map_of_mem he) le_rfl
  exact h1.trans (Finset.le_sup (f := fun u => ((G.adj u).map Prod.snd).foldr max 0)
    (Finset.mem_univ u))

/-- The largest weight of the weight-matrix instance is at most the largest edge weight. -/
theorem toInstance_maxWeight_le : G.toInstance.maxWeight ≤ G.maxWeight := by
  refine Finset.sup_le fun uv _ => ?_
  change (G.lightest uv.1 uv.2).getD 0 ≤ G.maxWeight
  cases h : G.lightest uv.1 uv.2 with
  | none => simp
  | some c => exact G.le_maxWeight ((G.lightest_eq_some_iff.mp h).1)

end ListInstance

/-- The relaxation of the distance word `d` through an edge of weight `c` from a vertex with
distance word `b ≠ 0`. -/
def edgeWord (b c d : ℕ) : ℕ := if d = 0 then b + c else if b + c < d then b + c else d

/-- The relaxation of the distance word `d` of `v` through the edges to `v` in the list `es`, in
order, from a vertex with distance word `b`. -/
def edgesWord {N : ℕ} (b : ℕ) (es : List (Fin N × ℕ)) (v : Fin N) (d : ℕ) : ℕ :=
  es.foldl (fun d e => if e.1 = v then edgeWord b e.2 d else d) d

/-- The relaxation through one edge decodes to the relaxation of the tentative distance. -/
private theorem decode_edgeWord {b : ℕ} (hb : b ≠ 0) (c d : ℕ) :
    decodeDist (edgeWord b c d) = min (decodeDist d) (decodeDist b + c) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb
  have he : b.succ + c - 1 = b + c := by omega
  cases d with
  | zero => simp [edgeWord, decodeDist, he]
  | succ d =>
    simp only [edgeWord, Nat.succ_ne_zero, ite_false]
    by_cases h : b.succ + c < d.succ
    · have hc : (b : ℕ∞) + c ≤ d := by exact_mod_cast (by omega : b + c ≤ d)
      simp [h, decodeDist, he, hc]
    · have hc : (d : ℕ∞) ≤ (b : ℕ∞) + c := by exact_mod_cast (by omega : d ≤ b + c)
      simp [h, decodeDist, hc]

/-- The relaxation through the edges to `v` in `es` decodes to the relaxation through the
lightest of them. -/
private theorem decode_edgesWord_list {N : ℕ} {b : ℕ} (hb : b ≠ 0) (es : List (Fin N × ℕ))
    (v : Fin N) (d : ℕ) :
    decodeDist (edgesWord b es v d) =
      match (es.filterMap fun e => if e.1 = v then some e.2 else none).min? with
      | none => decodeDist d
      | some c => min (decodeDist d) (decodeDist b + c) := by
  induction es generalizing d with
  | nil => rfl
  | cons e es ih =>
    rw [edgesWord, List.foldl_cons, ← edgesWord, ih]
    by_cases he : e.1 = v
    · simp only [List.filterMap_cons, he, ↓reduceIte, List.min?_cons]
      cases es.filterMap (fun e => if e.1 = v then some e.2 else none) |>.min? with
      | none => simp [decode_edgeWord hb]
      | some c =>
        simp only [decode_edgeWord hb, Option.elim_some]
        rw [min_assoc, min_add_add_left, Nat.mono_cast.map_min]
    · simp only [List.filterMap_cons, he, ↓reduceIte]

/-- **The scan of the edges out of `u` relaxes the tentative distances.** If `b ≠ 0` is the
distance word of `u` and `d` that of `v`, the relaxation of `d` through the edges from `u` to `v`
decodes to the relaxation of the tentative distance of `v` in the weight-matrix instance. -/
theorem decode_edgesWord (G : ListInstance) {D : Fin G.n → ℕ∞} {u v : Fin G.n} {b d : ℕ}
    (hb : b ≠ 0) (hu : D u = decodeDist b) (hv : D v = decodeDist d) :
    decodeDist (edgesWord b (G.adj u) v d) = G.toInstance.relax D u v := by
  rw [decode_edgesWord_list hb, ← hu, ← hv]
  rfl

end Cslib.Algorithms.WordRAM.Dijkstra

end
