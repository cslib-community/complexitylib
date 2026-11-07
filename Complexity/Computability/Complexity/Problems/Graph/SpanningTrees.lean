/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.Complexity.Problems.Graph
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Foundations.Combinatorics.SimpleGraph.MatrixTree
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Counting spanning trees in polynomial time

The number of spanning trees of the graph `G.induced` of a vertex and edge list `G : Graph` is
computable in polynomial time (`Cslib.Complexity.Graph.computableInPolyTime_spanningTreeCount`).
The program `Cslib.Complexity.Graph.spanningTreeCount` tabulates the reduced Laplacian of
`G.induced` on the distinct declared vertices other than the first one, and returns its
determinant by Bird's division-free algorithm `Cslib.Circuits.Rational.detRows`. By Kirchhoff's
matrix-tree theorem `SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree`, this is the number of
spanning trees (`Cslib.Complexity.Graph.spanningTreeCount_eq_natCard`). A graph without declared
vertices has no spanning tree, since a tree is nonempty.

## Main definitions

* `Cslib.Complexity.Graph.laplacianEntry`: an entry of the Laplacian of `G.induced`, from the edge
  list.
* `Cslib.Complexity.Graph.reducedLaplacianRows`: the reduced Laplacian as a list of integer rows.
* `Cslib.Complexity.Graph.spanningTreeCount`: its determinant, or `0` without vertices.

## Main results

* `Cslib.Complexity.Graph.spanningTreeCount_eq_natCard`: `spanningTreeCount G` is the number of
  spanning trees `T ≤ G.induced`.
* `Cslib.Complexity.Graph.computableInPolyTime_spanningTreeCount`: it is computable in polynomial
  time from `Cslib.Complexity.encGraph` to binary integers.
* `Cslib.Complexity.Graph.computableInPolyTime_natCard_isTree`: the number of spanning trees of
  `G.induced` is computable in polynomial time from `encGraph` to binary natural numbers.

## References

* [G. Kirchhoff, *Ueber die Auflösung der Gleichungen, auf welche man bei der Untersuchung der
  linearen Vertheilung galvanischer Ströme geführt wird*][Kirchhoff1847]
-/

public section

namespace Cslib.Complexity.Graph

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Circuits.Rational

/-- The entry at `(u, v)` of the Laplacian of `G.induced` on the distinct declared vertices: the
number of neighbours of `u` on the diagonal, and `-1` or `0` off the diagonal according to
adjacency. -/
@[expose] def laplacianEntry (G : Graph) (u v : ℕ) : ℤ :=
  if u = v then ((G.distinctVertices.filter fun w => G.adjBool u w).length : ℤ)
  else if G.adjBool u v then -1 else 0

/-- The reduced Laplacian of `G.induced` on the distinct declared vertices other than the first,
as a list of integer rows. -/
@[expose] def reducedLaplacianRows (G : Graph) : List (List ℤ) :=
  G.distinctVertices.tail.map fun u => G.distinctVertices.tail.map fun v => G.laplacianEntry u v

/-- The number of spanning trees of `G.induced`, computed by the matrix-tree theorem as the
determinant of the reduced Laplacian; `0` when `G` declares no vertex. -/
@[expose] def spanningTreeCount (G : Graph) : ℤ :=
  if G.distinctVertices = [] then 0 else detRows G.reducedLaplacianRows

/-! ### Correctness -/

/-- Adjacency in `G.induced` is decided by the executable test `Cslib.Complexity.Graph.adjBool`. -/
instance instDecidableRelInducedAdj (G : Graph) : DecidableRel G.induced.Adj := fun u v =>
  decidable_of_iff (G.adjBool u v = true) (by rw [adjBool_eq_true_iff, induced_adj])

/-- The degree of a declared vertex in `G.induced` is its number of neighbours among the distinct
declared vertices. -/
private theorem degree_induced (G : Graph) (u : {v // v ∈ G.1}) :
    G.induced.degree u = (G.distinctVertices.filter fun w => G.adjBool u w).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← List.toFinset_card_of_nodup (G.nodup_distinctVertices.filter _)]
  refine Finset.card_bij (fun v _ => (v : ℕ)) (fun v hv => ?_) (fun v _ w _ h => Subtype.ext h)
    (fun w hw => ?_)
  · rw [SimpleGraph.mem_neighborFinset, induced_adj] at hv
    simp only [List.mem_toFinset, List.mem_filter, mem_distinctVertices, adjBool_eq_true_iff]
    exact ⟨v.2, hv⟩
  · simp only [List.mem_toFinset, List.mem_filter, mem_distinctVertices,
      adjBool_eq_true_iff] at hw
    exact ⟨⟨w, hw.1⟩, by rw [SimpleGraph.mem_neighborFinset, induced_adj]; exact hw.2, rfl⟩

/-- The entries of a tabulated square table over a list. -/
private theorem rowEntry_map_map (l : List ℕ) (g : ℕ → ℕ → ℤ) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) : rowEntry (l.map fun u => l.map fun v => g u v) i j = g l[i] l[j] := by
  simp [rowEntry, List.getD_eq_getElem?_getD, hi, hj]

/-- The entries of the reduced Laplacian rows are Laplacian entries of the remaining vertices. -/
private theorem rowEntry_reducedLaplacianRows (G : Graph) {i j : ℕ}
    (hi : i < G.distinctVertices.tail.length) (hj : j < G.distinctVertices.tail.length) :
    rowEntry G.reducedLaplacianRows i j =
      G.laplacianEntry G.distinctVertices.tail[i] G.distinctVertices.tail[j] :=
  rowEntry_map_map _ _ hi hj

/-- **Correctness of `spanningTreeCount`**: it is the number of spanning trees of `G.induced`, by
Kirchhoff's matrix-tree theorem. -/
theorem spanningTreeCount_eq_natCard (G : Graph) :
    G.spanningTreeCount =
      Nat.card {T : SimpleGraph {v // v ∈ G.1} // T ≤ G.induced ∧ T.IsTree} := by
  unfold spanningTreeCount
  split_ifs with h
  · have : IsEmpty {v // v ∈ G.1} := ⟨fun v => by
      have := mem_distinctVertices.2 v.2
      rw [h] at this
      exact List.not_mem_nil this⟩
    rw [Nat.card_eq_zero.2 (Or.inl ⟨fun T => ?_⟩)]
    · rfl
    · obtain ⟨v⟩ := T.2.2.connected.nonempty
      exact this.elim v
  · obtain ⟨a, rest, hvs⟩ := List.exists_cons_of_ne_nil h
    have hnd := G.nodup_distinctVertices
    rw [hvs, List.nodup_cons] at hnd
    have htail : G.distinctVertices.tail = rest := by rw [hvs, List.tail_cons]
    have haG : a ∈ G.1 := mem_distinctVertices.1 (by rw [hvs]; exact List.mem_cons_self ..)
    have hmem : ∀ {w}, w ∈ rest → w ∈ G.1 := fun hw =>
      mem_distinctVertices.1 (by rw [hvs]; exact List.mem_cons_of_mem _ hw)
    set r : {v // v ∈ G.1} := ⟨a, haG⟩
    have hlen : G.reducedLaplacianRows.length = rest.length := by
      rw [reducedLaplacianRows, List.length_map, htail]
    let f : Fin G.reducedLaplacianRows.length → {v : {v // v ∈ G.1} // v ≠ r} := fun i =>
      ⟨⟨rest[i.1]'(hlen ▸ i.2), hmem (List.getElem_mem _)⟩, fun hr => hnd.1 (by
        have h : rest[i.1]'(hlen ▸ i.2) = a := congrArg Subtype.val hr
        rw [← h]
        exact List.getElem_mem _)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        have h : rest[i.1]'(hlen ▸ i.2) = rest[j.1]'(hlen ▸ j.2) :=
          congrArg (fun v => v.1.1) hij
        exact Fin.ext ((hnd.2.getElem_inj_iff).1 h)
      · rintro ⟨⟨w, hw⟩, hwr⟩
        have hwd : w ∈ G.distinctVertices := mem_distinctVertices.2 hw
        rw [hvs, List.mem_cons] at hwd
        have hwrest : w ∈ rest := hwd.resolve_left fun h => hwr (Subtype.ext h)
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hwrest
        exact ⟨⟨k, hlen ▸ hk⟩, rfl⟩
    let e := Equiv.ofBijective f hf
    rw [detRows_eq_det_ofRows, ← SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree r,
      ← Matrix.det_submatrix_equiv_self e]
    congr 1
    ext i j
    have hi : i.1 < rest.length := hlen ▸ i.2
    have hj : j.1 < rest.length := hlen ▸ j.2
    have hi' : i.1 < G.distinctVertices.tail.length := htail ▸ hi
    have hj' : j.1 < G.distinctVertices.tail.length := htail ▸ hj
    simp only [ofRows, Matrix.of_apply, Matrix.submatrix_apply]
    rw [rowEntry_reducedLaplacianRows G hi' hj']
    simp only [e, f, Equiv.ofBijective_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
      SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, laplacianEntry]
    simp only [htail]
    by_cases hij : i = j
    · subst hij
      simp [degree_induced]
    · have hne : rest[i.1] ≠ rest[j.1] := fun h => hij (Fin.ext ((hnd.2.getElem_inj_iff).1 h))
      have hne' : (⟨rest[i.1], hmem (List.getElem_mem _)⟩ : {v // v ∈ G.1}) ≠
          ⟨rest[j.1], hmem (List.getElem_mem _)⟩ := fun h => hne (congrArg Subtype.val h)
      by_cases hadj : G.toSimpleGraph.Adj rest[i.1] rest[j.1] <;> simp [hne, hne', hadj]

/-! ### Polynomial time -/

/-- Dropping the first distinct vertex is polynomial-time. -/
private theorem computableInPolyTime_tail_distinctVertices :
    ComputableInPolyTime (fun G : Graph => G.distinctVertices.tail) encGraph (encList encNat) := by
  simpa only [Function.comp_def, List.drop_one] using
    (dropUnary (encA := encNat)).comp (computableInPolyTime_distinctVertices.prod (const 1))

/-- Tabulating a Laplacian entry is polynomial-time. -/
private theorem computableInPolyTime_laplacianEntry :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.laplacianEntry p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encIntBin := by
  have hG : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1)
      (encPair (encPair encGraph encNat) encNat) encGraph := (fst _ _).fst'
  have hu : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.2)
      (encPair (encPair encGraph encNat) encNat) encNat := (fst _ _).snd'
  have hv : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.2)
      (encPair (encPair encGraph encNat) encNat) encNat := snd _ _
  have hfilter : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ => p.1.1.distinctVertices.filter fun w => p.1.1.adjBool p.1.2 w)
      (encPair (encPair encGraph encNat) encNat) (encList encNat) :=
    filterWithInput (computableInPolyTime_distinctVertices.comp hG)
      (computableInPolyTime_adjBool_comp (hG.comp (fst _ _)) (hu.comp (fst _ _)) (snd _ _))
  unfold laplacianEntry
  exact ite_decide (decide_eq' hu hv) (intBin_natCast.comp (length_list_binary' hfilter))
    (ite (computableInPolyTime_adjBool_comp hG hu hv) (const _) (const _))

/-- Tabulating the reduced Laplacian rows is polynomial-time. -/
private theorem computableInPolyTime_reducedLaplacianRows :
    ComputableInPolyTime reducedLaplacianRows encGraph (encList (encList encIntBin)) := by
  have htail := computableInPolyTime_tail_distinctVertices
  have hrow : ComputableInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.tail.map fun v => p.1.laplacianEntry p.2 v)
      (encPair encGraph encNat) (encList encIntBin) :=
    mapWithInput (htail.comp (fst _ _)) computableInPolyTime_laplacianEntry
  exact mapWithInput htail hrow

/-- **Counting spanning trees is polynomial-time**: `spanningTreeCount` is computable in
polynomial time from encoded graphs to binary integers. -/
theorem computableInPolyTime_spanningTreeCount :
    ComputableInPolyTime spanningTreeCount encGraph encIntBin := by
  unfold spanningTreeCount
  exact ite_decide (decide_eq' computableInPolyTime_distinctVertices (const []))
    (const 0) (detRows_polytime.comp computableInPolyTime_reducedLaplacianRows)

/-- **Counting spanning trees is polynomial-time**: the number of spanning trees of the graph
`G.induced` induced on the declared vertices is computable in polynomial time from encoded graphs to
binary natural numbers. -/
theorem computableInPolyTime_natCard_isTree :
    ComputableInPolyTime
      (fun G : Graph => Nat.card {T : SimpleGraph {v // v ∈ G.1} // T ≤ G.induced ∧ T.IsTree})
      encGraph encNat := by
  have h : (fun G : Graph => Nat.card {T : SimpleGraph {v // v ∈ G.1} // T ≤ G.induced ∧ T.IsTree})
      = fun G => G.spanningTreeCount.toNat :=
    funext fun G => by rw [spanningTreeCount_eq_natCard, Int.toNat_natCast]
  rw [h]
  exact intBin_toNat.comp computableInPolyTime_spanningTreeCount

end Cslib.Complexity.Graph
