/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Ramsey.FranklWilson
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Foundations.Data.List.IsSortedLT
public import Mathlib.Data.Finset.Sort
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# The Frankl–Wilson graph is strongly explicit

The Frankl–Wilson graph `SimpleGraph.franklWilsonGraph (Fin (p ^ 3)) p (p ^ 2 - 1)` has
`C(p³, p² - 1)` vertices and neither a clique nor an independent set of more than `C(p³, p - 1)`
vertices (`SimpleGraph.choose_lt_ramseyNumber_franklWilson`) [FranklWilson1981]. It is strongly
explicit in the sense of `CslibFrontier.Computability.Complexity.ExplicitRamsey`:

* a vertex, a `d`-subset of `Fin n`, is named by the list of its elements in increasing order
  (`Cslib.ExplicitRamsey.subsetLabel`), and the names are exactly the strictly increasing lists of
  length `d` with entries below `n` (`Cslib.ExplicitRamsey.subsetLabel_injective`,
  `Cslib.ExplicitRamsey.range_subsetLabel`);
* the names are recognized by `Cslib.ExplicitRamsey.isSubsetLabel` in polynomial time with binary
  naturals (`Cslib.ExplicitRamsey.computableInPolyTime_isSubsetLabel`);
* two vertices are adjacent exactly when the number of entries of the first name occurring in the
  second is not congruent to `d` mod `p`
  (`Cslib.ExplicitRamsey.franklWilsonGraph_adj_iff_subsetAdj`), which is polynomial time
  (`Cslib.ExplicitRamsey.computableInPolyTime_subsetAdj`).

For the Frankl–Wilson parameters, `Cslib.ExplicitRamsey.franklWilsonIsLabel` and
`Cslib.ExplicitRamsey.franklWilsonAdj` take only the prime `p`, and one machine serves every `p`
(`Cslib.ExplicitRamsey.computableInPolyTime_franklWilsonIsLabel`,
`Cslib.ExplicitRamsey.computableInPolyTime_franklWilsonAdj`). A name has `p² - 1` entries of
`O(log p)` bits, so its length is `O(p² log p) = O(log N)` for `N = C(p³, p² - 1)` vertices, and
both predicates run in time polylogarithmic in `N`.

## Main definitions

* `Cslib.ExplicitRamsey.subsetLabel`: the name of a `d`-subset of `Fin n`.
* `Cslib.ExplicitRamsey.isSubsetLabel`, `Cslib.ExplicitRamsey.subsetAdj`: recognition and
  Frankl–Wilson adjacency on names, for general `n`, `d` and `p`.
* `Cslib.ExplicitRamsey.franklWilsonIsLabel`, `Cslib.ExplicitRamsey.franklWilsonAdj`: the same for
  `n = p³` and `d = p² - 1`, from `p` alone.

## Main results

* `Cslib.ExplicitRamsey.subsetLabel_injective`, `Cslib.ExplicitRamsey.range_subsetLabel`: names
  are a bijection onto the strictly increasing lists of length `d` below `n`.
* `Cslib.ExplicitRamsey.franklWilsonGraph_adj_iff_subsetAdj`,
  `Cslib.ExplicitRamsey.franklWilsonGraph_adj_iff_franklWilsonAdj`: adjacency on names.
* `Cslib.ExplicitRamsey.computableInPolyTime_isSubsetLabel`,
  `Cslib.ExplicitRamsey.computableInPolyTime_subsetAdj`,
  `Cslib.ExplicitRamsey.computableInPolyTime_franklWilsonIsLabel`,
  `Cslib.ExplicitRamsey.computableInPolyTime_franklWilsonAdj`: all four predicates are polynomial
  time.

## References

* [P. Frankl, R. M. Wilson, *Intersection theorems with geometric consequences*][FranklWilson1981]
-/

public section

open Finset SimpleGraph Turing.MultiTapeTM

namespace Cslib.ExplicitRamsey

/-- Recognizes names of `d`-subsets of `Fin n`: strictly increasing lists of length `d` with
entries below `n`. The input is `(n, d, l)`. -/
@[expose] def isSubsetLabel (q : ℕ × ℕ × List ℕ) : Bool :=
  decide (q.2.2.length = q.2.1) && q.2.2.isSortedLT &&
    q.2.2.all fun x => decide (x < q.1)

/-- Frankl–Wilson adjacency on names: whether the number of entries of the first name occurring in
the second is not congruent to `d` mod `p`. The input is `(p, d, a, b)`. -/
@[expose] def subsetAdj (q : ℕ × ℕ × List ℕ × List ℕ) : Bool :=
  (q.2.2.1.filter fun x => decide (x ∈ q.2.2.2)).length % q.1 != q.2.1 % q.1

/-- Recognizes names of vertices of the Frankl–Wilson graph for the prime `p`: the
`(p² - 1)`-subsets of `Fin (p ^ 3)`. The input is `(p, l)`. -/
@[expose] def franklWilsonIsLabel (q : ℕ × List ℕ) : Bool :=
  isSubsetLabel (q.1 ^ 3, q.1 ^ 2 - 1, q.2)

/-- Adjacency on names in the Frankl–Wilson graph for the prime `p`. The input is `(p, a, b)`. -/
@[expose] def franklWilsonAdj (q : ℕ × List ℕ × List ℕ) : Bool :=
  subsetAdj (q.1, q.1 ^ 2 - 1, q.2)

/-- The name of a `d`-subset of `Fin n`: its elements in increasing order. -/
def subsetLabel {n d : ℕ} (s : {s : Finset (Fin n) // #s = d}) : List ℕ :=
  (s.1.sort).map Fin.val

private theorem sortedLT_subsetLabel {n d : ℕ} (s : {s : Finset (Fin n) // #s = d}) :
    (subsetLabel s).SortedLT := by
  rw [subsetLabel, List.sortedLT_iff_isChain, List.isChain_map]
  exact List.sortedLT_iff_isChain.1 (sortedLT_sort s.1)

private theorem mem_subsetLabel {n d : ℕ} (s : {s : Finset (Fin n) // #s = d}) (x : Fin n) :
    (x : ℕ) ∈ subsetLabel s ↔ x ∈ s.1 := by
  rw [subsetLabel, List.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← Fin.ext hyx]
    exact (mem_sort _).1 hy
  · exact fun h => ⟨x, (mem_sort _).2 h, rfl⟩

/-- Distinct vertices have distinct names. -/
theorem subsetLabel_injective {n d : ℕ} : Function.Injective (subsetLabel (n := n) (d := d)) := by
  intro s t h
  apply Subtype.ext
  ext x
  rw [← mem_subsetLabel s x, ← mem_subsetLabel t x, h]

/-- The names of the `d`-subsets of `Fin n` are exactly the lists accepted by `isSubsetLabel`, the
strictly increasing lists of length `d` with entries below `n`. -/
theorem range_subsetLabel (n d : ℕ) :
    Set.range (subsetLabel (n := n) (d := d)) = {l | isSubsetLabel (n, d, l) = true} := by
  ext l
  simp only [Set.mem_range, Set.mem_ofPred_eq, isSubsetLabel, Bool.and_eq_true, decide_eq_true_eq,
    List.isSortedLT_iff, List.all_eq_true]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨⟨?_, sortedLT_subsetLabel s⟩, fun x hx => ?_⟩
    · rw [subsetLabel, List.length_map, length_sort, s.2]
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact y.2
  · rintro ⟨⟨hlen, hsort⟩, hlt⟩
    set u : Finset (Fin n) := univ.filter fun i => (i : ℕ) ∈ l with hu
    have hmem : ∀ a, a ∈ (u.sort).map Fin.val ↔ a ∈ l := by
      intro a
      rw [List.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (mem_filter.1 ((mem_sort _).1 hy)).2
      · intro ha
        exact ⟨⟨a, hlt a ha⟩, (mem_sort _).2 (mem_filter.2 ⟨mem_univ _, ha⟩), rfl⟩
    have hsorted : ((u.sort).map Fin.val).SortedLT := by
      rw [List.sortedLT_iff_isChain, List.isChain_map]
      exact List.sortedLT_iff_isChain.1 (sortedLT_sort u)
    have heq := hsorted.eq_of_mem_iff hsort hmem
    have hcard : #u = d := by
      rw [← length_sort (· ≤ ·), ← List.length_map (f := Fin.val), heq, hlen]
    exact ⟨⟨u, hcard⟩, heq⟩

private theorem card_inter_eq_length {n d : ℕ} (s t : {s : Finset (Fin n) // #s = d}) :
    #(s.1 ∩ t.1) = ((subsetLabel s).filter fun x => decide (x ∈ subsetLabel t)).length := by
  have hnd : ((subsetLabel s).filter fun x => decide (x ∈ subsetLabel t)).Nodup :=
    (List.Nodup.map Fin.val_injective (sort_nodup s.1 _)).filter _
  rw [← List.toFinset_card_of_nodup hnd, ← card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, Fin.valEmbedding_apply, mem_inter, List.mem_toFinset, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨y, ⟨hys, hyt⟩, rfl⟩
    exact ⟨(mem_subsetLabel s y).2 hys, (mem_subsetLabel t y).2 hyt⟩
  · rintro ⟨hxs, hxt⟩
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 (show x ∈ (s.1.sort (· ≤ ·)).map Fin.val from hxs)
    exact ⟨y, ⟨(mem_subsetLabel s y).1 hxs, (mem_subsetLabel t y).1 hxt⟩, rfl⟩

/-- Adjacency in the Frankl–Wilson graph on the `d`-subsets of `Fin n` is `subsetAdj` on names. -/
theorem franklWilsonGraph_adj_iff_subsetAdj {n p d : ℕ} (s t : {s : Finset (Fin n) // #s = d}) :
    (franklWilsonGraph (Fin n) p d).Adj s t ↔
      subsetAdj (p, d, subsetLabel s, subsetLabel t) = true := by
  rw [franklWilsonGraph_adj, card_inter_eq_length, subsetAdj, bne_iff_ne]

/-- Adjacency in the Frankl–Wilson graph for the prime `p` is `franklWilsonAdj` on names. -/
theorem franklWilsonGraph_adj_iff_franklWilsonAdj {p : ℕ}
    (s t : {s : Finset (Fin (p ^ 3)) // #s = p ^ 2 - 1}) :
    (franklWilsonGraph (Fin (p ^ 3)) p (p ^ 2 - 1)).Adj s t ↔
      franklWilsonAdj (p, subsetLabel s, subsetLabel t) = true :=
  franklWilsonGraph_adj_iff_subsetAdj s t

/-- Names are recognized in polynomial time in the binary lengths of `n`, `d` and the name. -/
theorem computableInPolyTime_isSubsetLabel :
    ComputableInPolyTime isSubsetLabel (encPair encNat (encPair encNat (encList encNat)))
      encBool := by
  unfold isSubsetLabel List.isSortedLT
  fun_prop

/-- Adjacency on names is polynomial time in the binary lengths of `p`, `d` and the two names. -/
theorem computableInPolyTime_subsetAdj :
    ComputableInPolyTime subsetAdj
      (encPair encNat (encPair encNat (encPair (encList encNat) (encList encNat)))) encBool := by
  unfold subsetAdj
  fun_prop

/-- Names of vertices of the Frankl–Wilson graph are recognized in polynomial time, uniformly in
the prime `p`. -/
theorem computableInPolyTime_franklWilsonIsLabel :
    ComputableInPolyTime franklWilsonIsLabel (encPair encNat (encList encNat)) encBool := by
  unfold franklWilsonIsLabel isSubsetLabel List.isSortedLT
  fun_prop

/-- Adjacency in the Frankl–Wilson graph is polynomial time on names, uniformly in the prime `p`. -/
theorem computableInPolyTime_franklWilsonAdj :
    ComputableInPolyTime franklWilsonAdj
      (encPair encNat (encPair (encList encNat) (encList encNat))) encBool := by
  unfold franklWilsonAdj subsetAdj
  fun_prop

end Cslib.ExplicitRamsey

end
