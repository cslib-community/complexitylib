/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Multigraph
public import Complexity.Foundations.Combinatorics.WeightedCut

/-!
# The weight matrix of a multigraph given by its ends

A multigraph given by its ends `ends : E → Sym2 V` (`Cslib.Multigraph`) has a weight matrix
`Cslib.Multigraph.weightMatrix ends` counting the edges between distinct vertices; self-loops are
dropped. It is a weighted multigraph in the sense of `Cslib.WeightedCut.IsMultigraph`, and the
weight of each cut is the number of edges between the cut and its complement, so the global minimum
cut weight of the matrix is the least size of an edge cut of a non-trivial cut.

## Main definitions

* `Cslib.Multigraph.weightMatrix`: the number of edges joining two distinct vertices.

## Main results

* `Cslib.Multigraph.isMultigraph_weightMatrix`: the weight matrix is symmetric with zero diagonal.
* `Cslib.Multigraph.cutWeight_weightMatrix`: the weight of a cut is the size of its edge cut.
* `Cslib.Multigraph.minCut_weightMatrix_le_card_edgeCut`: the global minimum cut weight is at most
  the size of the edge cut of any non-trivial cut.
-/

@[expose] public section

namespace Cslib.Multigraph

open Finset

variable {V E : Type*} [Fintype E] [DecidableEq V] (ends : E → Sym2 V)

/-- The weight matrix of the multigraph `ends`: the number of edges joining `u` and `v` when they
are distinct, and `0` on the diagonal, so self-loops are dropped. -/
def weightMatrix (u v : V) : ℕ :=
  if u = v then 0 else #{e | ends e = s(u, v)}

/-- The weight matrix of a multigraph is symmetric with zero diagonal. -/
theorem isMultigraph_weightMatrix : WeightedCut.IsMultigraph (weightMatrix ends) := by
  refine ⟨fun u v => ?_, fun u => by simp [weightMatrix]⟩
  by_cases h : u = v
  · rw [h]
  · simp only [weightMatrix, h, Ne.symm h, ↓reduceIte, Sym2.eq_swap]

variable [Fintype V]

/-- The weight of a cut in the weight matrix of a multigraph is the number of edges between the cut
and its complement. -/
theorem cutWeight_weightMatrix (S : Finset V) :
    WeightedCut.cutWeight (weightMatrix ends) S = #(edgeCut ends S) := by
  classical
  have hcut : edgeCut ends S =
      (S ×ˢ Sᶜ).biUnion fun p => ({e | ends e = s(p.1, p.2)} : Finset E) := by
    ext e
    simp only [mem_edgeCut, mem_biUnion, mem_product, mem_filter, mem_univ, true_and,
      Prod.exists]
    constructor
    · rintro ⟨v, hv, w, hw, h⟩
      exact ⟨v, w, ⟨hv, hw⟩, h⟩
    · rintro ⟨v, w, ⟨hv, hw⟩, h⟩
      exact ⟨v, hv, w, hw, h⟩
  rw [hcut, card_biUnion, WeightedCut.cutWeight, ← compl_eq_univ_sdiff, sum_product]
  · refine sum_congr rfl fun u hu => sum_congr rfl fun v hv => ?_
    have huv : u ≠ v := fun h => mem_compl.1 hv (h ▸ hu)
    simp only [weightMatrix, huv, ↓reduceIte]
  · rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' hne
    simp only [coe_product, Set.mem_prod, mem_coe, mem_compl] at huv huv'
    simp only [Function.onFun, disjoint_left, mem_filter, mem_univ, true_and]
    intro e he he'
    rcases Sym2.eq_iff.1 (he.symm.trans he') with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne rfl
    · exact huv'.2 huv.1

/-- The global minimum cut weight of the weight matrix of a multigraph is at most the number of
edges leaving any non-trivial cut. -/
theorem minCut_weightMatrix_le_card_edgeCut {S : Finset V} (hS : WeightedCut.IsNonTrivialCut S) :
    WeightedCut.minCut (weightMatrix ends) ≤ #(edgeCut ends S) :=
  cutWeight_weightMatrix ends S ▸ WeightedCut.minCut_le_cutWeight _ hS

/-- With at least two vertices, the global minimum cut weight of the weight matrix of a multigraph
is the number of edges leaving some non-trivial cut. -/
theorem exists_card_edgeCut_eq_minCut_weightMatrix (hV : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, WeightedCut.IsNonTrivialCut S ∧
      #(edgeCut ends S) = WeightedCut.minCut (weightMatrix ends) := by
  obtain ⟨S, hS, h⟩ := WeightedCut.exists_minCut_achiever hV (weightMatrix ends)
  exact ⟨S, hS, cutWeight_weightMatrix ends S ▸ h⟩

end Cslib.Multigraph
