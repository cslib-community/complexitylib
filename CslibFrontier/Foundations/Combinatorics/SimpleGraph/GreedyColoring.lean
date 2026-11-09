/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Greedy coloring

A finite graph whose maximum degree is less than `q` has a proper `q`-coloring
(`SimpleGraph.colorable_of_maxDegree_lt`). The proof colors the vertices one at a time: a vertex
has fewer than `q` neighbors, so some color is unused among the neighbors colored so far. Hence
`χ(G) ≤ Δ(G) + 1` (`SimpleGraph.chromaticNumber_le_maxDegree_add_one`).

## Main results

* `SimpleGraph.colorable_of_maxDegree_lt`: a graph of maximum degree less than `q` is
  `q`-colorable.
* `SimpleGraph.chromaticNumber_le_maxDegree_add_one`: `χ(G) ≤ Δ(G) + 1`.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Greedy coloring**: a finite graph whose maximum degree is less than `q` is
`q`-colorable. -/
theorem colorable_of_maxDegree_lt {q : ℕ} (hq : G.maxDegree < q) : G.Colorable q := by
  classical
  suffices H : ∀ s : Finset V, ∃ x : V → Fin q,
      ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → x u ≠ x v by
    obtain ⟨x, hx⟩ := H Finset.univ
    exact ⟨Coloring.mk x fun {u v} huv => hx u (Finset.mem_univ u) v (Finset.mem_univ v) huv⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => ⟨0, by omega⟩, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨x, hx⟩ := ih
    have hcard : ((G.neighborFinset a).image x).card < q :=
      (Finset.card_image_le.trans (G.degree_le_maxDegree a)).trans_lt hq
    obtain ⟨c, hc⟩ : ∃ c : Fin q, c ∉ (G.neighborFinset a).image x := by
      by_contra h
      push Not at h
      have hsub : (Finset.univ : Finset (Fin q)) ⊆ (G.neighborFinset a).image x :=
        fun c _ => h c
      have := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hc' (v : V) (hv : G.Adj a v) : c ≠ x v := fun h =>
      hc (Finset.mem_image.2 ⟨v, (G.mem_neighborFinset a v).2 hv, h.symm⟩)
    refine ⟨Function.update x a c, fun u hu v hv huv => ?_⟩
    rcases Finset.mem_insert.1 hu with rfl | hu <;> rcases Finset.mem_insert.1 hv with rfl | hv
    · exact absurd rfl (G.ne_of_adj huv)
    · rw [Function.update_self, Function.update_of_ne (G.ne_of_adj huv).symm]
      exact hc' v huv
    · rw [Function.update_self, Function.update_of_ne (G.ne_of_adj huv)]
      exact (hc' u huv.symm).symm
    · rw [Function.update_of_ne (show u ≠ a from fun h => ha (h ▸ hu)),
        Function.update_of_ne (show v ≠ a from fun h => ha (h ▸ hv))]
      exact hx u hu v hv huv

/-- **Greedy coloring bound**: `χ(G) ≤ Δ(G) + 1`. -/
theorem chromaticNumber_le_maxDegree_add_one : G.chromaticNumber ≤ G.maxDegree + 1 := by
  exact_mod_cast (G.colorable_of_maxDegree_lt (Nat.lt_succ_self _)).chromaticNumber_le

end SimpleGraph
