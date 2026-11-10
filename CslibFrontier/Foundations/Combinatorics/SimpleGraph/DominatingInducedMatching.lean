/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, efficient edge domination)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Dominating induced matchings and their endpoint sets

A matching edge dominates itself and any edge sharing one of its endpoints. Every original edge
must be dominated by exactly one matching edge. The original edges are unordered `Sym2` edges,
and a matching is a conventional Mathlib subgraph, without extra certificates or isolated marks.
This is the efficient-edge-domination convention of [ChenJiangZhu2027], Corollary D.4 (PDF p. 36).

## Main definitions

* `SimpleGraph.Subgraph.IsDominatingInducedMatching`: a matching dominating every edge exactly once.

## Main results

* `SimpleGraph.Subgraph.isDominatingInducedMatching_iff`: equivalence to an induced matching
  whose endpoint set covers every original edge.
* `SimpleGraph.card_dominatingMatching_supports_eq`: exact Boolean-support/matching count bijection.
-/

public section

namespace SimpleGraph.Subgraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two matching edges sharing a vertex are the same unordered edge. -/
theorem IsMatching.edge_eq_of_mem {M : G.Subgraph} (h : M.IsMatching) (e f : M.edgeSet)
    {u : V} (he : u ∈ e.val) (hf : u ∈ f.val) : e = f := by
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp he
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp hf
  have hea : M.Adj u a := by simpa only [ha, Subgraph.mem_edgeSet] using e.property
  have hfb : M.Adj u b := by simpa only [hb, Subgraph.mem_edgeSet] using f.property
  apply Subtype.ext
  rw [ha, hb, h.eq_of_adj_left hea hfb]

/-- Each original edge shares an endpoint with exactly one matching edge, including itself. -/
@[expose] def IsDominatingInducedMatching (M : G.Subgraph) : Prop :=
  M.IsMatching ∧ ∀ u v, G.Adj u v → ∃! e : M.edgeSet, u ∈ e.val ∨ v ∈ e.val

/-- Efficient edge domination is precisely an induced matching with vertex-cover support. -/
theorem isDominatingInducedMatching_iff (M : G.Subgraph) :
    M.IsDominatingInducedMatching ↔ M.IsMatching ∧ M.IsInduced ∧
      ∀ u v, G.Adj u v → u ∈ M.verts ∨ v ∈ M.verts := by
  constructor
  · rintro ⟨hm, hd⟩
    refine ⟨hm, ?_, ?_⟩
    · intro u hu v hv huv
      let eu := hm.toEdge ⟨u, hu⟩
      let ev := hm.toEdge ⟨v, hv⟩
      have hue : u ∈ eu.val := hm.mem_coe_toEdge hu
      have hve : v ∈ ev.val := hm.mem_coe_toEdge hv
      have he : eu = ev := (hd u v huv).unique (Or.inl hue) (Or.inr hve)
      have hvu : v ∈ eu.val := by rw [he]; exact hve
      have heq : eu.val = s(u, v) :=
        (Sym2.mem_and_mem_iff (G.ne_of_adj huv)).mp ⟨hue, hvu⟩
      simpa only [heq, Subgraph.mem_edgeSet] using eu.property
    · intro u v huv
      obtain ⟨e, he, _⟩ := hd u v huv
      exact he.imp (M.mem_verts_of_mem_edge e.property) (M.mem_verts_of_mem_edge e.property)
  · rintro ⟨hm, hi, hc⟩
    refine ⟨hm, ?_⟩
    have aux (u v : V) (huv : G.Adj u v) (hu : u ∈ M.verts) :
        ∃! e : M.edgeSet, u ∈ e.val ∨ v ∈ e.val := by
      let e := hm.toEdge ⟨u, hu⟩
      have he : u ∈ e.val := hm.mem_coe_toEdge hu
      refine ⟨e, Or.inl he, fun f hf => ?_⟩
      rcases hf with hf | hf
      · exact hm.edge_eq_of_mem f e hf he
      · have hv : v ∈ M.verts := M.mem_verts_of_mem_edge f.property hf
        have ha : M.Adj u v := hi hu hv huv
        have hv' : v ∈ e.val := by
          change v ∈ (hm.toEdge ⟨u, hu⟩ : Sym2 V)
          rw [hm.toEdge_eq_of_adj ha]
          exact Sym2.mem_mk_right _ _
        exact hm.edge_eq_of_mem f e hf hv'
    intro u v huv
    rcases hc u v huv with hu | hv
    · exact aux u v huv hu
    · simpa only [or_comm] using aux v u huv.symm hv

end SimpleGraph.Subgraph

namespace SimpleGraph

open Classical in
/-- The support encoding counts each actual efficient edge dominating matching exactly once.
The inverse uses its endpoint set; no choice of orientations or private witnesses is counted. -/
theorem card_dominatingMatching_supports_eq {V : Type*} [Finite V] (G : SimpleGraph V) :
    Nat.card {σ : V → Bool //
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        ∀ u v, G.Adj u v → σ u = true ∨ σ v = true} =
      Nat.card {M : G.Subgraph // M.IsDominatingInducedMatching} := by
  let : Fintype V := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  let f : {σ : V → Bool //
      ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
        ∀ u v, G.Adj u v → σ u = true ∨ σ v = true} →
      {M : G.Subgraph // M.IsDominatingInducedMatching} := fun σ =>
        ⟨(⊤ : G.Subgraph).induce {u | σ.val u = true},
          (Subgraph.isDominatingInducedMatching_iff _).mpr ⟨σ.property.1,
            (Subgraph.isInduced_iff_exists_eq_induce_top _).mpr ⟨_, rfl⟩, σ.property.2⟩⟩
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro x y h
    apply Subtype.ext
    funext u
    have he := Set.ext_iff.mp (congrArg (fun z => z.val.verts) h) u
    change (x.val u = true) ↔ (y.val u = true) at he
    cases hx : x.val u <;> cases hy : y.val u <;> simp_all
  · intro M
    obtain ⟨hm, hi, hc⟩ := (Subgraph.isDominatingInducedMatching_iff _).mp M.property
    let σ (u : V) := decide (u ∈ M.val.verts)
    have hverts : {u | σ u = true} = M.val.verts := by ext u; simp [σ]
    have he : (⊤ : G.Subgraph).induce {u | σ u = true} = M.val := by
      rw [hverts]
      exact hi.induce_top_verts
    refine ⟨⟨σ, ?_, ?_⟩, ?_⟩
    · rw [he]
      exact hm
    · intro u v huv
      simpa only [σ, decide_eq_true_eq] using hc u v huv
    · exact Subtype.ext he

end SimpleGraph
