/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, induced matching supports)

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Weight
public import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Induced matching supports and edge cardinality

An induced matching is a conventional subgraph that is both a matching and induced. Its support
has twice as many vertices as it has unordered edges. Thus a cardinality circuit on the support
counts actual matching edges, without orientations or extra isolated marks. This is the support
reduction in [ChenJiangZhu2027], Proposition D.1 and Corollary 7.5 (PDF pp. 33–34).

## Main results

* `SimpleGraph.Subgraph.IsMatching.card_verts_eq_twice_edges`: exact endpoint cardinality.
* `SimpleGraph.card_inducedMatching_supports_eq`: size-preserving support/count correspondence.
-/

public section

namespace SimpleGraph.Subgraph

open Classical in
/-- Every finite matching has exactly two endpoints per unordered edge, including the empty one. -/
theorem IsMatching.card_verts_eq_twice_edges {V : Type*} [Finite V] {G : SimpleGraph V}
    {M : G.Subgraph} (h : M.IsMatching) : Nat.card M.verts = 2 * Nat.card M.edgeSet := by
  let : Fintype V := Fintype.ofFinite V
  have hf (e : M.edgeSet) : Nat.card {v : M.verts // h.toEdge v = e} = 2 := by
    rcases e with ⟨⟨u, v⟩, huv⟩
    change Nat.card (h.toEdge ⁻¹' {⟨s(u, v), huv⟩}) = 2
    rw [h.toEdge_preimage_singleton huv, Nat.card_coe_set_eq]
    apply Set.ncard_pair
    intro he
    exact G.ne_of_adj huv.adj_sub (congrArg Subtype.val he)
  calc
    _ = Nat.card (Σ e : M.edgeSet, {v : M.verts // h.toEdge v = e}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv h.toEdge).symm
    _ = 2 * Nat.card M.edgeSet := by
      rw [Nat.card_sigma]
      simp only [hf, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        Nat.card_eq_fintype_card, mul_comm]

end SimpleGraph.Subgraph

namespace SimpleGraph

open Classical in
/-- Boolean supports and actual induced matchings are in bijection, preserving any test on the
number of endpoints. In particular an edge interval is tested on twice the unordered edge count. -/
theorem card_inducedMatching_supports_eq {V : Type*} [Fintype V] (G : SimpleGraph V)
    (P : ℕ → Prop) :
    Nat.card {σ : V → Bool // ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
      P (Cslib.BitString.weight σ)} =
      Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ P (2 * Nat.card M.edgeSet)} := by
  have hw (σ : V → Bool) : Cslib.BitString.weight σ =
      Nat.card ((⊤ : G.Subgraph).induce {u | σ u = true}).verts := by
    rw [Cslib.BitString.weight_eq_card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  let f : {σ : V → Bool // ((⊤ : G.Subgraph).induce {u | σ u = true}).IsMatching ∧
      P (Cslib.BitString.weight σ)} →
      {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧ P (2 * Nat.card M.edgeSet)} := fun σ =>
        ⟨(⊤ : G.Subgraph).induce {u | σ.val u = true}, σ.property.1,
          (Subgraph.isInduced_iff_exists_eq_induce_top _).mpr ⟨_, rfl⟩,
          by simpa only [hw, σ.property.1.card_verts_eq_twice_edges] using σ.property.2⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_of_bijective (f := f)
  constructor
  · intro x y h
    apply Subtype.ext
    funext u
    have he := Set.ext_iff.mp (congrArg (fun z => z.val.verts) h) u
    change (x.val u = true) ↔ (y.val u = true) at he
    cases hx : x.val u <;> cases hy : y.val u <;> simp_all
  · intro M
    obtain ⟨hm, hi, hp⟩ := M.property
    let σ (u : V) := decide (u ∈ M.val.verts)
    have hverts : {u | σ u = true} = M.val.verts := by ext u; simp [σ]
    have he : (⊤ : G.Subgraph).induce {u | σ u = true} = M.val := by
      rw [hverts]
      exact hi.induce_top_verts
    refine ⟨⟨σ, ?_, ?_⟩, Subtype.ext he⟩
    · rw [he]; exact hm
    · simpa only [hw, he, hm.card_verts_eq_twice_edges] using hp

end SimpleGraph
