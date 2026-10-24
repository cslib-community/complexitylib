/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Compression
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

/-!
# The layout hypothesis in every degree, from spanning trees

A tree of maximum degree `d` on `N` vertices has a layout of width at most `d log₂ N`: in a
compression of a tree with the fewest blocks, some block has at most one edge leaving it, so it
merges with a neighbour unless it is the only block, and then the expansion of the trivial
layout of the quotient is the layout (`exists_width_le_of_card_add_one_eq`).

A connected multigraph has a spanning tree, obtained from one of its underlying simple graph
(`exists_spanningTree`). Laying out the spanning tree and putting back the `β₁` edges outside it
costs at most `β₁` edges at each frontier (`exists_width_le_cycleRank_add`). So every fixed
maximum degree has layout coefficient one (`layoutBound_one`), which yields unconditional
circuit lower bounds for every fan-in (the module
`Complexity.Computability.Circuit.Frontier.Unconditional`).

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.edgeRestrict`: the multigraph keeping a set of edges.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.exists_spanningTree`: a connected multigraph has a
  connected spanning sub-multigraph with `|V| - 1` edges.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_of_card_add_one_eq`: trees of maximum
  degree `d` have layouts of width at most `d log₂ |V|`.
* `Cslib.Circuits.Frontier.Multigraph.exists_width_le_cycleRank_add`: connected multigraphs of
  maximum degree `d` have layouts of width at most `β₁ + d log₂ |V|`.
* `Cslib.Circuits.Frontier.layoutBound_one`: the layout hypothesis with coefficient one, in every
  degree.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The multigraph keeping the edges in `F`, and all the vertices. -/
def edgeRestrict (F : Set E) : Multigraph V F where
  src e := G.src e.1
  tgt e := G.tgt e.1

variable {G}

/-- Removing edges does not increase degrees. -/
private theorem MaxDegreeLE.edgeRestrict [Finite E] {d : ℕ} (hd : G.MaxDegreeLE d) (F : Set E) :
    (G.edgeRestrict F).MaxDegreeLE d := by
  intro v
  rw [← ncard_image_of_injective _ Subtype.val_injective]
  exact (ncard_le_ncard (by rintro _ ⟨e, he, rfl⟩; exact he)).trans (hd v)

/-- **Spanning trees.** A finite connected multigraph has a set of `|V| - 1` edges that still
connects it. The edges are chosen along a spanning tree of the underlying simple graph. -/
theorem exists_spanningTree [Finite V] (hG : G.toSimpleGraph.Connected) :
    ∃ F : Set E, (G.edgeRestrict F).toSimpleGraph.Connected ∧ Nat.card F + 1 = Nat.card V := by
  obtain ⟨T, hTG, hT⟩ := hG.exists_isTree_le
  -- Every edge of the spanning tree is the pair of ends of an edge of `G`.
  have hends (s : T.edgeSet) : ∃ e, G.ends e = s.1 := by
    have hs := SimpleGraph.edgeSet_mono hTG s.2
    rw [toSimpleGraph_eq, _root_.Cslib.Multigraph.edgeSet_toSimpleGraph] at hs
    exact hs.1
  choose g hg using hends
  have hginj : g.Injective := fun s s' h => Subtype.ext ((hg s).symm.trans (h ▸ hg s'))
  refine ⟨range g, hT.connected.mono fun u v huv => ?_, ?_⟩
  · exact toSimpleGraph_adj.mpr ⟨huv.ne, ⟨g ⟨s(u, v), huv⟩, mem_range_self _⟩, hg _⟩
  · rw [Nat.card_range_of_injective hginj]
    exact (SimpleGraph.isTree_iff_connected_and_card.mp hT).2

/-- **Trees have logarithmic width.** A finite connected multigraph of maximum degree `d` with
one edge fewer than vertices has a layout of width at most `d log₂ |V|`. -/
theorem exists_width_le_of_card_add_one_eq [Finite V] [Finite E] {d : ℕ}
    (hG : G.toSimpleGraph.Connected) (hcard : Nat.card E + 1 = Nat.card V)
    (hd : G.MaxDegreeLE d) : ∃ π : Layout V, G.width π ≤ d * Nat.log 2 (Nat.card V) := by
  classical
  obtain ⟨c, hc⟩ := Compression.exists_saturated hd
  have hcount := c.card_add_card_external_le
  -- A saturated compression of a tree has only one block, so no edge is external.
  have hext : Nat.card c.external = 0 := by
    by_contra hne
    have two : 1 < Nat.card c.blocks := by omega
    -- The cuts of the blocks add up to `2 |E_B| < 2 |B|`: some block has at most one edge
    -- leaving it.
    obtain ⟨B, -, hB⟩ : ∃ B ∈ (Finset.univ : Finset c.blocks),
        (G.edgeCut {v | v ∈ B.1}).ncard < 2 := by
      refine Finset.exists_lt_of_sum_lt ?_
      rw [c.sum_ncard_edgeCut, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        ← Nat.card_eq_fintype_card]
      omega
    -- It merges with the block at the other end of an edge leaving it.
    obtain ⟨e, he⟩ := c.edgeCut_nonempty hG two B
    obtain ⟨B', hB'B, he'⟩ := c.exists_ne_mem_edgeCut he
    have hsum := G.ncard_edgeCut_union_add (c.disjoint_of_ne hB'B.symm)
    have hjoin : (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).Nonempty := ⟨e, he, he'⟩
    have := hjoin.ncard_pos
    have := c.ncard_edgeCut_le _ B'.2
    have := hc _ B.2 _ B'.2 (fun h => hB'B (Subtype.ext h).symm) hjoin
    omega
  obtain ⟨π, hπ⟩ := c.exists_width_le (Classical.arbitrary _)
  refine ⟨π, hπ.trans ?_⟩
  have := c.quotient.width_le_card (Classical.arbitrary _)
  omega

/-- **Layouts from spanning trees.** A finite connected multigraph of maximum degree `d` has a
layout of width at most `β₁ + d log₂ |V|`, where `β₁` is its cycle rank: lay out a spanning tree,
and put back the `β₁` edges outside it. -/
theorem exists_width_le_cycleRank_add [Finite V] [Finite E] {d : ℕ}
    (hG : G.toSimpleGraph.Connected) (hd : G.MaxDegreeLE d) :
    ∃ π : Layout V, G.width π ≤ G.cycleRank + d * Nat.log 2 (Nat.card V) := by
  obtain ⟨F, hF, hFcard⟩ := exists_spanningTree hG
  obtain ⟨π, hπ⟩ := exists_width_le_of_card_add_one_eq hF hFcard (hd.edgeRestrict F)
  refine ⟨π, (G.width_le_iff π).2 fun t => ?_⟩
  have hsub : G.frontier π t ⊆ Subtype.val '' (G.edgeRestrict F).frontier π t ∪ Fᶜ := by
    intro e he
    by_cases heF : e ∈ F
    · exact Or.inl ⟨⟨e, heF⟩, he, rfl⟩
    · exact Or.inr heF
  have hcompl : Fᶜ.ncard = G.cycleRank := by
    have := ncard_add_ncard_compl F
    rw [← Nat.card_coe_set_eq F] at this
    rw [cycleRank]
    omega
  have := (G.edgeRestrict F).ncard_frontier_le_width π t
  have := (ncard_le_ncard hsub).trans (ncard_union_le _ _)
  rw [ncard_image_of_injective _ Subtype.val_injective, hcompl] at this
  omega

end Multigraph

/-- **The layout hypothesis with coefficient one**, in every degree: connected multigraphs of
maximum degree `d` have layouts of width at most `β₁ + d log₂ |V|`. -/
theorem layoutBound_one (d : ℕ) : LayoutBound d 1 :=
  LayoutBound.of_natLog (D := d) fun η hη => ⟨0, fun V E _ _ G hG _ hd => by
    obtain ⟨π, hπ⟩ := G.exists_width_le_cycleRank_add hG hd
    refine ⟨π, ?_⟩
    have : (G.width π : ℝ) ≤ G.cycleRank + d * Nat.log 2 (Nat.card V) := by exact_mod_cast hπ
    have := mul_nonneg hη.le (Nat.cast_nonneg (α := ℝ) G.cycleRank)
    linarith⟩

end Cslib.Circuits.Frontier
