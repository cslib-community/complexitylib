/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Compression
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# From cubic graphs to subcubic multigraphs

The circuits of fan-in two give subcubic multigraphs, so the layout hypothesis that matters most
is `LayoutBound 3 A`. This file reduces it to laying out cubic graphs, those without loops or
parallel edges in which every vertex has exactly three edges.

`CubicLayoutBound c` says that for every `ξ > 0`, every large enough cubic graph on `h` vertices
has a layout of width at most `(c + ξ) h`. A connected cubic graph on `h` vertices has cycle rank
`h/2 + 1`, which is why a cubic coefficient `c` becomes the layout coefficient `2c`
(`LayoutBound.of_cubic`).

**The quotient.** Let `G` be a connected multigraph of maximum degree three, with `N` vertices,
`M` edges and cycle rank `β₁ = M - N + 1`, and take a saturated compression of `G` with budget
three. Two distinct blocks are joined by at most one edge, and if there are at least two blocks
then exactly three edges leave each block: by connectivity, a block with fewer would merge with
a neighbour. So the quotient is a cubic graph. Its `h` vertices span `3h/2` edges, and the
counting invariant of compressions gives `h + 2N ≤ 2M`, so the quotient has at most `2 β₁`
vertices (`Saturated.card_blocks_le`).

**The bound.** Given `η > 0`, take the cubic bound with slack `ξ = η/2`. A quotient on `h > N₀`
vertices has a layout of width at most `(c + ξ) h ≤ (2c + η) β₁`, and a quotient on at most
`N₀ + 1` vertices has at most `3 (N₀ + 1)` edges. Expanding the layout of the quotient costs at
most `3 log₂ N` more edges at each frontier, which is at most `η N` plus a constant.

## Main definitions

* `Cslib.Circuits.Frontier.CubicLayoutBound`: the layout hypothesis for cubic graphs.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.injective_ends_quotient`,
  `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.ncard_incidenceSet_quotient`: the
  quotient of a saturated compression with budget three is a cubic graph.
* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le`: it has at most
  `2 β₁` vertices.
* `Cslib.Circuits.Frontier.LayoutBound.of_cubic`: the cubic layout bound with coefficient `c`
  gives the layout hypothesis for maximum degree three with coefficient `2c`.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- **The cubic layout bound** with coefficient `c`: for every `ξ > 0`, every large enough cubic
graph on `h` vertices has a layout of width at most `(c + ξ) h`. A cubic graph is presented as a
multigraph without loops or parallel edges in which every vertex has exactly three edges. -/
def CubicLayoutBound (c : ℝ) : Prop :=
  ∀ ξ > 0, ∃ N₀ : ℕ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
    G.Loopless → Function.Injective G.ends → (∀ v, (G.incidenceSet v).ncard = 3) →
      N₀ < Nat.card V → ∃ π : Layout V, (G.width π : ℝ) ≤ (c + ξ) * Nat.card V

namespace Multigraph.Compression

variable {V E : Type*} {G : Multigraph V E} {c : Compression G 3}

/-- In a saturated compression with budget three, two distinct blocks are joined by at most one
edge. -/
private theorem Saturated.ncard_edgeCut_inter_le_one [Finite E] (hc : c.Saturated) {B B' : c.blocks}
    (hne : B ≠ B') : (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).ncard ≤ 1 := by
  rcases (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).eq_empty_or_nonempty with h | h
  · simp [h]
  have := hc _ B.2 _ B'.2 (fun h => hne (Subtype.ext h)) h
  have := G.ncard_edgeCut_union_add (c.disjoint_of_ne hne)
  have := c.ncard_edgeCut_le _ B.2
  have := c.ncard_edgeCut_le _ B'.2
  omega

/-- In a saturated compression with budget three of a connected multigraph into at least two
blocks, exactly three edges leave each block. -/
private theorem Saturated.ncard_edgeCut_eq_three [Finite E] (hc : c.Saturated)
    (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) (B : c.blocks) :
    (G.edgeCut {v | v ∈ B.1}).ncard = 3 := by
  obtain ⟨e, he⟩ := c.edgeCut_nonempty hG two B
  obtain ⟨B', hB'B, he'⟩ := c.exists_ne_mem_edgeCut he
  have hjoin : (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).Nonempty := ⟨e, he, he'⟩
  have := hc _ B.2 _ B'.2 (fun h => hB'B (Subtype.ext h).symm) hjoin
  have := G.ncard_edgeCut_union_add (c.disjoint_of_ne hB'B.symm)
  have := hjoin.ncard_pos
  have := c.ncard_edgeCut_le _ B.2
  have := c.ncard_edgeCut_le _ B'.2
  omega

/-- The quotient of a saturated compression with budget three has no parallel edges. -/
theorem Saturated.injective_ends_quotient [Finite E] (hc : c.Saturated) :
    Function.Injective c.quotient.ends := by
  intro e e' h
  have hne : c.blockOf (G.src e.1) ≠ c.blockOf (G.tgt e.1) := e.2
  -- Both edges join the blocks of the endpoints of `e`.
  have hmem (f : c.external) (hf : c.quotient.ends f = c.quotient.ends e) :
      f.1 ∈ G.edgeCut {v | v ∈ (c.blockOf (G.src e.1)).1} ∩
        G.edgeCut {v | v ∈ (c.blockOf (G.tgt e.1)).1} := by
    simp only [ends, quotient_src, quotient_tgt, Sym2.eq_iff] at hf
    simp only [mem_inter_iff, mem_edgeCut_block]
    grind
  exact Subtype.ext ((ncard_le_one (toFinite _)).mp (hc.ncard_edgeCut_inter_le_one hne) _
    (hmem e rfl) _ (hmem e' h.symm))

/-- The quotient of a saturated compression with budget three of a connected multigraph into at
least two blocks is cubic. -/
theorem Saturated.ncard_incidenceSet_quotient [Finite E] (hc : c.Saturated)
    (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) (B : c.blocks) :
    (c.quotient.incidenceSet B).ncard = 3 :=
  (c.ncard_incidenceSet_quotient B).trans (hc.ncard_edgeCut_eq_three hG two B)

/-- **The size of the quotient.** A saturated compression with budget three of a connected
multigraph into at least two blocks has at most `2 β₁` blocks. -/
theorem Saturated.card_blocks_le [Finite E] (hc : c.Saturated)
    (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) :
    Nat.card c.blocks ≤ 2 * G.cycleRank := by
  have hsum := c.sum_ncard_edgeCut
  simp only [hc.ncard_edgeCut_eq_three hG two, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] at hsum
  have := c.card_add_card_external_le
  rw [cycleRank]
  omega

end Multigraph.Compression

/-- **From cubic graphs to subcubic multigraphs.** The cubic layout bound with coefficient `c`
gives the layout hypothesis for maximum degree three with coefficient `2c`. -/
theorem LayoutBound.of_cubic {c : ℝ} (hc : 0 ≤ c) (h : CubicLayoutBound c) :
    LayoutBound 3 (2 * c) := by
  refine LayoutBound.of_natLog (D := 3) fun η hη => ?_
  obtain ⟨N₀, hN₀⟩ := h (η / 2) (by positivity)
  refine ⟨3 * (N₀ + 1), fun V E _ _ G hG _ hdeg => ?_⟩
  obtain ⟨Q, hQ⟩ := Multigraph.Compression.exists_saturated hdeg
  have hβ : 0 ≤ (2 * c + η) * G.cycleRank := by positivity
  -- A layout of the quotient.
  obtain ⟨σ, hσ⟩ : ∃ σ : Layout Q.blocks,
      (Q.quotient.width σ : ℝ) ≤ (2 * c + η) * G.cycleRank + 3 * (N₀ + 1) := by
    by_cases hbig : 1 < Nat.card Q.blocks ∧ N₀ < Nat.card Q.blocks
    · -- A large quotient is laid out by the cubic layout bound.
      obtain ⟨σ, hσ⟩ := hN₀ Q.blocks Q.external Q.quotient Q.quotient_loopless
        hQ.injective_ends_quotient (hQ.ncard_incidenceSet_quotient hG hbig.1) hbig.2
      refine ⟨σ, hσ.trans ?_⟩
      have : (Nat.card Q.blocks : ℝ) ≤ 2 * G.cycleRank := by
        exact_mod_cast hQ.card_blocks_le hG hbig.1
      nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ c + η / 2)]
    · -- A small quotient has few edges.
      refine ⟨Classical.arbitrary _, ?_⟩
      have hw := Q.quotient.width_le_card (Classical.arbitrary _)
      have hsum := Q.sum_ncard_edgeCut
      have hle : ∑ B : Q.blocks, (G.edgeCut {v | v ∈ B.1}).ncard ≤ ∑ _B : Q.blocks, 3 :=
        Finset.sum_le_sum fun B _ => Q.ncard_edgeCut_le _ B.2
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hle
      have : Q.quotient.width (Classical.arbitrary _) ≤ 3 * (N₀ + 1) := by omega
      have : (Q.quotient.width (Classical.arbitrary _) : ℝ) ≤ 3 * (N₀ + 1) := by
        exact_mod_cast this
      linarith
  obtain ⟨π, hπ⟩ := Q.exists_width_le σ
  refine ⟨π, ?_⟩
  have : (G.width π : ℝ) ≤ Q.quotient.width σ + 3 * Nat.log 2 (Nat.card V) := by
    exact_mod_cast hπ
  push_cast
  linarith

end Cslib.Circuits.Frontier
