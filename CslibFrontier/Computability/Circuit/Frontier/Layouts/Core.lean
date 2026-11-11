/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Compression
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# The density of the core of a saturated compression

Let `G` be a connected multigraph of maximum degree `d`, with `N` vertices, `M` edges and cycle
rank `β₁ = M - N + 1`, and let a saturated compression of `G` with budget `d` have at least two
blocks. Its quotient, the *core*, is a loopless multigraph of maximum degree `d` in which:

* the ends of every edge have at least `d + 3` edges between them, counted with multiplicity,
  since more than `d` edges leave their union and the edges between them are counted twice
  (`Saturated.add_three_le_ncard_incidenceSet_quotient`);
* hence every block has at least three edges
  (`Saturated.three_le_ncard_incidenceSet_quotient`).

By the density of cores (`Cslib.Circuits.Frontier.Multigraph.core_density`),
`3 d |blocks| ≤ (d + 3) |E(core)|`, and with the counting invariant of compressions,
`|E(core)| - |blocks| ≤ β₁ - 1`, this gives `(2d - 3) |E(core)| ≤ 3 d β₁`
(`Saturated.mul_card_external_le`).

## Main results

* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.three_le_ncard_incidenceSet_quotient`:
  the blocks of the core have at least three edges.
* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.card_blocks_le_card_external`: the
  core has at least as many edges as blocks.
* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated.mul_card_external_le`: the core has
  at most `3 d β₁ / (2d - 3)` edges.
-/

public section

namespace Cslib.Circuits.Frontier.Multigraph.Compression

open Set

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} {c : Compression G d}

/-- An edge leaving a block is external. -/
theorem mem_external_of_mem_edgeCut {B : c.blocks} {e : E} (he : e ∈ G.edgeCut {v | v ∈ B.1}) :
    e ∈ c.external := by
  rw [mem_edgeCut_block] at he
  intro h
  exact he (by rw [h])

/-- In a saturated compression, the ends of an edge of the quotient have at least `d + 3` edges
between them: more than `d` edges leave their union, and the edges between them are counted
twice. The relevant cuts are finite because saturation bounds their unions from below. -/
theorem Saturated.add_three_le_ncard_incidenceSet_quotient (hc : c.Saturated) (e : c.external) :
    d + 3 ≤ (c.quotient.incidenceSet (c.quotient.src e)).ncard +
      (c.quotient.incidenceSet (c.quotient.tgt e)).ncard := by
  set B := c.quotient.src e
  set B' := c.quotient.tgt e
  have hne : B ≠ B' := e.2
  have hjoin : (G.edgeCut {v | v ∈ B.1} ∩ G.edgeCut {v | v ∈ B'.1}).Nonempty := by
    refine ⟨e.1, ?_, ?_⟩ <;> rw [mem_edgeCut_block]
    · exact fun h => hne (h.mp rfl).symm
    · exact fun h => hne (h.mpr rfl)
  have hlt := hc _ B.2 _ B'.2 (fun h => hne (Subtype.ext h)) hjoin
  -- Some edge `f` leaves `B ∪ B'`, joining a block `Y ∈ {B, B'}` to a block `C ∉ {B, B'}`.
  obtain ⟨f, hf⟩ := nonempty_of_ncard_ne_zero (s := G.edgeCut ({v | v ∈ B.1} ∪ {v | v ∈ B'.1}))
    (by omega)
  simp only [mem_edgeCut, mem_union, mem_ofPred_eq, c.mem_iff_blockOf_eq] at hf
  obtain ⟨Y, C, hY, hCB, hCB', hYC⟩ : ∃ Y C : c.blocks, (Y = B ∨ Y = B') ∧ C ≠ B ∧ C ≠ B' ∧
      (G.edgeCut {v | v ∈ Y.1} ∩ G.edgeCut {v | v ∈ C.1}).Nonempty := by
    by_cases hs : c.blockOf (G.src f) = B ∨ c.blockOf (G.src f) = B'
    · refine ⟨c.blockOf (G.src f), c.blockOf (G.tgt f), hs, fun h => ?_, fun h => ?_, f, ?_, ?_⟩ <;>
        (try rw [mem_edgeCut_block]) <;> grind
    · refine ⟨c.blockOf (G.tgt f), c.blockOf (G.src f), by tauto, fun h => hs (.inl h),
        fun h => hs (.inr h), f, ?_, ?_⟩ <;> rw [mem_edgeCut_block] <;> grind
  -- The cuts of `B` and `B'` lie in two cuts bounded by saturation, so they are finite.
  have hYC' := hc _ Y.2 _ C.2 (fun h => by grind [Subtype.ext h]) hYC
  have hfin : (G.edgeCut {v | v ∈ B.1} ∪ G.edgeCut {v | v ∈ B'.1}).Finite := by
    refine ((finite_of_ncard_ne_zero (s := G.edgeCut ({v | v ∈ B.1} ∪ {v | v ∈ B'.1}))
      (by omega)).union (finite_of_ncard_ne_zero (s := G.edgeCut ({v | v ∈ Y.1} ∪ {v | v ∈ C.1}))
      (by omega))).subset fun g hg => ?_
    simp only [mem_edgeCut, mem_union, mem_ofPred_eq, c.mem_iff_blockOf_eq] at hg ⊢
    rcases hY with rfl | rfl <;> grind
  have hsum := G.ncard_edgeCut_union_add (c.disjoint_of_ne hne)
    (hfin.subset subset_union_left) (hfin.subset subset_union_right)
  have hpos := (ncard_pos (hfin.subset (inter_subset_left.trans subset_union_left))).mpr hjoin
  rw [c.ncard_incidenceSet_quotient, c.ncard_incidenceSet_quotient]
  omega

variable [Finite E]

/-- In a saturated compression of a connected multigraph into at least two blocks, every block
has at least three edges in the quotient. -/
theorem Saturated.three_le_ncard_incidenceSet_quotient (hc : c.Saturated)
    (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) (B : c.blocks) :
    3 ≤ (c.quotient.incidenceSet B).ncard := by
  obtain ⟨e, he⟩ := c.edgeCut_nonempty hG two B
  let e' : c.external := ⟨e, mem_external_of_mem_edgeCut he⟩
  have hsum := hc.add_three_le_ncard_incidenceSet_quotient e'
  have hs := c.quotient_maxDegreeLE (c.quotient.src e')
  have ht := c.quotient_maxDegreeLE (c.quotient.tgt e')
  have hi : c.quotient.src e' = B ∨ c.quotient.tgt e' = B := by
    grind [mem_edgeCut_block, quotient_src, quotient_tgt]
  rcases hi with h | h <;> rw [h] at hsum <;> omega

/-- A saturated compression of a connected multigraph into at least two blocks has at least as
many external edges as blocks. -/
theorem Saturated.card_blocks_le_card_external (hc : c.Saturated)
    (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks) :
    Nat.card c.blocks ≤ Nat.card c.external := by
  have hsum := c.quotient.sum_ncard_incidenceSet c.quotient_loopless
  have hmin := Finset.sum_le_sum (s := Finset.univ)
    fun B _ => hc.three_le_ncard_incidenceSet_quotient hG two B
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card] at hmin
  omega

/-- **The density of the core.** A saturated compression with budget `d` of a connected
multigraph into at least two blocks has at most `3 d / (2d - 3)` times the cycle rank of the
multigraph external edges: `(2d - 3) |E(core)| ≤ 3 d β₁`. -/
theorem Saturated.mul_card_external_le (hc : c.Saturated) (hG : G.toSimpleGraph.Connected)
    (two : 1 < Nat.card c.blocks) :
    (2 * d - 3) * Nat.card c.external ≤ 3 * d * G.cycleRank := by
  classical
  have := Fintype.ofFinite c.external
  have hdens := Multigraph.core_density c.quotient_loopless
    (hc.three_le_ncard_incidenceSet_quotient hG two) c.quotient_maxDegreeLE
    hc.add_three_le_ncard_incidenceSet_quotient
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at hdens
  have hcard := c.card_add_card_external_le
  have hconn := G.card_le_card_add_one_of_connected hG
  have hβ : Nat.card E + 1 ≤ G.cycleRank + Nat.card V := by grind [cycleRank]
  -- Some block of the core has between three and `d` edges, so `d = k + 3`.
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := by
    obtain ⟨B⟩ := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card c.blocks)).1
    have h3 := (hc.three_le_ncard_incidenceSet_quotient hG two B).trans
      (c.quotient_maxDegreeLE B)
    exact ⟨d - 3, by omega⟩
  rw [show 2 * (k + 3) - 3 = 2 * k + 3 by omega]
  -- Multiply the counting invariant and the cycle rank by `3 d`, and add the density.
  have h₁ := Nat.mul_le_mul_left (3 * (k + 3)) hcard
  have h₂ := Nat.mul_le_mul_left (3 * (k + 3)) hβ
  nlinarith

end Cslib.Circuits.Frontier.Multigraph.Compression
