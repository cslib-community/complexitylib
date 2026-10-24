/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Compressions of multigraphs

Laying out a multigraph of bounded degree reduces to laying out a smaller multigraph, its
*quotient* by a compression. Fix a budget `d`, at least the maximum degree. Partition the
vertices into *blocks*, each listing its vertices in order, starting from single vertices. Two
distinct blocks joined by an edge may be *merged* when at most `d` edges leave their union; the
merged block lists the longer block first. A `Compression` records the invariants of this
process:

* at most `d` edges leave a block;
* at most `d log₂ |B|` edges leave a proper prefix of a block `B`. A proper prefix of a merged
  block is a proper prefix of its first part, or all of its first part followed by a proper
  prefix of its second part, which has at most half as many vertices;
* there are at least as many blocks and edges inside blocks as vertices, since a merge loses
  one block and moves at least one edge inside.

Each merge loses a block, so merging ends in a *saturated* compression, to which no merge
applies (`Compression.exists_saturated`).

The *quotient* of a compression is the multigraph whose vertices are the blocks and whose edges
are the edges of the original multigraph between distinct blocks. By the counting invariant its
cycle rank is at most that of the original multigraph (`Compression.card_add_card_external_le`).
A layout of the quotient *expands* to a layout of the original multigraph, block by block and
each block in its own order; the frontiers of the expanded layout exceed those of the layout of
the quotient by at most `d log₂ |V|` edges (`Compression.exists_width_le`).

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.Compression`: a partition into ordered blocks, with the
  invariants of merging.
* `Cslib.Circuits.Frontier.Multigraph.Compression.Saturated`: no merge applies.
* `Cslib.Circuits.Frontier.Multigraph.Compression.quotient`: the multigraph on the blocks.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.Compression.exists_saturated`: merging terminates.
* `Cslib.Circuits.Frontier.Multigraph.Compression.ncard_edgeCut_preimage`: the cut of a union of
  whole blocks is the cut of the quotient.
* `Cslib.Circuits.Frontier.Multigraph.Compression.card_add_card_external_le`: the cycle rank of
  the quotient is at most that of the multigraph.
* `Cslib.Circuits.Frontier.Multigraph.Compression.exists_width_le`: expanding a layout of the
  quotient.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Multigraph

open Set

variable {V E : Type*}

/-- A *compression* of `G` with budget `d`: a partition of its vertices into *blocks*, each
listing its vertices in order, with the invariants maintained by merging. A block `B` is
identified with its vertex set `{v | v ∈ B}`. -/
structure Compression (G : Multigraph V E) (d : ℕ) where
  /-- The blocks. -/
  blocks : Finset (List V)
  /-- Every vertex lies in a block. -/
  exists_mem : ∀ v, ∃ B ∈ blocks, v ∈ B
  /-- Blocks sharing a vertex are equal. -/
  eq_of_mem : ∀ B ∈ blocks, ∀ B' ∈ blocks, ∀ v ∈ B, v ∈ B' → B = B'
  /-- A block lists each of its vertices once. -/
  nodup : ∀ B ∈ blocks, B.Nodup
  /-- Blocks are nonempty. -/
  ne_nil : ∀ B ∈ blocks, B ≠ []
  /-- At most `d` edges leave a block. -/
  ncard_edgeCut_le : ∀ B ∈ blocks, (G.edgeCut {v | v ∈ B}).ncard ≤ d
  /-- At most `d log₂ |B|` edges leave a proper prefix of a block `B`. -/
  ncard_edgeCut_take_le : ∀ B ∈ blocks, ∀ k < B.length,
    (G.edgeCut {v | v ∈ B.take k}).ncard ≤ d * Nat.log 2 B.length
  /-- There are at least as many blocks and edges inside blocks as vertices. -/
  card_le : Nat.card V ≤ blocks.card + {e | ∃ B ∈ blocks, G.src e ∈ B ∧ G.tgt e ∈ B}.ncard

namespace Compression

variable {G : Multigraph V E} {d : ℕ}

/-! ### Merging -/

/-- The compression into single vertices. -/
private def singletons [Fintype V] [DecidableEq V] [Finite E] (hG : G.MaxDegreeLE d) :
    Compression G d where
  blocks := Finset.univ.image fun v => [v]
  exists_mem v := ⟨[v], Finset.mem_image_of_mem _ (Finset.mem_univ v),
    List.mem_singleton_self v⟩
  eq_of_mem := by simp
  nodup := by simp
  ne_nil := by simp
  ncard_edgeCut_le := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
      forall_apply_eq_imp_iff, List.mem_singleton]
    intro v
    refine (ncard_le_ncard fun e he => ?_).trans (hG v)
    simp only [mem_edgeCut, mem_ofPred_eq] at he
    rw [mem_incidenceSet]
    tauto
  ncard_edgeCut_take_le := by simp
  card_le := by
    rw [Finset.card_image_of_injective _ List.singleton_injective, Finset.card_univ,
      Nat.card_eq_fintype_card]
    exact Nat.le_add_right _ _

variable (c : Compression G d)

/-- **Merging.** Two distinct blocks joined by an edge, with at most `d` edges leaving their
union, may be replaced by their union, listing the longer block first. -/
private theorem exists_merge [Finite E] {B B' : List V} (hB : B ∈ c.blocks) (hB' : B' ∈ c.blocks)
    (hne : B ≠ B') (hjoin : (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}).Nonempty)
    (hcut : (G.edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard ≤ d) :
    ∃ c' : Compression G d, c'.blocks.card < c.blocks.card := by
  classical
  wlog hlen : B'.length ≤ B.length generalizing B B'
  · rw [inter_comm] at hjoin
    rw [union_comm] at hcut
    exact this hB' hB hne.symm hjoin hcut (by omega)
  have hd (v : V) (hv : v ∈ B) : v ∉ B' := fun hv' => hne (c.eq_of_mem B hB B' hB' v hv hv')
  have hrest (C : List V) (hC : C ∈ c.blocks) (hCB : C ≠ B) (hCB' : C ≠ B') (v : V)
      (hv : v ∈ C) : v ∉ B ∧ v ∉ B' :=
    ⟨fun h => hCB (c.eq_of_mem C hC B hB v hv h),
      fun h => hCB' (c.eq_of_mem C hC B' hB' v hv h)⟩
  have hmem {C : List V} : C ∈ insert (B ++ B') ((c.blocks.erase B).erase B') ↔
      C = B ++ B' ∨ (C ≠ B' ∧ C ≠ B ∧ C ∈ c.blocks) := by
    simp only [Finset.mem_insert, Finset.mem_erase]
  -- Every old block lies inside a new one.
  have hsup (C : List V) (hC : C ∈ c.blocks) :
      ∃ D ∈ insert (B ++ B') ((c.blocks.erase B).erase B'), ∀ v ∈ C, v ∈ D := by
    by_cases h : C = B ∨ C = B'
    · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
      rcases h with rfl | rfl <;> intro v hv <;> simp [hv]
    · rw [not_or] at h
      exact ⟨C, hmem.2 (Or.inr ⟨h.2, h.1, hC⟩), fun v hv => hv⟩
  have hcard : (insert (B ++ B') ((c.blocks.erase B).erase B')).card + 1 = c.blocks.card := by
    have hnot : B ++ B' ∉ (c.blocks.erase B).erase B' := by
      intro h
      simp only [Finset.mem_erase] at h
      obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil B (c.ne_nil B hB)
      exact h.2.1 (c.eq_of_mem _ h.2.2 B hB v (List.mem_append_left _ hv) hv)
    rw [Finset.card_insert_of_notMem hnot, Finset.card_erase_of_mem
      (Finset.mem_erase.2 ⟨hne.symm, hB'⟩), Finset.card_erase_of_mem hB]
    have := Finset.one_lt_card.2 ⟨B, hB, B', hB', hne⟩
    omega
  have happ (L L' : List V) : {v | v ∈ L ++ L'} = {v | v ∈ L} ∪ {v | v ∈ L'} :=
    Set.ext fun _ => List.mem_append
  refine ⟨{ blocks := insert (B ++ B') ((c.blocks.erase B).erase B')
            exists_mem := ?_, eq_of_mem := ?_, nodup := ?_, ne_nil := ?_
            ncard_edgeCut_le := ?_, ncard_edgeCut_take_le := ?_, card_le := ?_ },
    Nat.lt_of_succ_le hcard.le⟩
  · intro v
    obtain ⟨C, hC, hv⟩ := c.exists_mem v
    obtain ⟨D, hD, hCD⟩ := hsup C hC
    exact ⟨D, hD, hCD v hv⟩
  · simp only [hmem]
    rintro C (rfl | ⟨hC₁, hC₂, hC⟩) C' (rfl | ⟨hC₁', hC₂', hC'⟩) v hv hv'
    · rfl
    · rw [List.mem_append] at hv
      have := hrest C' hC' hC₂' hC₁' v hv'
      tauto
    · rw [List.mem_append] at hv'
      have := hrest C hC hC₂ hC₁ v hv
      tauto
    · exact c.eq_of_mem C hC C' hC' v hv hv'
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.nodup_append.2 ⟨c.nodup B hB, c.nodup B' hB',
        fun a ha b hb hab => hd a ha (hab ▸ hb)⟩
    · exact c.nodup C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · exact List.append_ne_nil_of_left_ne_nil (c.ne_nil B hB) _
    · exact c.ne_nil C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩)
    · rwa [happ]
    · exact c.ncard_edgeCut_le C hC
  · simp only [hmem]
    rintro C (rfl | ⟨-, -, hC⟩) k hk
    · rw [List.length_append] at hk ⊢
      rw [List.take_append]
      rcases lt_or_ge k B.length with hk' | hk'
      · -- A proper prefix of the first part.
        rw [Nat.sub_eq_zero_of_le hk'.le, List.take_zero, List.append_nil]
        exact (c.ncard_edgeCut_take_le B hB k hk').trans
          (Nat.mul_le_mul_left d (Nat.log_mono_right (by omega)))
      · -- The first part followed by a proper prefix of the second, at most half as long.
        rw [List.take_of_length_le hk']
        have hb : B'.length ≠ 0 := by omega
        have h₁ := G.ncard_edgeCut_union_le {v | v ∈ B} {v | v ∈ B'.take (k - B.length)}
        have h₃ := c.ncard_edgeCut_le B hB
        have h₄ := c.ncard_edgeCut_take_le B' hB' (k - B.length) (by omega)
        have h₅ : Nat.log 2 B'.length + 1 ≤ Nat.log 2 (B.length + B'.length) := by
          rw [← Nat.log_mul_base one_lt_two hb]
          exact Nat.log_mono_right (by omega)
        have h₆ := Nat.mul_le_mul_left d h₅
        simp only [Nat.mul_add, Nat.mul_one] at h₆
        rw [happ]
        omega
    · exact c.ncard_edgeCut_take_le C hC k hk
  · -- The old inside edges and the edges joining `B` to `B'` are now inside.
    have hsub : {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D} ∪
        (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}) ⊆ {e | ∃ D ∈ insert (B ++ B')
          ((c.blocks.erase B).erase B'), G.src e ∈ D ∧ G.tgt e ∈ D} := by
      rintro e (⟨C, hC, hs, ht⟩ | ⟨h₁, h₂⟩)
      · obtain ⟨D, hD, hCD⟩ := hsup C hC
        exact ⟨D, hD, hCD _ hs, hCD _ ht⟩
      · refine ⟨B ++ B', Finset.mem_insert_self _ _, ?_⟩
        have := hd (G.src e)
        have := hd (G.tgt e)
        simp only [mem_edgeCut, mem_ofPred_eq] at h₁ h₂
        simp only [List.mem_append]
        tauto
    have hdisj : Disjoint {e | ∃ D ∈ c.blocks, G.src e ∈ D ∧ G.tgt e ∈ D}
        (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}) := by
      refine disjoint_left.2 ?_
      rintro e ⟨D, hD, hs, ht⟩ ⟨h₁, h₂⟩
      have key (C : List V) (hC : C ∈ c.blocks) (h : e ∈ G.edgeCut {v | v ∈ C}) : D = C := by
        simp only [mem_edgeCut, mem_ofPred_eq] at h
        by_cases hs' : G.src e ∈ C
        · exact c.eq_of_mem D hD C hC _ hs hs'
        · exact c.eq_of_mem D hD C hC _ ht (by tauto)
      exact hne ((key B hB h₁).symm.trans (key B' hB' h₂))
    have := ncard_le_ncard hsub
    rw [ncard_union_eq hdisj] at this
    have := hjoin.ncard_pos
    have := c.card_le
    omega

/-- A compression is *saturated* when no merge applies: more than `d` edges leave the union of
any two distinct blocks joined by an edge. -/
def Saturated : Prop :=
  ∀ B ∈ c.blocks, ∀ B' ∈ c.blocks, B ≠ B' →
    (G.edgeCut {v | v ∈ B} ∩ G.edgeCut {v | v ∈ B'}).Nonempty →
      d < (G.edgeCut ({v | v ∈ B} ∪ {v | v ∈ B'})).ncard

/-- **Merging terminates.** Every finite multigraph of maximum degree `d` has a saturated
compression with budget `d`: one with the fewest blocks. -/
theorem exists_saturated [Finite V] [Finite E] (hG : G.MaxDegreeLE d) :
    ∃ c : Compression G d, c.Saturated := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨c, -, hmin⟩ := (measure fun c : Compression G d => c.blocks.card).wf.has_min univ
    ⟨singletons hG, trivial⟩
  refine ⟨c, fun B hB B' hB' hne hjoin => ?_⟩
  by_contra! h
  obtain ⟨c', hc'⟩ := c.exists_merge hB hB' hne hjoin h
  exact hmin c' trivial hc'

/-! ### The quotient -/

/-- The block containing a vertex. -/
noncomputable def blockOf (v : V) : c.blocks :=
  ⟨(c.exists_mem v).choose, (c.exists_mem v).choose_spec.1⟩

theorem mem_blockOf (v : V) : v ∈ (c.blockOf v).1 :=
  (c.exists_mem v).choose_spec.2

theorem mem_iff_blockOf_eq {v : V} {B : c.blocks} : v ∈ B.1 ↔ c.blockOf v = B :=
  ⟨fun h => Subtype.ext (c.eq_of_mem _ (c.blockOf v).2 _ B.2 v (c.mem_blockOf v) h),
    fun h => h ▸ c.mem_blockOf v⟩

/-- The vertices of a block are those it contains. -/
private theorem preimage_blockOf_singleton (B : c.blocks) : c.blockOf ⁻¹' {B} = {v | v ∈ B.1} := by
  ext v
  simp [c.mem_iff_blockOf_eq]

/-- Distinct blocks are disjoint. -/
theorem disjoint_of_ne {B B' : c.blocks} (h : B ≠ B') :
    Disjoint {v | v ∈ B.1} {v | v ∈ B'.1} :=
  disjoint_left.mpr fun _ hv hv' =>
    h ((c.mem_iff_blockOf_eq.mp hv).symm.trans (c.mem_iff_blockOf_eq.mp hv'))

theorem mem_edgeCut_block {B : c.blocks} {e : E} :
    e ∈ G.edgeCut {v | v ∈ B.1} ↔ ¬(c.blockOf (G.src e) = B ↔ c.blockOf (G.tgt e) = B) := by
  simp only [mem_edgeCut, mem_ofPred_eq, c.mem_iff_blockOf_eq]

/-- An edge leaving a block leaves another block too. -/
theorem exists_ne_mem_edgeCut {B : c.blocks} {e : E} (he : e ∈ G.edgeCut {v | v ∈ B.1}) :
    ∃ B' : c.blocks, B' ≠ B ∧ e ∈ G.edgeCut {v | v ∈ B'.1} := by
  rw [mem_edgeCut_block] at he
  by_cases hs : c.blockOf (G.src e) = B
  · refine ⟨c.blockOf (G.tgt e), fun h => he (iff_of_true hs h), ?_⟩
    rw [mem_edgeCut_block]
    grind
  · refine ⟨c.blockOf (G.src e), hs, ?_⟩
    rw [mem_edgeCut_block]
    grind

/-- In a connected multigraph, some edge leaves each block, unless there is only one. -/
theorem edgeCut_nonempty (hG : G.toSimpleGraph.Connected) (two : 1 < Nat.card c.blocks)
    (B : c.blocks) : (G.edgeCut {v | v ∈ B.1}).Nonempty := by
  have := Finite.one_lt_card_iff_nontrivial.mp two
  obtain ⟨B', hB'⟩ := exists_ne B
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B.2)
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (c.ne_nil _ B'.2)
  refine Multigraph.edgeCut_nonempty hG (S := {v | v ∈ B.1}) (v := w) hu fun h => hB' ?_
  rw [mem_ofPred_eq, c.mem_iff_blockOf_eq] at h
  rw [c.mem_iff_blockOf_eq] at hw
  exact hw.symm.trans h

/-- The *external* edges: those between distinct blocks. -/
def external : Set E :=
  {e | c.blockOf (G.src e) ≠ c.blockOf (G.tgt e)}

/-- The edges outside the external edges are those inside a block. -/
private theorem compl_external : c.externalᶜ = {e | ∃ B ∈ c.blocks, G.src e ∈ B ∧ G.tgt e ∈ B} := by
  ext e
  simp only [external, mem_compl_iff, mem_ofPred_eq, not_not]
  constructor
  · intro h
    exact ⟨_, (c.blockOf (G.src e)).2, c.mem_blockOf _, h ▸ c.mem_blockOf _⟩
  · rintro ⟨B, hB, hs, ht⟩
    rw [(c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 hs, (c.mem_iff_blockOf_eq (B := ⟨B, hB⟩)).1 ht]

/-- The *quotient* of a compression: the multigraph whose vertices are the blocks and whose
edges are the external edges, each joining the blocks of its endpoints. -/
noncomputable def quotient : Multigraph c.blocks c.external where
  src e := c.blockOf (G.src e.1)
  tgt e := c.blockOf (G.tgt e.1)

@[simp] theorem quotient_src (e : c.external) : c.quotient.src e = c.blockOf (G.src e.1) :=
  rfl

@[simp] theorem quotient_tgt (e : c.external) : c.quotient.tgt e = c.blockOf (G.tgt e.1) :=
  rfl

theorem quotient_loopless : c.quotient.Loopless :=
  fun e => e.2

/-- The cut of a union of whole blocks consists of the edges of the cut of the quotient. -/
private theorem edgeCut_preimage (T : Set c.blocks) :
    G.edgeCut (c.blockOf ⁻¹' T) = Subtype.val '' c.quotient.edgeCut T := by
  ext e
  simp only [mem_edgeCut, mem_preimage, mem_image, Subtype.exists, exists_and_right,
    exists_eq_right, quotient_src, quotient_tgt]
  constructor
  · intro h
    exact ⟨fun h' => h (by rw [h']), h⟩
  · exact fun ⟨_, h⟩ => h

/-- **Cuts of unions of whole blocks** are cuts of the quotient. -/
theorem ncard_edgeCut_preimage (T : Set c.blocks) :
    (G.edgeCut (c.blockOf ⁻¹' T)).ncard = (c.quotient.edgeCut T).ncard := by
  rw [c.edgeCut_preimage, ncard_image_of_injective _ Subtype.val_injective]

/-- The edges at a block of the quotient are the edges leaving the block. -/
theorem ncard_incidenceSet_quotient (B : c.blocks) :
    (c.quotient.incidenceSet B).ncard = (G.edgeCut {v | v ∈ B.1}).ncard := by
  rw [← edgeCut_singleton _ c.quotient_loopless, ← c.ncard_edgeCut_preimage,
    c.preimage_blockOf_singleton]

theorem quotient_maxDegreeLE [Finite E] : c.quotient.MaxDegreeLE d := fun B =>
  (c.ncard_incidenceSet_quotient B).trans_le (c.ncard_edgeCut_le _ B.2)

/-- The cuts of the blocks count every external edge twice. -/
theorem sum_ncard_edgeCut [Finite E] :
    ∑ B : c.blocks, (G.edgeCut {v | v ∈ B.1}).ncard = 2 * Nat.card c.external := by
  simp only [← c.ncard_incidenceSet_quotient]
  exact c.quotient.sum_ncard_incidenceSet c.quotient_loopless

/-- **The quotient is no more cyclic than the multigraph**: `|V| - |B| ≤ |E| - |E_B|`, where
`B` is the set of blocks and `E_B` the set of external edges. -/
theorem card_add_card_external_le [Finite E] :
    Nat.card V + Nat.card c.external ≤ Nat.card c.blocks + Nat.card E := by
  have h := ncard_add_ncard_compl c.external
  rw [c.compl_external] at h
  have := c.card_le
  rw [Nat.card_coe_set_eq, Nat.card_eq_finsetCard]
  omega

/-! ### Expansion -/

/-- **Expansion.** Lay out the vertices block by block, ordering the blocks by a layout `σ` of
the quotient and each block by its list. Each frontier consists of whole blocks, which are cut
by a frontier of `σ`, and a proper prefix of one more block. So the width exceeds that of `σ`
by at most `d log₂ |V|`. -/
theorem exists_width_le [Finite V] [Finite E] (σ : Layout c.blocks) :
    ∃ π : Layout V, G.width π ≤ c.quotient.width σ + d * Nat.log 2 (Nat.card V) := by
  classical
  have := Fintype.ofFinite V
  let f (v : V) : ℕ ×ₗ ℕ := toLex ((σ (c.blockOf v) : ℕ), (c.blockOf v).1.idxOf v)
  have hσ {B B' : c.blocks} : (σ B : ℕ) = σ B' ↔ B = B' :=
    Fin.val_inj.trans σ.injective.eq_iff
  have hf : f.Injective := by
    intro v w h
    simp only [f, toLex_inj, Prod.mk.injEq, hσ] at h
    obtain ⟨hb, hi⟩ := h
    rw [hb] at hi
    exact (List.idxOf_inj (c.mem_iff_blockOf_eq.2 hb)).1 hi
  obtain ⟨π, hπ⟩ := Layout.exists_lt_iff hf
  refine ⟨π, Finset.sup_le fun t ht => ?_⟩
  have ht := Finset.mem_range.mp ht
  set w := π.symm ⟨t, ht⟩
  set B := c.blockOf w
  -- The frontier: the blocks before that of `w`, and the vertices of its block before `w`.
  have hL : π.initial t =
      c.blockOf ⁻¹' σ.initial (σ B) ∪ {v | v ∈ B.1.take (B.1.idxOf w)} := by
    rw [Layout.initial_eq_of_lt_iff hπ ht]
    ext v
    simp only [f, mem_ofPred_eq, mem_union, mem_preimage, Layout.mem_initial,
      Prod.Lex.toLex_lt_toLex, hσ]
    refine or_congr Iff.rfl ⟨fun ⟨hb, hi⟩ => ?_, fun hv => ?_⟩
    · rw [hb] at hi
      exact (List.mem_take_iff_idxOf_lt (c.mem_iff_blockOf_eq.2 hb)).2 hi
    · have hb := c.mem_iff_blockOf_eq.1 (List.mem_of_mem_take hv)
      refine ⟨hb, ?_⟩
      rw [hb]
      exact (List.mem_take_iff_idxOf_lt (List.mem_of_mem_take hv)).1 hv
  have hwhole : (G.edgeCut (c.blockOf ⁻¹' σ.initial (σ B))).ncard ≤ c.quotient.width σ := by
    rw [c.ncard_edgeCut_preimage]
    exact c.quotient.ncard_frontier_le_width σ _
  have hpart : (G.edgeCut {v | v ∈ B.1.take (B.1.idxOf w)}).ncard ≤
      d * Nat.log 2 (Nat.card V) := by
    refine (c.ncard_edgeCut_take_le _ B.2 _ (List.idxOf_lt_length_of_mem
      (c.mem_blockOf w))).trans (Nat.mul_le_mul_left d (Nat.log_mono_right ?_))
    rw [Nat.card_eq_fintype_card]
    exact (c.nodup _ B.2).length_le_card
  rw [frontier, hL]
  exact (G.ncard_edgeCut_union_le _ _).trans (Nat.add_le_add hwhole hpart)

end Compression

end Cslib.Circuits.Frontier.Multigraph
