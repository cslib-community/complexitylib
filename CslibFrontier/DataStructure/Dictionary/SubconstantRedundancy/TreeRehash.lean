/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeBuild

/-!
# Localized Subtree Rehashing (`Algorithm 4`) in the Multi-Level Dictionary Tree

This file formalizes localized subtree rehashing (`Algorithm 4`, `Rehash(u)`) of Tianxiao Li,
Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per
Key* ([LiLiangYuZhou2024, Section 5.5, Algorithm 4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 34 / printed p. 33).

When node `(ℓ₀, u₀)` (`0 ≤ ℓ₀ ≤ depth`) is rehashed with resampled subtree seeds `seeds'`
agreeing with `st.seeds` outside `InSubtree ℓ₀ u₀`, `rehashSubtree` reconstructs `InSubtree ℓ₀ u₀`,
updates only the `ℓ₀ - 1` strict ancestor nodes `(j, ancestorAt u₀)` (`1 ≤ j < ℓ₀`), and leaves all
other root trees and sibling subtrees untouched.

## Main definitions

* `TreeSchedule.TreeState.rehashSubtree`: localized subtree reconstruction (`Algorithm 4`).

## Main results

* `TreeSchedule.TreeState.seeds_rehashSubtree`, `TreeSchedule.TreeState.sentCount_rehashSubtree`:
  exact seed assignment and sentinel-count preservation.
* `TreeSchedule.TreeState.rehashSubtree_untouched_roots`,
  `TreeSchedule.TreeState.rehashSubtree_untouched_inner`,
  `TreeSchedule.TreeState.rehashSubtree_untouched_leaves`: strict locality outside `u₀`'s subtree
  and ancestor path.
* `TreeSchedule.TreeState.wellFormedPadded_rehashSubtree`: preservation of `WellFormedPadded`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

namespace TreeSchedule.TreeState

variable {P : TreeSchedule}

private theorem card_wait_rehash_eq
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    let S := P.paddedDom d
    let A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
    let canonLvl := canonicalStoreLvl seeds' S hgood'
    (A₀.filter fun w => storeLvl w < ℓ₀).card = (A₀.filter fun w => canonLvl w < ℓ₀).card := by
  intro S A₀ canonLvl
  have hwf_canon := P.wellFormedPadded_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hseeds_canon := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hact₀ : A₀ = st.seeds.activeAt S ℓ₀ hℓ₀ u₀ := by
    ext x
    simp only [A₀, SeedAssignment.mem_activeAt_iff,
      (SeedAssignment.primCoordAt_congr_ancestors hℓ₀ u₀
        (fun j hj => houtside j (hj.le.trans hℓ₀) _ fun ⟨hge, _⟩ => by omega) x).1]
  have hp1 := card_filter_add_card_filter_not (s := A₀) (p := fun w => storeLvl w < ℓ₀)
  have hp2 := card_filter_add_card_filter_not (s := A₀) (p := fun w => canonLvl w < ℓ₀)
  have hn1 : (A₀.filter fun w => ¬ storeLvl w < ℓ₀) =
      (st.seeds.activeAt S ℓ₀ hℓ₀ u₀).filter fun w => ℓ₀ ≤ storeLvl w := by
    rw [hact₀]; exact filter_congr fun _ _ => by omega
  have hn2 : (A₀.filter fun w => ¬ canonLvl w < ℓ₀) =
      ((P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood').seeds.activeAt
        S ℓ₀ hℓ₀ u₀).filter fun w => ℓ₀ ≤ canonLvl w := by
    dsimp only [A₀]; rw [hseeds_canon]; exact filter_congr fun _ _ => by omega
  rw [hn1, subtree_stored_card_eq_nLow hwf h2₀ hℓ₀ u₀] at hp1
  rw [hn2, subtree_stored_card_eq_nLow hwf_canon h2₀ hℓ₀ u₀] at hp2
  omega

private noncomputable def rehashWaitEquiv
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    { w // w ∈ (seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter fun w => storeLvl w < ℓ₀ } ≃
    { w // w ∈ (seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
      fun w => canonicalStoreLvl seeds' (P.paddedDom d) hgood' w < ℓ₀ } :=
  (((seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
    fun w => storeLvl w < ℓ₀).orderIsoOfFin rfl).toEquiv.symm.trans
    (((seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀).filter
      fun w => canonicalStoreLvl seeds' (P.paddedDom d) hgood' w < ℓ₀).orderIsoOfFin
      (card_wait_rehash_eq hwf h2₀ hℓ₀ u₀ houtside hgood').symm).toEquiv

private noncomputable def rehashStoreLvlTwo
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) : Fin P.paddedUniv → ℕ :=
  let S := P.paddedDom d
  let A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
  let canonLvl := canonicalStoreLvl seeds' S hgood'
  let φ := rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood'
  fun x =>
    if hxA : x ∈ A₀ then
      if hlt_c : canonLvl x < ℓ₀ then
        storeLvl (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).1
      else canonLvl x
    else storeLvl x

private theorem notMem_A0_of_not_anc_not_sub
    {S : Finset (Fin P.paddedUniv)} {ℓ₀ : ℕ} (hℓ₀ : ℓ₀ ≤ P.depth)
    (u₀ : Fin (P.numNodes ℓ₀)) {seeds' : P.SeedAssignment}
    {j : ℕ} (hj : j ≤ P.depth) (v : Fin (P.numNodes j))
    (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ j v)
    (hnot_anc : ¬ ∃ hlt : j < ℓ₀, v = P.ancestorAt hlt.le u₀)
    {x : Fin P.paddedUniv} (hx : x ∈ seeds'.activeAt S j hj v) :
    x ∉ seeds'.activeAt S ℓ₀ hℓ₀ u₀ := by
  intro hxA
  have hnv : seeds'.nodeAt j hj x = v := (SeedAssignment.mem_activeAt_iff.mp hx).2
  have hnu₀ : seeds'.nodeAt ℓ₀ hℓ₀ x = u₀ := (SeedAssignment.mem_activeAt_iff.mp hxA).2
  by_cases hlt : j < ℓ₀
  · refine hnot_anc ⟨hlt, ?_⟩
    rw [← hnv, ← hnu₀, (seeds'.ancestorAt_nodeAt hlt.le hℓ₀ x).symm]
  · have h0j : ℓ₀ ≤ j := by omega
    refine hnot_sub ⟨h0j, ?_⟩
    rw [← hnv, seeds'.ancestorAt_nodeAt h0j hj x, hnu₀]

private theorem rehashStoreLvlTwo_ge_iff
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    {x : Fin P.paddedUniv} (hxA : x ∈ seeds'.activeAt (P.paddedDom d) ℓ₀ hℓ₀ u₀)
    {j : ℕ} (hj : ℓ₀ ≤ j) :
    (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x = j ↔
      canonicalStoreLvl seeds' (P.paddedDom d) hgood' x = j) ∧
    (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood' x < j ↔
      canonicalStoreLvl seeds' (P.paddedDom d) hgood' x < j) := by
  dsimp only [rehashStoreLvlTwo]
  rw [dite_eq_left hxA]
  by_cases hlt_c : canonicalStoreLvl seeds' (P.paddedDom d) hgood' x < ℓ₀
  · rw [dite_eq_left hlt_c]
    set y_sub := (rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood').symm
      ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩
    have hy_lt : storeLvl y_sub.1 < ℓ₀ := (mem_filter.mp y_sub.2).2
    exact ⟨⟨fun h => by omega, fun h => by omega⟩, ⟨fun _ => by omega, fun _ => by omega⟩⟩
  · rw [dite_eq_right hlt_c]
    exact ⟨Iff.rfl, Iff.rfl⟩

private theorem validStoreLvl_rehashStoreLvlTwo
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    {seeds' : P.SeedAssignment}
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    ValidStoreLvl seeds' (P.paddedDom d)
      (rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood') := by
  set S := P.paddedDom d
  set A₀ := seeds'.activeAt S ℓ₀ hℓ₀ u₀
  set canonLvl := canonicalStoreLvl seeds' S hgood'
  set U_old := A₀.filter fun w => storeLvl w < ℓ₀
  let φ := rehashWaitEquiv hwf h2₀ hℓ₀ u₀ houtside hgood'
  set storeLvl' := rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
  have hvsl_old := ValidStoreLvl.of_wellFormedPadded hwf
  have hvsl_can := validStoreLvl_canonicalStoreLvl seeds' S hgood'
  have hact_outside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.activeAt S j hj v = st.seeds.activeAt S j hj v := by
    intro j hj v hnot; ext x
    simp only [SeedAssignment.mem_activeAt_iff,
      (SeedAssignment.primCoordAt_congr_ancestors hj v
        (fun i hi => houtside i (hi.le.trans hj) _
          (P.not_inSubtree_ancestor_of_not_inSubtree hi.le hnot)) x).1]
  have hact₀ : A₀ = st.seeds.activeAt S ℓ₀ hℓ₀ u₀ := by
    ext x
    simp only [A₀, SeedAssignment.mem_activeAt_iff,
      (SeedAssignment.primCoordAt_congr_ancestors hℓ₀ u₀
        (fun i hi => houtside i (hi.le.trans hℓ₀) _ fun ⟨hge, _⟩ => by omega) x).1]
  refine
    { bounds := fun x hx => by
        dsimp only [storeLvl', rehashStoreLvlTwo]
        by_cases hxA : x ∈ A₀
        · rw [dite_eq_left hxA]
          by_cases hlt_c : canonLvl x < ℓ₀
          · rw [dite_eq_left hlt_c]
            have hyS : (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).1 ∈ S :=
              (SeedAssignment.mem_activeAt_iff.mp
                (mem_filter.mp (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).2).1).1
            exact hvsl_old.bounds _ hyS
          · rw [dite_eq_right hlt_c]; exact hvsl_can.bounds x hx
        · rw [dite_eq_right hxA]; exact hvsl_old.bounds x hx
      outside := fun x hx => by
        have hxA : x ∉ A₀ := fun hm => hx (SeedAssignment.mem_activeAt_iff.mp hm).1
        dsimp only [storeLvl', rehashStoreLvlTwo]
        rw [dite_eq_right hxA]
        exact hvsl_old.outside x hx
      inner_card := fun j h2 hlt u => ?_
      leaf_card := fun u => ?_ }
  · by_cases hsub : P.InSubtree ℓ₀ u₀ j u
    · obtain ⟨h0j, hanc_u⟩ := hsub
      have hfeq : ((seeds'.activeAt S j hlt.le u).filter fun x => storeLvl' x = j) =
          (seeds'.activeAt S j hlt.le u).filter fun x => canonLvl x = j :=
        filter_congr fun x hx =>
          (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_u ▸ seeds'.activeAt_subset_ancestor h0j hlt.le u hx) h0j).1
      rw [hfeq]
      exact hvsl_can.inner_card j h2 hlt u
    · by_cases hanc_ex : ∃ hj_lt : j < ℓ₀, u = P.ancestorAt hj_lt.le u₀
      · obtain ⟨hj_lt, rfl⟩ := hanc_ex
        let B := seeds'.activeAt S j hlt.le (P.ancestorAt hj_lt.le u₀)
        have hB_eq : B = st.seeds.activeAt S j hlt.le (P.ancestorAt hj_lt.le u₀) :=
          hact_outside j hlt.le _ hsub
        have hA_sub_B : A₀ ⊆ B := seeds'.activeAt_subset_ancestor hj_lt.le hℓ₀ u₀
        have hsplit1 : (B.filter fun x => storeLvl' x = j) =
            ((B \ A₀).filter fun x => storeLvl' x = j) ∪ (A₀.filter fun x => storeLvl' x = j) := by
          ext x; simp only [mem_filter, mem_union, mem_sdiff]
          exact ⟨fun ⟨hxB, he⟩ => if hxA : x ∈ A₀ then Or.inr ⟨hxA, he⟩
            else Or.inl ⟨⟨hxB, hxA⟩, he⟩,
            fun h => h.elim (fun ⟨⟨hxB, _⟩, he⟩ => ⟨hxB, he⟩)
              (fun ⟨hxA, he⟩ => ⟨hA_sub_B hxA, he⟩)⟩
        have hsplit2 : (B.filter fun x => storeLvl x = j) =
            ((B \ A₀).filter fun x => storeLvl x = j) ∪ (A₀.filter fun x => storeLvl x = j) := by
          ext x; simp only [mem_filter, mem_union, mem_sdiff]
          exact ⟨fun ⟨hxB, he⟩ => if hxA : x ∈ A₀ then Or.inr ⟨hxA, he⟩
            else Or.inl ⟨⟨hxB, hxA⟩, he⟩,
            fun h => h.elim (fun ⟨⟨hxB, _⟩, he⟩ => ⟨hxB, he⟩)
              (fun ⟨hxA, he⟩ => ⟨hA_sub_B hxA, he⟩)⟩
        have hdisj1 : Disjoint ((B \ A₀).filter fun x => storeLvl' x = j)
            (A₀.filter fun x => storeLvl' x = j) := by
          rw [Finset.disjoint_left]; intro x h1 h2
          exact (mem_sdiff.mp (mem_filter.mp h1).1).2 (mem_filter.mp h2).1
        have hdisj2 : Disjoint ((B \ A₀).filter fun x => storeLvl x = j)
            (A₀.filter fun x => storeLvl x = j) := by
          rw [Finset.disjoint_left]; intro x h1 h2
          exact (mem_sdiff.mp (mem_filter.mp h1).1).2 (mem_filter.mp h2).1
        have hsdiff_eq : ((B \ A₀).filter fun x => storeLvl' x = j) =
            (B \ A₀).filter fun x => storeLvl x = j :=
          filter_congr fun x hx => by
            have hxA := (mem_sdiff.mp hx).2
            dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
        have hA_bij : (A₀.filter fun x => storeLvl' x = j).card =
            (A₀.filter fun y => storeLvl y = j).card := by
          have hlt_of_mem : ∀ {x}, x ∈ A₀.filter (fun x => storeLvl' x = j) → canonLvl x < ℓ₀ := by
            intro x hx
            obtain ⟨hxA, hsl⟩ := mem_filter.mp hx
            by_contra hge
            dsimp only [canonLvl, S] at hge
            dsimp only [storeLvl', rehashStoreLvlTwo] at hsl
            rw [dite_eq_left hxA, dite_eq_right hge] at hsl
            omega
          refine Finset.card_bij
            (fun x hx => (φ.symm ⟨x, mem_filter.mpr ⟨(mem_filter.mp hx).1, hlt_of_mem hx⟩⟩).1)
            (fun x hx => ?_) (fun x₁ hx₁ x₂ hx₂ heq => ?_) (fun y hy => ?_)
          · obtain ⟨hxA, hsl⟩ := mem_filter.mp hx
            have hlt_c := hlt_of_mem hx
            dsimp only [storeLvl', rehashStoreLvlTwo] at hsl
            rw [dite_eq_left hxA, dite_eq_left hlt_c] at hsl
            have hy_mem := (mem_filter.mp (φ.symm ⟨x, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).2).1
            exact mem_filter.mpr ⟨hy_mem, hsl⟩
          · have hsub_eq : φ.symm ⟨x₁, mem_filter.mpr ⟨(mem_filter.mp hx₁).1, hlt_of_mem hx₁⟩⟩ =
                φ.symm ⟨x₂, mem_filter.mpr ⟨(mem_filter.mp hx₂).1, hlt_of_mem hx₂⟩⟩ :=
              Subtype.ext heq
            exact congrArg Subtype.val (φ.symm.injective hsub_eq)
          · obtain ⟨hyA, hsly⟩ := mem_filter.mp hy
            have hyU : y ∈ U_old := mem_filter.mpr ⟨hyA, by omega⟩
            let x_sub := φ ⟨y, hyU⟩
            obtain ⟨hxA, hlt_c⟩ := mem_filter.mp x_sub.2
            have hsymm : φ.symm ⟨x_sub.1, mem_filter.mpr ⟨hxA, hlt_c⟩⟩ = ⟨y, hyU⟩ :=
              φ.symm_apply_apply ⟨y, hyU⟩
            have hx_mem : x_sub.1 ∈ A₀.filter (fun x => storeLvl' x = j) := by
              refine mem_filter.mpr ⟨hxA, ?_⟩
              dsimp only [storeLvl', rehashStoreLvlTwo]
              rw [dite_eq_left hxA, dite_eq_left hlt_c]
              change storeLvl (φ.symm ⟨x_sub.1, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).1 = j
              rw [hsymm]; exact hsly
            refine ⟨x_sub.1, hx_mem, ?_⟩
            change (φ.symm ⟨x_sub.1, mem_filter.mpr ⟨hxA, hlt_c⟩⟩).1 = y
            rw [hsymm]
        have hold_card : (B.filter fun x => storeLvl x = j).card = P.tableCap j := by
          rw [hB_eq]; exact hvsl_old.inner_card j h2 hlt _
        rw [hsplit1, card_union_of_disjoint hdisj1, hsdiff_eq, hA_bij,
          ← card_union_of_disjoint hdisj2, ← hsplit2, hold_card]
      · have hfeq : ((seeds'.activeAt S j hlt.le u).filter fun x => storeLvl' x = j) =
            (st.seeds.activeAt S j hlt.le u).filter fun x => storeLvl x = j := by
          have ha := hact_outside j hlt.le u hsub
          rw [← ha]
          refine filter_congr fun x hx => ?_
          have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hlt.le u hsub hanc_ex hx
          dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
        rw [hfeq]; exact hvsl_old.inner_card j h2 hlt u
  · by_cases hsub : P.InSubtree ℓ₀ u₀ P.depth u
    · obtain ⟨h0d, hanc_u⟩ := hsub
      have hfeq : ((seeds'.activeAt S P.depth le_rfl u).filter fun x => storeLvl' x = P.depth) =
          (seeds'.activeAt S P.depth le_rfl u).filter fun x => canonLvl x = P.depth :=
        filter_congr fun x hx =>
          (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_u ▸ seeds'.activeAt_subset_ancestor h0d le_rfl u hx) h0d).1
      rw [hfeq]; exact hvsl_can.leaf_card u
    · have hnot_anc : ¬ ∃ hlt : P.depth < ℓ₀, u = P.ancestorAt hlt.le u₀ :=
        fun ⟨hlt, _⟩ => by omega
      have hfeq : ((seeds'.activeAt S P.depth le_rfl u).filter fun x => storeLvl' x = P.depth) =
          (st.seeds.activeAt S P.depth le_rfl u).filter fun x => storeLvl x = P.depth := by
        have ha := hact_outside P.depth le_rfl u hsub
        rw [← ha]
        refine filter_congr fun x hx => ?_
        have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ le_rfl u hsub hnot_anc hx
        dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
      rw [hfeq]; exact hvsl_old.leaf_card u

/-- **`Algorithm 4` (`Rehash(u₀)`, [LiLiangYuZhou2024, Section 5.5], PDF p. 34 / printed p. 33)**:
rebuilds the subtree rooted at `(ℓ₀, u₀)` (`0 ≤ ℓ₀ ≤ depth`) using new subtree seeds `seeds'`
agreeing with `st.seeds` outside `InSubtree ℓ₀ u₀`, adjusting only the `ℓ₀ - 1` strict ancestor
nodes `(j, ancestorAt u₀)` (`1 ≤ j < ℓ₀`) and leaving all sibling subtrees untouched. -/
noncomputable def rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) : P.TreeState :=
  let st_canon := P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  if h0 : ℓ₀ = 0 then
    st_canon
  else if h1 : ℓ₀ = 1 then
    { topSeed := st.topSeed
      roots := fun u₁ => if P.InSubtree ℓ₀ u₀ 1 u₁ then st_canon.roots u₁ else st.roots u₁
      inner := fun ℓ h2 hlt v =>
        if P.InSubtree ℓ₀ u₀ ℓ v then st_canon.inner ℓ h2 hlt v else st.inner ℓ h2 hlt v
      leaves := fun v => if P.InSubtree ℓ₀ u₀ P.depth v then st_canon.leaves v else st.leaves v
      sentCount := st.sentCount }
  else
    have h2₀ : 2 ≤ ℓ₀ := by omega
    have h1lt₀ : 1 < ℓ₀ := by omega
    let hvsl' := validStoreLvl_rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
    { topSeed := st.topSeed
      roots := fun u₁ =>
        if u₁ = P.ancestorAt h1lt₀.le u₀ then buildRootOfStoreLvl d seeds' hgood' hvsl' u₁
        else st.roots u₁
      inner := fun ℓ h2 hlt v =>
        if P.InSubtree ℓ₀ u₀ ℓ v then st_canon.inner ℓ h2 hlt v
        else if hlt₀ : ℓ < ℓ₀ then
          if v = P.ancestorAt hlt₀.le u₀ then
            buildInnerOfStoreLvl d seeds' hgood' hvsl' ℓ h2 hlt v
          else st.inner ℓ h2 hlt v
        else st.inner ℓ h2 hlt v
      leaves := fun v => if P.InSubtree ℓ₀ u₀ P.depth v then st_canon.leaves v else st.leaves v
      sentCount := st.sentCount }

@[simp]
theorem sentCount_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').sentCount = st.sentCount := by
  dsimp only [rehashSubtree]; split_ifs <;> simp

@[simp]
theorem seeds_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').seeds = seeds' := by
  have hsc := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  dsimp only [rehashSubtree]
  split_ifs with h0 h1
  · exact hsc
  · ext j hj v
    by_cases hj0 : j = 0
    · subst hj0; rw [seeds_zero, ← seeds_zero st hj v]
      exact (houtside 0 hj v fun ⟨hg, _⟩ => by omega).symm
    · by_cases hj1 : j = 1
      · subst hj1; simp only [seeds_one]
        split_ifs with hsub
        · rw [← seeds_one (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood') hj v, hsc]
        · rw [← seeds_one st hj v, houtside 1 hj v hsub]
      · by_cases hlt : j < P.depth
        · simp only [seeds_inner _ (by omega) hlt hj]
          split_ifs with hsub
          · rw [← seeds_inner (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood')
              (by omega) hlt hj v, hsc]
          · rw [← seeds_inner st (by omega) hlt hj v, houtside j hj v hsub]
        · have hd : j = P.depth := by omega
          subst hd; simp only [seeds_depth]
          split_ifs with hsub
          · rw [← seeds_depth (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood') hj v, hsc]
          · rw [← seeds_depth st hj v, houtside P.depth hj v hsub]
  · ext j hj v
    by_cases hj0 : j = 0
    · subst hj0; rw [seeds_zero, ← seeds_zero st hj v]
      exact (houtside 0 hj v fun ⟨hg, _⟩ => by omega).symm
    · by_cases hj1 : j = 1
      · subst hj1; simp only [seeds_one]
        split_ifs with heq
        · simp
        · rw [← seeds_one st hj v, houtside 1 hj v fun ⟨hg, _⟩ => by omega]
      · by_cases hlt : j < P.depth
        · simp only [seeds_inner _ (by omega) hlt hj]
          split_ifs with hsub hlt0 heq
          · rw [← seeds_inner (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood')
              (by omega) hlt hj v, hsc]
          · simp
          · rw [← seeds_inner st (by omega) hlt hj v, houtside j hj v hsub]
          · rw [← seeds_inner st (by omega) hlt hj v, houtside j hj v hsub]
        · have hd : j = P.depth := by omega
          subst hd; simp only [seeds_depth]
          split_ifs with hsub
          · rw [← seeds_depth (P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood') hj v, hsc]
          · rw [← seeds_depth st hj v, houtside P.depth hj v hsub]

/-- Non-ancestor root trees (`u₁ ≠ ancestorAt u₀`, `1 ≤ ℓ₀`) are untouched by `rehashSubtree`. -/
theorem rehashSubtree_untouched_roots
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (u₁ : Fin (P.numNodes 1)) (hu₁ : u₁ ≠ P.ancestorAt h1₀ u₀) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').roots u₁ = st.roots u₁ := by
  dsimp only [rehashSubtree]
  rw [dite_eq_right (by omega)]
  by_cases h1 : ℓ₀ = 1
  · subst h1
    rw [dite_eq_left rfl]
    have hnot : ¬ P.InSubtree 1 u₀ 1 u₁ := fun ⟨_, he⟩ =>
      hu₁ (by simpa only [P.ancestorAt_refl] using he)
    simp [hnot]
  · rw [dite_eq_right h1]; simp [hu₁]

/-- Inner nodes outside `InSubtree ℓ₀ u₀` and off `u₀`'s ancestor path are untouched. -/
theorem rehashSubtree_untouched_inner
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (v : Fin (P.numNodes ℓ))
    (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ ℓ v)
    (hnot_anc : ∀ hlt₀ : ℓ < ℓ₀, v ≠ P.ancestorAt hlt₀.le u₀) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').inner ℓ h2 hlt v =
      st.inner ℓ h2 hlt v := by
  dsimp only [rehashSubtree]
  rw [dite_eq_right (by omega)]
  by_cases h1 : ℓ₀ = 1
  · rw [dite_eq_left h1]; dsimp only; rw [ite_eq_right hnot_sub]
  · rw [dite_eq_right h1]; dsimp only; rw [ite_eq_right hnot_sub]
    split_ifs with hlt0 heq
    · exact False.elim (hnot_anc hlt0 heq)
    · rfl
    · rfl

/-- Leaf nodes outside `InSubtree ℓ₀ u₀` (`1 ≤ ℓ₀`) are untouched by `rehashSubtree`. -/
theorem rehashSubtree_untouched_leaves
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (v : Fin (P.numNodes P.depth)) (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ P.depth v) :
    (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').leaves v = st.leaves v := by
  dsimp only [rehashSubtree]
  rw [dite_eq_right (by omega)]
  split_ifs <;> simp [hnot_sub]

/-- **`Algorithm 4` (`rehashSubtree`) preserves `WellFormedPadded`**. -/
theorem wellFormedPadded_rehashSubtree
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d)) :
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      (st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood').WellFormedPadded
        scheme d storeLvl' := by
  set S := P.paddedDom d
  set st_canon := P.buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  set canonLvl := canonicalStoreLvl seeds' S hgood'
  have hwf_canon := P.wellFormedPadded_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hseeds_canon := P.seeds_buildTreeFromSeeds scheme d st.sentCount seeds' hgood'
  have hseeds_fin := st.seeds_rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
  have hcoord_outside : ∀ {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v →
        seeds'.activeAt S j hj v = st.seeds.activeAt S j hj v ∧
        ∀ x, seeds'.nodeAt j hj x = v →
          seeds'.levelCoordEquiv j hj1 hj x = st.seeds.levelCoordEquiv j hj1 hj x := by
    intro j hj1 hj v hnot
    have hanc_le : ∀ (i : ℕ) (hi : i ≤ j),
        seeds'.seed i (hi.trans hj) (P.ancestorAt hi v) =
          st.seeds.seed i (hi.trans hj) (P.ancestorAt hi v) := fun i hi =>
      houtside i (hi.trans hj) _ (P.not_inSubtree_ancestor_of_not_inSubtree hi hnot)
    refine ⟨?_, fun x hnx => SeedAssignment.levelCoordEquiv_congr_ancestors hj1 hj v hanc_le x hnx⟩
    ext x
    simp only [SeedAssignment.mem_activeAt_iff,
      (SeedAssignment.primCoordAt_congr_ancestors hj v (fun i hi => hanc_le i hi.le) x).1]
  by_cases h0 : ℓ₀ = 0
  · refine ⟨canonLvl, ?_⟩
    dsimp only [rehashSubtree]; rw [dite_eq_left h0]; exact hwf_canon
  · by_cases h1 : ℓ₀ = 1
    · subst h1
      let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
      let storeLvl' : Fin P.paddedUniv → ℕ := fun x =>
        if seeds'.nodeAt 1 h1d x = u₀ then canonLvl x else storeLvl x
      have hn1_eq : ∀ x, seeds'.nodeAt 1 h1d x = st.seeds.nodeAt 1 h1d x := fun x => by
        let v := seeds'.nodeAt 1 h1d x
        exact ((SeedAssignment.primCoordAt_congr_ancestors h1d v
          (fun i hi => houtside i (hi.le.trans h1d) _ fun ⟨hg, _⟩ => by omega) x).1.mp rfl).symm
      set st_fin := st.rehashSubtree hwf 1 hℓ₀ u₀ seeds' houtside hgood'
      have hdom_fin : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
          st_fin.nodeDom j hj1 hj v =
            if P.InSubtree 1 u₀ j v then st_canon.nodeDom j hj1 hj v
            else st.nodeDom j hj1 hj v := by
        intro j hj1 hj v
        dsimp only [st_fin, rehashSubtree]
        rw [dite_eq_right (by omega), dite_eq_left rfl]
        by_cases hj_one : j = 1
        · subst hj_one; rw [nodeDom_one, nodeDom_one, nodeDom_one]
          by_cases hsub : P.InSubtree 1 u₀ 1 v <;> simp [hsub, st_canon]
        · by_cases hlt : j < P.depth
          · rw [nodeDom_inner _ hj1 (by omega) hlt hj, nodeDom_inner _ hj1 (by omega) hlt hj,
              nodeDom_inner _ hj1 (by omega) hlt hj]
            by_cases hsub : P.InSubtree 1 u₀ j v <;> simp [hsub, st_canon]
          · have hd : j = P.depth := by omega
            subst hd; rw [nodeDom_depth, nodeDom_depth, nodeDom_depth]
            by_cases hsub : P.InSubtree 1 u₀ P.depth v <;> simp [hsub, st_canon]
      have hq_fin : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) k,
          st_fin.nodeQuery scheme j hj1 hj v k =
            if P.InSubtree 1 u₀ j v then st_canon.nodeQuery scheme j hj1 hj v k
            else st.nodeQuery scheme j hj1 hj v k := by
        intro j hj1 hj v k
        dsimp only [st_fin, rehashSubtree]
        rw [dite_eq_right (by omega), dite_eq_left rfl]
        by_cases hj_one : j = 1
        · subst hj_one; rw [nodeQuery_one, nodeQuery_one, nodeQuery_one]
          by_cases hsub : P.InSubtree 1 u₀ 1 v <;> simp [hsub, st_canon]
        · by_cases hlt : j < P.depth
          · rw [nodeQuery_inner _ _ hj1 (by omega) hlt hj,
              nodeQuery_inner _ _ hj1 (by omega) hlt hj,
              nodeQuery_inner _ _ hj1 (by omega) hlt hj]
            by_cases hsub : P.InSubtree 1 u₀ j v <;> simp [hsub, st_canon]
          · have hd : j = P.depth := by omega
            subst hd; rw [nodeQuery_depth, nodeQuery_depth, nodeQuery_depth]
            by_cases hsub : P.InSubtree 1 u₀ P.depth v <;> simp [hsub, st_canon]
      have hw_fin : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
          st_fin.nodeWait j hj2 hj v =
            if P.InSubtree 1 u₀ j v then st_canon.nodeWait j hj2 hj v
            else st.nodeWait j hj2 hj v := by
        intro j hj2 hj v
        dsimp only [st_fin, rehashSubtree]
        rw [dite_eq_right (by omega), dite_eq_left rfl]
        by_cases hlt : j < P.depth
        · rw [nodeWait_inner _ hj2 hlt hj, nodeWait_inner _ hj2 hlt hj,
            nodeWait_inner _ hj2 hlt hj]
          by_cases hsub : P.InSubtree 1 u₀ j v <;> simp [hsub, st_canon]
        · have hd : j = P.depth := by omega
          subst hd; rw [nodeWait_depth, nodeWait_depth, nodeWait_depth]
          by_cases hsub : P.InSubtree 1 u₀ P.depth v <;> simp [hsub, st_canon]
      refine ⟨storeLvl',
        { goodSeeds := by rw [hseeds_fin]; exact hgood'
          storeLvl_bounds := fun x hx => by
            dsimp only [storeLvl']; split_ifs
            · exact hwf_canon.storeLvl_bounds x hx
            · exact hwf.storeLvl_bounds x hx
          storeLvl_outside := fun x hx => by
            dsimp only [storeLvl']; split_ifs
            · exact hwf_canon.storeLvl_outside x hx
            · exact hwf.storeLvl_outside x hx
          dom_eq := fun j hj1 hj v => by
            rw [hseeds_fin, hdom_fin]
            split_ifs with hsub
            · obtain ⟨_, hanc⟩ := hsub
              rw [hwf_canon.dom_eq j hj1 hj v, hseeds_canon]
              congr 1; refine filter_congr fun x hx => ?_
              have hn1 : seeds'.nodeAt 1 h1d x = u₀ := by
                rw [← seeds'.ancestorAt_nodeAt hj1 hj x, (SeedAssignment.mem_activeAt_iff.mp hx).2,
                  hanc]
              dsimp only [storeLvl']; rw [ite_eq_left hn1]
            · obtain ⟨hact_eq, hce⟩ := hcoord_outside hj1 hj v hsub
              rw [hwf.dom_eq j hj1 hj v, ← hact_eq]
              have hf : ((seeds'.activeAt S j hj v).filter fun x => storeLvl x = j) =
                  (seeds'.activeAt S j hj v).filter fun x => storeLvl' x = j :=
                filter_congr fun x hx => by
                  have hn1 : seeds'.nodeAt 1 h1d x ≠ u₀ := fun h =>
                    hsub ⟨hj1, by rw [← (SeedAssignment.mem_activeAt_iff.mp hx).2,
                      seeds'.ancestorAt_nodeAt hj1 hj x, h]⟩
                  dsimp only [storeLvl']; rw [ite_eq_right hn1]
              rw [hf]
              refine image_congr fun x hx => ?_
              exact congrArg (fun c => c.2.1)
                (hce x (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx).1).2).symm
          query_eq_of_storeLvl := fun j hj1 hj v x vx hdx hnx hsl => by
            rw [hseeds_fin] at hnx ⊢
            rw [hq_fin]
            split_ifs with hsub
            · obtain ⟨_, hanc⟩ := hsub
              have hn1 : seeds'.nodeAt 1 h1d x = u₀ := by
                rw [← seeds'.ancestorAt_nodeAt hj1 hj x, hnx, hanc]
              dsimp only [storeLvl'] at hsl; rw [ite_eq_left hn1] at hsl
              have hq := hwf_canon.query_eq_of_storeLvl j hj1 hj v x vx hdx
                (by rw [hseeds_canon]; exact hnx) hsl
              rwa [hseeds_canon] at hq
            · obtain ⟨_, hce⟩ := hcoord_outside hj1 hj v hsub
              have hn1 : seeds'.nodeAt 1 h1d x ≠ u₀ := fun h =>
                hsub ⟨hj1, by rw [← hnx, seeds'.ancestorAt_nodeAt hj1 hj x, h]⟩
              dsimp only [storeLvl'] at hsl; rw [ite_eq_right hn1] at hsl
              have hc := hce x hnx
              have hnx_old : st.seeds.nodeAt j hj x = v := by
                rw [← st.seeds.levelCoordEquiv_fst hj1 hj x, ← hc,
                  seeds'.levelCoordEquiv_fst hj1 hj x, hnx]
              have hq := hwf.query_eq_of_storeLvl j hj1 hj v x vx hdx hnx_old hsl
              have hid_eq : seeds'.idAt j hj1 hj x = st.seeds.idAt j hj1 hj x :=
                congrArg (fun c => c.2.1) hc
              have hqt_eq : seeds'.quotAt j hj1 hj x = st.seeds.quotAt j hj1 hj x :=
                congrArg (fun c => c.2.2) hc
              rw [hid_eq, hqt_eq, hq]
          inner_full := fun j hj2 hlt v => by
            dsimp only [st_fin, rehashSubtree]
            rw [dite_eq_right (by omega), dite_eq_left rfl]
            dsimp only
            split_ifs
            · exact hwf_canon.inner_full j hj2 hlt v
            · exact hwf.inner_full j hj2 hlt v
          wait_dom_eq := fun j hj2 hj v => by
            rw [hseeds_fin, hw_fin]
            split_ifs with hsub
            · obtain ⟨h1j, hanc⟩ := hsub
              rw [hwf_canon.wait_dom_eq j hj2 hj v, hseeds_canon]
              congr 1; refine filter_congr fun x hx => ?_
              have hn1 : seeds'.nodeAt 1 h1d x = u₀ := by
                rw [← seeds'.ancestorAt_nodeAt h1j hj x, (SeedAssignment.mem_activeAt_iff.mp hx).2,
                  hanc]
              dsimp only [storeLvl']; rw [ite_eq_left hn1]
            · obtain ⟨hact_eq, hce⟩ := hcoord_outside (by omega) hj v hsub
              rw [hwf.wait_dom_eq j hj2 hj v, ← hact_eq]
              have hf : ((seeds'.activeAt S j hj v).filter fun x => storeLvl x < j) =
                  (seeds'.activeAt S j hj v).filter fun x => storeLvl' x < j :=
                filter_congr fun x hx => by
                  have hn1 : seeds'.nodeAt 1 (by omega) x ≠ u₀ := fun h =>
                    hsub ⟨by omega, by rw [← (SeedAssignment.mem_activeAt_iff.mp hx).2,
                      seeds'.ancestorAt_nodeAt (by omega) hj x, h]⟩
                  dsimp only [storeLvl']; rw [ite_eq_right hn1]
              rw [hf]
              refine image_congr fun x hx => ?_
              exact congrArg (fun c => c.2.1)
                (hce x (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx).1).2).symm
          wait_lookup_eq := fun j hj2 hj v x hx hsl => by
            rw [hseeds_fin] at hx ⊢
            rw [hw_fin]
            split_ifs with hsub
            · obtain ⟨h1j, hanc⟩ := hsub
              have hn1 : seeds'.nodeAt 1 h1d x = u₀ := by
                rw [← seeds'.ancestorAt_nodeAt h1j hj x, (SeedAssignment.mem_activeAt_iff.mp hx).2,
                  hanc]
              dsimp only [storeLvl'] at hsl; rw [ite_eq_left hn1] at hsl
              have hw := hwf_canon.wait_lookup_eq j hj2 hj v x
                (by rw [hseeds_canon]; exact hx) hsl
              rwa [hseeds_canon] at hw
            · obtain ⟨hact_eq, hce⟩ := hcoord_outside (by omega) hj v hsub
              have hnot_prev : ¬ P.InSubtree 1 u₀ (j - 1) (P.ancestorAt (by omega) v) :=
                P.not_inSubtree_ancestor_of_not_inSubtree (by omega) hsub
              obtain ⟨_, hce_prev⟩ := hcoord_outside (by omega) (by omega) _ hnot_prev
              have hnx := (SeedAssignment.mem_activeAt_iff.mp hx).2
              have hn1 : seeds'.nodeAt 1 h1d x ≠ u₀ := fun h =>
                hsub ⟨by omega, by rw [← hnx, seeds'.ancestorAt_nodeAt (by omega) hj x, h]⟩
              dsimp only [storeLvl'] at hsl; rw [ite_eq_right hn1] at hsl
              have hc := hce x hnx
              have hc_prev := hce_prev x (by rw [← hnx, seeds'.ancestorAt_nodeAt])
              have hx_old : x ∈ st.seeds.activeAt S j hj v := hact_eq ▸ hx
              have hw := hwf.wait_lookup_eq j hj2 hj v x hx_old hsl
              have hid_eq : seeds'.idAt j (by omega) hj x = st.seeds.idAt j (by omega) hj x :=
                congrArg (fun c => c.2.1) hc
              have hid_p : seeds'.idAt (j - 1) (by omega) (by omega) x =
                  st.seeds.idAt (j - 1) (by omega) (by omega) x :=
                congrArg (fun c => c.2.1) hc_prev
              rw [hid_eq, hid_p, hw] }⟩
    · have h2₀ : 2 ≤ ℓ₀ := by omega
      have h1lt₀ : 1 < ℓ₀ := by omega
      let storeLvl' := rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
      have hvsl' := validStoreLvl_rehashStoreLvlTwo hwf h2₀ hℓ₀ u₀ houtside hgood'
      set st_fin := st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
      have h2_out : ∀ {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
          ¬ P.InSubtree ℓ₀ u₀ j v → (¬ ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀) →
            st_fin.nodeDom j hj1 hj v = st.nodeDom j hj1 hj v ∧
            ∀ k, st_fin.nodeQuery scheme j hj1 hj v k = st.nodeQuery scheme j hj1 hj v k := by
        intro j hj1 hj v hsub hanc
        by_cases hj_one : j = 1
        · subst hj_one
          have hrt := st.rehashSubtree_untouched_roots hwf (by omega) hℓ₀ u₀ seeds' houtside
            hgood' v fun he => hanc ⟨h1lt₀, he⟩
          exact ⟨by rw [nodeDom_one, nodeDom_one, hrt],
            fun k => by rw [nodeQuery_one, nodeQuery_one, hrt]⟩
        · by_cases hlt : j < P.depth
          · have hin := st.rehashSubtree_untouched_inner hwf (by omega) hℓ₀ u₀ seeds' houtside
              hgood' (by omega) hlt v hsub fun hlt0 he => hanc ⟨hlt0, he⟩
            exact ⟨by rw [nodeDom_inner _ hj1 (by omega) hlt hj,
              nodeDom_inner _ hj1 (by omega) hlt hj, hin],
              fun k => by rw [nodeQuery_inner _ _ hj1 (by omega) hlt hj,
                nodeQuery_inner _ _ hj1 (by omega) hlt hj, hin]⟩
          · have hd : j = P.depth := by omega
            subst hd
            have hlf := st.rehashSubtree_untouched_leaves hwf (by omega) hℓ₀ u₀ seeds' houtside
              hgood' v hsub
            exact ⟨by rw [nodeDom_depth, nodeDom_depth, hlf],
              fun k => by rw [nodeQuery_depth, nodeQuery_depth, hlf]⟩
      have h2_sub : ∀ {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
          P.InSubtree ℓ₀ u₀ j v →
            st_fin.nodeDom j hj1 hj v = st_canon.nodeDom j hj1 hj v ∧
            (∀ k, st_fin.nodeQuery scheme j hj1 hj v k = st_canon.nodeQuery scheme j hj1 hj v k) ∧
            ∀ hj2 : 2 ≤ j, st_fin.nodeWait j hj2 hj v = st_canon.nodeWait j hj2 hj v := by
        intro j hj1 hj v hsub
        have hj2 : 2 ≤ j := h2₀.trans hsub.1
        by_cases hlt : j < P.depth
        · have hin : st_fin.inner j hj2 hlt v = st_canon.inner j hj2 hlt v := by
            dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]; dsimp only
            rw [ite_eq_left hsub]
          exact ⟨by rw [nodeDom_inner _ hj1 hj2 hlt hj, nodeDom_inner _ hj1 hj2 hlt hj, hin],
            fun k => by rw [nodeQuery_inner _ _ hj1 hj2 hlt hj,
              nodeQuery_inner _ _ hj1 hj2 hlt hj, hin],
            fun hj2' => by rw [nodeWait_inner _ hj2' hlt hj, nodeWait_inner _ hj2' hlt hj, hin]⟩
        · have hd : j = P.depth := by omega
          subst hd
          have hlf : st_fin.leaves v = st_canon.leaves v := by
            dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]; dsimp only
            rw [ite_eq_left hsub]
          exact ⟨by rw [nodeDom_depth, nodeDom_depth, hlf],
            fun k => by rw [nodeQuery_depth, nodeQuery_depth, hlf],
            fun _ => by rw [nodeWait_depth, nodeWait_depth, hlf]⟩
      have hw2_out : ∀ {j : ℕ} (hj2 : 2 ≤ j) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
          ¬ P.InSubtree ℓ₀ u₀ j v → (¬ ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀) →
            st_fin.nodeWait j hj2 hj v = st.nodeWait j hj2 hj v := by
        intro j hj2 hj v hsub hanc
        by_cases hlt : j < P.depth
        · rw [nodeWait_inner _ hj2 hlt hj, nodeWait_inner _ hj2 hlt hj,
            st.rehashSubtree_untouched_inner hwf (by omega) hℓ₀ u₀ seeds' houtside hgood'
              hj2 hlt v hsub fun hlt0 he => hanc ⟨hlt0, he⟩]
        · have hd : j = P.depth := by omega
          subst hd
          rw [nodeWait_depth, nodeWait_depth,
            st.rehashSubtree_untouched_leaves hwf (by omega) hℓ₀ u₀ seeds' houtside hgood' v hsub]
      refine ⟨storeLvl',
        { goodSeeds := by rw [hseeds_fin]; exact hgood'
          storeLvl_bounds := hvsl'.bounds
          storeLvl_outside := hvsl'.outside
          dom_eq := fun j hj1 hj v => ?_
          query_eq_of_storeLvl := fun j hj1 hj v x vx hdx hnx hsl => ?_
          inner_full := fun j hj2 hlt v => ?_
          wait_dom_eq := fun j hj2 hj v => ?_
          wait_lookup_eq := fun j hj2 hj v x hx hsl => ?_ }⟩
      · rw [hseeds_fin]
        by_cases hsub : P.InSubtree ℓ₀ u₀ j v
        · obtain ⟨h0j, hanc_v⟩ := hsub
          rw [(h2_sub hj1 hj v ⟨h0j, hanc_v⟩).1, hwf_canon.dom_eq j hj1 hj v, hseeds_canon]
          congr 1; refine filter_congr fun x hx => ?_
          exact (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_v ▸ seeds'.activeAt_subset_ancestor h0j hj v hx) h0j).1.symm
        · by_cases hanc_ex : ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀
          · obtain ⟨hlt0, hv⟩ := hanc_ex
            by_cases hj_one : j = 1
            · subst hj_one; rw [nodeDom_one]
              dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
              dsimp only; rw [ite_eq_left hv, dom_buildRootOfStoreLvl]
            · have hlt : j < P.depth := hlt0.trans_le hℓ₀
              rw [nodeDom_inner st_fin hj1 (by omega) hlt hj]
              dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
              dsimp only
              rw [ite_eq_right hsub, dite_eq_left hlt0, ite_eq_left hv, dom_buildInnerOfStoreLvl]
          · obtain ⟨hact_eq, hce⟩ := hcoord_outside hj1 hj v hsub
            rw [(h2_out hj1 hj v hsub hanc_ex).1, hwf.dom_eq j hj1 hj v, ← hact_eq]
            have hf : ((seeds'.activeAt S j hj v).filter fun x => storeLvl x = j) =
                (seeds'.activeAt S j hj v).filter fun x => storeLvl' x = j :=
              filter_congr fun x hx => by
                have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj v hsub hanc_ex hx
                dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
            rw [hf]
            refine image_congr fun x hx =>
              congrArg (fun c => c.2.1)
                (hce x (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx).1).2).symm
      · rw [hseeds_fin] at hnx ⊢
        have hx_act : x ∈ seeds'.activeAt S j hj v :=
          SeedAssignment.mem_activeAt_iff.mpr ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩
        by_cases hsub : P.InSubtree ℓ₀ u₀ j v
        · obtain ⟨h0j, hanc_v⟩ := hsub
          rw [((h2_sub hj1 hj v ⟨h0j, hanc_v⟩).2.1 _)]
          have hsl_c := (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_v ▸ seeds'.activeAt_subset_ancestor h0j hj v hx_act) h0j).1.mp hsl
          have hq := hwf_canon.query_eq_of_storeLvl j hj1 hj v x vx hdx
            (by rw [hseeds_canon]; exact hnx) hsl_c
          rwa [hseeds_canon] at hq
        · by_cases hanc_ex : ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀
          · obtain ⟨hlt0, hv⟩ := hanc_ex
            by_cases hj_one : j = 1
            · subst hj_one; rw [nodeQuery_one]
              dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
              dsimp only; rw [ite_eq_left hv]
              exact query_buildRootOfStoreLvl hgood' hvsl' v hdx hnx hsl
            · have hlt : j < P.depth := hlt0.trans_le hℓ₀
              rw [nodeQuery_inner scheme st_fin hj1 (by omega) hlt hj]
              dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]
              dsimp only; rw [ite_eq_right hsub, dite_eq_left hlt0, ite_eq_left hv]
              exact query_buildInnerOfStoreLvl hgood' hvsl' hj1 (by omega) hlt v hdx hnx hsl
          · rw [(h2_out hj1 hj v hsub hanc_ex).2]
            have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj v hsub hanc_ex hx_act
            dsimp only [storeLvl', rehashStoreLvlTwo] at hsl; rw [dite_eq_right hxA] at hsl
            obtain ⟨_, hce⟩ := hcoord_outside hj1 hj v hsub
            have hc := hce x hnx
            have hnx_old : st.seeds.nodeAt j hj x = v := by
              rw [← st.seeds.levelCoordEquiv_fst hj1 hj x, ← hc,
                seeds'.levelCoordEquiv_fst hj1 hj x, hnx]
            have hq := hwf.query_eq_of_storeLvl j hj1 hj v x vx hdx hnx_old hsl
            have hid_eq : seeds'.idAt j hj1 hj x = st.seeds.idAt j hj1 hj x :=
              congrArg (fun c => c.2.1) hc
            have hqt_eq : seeds'.quotAt j hj1 hj x = st.seeds.quotAt j hj1 hj x :=
              congrArg (fun c => c.2.2) hc
            rw [hid_eq, hqt_eq, hq]
      · dsimp only [st_fin, rehashSubtree]
        rw [dite_eq_right h0, dite_eq_right h1]
        dsimp only
        split_ifs with hsub hlt0 hv
        · exact hwf_canon.inner_full j hj2 hlt v
        · exact card_dom_buildInnerOfStoreLvl d seeds' hgood' hvsl' j hj2 hlt v
        · exact hwf.inner_full j hj2 hlt v
        · exact hwf.inner_full j hj2 hlt v
      · rw [hseeds_fin]
        by_cases hsub : P.InSubtree ℓ₀ u₀ j v
        · obtain ⟨h0j, hanc_v⟩ := hsub
          rw [(h2_sub (by omega) hj v ⟨h0j, hanc_v⟩).2.2 hj2, hwf_canon.wait_dom_eq j hj2 hj v,
            hseeds_canon]
          congr 1; refine filter_congr fun x hx => ?_
          exact (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_v ▸ seeds'.activeAt_subset_ancestor h0j hj v hx) h0j).2.symm
        · by_cases hanc_ex : ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀
          · obtain ⟨hlt0, hv⟩ := hanc_ex
            have hlt : j < P.depth := hlt0.trans_le hℓ₀
            rw [nodeWait_inner st_fin hj2 hlt hj]
            dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]; dsimp only
            rw [ite_eq_right hsub, dite_eq_left hlt0, ite_eq_left hv, wait_dom_buildInnerOfStoreLvl]
          · obtain ⟨hact_eq, hce⟩ := hcoord_outside (by omega) hj v hsub
            rw [hw2_out hj2 hj v hsub hanc_ex, hwf.wait_dom_eq j hj2 hj v, ← hact_eq]
            have hf : ((seeds'.activeAt S j hj v).filter fun x => storeLvl x < j) =
                (seeds'.activeAt S j hj v).filter fun x => storeLvl' x < j :=
              filter_congr fun x hx => by
                have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj v hsub hanc_ex hx
                dsimp only [storeLvl', rehashStoreLvlTwo]; rw [dite_eq_right hxA]
            rw [hf]
            refine image_congr fun x hx =>
              congrArg (fun c => c.2.1)
                (hce x (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx).1).2).symm
      · rw [hseeds_fin] at hx ⊢
        have hnx := (SeedAssignment.mem_activeAt_iff.mp hx).2
        by_cases hsub : P.InSubtree ℓ₀ u₀ j v
        · obtain ⟨h0j, hanc_v⟩ := hsub
          rw [(h2_sub (by omega) hj v ⟨h0j, hanc_v⟩).2.2 hj2]
          have hsl_c := (rehashStoreLvlTwo_ge_iff hwf h2₀ hℓ₀ u₀ houtside hgood'
            (hanc_v ▸ seeds'.activeAt_subset_ancestor h0j hj v hx) h0j).2.mp hsl
          have hw := hwf_canon.wait_lookup_eq j hj2 hj v x
            (by rw [hseeds_canon]; exact hx) hsl_c
          rwa [hseeds_canon] at hw
        · by_cases hanc_ex : ∃ hlt0 : j < ℓ₀, v = P.ancestorAt hlt0.le u₀
          · obtain ⟨hlt0, hv⟩ := hanc_ex
            have hlt : j < P.depth := hlt0.trans_le hℓ₀
            rw [nodeWait_inner st_fin hj2 hlt hj]
            dsimp only [st_fin, rehashSubtree]; rw [dite_eq_right h0, dite_eq_right h1]; dsimp only
            rw [ite_eq_right hsub, dite_eq_left hlt0, ite_eq_left hv]
            exact wait_lookup_buildInnerOfStoreLvl hgood' hvsl' hj2 hlt v hx hsl
          · rw [hw2_out hj2 hj v hsub hanc_ex]
            have hxA := notMem_A0_of_not_anc_not_sub hℓ₀ u₀ hj v hsub hanc_ex hx
            dsimp only [storeLvl', rehashStoreLvlTwo] at hsl; rw [dite_eq_right hxA] at hsl
            obtain ⟨hact_eq, hce⟩ := hcoord_outside (by omega) hj v hsub
            have hnot_prev : ¬ P.InSubtree ℓ₀ u₀ (j - 1) (P.ancestorAt (by omega) v) :=
              P.not_inSubtree_ancestor_of_not_inSubtree (by omega) hsub
            obtain ⟨_, hce_prev⟩ := hcoord_outside (by omega) (by omega) _ hnot_prev
            have hc := hce x hnx
            have hc_prev := hce_prev x (by rw [← hnx, seeds'.ancestorAt_nodeAt])
            have hw := hwf.wait_lookup_eq j hj2 hj v x (hact_eq ▸ hx) hsl
            have hid_eq : seeds'.idAt j (by omega) hj x = st.seeds.idAt j (by omega) hj x :=
              congrArg (fun c => c.2.1) hc
            have hid_p : seeds'.idAt (j - 1) (by omega) (by omega) x =
                st.seeds.idAt (j - 1) (by omega) (by omega) x :=
              congrArg (fun c => c.2.1) hc_prev
            rw [hid_eq, hid_p, hw]

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
