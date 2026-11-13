/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeQuery

/-!
# Normal-Path Fresh Insertion in the Multi-Level Dictionary Tree

This file formalizes collision- and overflow-free fresh insertion (`normalInsertFresh`) for the
subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou,
*Dynamic Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 30–31 / printed pp. 29–30).

When all node seeds remain good on `Insert.insert x (P.paddedDom d)`, `normalInsertFresh` stores
`(x_quot^[1], v)` directly in the level-1 root storage table at `u_1 = nodeAt 1 x` and pushes
`(x_id^[ℓ], x_id^[ℓ - 1])` onto the waiting list of every visited node `u_ℓ = nodeAt ℓ x` across
levels `2 ≤ ℓ ≤ depth`.

## Main definitions

* `TreeSchedule.TreeState.normalInsertFresh`: normal-path fresh key insertion.

## Main results

* `TreeSchedule.TreeState.wellFormedPadded_normalInsertFresh`: preservation of `WellFormedPadded`
  with storage-level map `Function.update storeLvl x 1`.

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

/-- Normal-path insertion of a fresh internal key `x ∉ P.paddedDom d` when all current node seeds
remain good on `Insert.insert x (P.paddedDom d)` (`Section 5.3`, PDF pp. 30–31 / printed
pp. 29–30): stores `(q_1, v)` at the root `u_1` and pushes `(x_id^[ℓ], x_id^[ℓ - 1])` onto each
visited node's waiting list at `2 ≤ ℓ ≤ depth`. -/
noncomputable def normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) : P.TreeState :=
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  let u₁ := st.seeds.nodeAt 1 h1d x
  let id₁ := st.seeds.idAt 1 le_rfl h1d x
  let q₁ := st.seeds.quotAt 1 le_rfl h1d x
  have hact_ins : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth),
      st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) =
        Insert.insert x (st.seeds.activeAt (P.paddedDom d) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x)) := by
    intro ℓ hℓ; ext y
    simp only [SeedAssignment.mem_activeAt_iff, mem_insert]
    constructor
    · rintro ⟨rfl | hy, hny⟩
      · left; rfl
      · right; exact ⟨hy, hny⟩
    · rintro (rfl | ⟨hy, hny⟩)
      · exact ⟨Or.inl rfl, rfl⟩
      · exact ⟨Or.inr hy, hny⟩
  have hnotMem_act : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth),
      x ∉ st.seeds.activeAt (P.paddedDom d) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) := fun ℓ hℓ h =>
    hx_fresh (SeedAssignment.mem_activeAt_iff.mp h).1
  have hroot_cap : (st.roots u₁).table.tableMeta.dom.card < P.tableCap 1 := by
    have hsum1 := card_root_dom_add_eq hwf u₁
    have hhi1 := (st.seeds.load_bounds_of_allGoodSeeds hgood' h1d u₁).2
    dsimp only [u₁] at hsum1 hhi1 ⊢
    rw [hact_ins 1 h1d, card_insert_of_notMem (hnotMem_act 1 h1d)] at hhi1
    have hcap1 : P.tableCap 1 = P.nHigh 1 - P.branchFactor 1 * P.nLow 2 := by
      dsimp only [tableCap]; rw [ite_eq_left rfl]
    omega
  have hid₁_notMem : id₁ ∉ (st.roots u₁).table.tableMeta.dom := by
    intro hmem
    have hdom1 := hwf.dom_eq 1 le_rfl h1d u₁
    rw [nodeDom_one] at hdom1
    rw [hdom1] at hmem
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp hmem
    have hy_act := (mem_filter.mp hy_filt).1
    have hinj := st.seeds.injOn_idAt_activeAt hgood' le_rfl h1d u₁
    dsimp only [u₁, id₁] at hy_act hinj hid_eq
    rw [hact_ins 1 h1d] at hinj
    have hyx := hinj (mem_insert_of_mem hy_act) (mem_insert_self x _) hid_eq
    exact hnotMem_act 1 h1d (hyx ▸ hy_act)
  have hwait_cap : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth),
      (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).entries.length + 1 ≤ P.waitCap ℓ := by
    intro ℓ h2 hℓ
    rw [← WaitingList.card_dom, card_nodeWait_dom_eq hwf h2 hℓ]
    have hlo := (st.seeds.load_bounds_of_allGoodSeeds hwf.goodSeeds hℓ (st.seeds.nodeAt ℓ hℓ x)).1
    have hhi := (st.seeds.load_bounds_of_allGoodSeeds hgood' hℓ (st.seeds.nodeAt ℓ hℓ x)).2
    rw [hact_ins ℓ hℓ, card_insert_of_notMem (hnotMem_act ℓ hℓ)] at hhi
    have hdiff := P.nHigh_sub_nLow (by omega : 1 ≤ ℓ) hℓ
    omega
  have hwait_notMem : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth),
      st.seeds.idAt ℓ (by omega) hℓ x ∉
        (st.nodeWait ℓ h2 hℓ (st.seeds.nodeAt ℓ hℓ x)).dom := by
    intro ℓ h2 hℓ hmem
    rw [hwf.wait_dom_eq ℓ h2 hℓ] at hmem
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp hmem
    have hy_act := (mem_filter.mp hy_filt).1
    have hinj := st.seeds.injOn_idAt_activeAt hgood' (by omega) hℓ (st.seeds.nodeAt ℓ hℓ x)
    rw [hact_ins ℓ hℓ] at hinj
    have hyx := hinj (mem_insert_of_mem hy_act) (mem_insert_self x _) hid_eq
    exact hnotMem_act ℓ hℓ (hyx ▸ hy_act)
  let u_d := st.seeds.nodeAt P.depth le_rfl x
  let ln := st.leaves u_d
  have hwc_d : ln.leafMeta.wait.entries.length + 1 ≤ P.waitCap P.depth := by
    simpa only [nodeWait_depth] using hwait_cap P.depth P.two_le_depth le_rfl
  have hwn_d : st.seeds.idAt P.depth h1d le_rfl x ∉ ln.leafMeta.wait.dom := by
    simpa only [nodeWait_depth] using hwait_notMem P.depth P.two_le_depth le_rfl
  { topSeed := st.topSeed
    roots := Function.update st.roots u₁
      { (st.roots u₁) with table := (st.roots u₁).table.insert id₁ (q₁, v) hroot_cap hid₁_notMem }
    inner := fun ℓ h2 hlt u =>
      if hu : u = st.seeds.nodeAt ℓ hlt.le x then
        have hwc : (st.inner ℓ h2 hlt u).wait.entries.length + 1 ≤ P.waitCap ℓ := by
          subst hu; simpa only [nodeWait_inner _ h2 hlt hlt.le] using hwait_cap ℓ h2 hlt.le
        have hwn : st.seeds.idAt ℓ (by omega) hlt.le x ∉ (st.inner ℓ h2 hlt u).wait.dom := by
          subst hu; simpa only [nodeWait_inner _ h2 hlt hlt.le] using hwait_notMem ℓ h2 hlt.le
        { (st.inner ℓ h2 hlt u) with
          wait := (st.inner ℓ h2 hlt u).wait.push
            (st.seeds.idAt ℓ (by omega) hlt.le x)
            (st.seeds.idAt (ℓ - 1) (by omega) (by omega) x) hwc hwn }
      else st.inner ℓ h2 hlt u
    leaves := Function.update st.leaves u_d
      { ln with
        leafMeta :=
          { ln.leafMeta with
            wait := ln.leafMeta.wait.push (st.seeds.idAt P.depth h1d le_rfl x)
              (st.seeds.idAt (P.depth - 1) (by have := P.two_le_depth; omega) (by omega) x)
              hwc_d hwn_d } }
    sentCount := st.sentCount }

theorem seeds_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').seeds = st.seeds := by
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0; simp [normalInsertFresh]
  · by_cases h1 : ℓ = 1
    · subst h1; simp only [seeds_one, normalInsertFresh]
      by_cases hu : u = st.seeds.nodeAt 1 (Nat.one_le_of_lt P.two_le_depth) x <;> simp [hu]
    · by_cases hlt : ℓ < P.depth
      · simp only [seeds_inner _ (by omega) hlt hℓ, normalInsertFresh]
        split_ifs <;> rfl
      · have hd : ℓ = P.depth := by omega
        subst hd
        simp only [seeds_depth, normalInsertFresh]
        by_cases hu : u = st.seeds.nodeAt P.depth le_rfl x <;> simp [hu]

theorem sentCount_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').sentCount = st.sentCount := by
  unfold normalInsertFresh; rfl

/-- **Normal-path fresh insertion preserves `WellFormedPadded`** (`storeLvl` extended with
`x ↦ 1`). -/
theorem wellFormedPadded_normalInsertFresh
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    (st : P.TreeState) {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    (x : Fin P.paddedUniv) (v : Fin P.valBound) (hx_fresh : x ∉ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))) :
    (st.normalInsertFresh hwf x v hx_fresh hgood').WellFormedPadded scheme
      (Function.update d x (some v)) (Function.update storeLvl x 1) := by
  set st' := st.normalInsertFresh hwf x v hx_fresh hgood'
  have hseeds : st'.seeds = st.seeds :=
    st.seeds_normalInsertFresh hwf x v hx_fresh hgood'
  have hdom_upd : P.paddedDom (Function.update d x (some v)) = Insert.insert x (P.paddedDom d) :=
    P.paddedDom_update_some d x v
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  refine
    { goodSeeds := by rw [hseeds, hdom_upd]; exact hgood'
      storeLvl_bounds := fun y hy => by
        rw [hdom_upd, mem_insert] at hy
        rcases hy with rfl | hy_old
        · simp [h1d]
        · have hyx : y ≠ x := fun h => hx_fresh (h ▸ hy_old)
          rw [Function.update_of_ne hyx]
          exact hwf.storeLvl_bounds y hy_old
      storeLvl_outside := fun y hy => by
        rw [hdom_upd, mem_insert, not_or] at hy
        rw [Function.update_of_ne hy.1]
        exact hwf.storeLvl_outside y hy.2
      dom_eq := fun ℓ h1 hℓ u => ?_
      query_eq_of_storeLvl := fun ℓ h1 hℓ u y vy hdy hny hsly => ?_
      inner_full := fun ℓ h2 hlt u => by
        dsimp only [st', normalInsertFresh]
        split_ifs
        · exact hwf.inner_full ℓ h2 hlt u
        · exact hwf.inner_full ℓ h2 hlt u
      wait_dom_eq := fun ℓ h2 hℓ u => ?_
      wait_lookup_eq := fun ℓ h2 hℓ u y hy hsly => ?_ }
  · rw [hseeds, hdom_upd]
    by_cases h_one : ℓ = 1
    · subst h_one
      rw [nodeDom_one]
      have hd_old := hwf.dom_eq 1 le_rfl hℓ u
      rw [nodeDom_one] at hd_old
      dsimp only [st', normalInsertFresh]
      by_cases hu : u = st.seeds.nodeAt 1 h1d x
      · subst hu
        rw [Function.update_self, StorageTable.dom_insert, hd_old]
        have hf_eq : ((st.seeds.activeAt (Insert.insert x (P.paddedDom d)) 1 h1d
            (st.seeds.nodeAt 1 h1d x)).filter fun y => Function.update storeLvl x 1 y = 1) =
            Insert.insert x ((st.seeds.activeAt (P.paddedDom d) 1 h1d
              (st.seeds.nodeAt 1 h1d x)).filter fun y => storeLvl y = 1) := by
          ext y
          simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert]
          by_cases hyx : y = x
          · subst hyx; simp
          · simp [hyx]
        rw [hf_eq, image_insert]
      · rw [Function.update_of_ne hu, hd_old]
        congr 1; ext y
        simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert]
        by_cases hyx : y = x
        · subst hyx; simp [Ne.symm hu]
        · simp [hyx]
    · have h2 : 2 ≤ ℓ := by omega
      have hf_eq : ((st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ u).filter
          fun y => Function.update storeLvl x 1 y = ℓ) =
          (st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun y => storeLvl y = ℓ := by
        ext y
        by_cases hyx : y = x
        · subst hyx
          simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert_self, true_and,
            Function.update_self]
          exact ⟨fun h => absurd h.2 (by omega), fun h => absurd h.1.1 hx_fresh⟩
        · simp [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert, hyx]
      rw [hf_eq, ← hwf.dom_eq ℓ h1 hℓ u]
      by_cases hlt : ℓ < P.depth
      · rw [nodeDom_inner _ h1 h2 hlt hℓ, nodeDom_inner _ h1 h2 hlt hℓ]
        dsimp only [st', normalInsertFresh]; split_ifs <;> rfl
      · have hd : ℓ = P.depth := by omega
        subst hd
        rw [nodeDom_depth, nodeDom_depth]
        dsimp only [st', normalInsertFresh]
        by_cases hu : u = st.seeds.nodeAt P.depth le_rfl x
        · subst hu; rw [Function.update_self]; rfl
        · rw [Function.update_of_ne hu]
  · rw [hseeds] at hny ⊢
    by_cases h_one : ℓ = 1
    · subst h_one
      rw [nodeQuery_one]
      dsimp only [st', normalInsertFresh]
      by_cases hyx : y = x
      · subst hyx
        rw [Function.update_self] at hdy
        have hvy : vy = v := (Option.some.inj hdy).symm
        subst hvy; subst hny
        rw [Function.update_self, StorageTable.query_insert, Function.update_self]
      · rw [Function.update_of_ne hyx] at hdy hsly
        have hy_old := hwf.query_eq_of_storeLvl 1 le_rfl hℓ u y vy hdy hny hsly
        rw [nodeQuery_one] at hy_old
        by_cases hu : u = st.seeds.nodeAt 1 h1d x
        · subst hu
          rw [Function.update_self, StorageTable.query_insert]
          have hinj := st.seeds.injOn_idAt_activeAt hgood' le_rfl h1d (st.seeds.nodeAt 1 h1d x)
          have hy_in : y ∈ P.paddedDom d := (P.mem_paddedDom_iff d y).mpr (by simp [hdy])
          have hy_act : y ∈ st.seeds.activeAt (Insert.insert x (P.paddedDom d)) 1 h1d
              (st.seeds.nodeAt 1 h1d x) :=
            SeedAssignment.mem_activeAt_iff.mpr ⟨mem_insert_of_mem hy_in, hny⟩
          have hx_act : x ∈ st.seeds.activeAt (Insert.insert x (P.paddedDom d)) 1 h1d
              (st.seeds.nodeAt 1 h1d x) :=
            SeedAssignment.mem_activeAt_iff.mpr ⟨mem_insert_self x _, rfl⟩
          have hid_ne : st.seeds.idAt 1 le_rfl h1d y ≠ st.seeds.idAt 1 le_rfl h1d x :=
            fun h => hyx (hinj hy_act hx_act h)
          rw [Function.update_of_ne hid_ne, hy_old]
        · rw [Function.update_of_ne hu, hy_old]
    · have h2 : 2 ≤ ℓ := by omega
      have hyx : y ≠ x := fun h => by subst h; rw [Function.update_self] at hsly; omega
      rw [Function.update_of_ne hyx] at hdy hsly
      have hy_old := hwf.query_eq_of_storeLvl ℓ h1 hℓ u y vy hdy hny hsly
      by_cases hlt : ℓ < P.depth
      · rw [nodeQuery_inner _ _ h1 h2 hlt hℓ] at hy_old ⊢
        dsimp only [st', normalInsertFresh]; split_ifs <;> exact hy_old
      · have hd : ℓ = P.depth := by omega
        subst hd
        rw [nodeQuery_depth] at hy_old ⊢
        dsimp only [st', normalInsertFresh]
        by_cases hu : u = st.seeds.nodeAt P.depth le_rfl x
        · subst hu; rw [Function.update_self]; exact hy_old
        · rw [Function.update_of_ne hu, hy_old]
  · rw [hseeds, hdom_upd]
    have hw_old := hwf.wait_dom_eq ℓ h2 hℓ u
    by_cases hu : u = st.seeds.nodeAt ℓ hℓ x
    · subst hu
      have hf_eq : ((st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ
          (st.seeds.nodeAt ℓ hℓ x)).filter fun y => Function.update storeLvl x 1 y < ℓ) =
          Insert.insert x ((st.seeds.activeAt (P.paddedDom d) ℓ hℓ
            (st.seeds.nodeAt ℓ hℓ x)).filter fun y => storeLvl y < ℓ) := by
        ext y
        simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert]
        by_cases hyx : y = x
        · subst hyx; simp [show 1 < ℓ by omega]
        · simp [hyx]
      rw [hf_eq, image_insert, ← hw_old]
      by_cases hlt : ℓ < P.depth
      · rw [nodeWait_inner _ h2 hlt hℓ, nodeWait_inner _ h2 hlt hℓ]
        dsimp only [st', normalInsertFresh]
        rw [dite_eq_left rfl, WaitingList.dom_push]
      · have hd : ℓ = P.depth := by omega
        subst hd
        rw [nodeWait_depth, nodeWait_depth]
        dsimp only [st', normalInsertFresh]
        rw [Function.update_self, WaitingList.dom_push]
    · have hf_eq : ((st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ u).filter
          fun y => Function.update storeLvl x 1 y < ℓ) =
          (st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun y => storeLvl y < ℓ := by
        ext y
        simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_insert]
        by_cases hyx : y = x
        · subst hyx; simp [Ne.symm hu]
        · simp [hyx]
      rw [hf_eq, ← hw_old]
      by_cases hlt : ℓ < P.depth
      · rw [nodeWait_inner _ h2 hlt hℓ, nodeWait_inner _ h2 hlt hℓ]
        dsimp only [st', normalInsertFresh]; rw [dite_eq_right hu]
      · have hd : ℓ = P.depth := by omega
        subst hd
        rw [nodeWait_depth, nodeWait_depth]
        dsimp only [st', normalInsertFresh]; rw [Function.update_of_ne hu]
  · rw [hseeds, hdom_upd] at hy
    rw [hseeds]
    obtain ⟨hy_ins, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy
    by_cases hu : u = st.seeds.nodeAt ℓ hℓ x
    · subst hu
      have hinj := st.seeds.injOn_idAt_activeAt hgood' (by omega) hℓ (st.seeds.nodeAt ℓ hℓ x)
      have hx_act : x ∈ st.seeds.activeAt (Insert.insert x (P.paddedDom d)) ℓ hℓ
          (st.seeds.nodeAt ℓ hℓ x) :=
        SeedAssignment.mem_activeAt_iff.mpr ⟨mem_insert_self x _, rfl⟩
      by_cases hyx : y = x
      · subst hyx
        by_cases hlt : ℓ < P.depth
        · rw [nodeWait_inner _ h2 hlt hℓ]
          dsimp only [st', normalInsertFresh]
          rw [dite_eq_left rfl, WaitingList.lookup_push, Function.update_self]
        · have hd : ℓ = P.depth := by omega
          subst hd
          rw [nodeWait_depth]
          dsimp only [st', normalInsertFresh]
          rw [Function.update_self, WaitingList.lookup_push, Function.update_self]
      · have hy_dom : y ∈ P.paddedDom d := by
          rcases mem_insert.mp hy_ins with rfl | h
          · exact absurd rfl hyx
          · exact h
        rw [Function.update_of_ne hyx] at hsly
        have hy_old := hwf.wait_lookup_eq ℓ h2 hℓ _ y
          (SeedAssignment.mem_activeAt_iff.mpr ⟨hy_dom, hny⟩) hsly
        have hid_ne : st.seeds.idAt ℓ (by omega) hℓ y ≠ st.seeds.idAt ℓ (by omega) hℓ x :=
          fun h => hyx (hinj hy hx_act h)
        by_cases hlt : ℓ < P.depth
        · rw [nodeWait_inner _ h2 hlt hℓ] at hy_old ⊢
          dsimp only [st', normalInsertFresh]
          rw [dite_eq_left rfl, WaitingList.lookup_push, Function.update_of_ne hid_ne, hy_old]
        · have hd : ℓ = P.depth := by omega
          subst hd
          rw [nodeWait_depth] at hy_old ⊢
          dsimp only [st', normalInsertFresh]
          rw [Function.update_self, WaitingList.lookup_push, Function.update_of_ne hid_ne, hy_old]
    · have hyx : y ≠ x := fun h => by subst h; exact hu hny.symm
      have hy_dom : y ∈ P.paddedDom d := by
        rcases mem_insert.mp hy_ins with rfl | h
        · exact absurd rfl hyx
        · exact h
      rw [Function.update_of_ne hyx] at hsly
      have hy_old := hwf.wait_lookup_eq ℓ h2 hℓ u y
        (SeedAssignment.mem_activeAt_iff.mpr ⟨hy_dom, hny⟩) hsly
      by_cases hlt : ℓ < P.depth
      · rw [nodeWait_inner _ h2 hlt hℓ] at hy_old ⊢
        dsimp only [st', normalInsertFresh]; rw [dite_eq_right hu, hy_old]
      · have hd : ℓ = P.depth := by omega
        subst hd
        rw [nodeWait_depth] at hy_old ⊢
        dsimp only [st', normalInsertFresh]; rw [Function.update_of_ne hu, hy_old]

/-! ## Section 1: Uniform node helpers for `Algorithm 3` (`removeWaitAtNode`, `replaceAtNode`) -/

private def removeWaitLeafAt (st : P.TreeState) (u : Fin (P.numNodes P.depth))
    (k : Fin (2 ^ P.idBits P.depth)) : P.TreeState :=
  let ln := st.leaves u
  st.updateLeaf u
    { ln with leafMeta := { ln.leafMeta with wait := ln.leafMeta.wait.remove k } }

/-- Remove `k` from the waiting list of node `(L, uL)` (`2 ≤ L ≤ depth`). -/
def removeWaitAtNode (st : P.TreeState) (L : ℕ) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) : P.TreeState :=
  if hlt : L < P.depth then
    let nd := st.inner L h2L hlt uL
    st.updateInner L h2L hlt uL { nd with wait := nd.wait.remove k }
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) → P.TreeState)
      (removeWaitLeafAt st) hd.symm uL k

theorem seeds_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).seeds = st.seeds := by
  dsimp only [removeWaitAtNode]
  by_cases hlt : L < P.depth
  · rw [dite_eq_left hlt]; exact st.seeds_updateInner_of_seed_eq _ _ _ _ rfl
  · have hd : L = P.depth := by omega
    subst hd; rw [dite_eq_right (lt_irrefl _)]; exact st.seeds_updateLeaf_of_seed_eq _ _ rfl

theorem sentCount_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).sentCount = st.sentCount := by
  dsimp only [removeWaitAtNode]
  by_cases hlt : L < P.depth
  · rw [dite_eq_left hlt]; rfl
  · have hd : L = P.depth := by omega
    subst hd; rw [dite_eq_right (lt_irrefl _)]; rfl

theorem nodeDom_removeWaitAtNode (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeDom ℓ h1 hℓ u = st.nodeDom ℓ h1 hℓ u := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]
    by_cases hℓ1 : ℓ = 1
    · subst hℓ1; simp [updateInner]
    · by_cases hlt' : ℓ < P.depth
      · simp only [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateInner]
        by_cases hℓL : ℓ = L
        · subst hℓL; rw [dite_eq_left rfl]; by_cases hu : u = uL <;> simp [hu]
        · rw [dite_eq_right hℓL]
      · have hd' : ℓ = P.depth := by omega
        subst hd'; simp [updateInner]
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [removeWaitLeafAt]
    by_cases hℓ1 : ℓ = 1
    · subst hℓ1; simp [updateLeaf]
    · by_cases hlt' : ℓ < P.depth
      · simp [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateLeaf]
      · have hd' : ℓ = P.depth := by omega
        subst hd'; simp only [nodeDom_depth, updateLeaf]
        by_cases hu : u = uL
        · subst hu; rw [Function.update_self]; rfl
        · simp [hu]

theorem nodeQuery_removeWaitAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]
    by_cases hℓ1 : ℓ = 1
    · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; rfl
    · by_cases hlt' : ℓ < P.depth
      · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ, nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]
        dsimp only [updateInner]
        by_cases hℓL : ℓ = L
        · subst hℓL; rw [dite_eq_left rfl]; dsimp only
          by_cases hu : u = uL <;> simp [hu]
        · rw [dite_eq_right hℓL]
      · have hd' : ℓ = P.depth := by omega
        subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; rfl
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [removeWaitLeafAt]
    by_cases hℓ1 : ℓ = 1
    · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; rfl
    · by_cases hlt' : ℓ < P.depth
      · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ, nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]
        rfl
      · have hd' : ℓ = P.depth := by omega
        subst hd'; rw [nodeQuery_depth, nodeQuery_depth]
        dsimp only [updateLeaf]
        by_cases hu : u = uL
        · subst hu; rw [Function.update_self]; rfl
        · rw [Function.update_of_ne hu]

theorem nodeWait_removeWaitAtNode_same (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L)
    (hLL : L ≤ P.depth) (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L)) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeWait L h2L hLL uL =
      (st.nodeWait L h2L hLL uL).remove k := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt, nodeWait_inner _ h2L hLlt hLL, nodeWait_inner _ h2L hLlt hLL]
    simp [updateInner]
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _), nodeWait_depth, nodeWait_depth]
    simp [removeWaitLeafAt, updateLeaf]

theorem nodeWait_removeWaitAtNode_other (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L)
    (hLL : L ≤ P.depth) (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.removeWaitAtNode L h2L hLL uL k).nodeWait ℓ h2 hℓ u = st.nodeWait ℓ h2 hℓ u := by
  dsimp only [removeWaitAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]
    by_cases hlt' : ℓ < P.depth
    · rw [nodeWait_inner _ h2 hlt' hℓ, nodeWait_inner _ h2 hlt' hℓ]
      dsimp only [updateInner]
      by_cases hℓL : ℓ = L
      · subst hℓL; rw [dite_eq_left rfl]; dsimp only; rw [Function.update_of_ne (hdiff rfl)]
      · rw [dite_eq_right hℓL]
    · have hd' : ℓ = P.depth := by omega
      subst hd'; rw [nodeWait_depth, nodeWait_depth]; rfl
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [removeWaitLeafAt]
    by_cases hlt' : ℓ < P.depth
    · rw [nodeWait_inner _ h2 hlt' hℓ, nodeWait_inner _ h2 hlt' hℓ]; rfl
    · have hd' : ℓ = P.depth := by omega
      subst hd'; rw [nodeWait_depth, nodeWait_depth]; simp [updateLeaf, hdiff rfl]

private def replaceInnerAt (st : P.TreeState) (L : ℕ) (h2 : 2 ≤ L) (hlt : L < P.depth)
    (u : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L)) (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    P.TreeState :=
  let nd := st.inner L h2 hlt u
  if h : k_old ∈ nd.table.tableMeta.dom ∧ k_new ∉ nd.table.tableMeta.dom.erase k_old then
    st.updateInner L h2 hlt u
      { nd with wait := wait', table := nd.table.replace k_old k_new qv_new h.1 h.2 }
  else st

private def replaceLeafAt
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin (P.numNodes P.depth))
    (wait' : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (k_old k_new : Fin (2 ^ P.idBits P.depth))
    (qv_new : Fin (P.quotUniv P.depth) × Fin P.valBound) : P.TreeState :=
  let ln := st.leaves u
  if h : k_old ∈ ln.dom ∧ k_new ∉ ln.dom.erase k_old then
    st.updateLeaf u (ln.replace scheme wait' k_old k_new qv_new h.1 h.2)
  else st

/-- Replace `k_old` with `(k_new, qv_new)` and update waiting list to `wait'` at `(L, uL)`
(`2 ≤ L ≤ depth`, `Algorithm 3` Branch 2). -/
def replaceAtNode (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (L : ℕ) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if hlt : L < P.depth then
    replaceInnerAt st L h2L hlt uL wait' k_old k_new qv_new
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) →
        WaitingList (P.idBits m) (P.idBits (m - 1)) (P.waitCap m) →
        Fin (2 ^ P.idBits m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (replaceLeafAt scheme st) hd.symm uL wait' k_old k_new qv_new

theorem seeds_replaceAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).seeds = st.seeds := by
  dsimp only [replaceAtNode]
  by_cases hlt : L < P.depth
  · rw [dite_eq_left hlt]; dsimp only [replaceInnerAt]
    split_ifs with h
    · exact st.seeds_updateInner_of_seed_eq _ _ _ _ rfl
    · rfl
  · have hd : L = P.depth := by omega
    subst hd; rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]
    split_ifs with h
    · exact st.seeds_updateLeaf_of_seed_eq _ _ rfl
    · rfl

theorem sentCount_replaceAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).sentCount = st.sentCount := by
  dsimp only [replaceAtNode]
  by_cases hlt : L < P.depth
  · rw [dite_eq_left hlt]; dsimp only [replaceInnerAt]; split_ifs <;> rfl
  · have hd : L = P.depth := by omega
    subst hd; rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]; split_ifs <;> rfl

theorem nodeDom_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeDom L h1L hLL uL =
      Insert.insert k_new ((st.nodeDom L h1L hLL uL).erase k_old) := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew
    rw [dite_eq_left hLlt, nodeDom_inner _ h1L h2L hLlt hLL, nodeDom_inner st h1L h2L hLlt hLL]
    dsimp only [replaceInnerAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    simp [updateInner]
  · have hdL : L = P.depth := by omega
    subst hdL
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeDom_depth, nodeDom_depth]
    dsimp only [replaceLeafAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    simp [updateLeaf]

theorem nodeDom_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeDom ℓ h1 hℓ u =
      st.nodeDom ℓ h1 hℓ u := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]; dsimp only [replaceInnerAt]
    split_ifs with h
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; simp [updateInner]
      · by_cases hlt' : ℓ < P.depth
        · simp only [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateInner]
          by_cases hℓL : ℓ = L
          · subst hℓL; rw [dite_eq_left rfl]; dsimp only; rw [Function.update_of_ne (hdiff rfl)]
          · rw [dite_eq_right hℓL]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; simp [updateInner]
    · rfl
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]
    split_ifs with h
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; simp [updateLeaf]
      · by_cases hlt' : ℓ < P.depth
        · simp [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateLeaf]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; simp only [nodeDom_depth, updateLeaf]; simp [hdiff rfl]
    · rfl

theorem nodeQuery_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new k' : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeQuery scheme L h1L hLL uL
      k' = Function.update
        (Function.update (st.nodeQuery scheme L h1L hLL uL) k_old none) k_new (some qv_new) k' := by
  have hrhs : Function.update
      (Function.update (st.nodeQuery scheme L h1L hLL uL) k_old none) k_new (some qv_new) k' =
      if k' = k_new then some qv_new
      else if k' = k_old then none
      else st.nodeQuery scheme L h1L hLL uL k' := by
    by_cases hn : k' = k_new
    · subst hn; simp
    · by_cases ho : k' = k_old
      · subst ho; simp [hn]
      · simp [hn, ho]
  rw [hrhs]
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew
    rw [dite_eq_left hLlt, nodeQuery_inner _ _ h1L h2L hLlt hLL,
      nodeQuery_inner _ _ h1L h2L hLlt hLL]
    dsimp only [replaceInnerAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    by_cases hn : k' = k_new
    · subst hn; simp [updateInner]
    · by_cases ho : k' = k_old
      · subst ho; simp [updateInner, hn]
      · simp [updateInner, hn, ho]
  · have hdL : L = P.depth := by omega
    subst hdL
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeQuery_depth, nodeQuery_depth]
    dsimp only [replaceLeafAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    by_cases hn : k' = k_new
    · subst hn; simp [updateLeaf]
    · by_cases ho : k' = k_old
      · subst ho; simp [updateLeaf, hn]
      · simp [updateLeaf, hn, ho]

theorem nodeQuery_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]; dsimp only [replaceInnerAt]
    split_ifs with h
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; rfl
      · by_cases hlt' : ℓ < P.depth
        · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ,
            nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]
          dsimp only [updateInner]
          by_cases hℓL : ℓ = L
          · subst hℓL; rw [dite_eq_left rfl]; dsimp only; rw [Function.update_of_ne (hdiff rfl)]
          · rw [dite_eq_right hℓL]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; rfl
    · rfl
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]
    split_ifs with h
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; rfl
      · by_cases hlt' : ℓ < P.depth
        · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ,
            nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]; rfl
        · have hd' : ℓ = P.depth := by omega
          subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; simp [updateLeaf, hdiff rfl]
    · rfl

theorem nodeWait_replaceAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    (hold : k_old ∈ st.nodeDom L h1L hLL uL)
    (hnew : k_new ∉ (st.nodeDom L h1L hLL uL).erase k_old) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeWait L h2L hLL uL =
      wait' := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [nodeDom_inner st h1L h2L hLlt hLL] at hold hnew
    rw [dite_eq_left hLlt, nodeWait_inner _ h2L hLlt hLL]
    dsimp only [replaceInnerAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    simp [updateInner]
  · have hdL : L = P.depth := by omega
    subst hdL
    rw [nodeDom_depth] at hold hnew
    rw [dite_eq_right (lt_irrefl _), nodeWait_depth]
    dsimp only [replaceLeafAt]
    rw [dite_eq_left ⟨hold, hnew⟩]
    simp [updateLeaf, LeafNode.replace, LeafNode.ofFixedEncoded]

theorem nodeWait_replaceAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h2L : 2 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L))
    (wait' : WaitingList (P.idBits L) (P.idBits (L - 1)) (P.waitCap L))
    (k_old k_new : Fin (2 ^ P.idBits L))
    (qv_new : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.replaceAtNode scheme L h2L hLL uL wait' k_old k_new qv_new).nodeWait ℓ h2 hℓ u =
      st.nodeWait ℓ h2 hℓ u := by
  dsimp only [replaceAtNode]
  by_cases hLlt : L < P.depth
  · rw [dite_eq_left hLlt]; dsimp only [replaceInnerAt]
    split_ifs with h
    · by_cases hlt' : ℓ < P.depth
      · rw [nodeWait_inner _ h2 hlt' hℓ, nodeWait_inner _ h2 hlt' hℓ]
        dsimp only [updateInner]
        by_cases hℓL : ℓ = L
        · subst hℓL; rw [dite_eq_left rfl]; dsimp only; rw [Function.update_of_ne (hdiff rfl)]
        · rw [dite_eq_right hℓL]
      · have hd' : ℓ = P.depth := by omega
        subst hd'; rw [nodeWait_depth, nodeWait_depth]; rfl
    · rfl
  · have hdL : L = P.depth := by omega
    subst hdL; rw [dite_eq_right (lt_irrefl _)]; dsimp only [replaceLeafAt]
    split_ifs with h
    · by_cases hlt' : ℓ < P.depth
      · rw [nodeWait_inner _ h2 hlt' hℓ, nodeWait_inner _ h2 hlt' hℓ]; rfl
      · have hd' : ℓ = P.depth := by omega
        subst hd'; rw [nodeWait_depth, nodeWait_depth]; simp [updateLeaf, hdiff rfl]
    · rfl

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
