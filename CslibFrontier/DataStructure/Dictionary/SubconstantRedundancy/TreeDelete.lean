/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeInsert

/-!
# Quotient-Recovering Deletion (`Algorithm 3`) in the Multi-Level Dictionary Tree

This file formalizes `Algorithm 3` (`deleteAndGetQuotient`) and normal-path deletion
(`normalDeleteMem`) of Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic
Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3, Algorithm 3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 31 / printed p. 30).

## Main definitions

* `TreeSchedule.TreeState.deleteAndGetQuotient`: recursive upward deletion and quotient recovery
  (`Algorithm 3`).
* `TreeSchedule.TreeState.normalDeleteMem`: normal-path deletion starting at leaf level `depth`.

## Main results

* `TreeSchedule.TreeState.deleteAndGetQuotient_spec`: exact quotient-and-value recovery
  (`(q_out, v_out) = (quotAt ℓ z, v_z)`) and prefix invariant preservation across levels `1 .. ℓ`.
* `TreeSchedule.TreeState.wellFormedPadded_normalDeleteMem`: preservation of `WellFormedPadded`
  under non-underflowing deletion.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

private theorem image_erase_of_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S F : Finset α} (hFS : F ⊆ S) {f : α → β} (hinj : Set.InjOn f S) {x : α} (hx : x ∈ S) :
    (F.image f).erase (f x) = (F.erase x).image f := by
  ext b
  simp only [mem_erase, mem_image]
  constructor
  · rintro ⟨hb_ne, a, ha, rfl⟩
    exact ⟨a, ⟨fun hax => hb_ne (congrArg f hax), ha⟩, rfl⟩
  · rintro ⟨a, ⟨hax, ha⟩, rfl⟩
    exact ⟨fun heq => hax (hinj (hFS ha) hx heq), a, ha, rfl⟩

namespace TreeSchedule.TreeState

variable {P : TreeSchedule}
/-! ## Section 2: `Algorithm 3` (`deleteAndGetQuotient`) and `normalDeleteMem` -/

/-- **`Algorithm 3` (`DeleteAndGetQuotient`, [LiLiangYuZhou2024, Section 5.3], PDF p. 31 /
printed p. 30)**: recursively deletes `z_id` from levels `1 .. ℓ` along `u`'s ancestor path while
maintaining full capacity at levels `2 .. ℓ` via waiting-list replacement and returning
`(st', z_quot^[ℓ], z_val)`. -/
noncomputable def deleteAndGetQuotient
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) :
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ P.depth → Fin (P.numNodes ℓ) → Fin (2 ^ P.idBits ℓ) →
      P.TreeState × Fin (P.quotUniv ℓ) × Fin P.valBound
  | 0, h1, _, _, _ => False.elim (by omega)
  | 1, _, _, u₁, z_id =>
    let qv := ((st.roots u₁).table.query z_id).getD (⟨0, P.quotUniv_pos 1⟩, ⟨0, P.val_pos⟩)
    (st.updateRoot u₁ { (st.roots u₁) with table := (st.roots u₁).table.delete z_id },
      qv.1, qv.2)
  | m + 2, _, hℓ, u_cur, z_id =>
    have h2 : 2 ≤ m + 2 := by omega
    have h1_prev : 1 ≤ m + 1 := by omega
    have hlt_prev : m + 1 < P.depth := by omega
    let u_prev := P.parentNode (m + 1) u_cur
    let w := st.nodeWait (m + 2) h2 hℓ u_cur
    match w.lookup z_id with
    | some z_id_prev =>
      let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev z_id_prev
      let z_quot_cur :=
        (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, z_id_prev, res.2.1)).2.2
      (res.1.removeWaitAtNode (m + 2) h2 hℓ u_cur z_id, z_quot_cur, res.2.2)
    | none =>
      let z_qv := (st.nodeQuery scheme (m + 2) (by omega) hℓ u_cur z_id).getD
        (⟨0, P.quotUniv_pos (m + 2)⟩, ⟨0, P.val_pos⟩)
      if hne : w.dom.Nonempty then
        let popRes := w.pop hne
        let y_id_cur := popRes.1.1
        let y_id_prev := popRes.1.2
        let wait' := popRes.2
        let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev y_id_prev
        let y_quot_cur :=
          (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res.2.1)).2.2
        (res.1.replaceAtNode scheme (m + 2) h2 hℓ u_cur wait' z_id y_id_cur
          (y_quot_cur, res.2.2), z_qv.1, z_qv.2)
      else
        (st, z_qv.1, z_qv.2)

private theorem deleteAndGetQuotient_succ_succ
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (m : ℕ) (h1 : 1 ≤ m + 2) (hℓ : m + 2 ≤ P.depth)
    (u_cur : Fin (P.numNodes (m + 2))) (z_id : Fin (2 ^ P.idBits (m + 2))) :
    st.deleteAndGetQuotient scheme (m + 2) h1 hℓ u_cur z_id =
      let h2 : 2 ≤ m + 2 := by omega
      let h1_prev : 1 ≤ m + 1 := by omega
      let hlt_prev : m + 1 < P.depth := by omega
      let u_prev := P.parentNode (m + 1) u_cur
      let w := st.nodeWait (m + 2) h2 hℓ u_cur
      match w.lookup z_id with
      | some z_id_prev =>
        let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev z_id_prev
        let z_quot_cur :=
          (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, z_id_prev, res.2.1)).2.2
        (res.1.removeWaitAtNode (m + 2) h2 hℓ u_cur z_id, z_quot_cur, res.2.2)
      | none =>
        let z_qv := (st.nodeQuery scheme (m + 2) (by omega) hℓ u_cur z_id).getD
          (⟨0, P.quotUniv_pos (m + 2)⟩, ⟨0, P.val_pos⟩)
        if hne : w.dom.Nonempty then
          let popRes := w.pop hne
          let y_id_cur := popRes.1.1
          let y_id_prev := popRes.1.2
          let wait' := popRes.2
          let res := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev y_id_prev
          let y_quot_cur :=
            (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res.2.1)).2.2
          (res.1.replaceAtNode scheme (m + 2) h2 hℓ u_cur wait' z_id y_id_cur
            (y_quot_cur, res.2.2), z_qv.1, z_qv.2)
        else
          (st, z_qv.1, z_qv.2) := rfl

private theorem stepCoordEquiv_quotAt (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hlt : m < P.depth) (u_cur : Fin (P.numNodes (m + 1))) (w : Fin P.paddedUniv)
    (hnw : seeds.nodeAt (m + 1) hlt w = u_cur) :
    (seeds.stepCoordEquiv h1 hlt
      (P.parentNode m u_cur, seeds.idAt m h1 hlt.le w, seeds.quotAt m h1 hlt.le w)).2.2 =
      seeds.quotAt (m + 1) (by omega) hlt w := by
  have hu_prev : P.parentNode m u_cur = seeds.nodeAt m hlt.le w := by
    rw [← hnw, seeds.parentNode_nodeAt hlt w]
  have hc_eq : (P.parentNode m u_cur, seeds.idAt m h1 hlt.le w, seeds.quotAt m h1 hlt.le w) =
      seeds.levelCoordEquiv m h1 hlt.le w :=
    Prod.ext (hu_prev.trans (seeds.levelCoordEquiv_fst h1 hlt.le w).symm) rfl
  rw [hc_eq]
  have hstep := seeds.levelCoordEquiv_succ h1 hlt
  exact congrArg (fun c => c.2.2) (congrFun (congrArg DFunLike.coe hstep.symm) w)

/-- Inductive prefix postcondition of `deleteAndGetQuotient` at level `ℓ` (`1 ≤ ℓ ≤ depth`). -/
structure DeletePrefixPost
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st st' : P.TreeState) (d : P.PaddedDict) (storeLvl storeLvl' : Fin P.paddedUniv → ℕ)
    (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (z : Fin P.paddedUniv) : Prop where
  seeds_eq : st'.seeds = st.seeds
  sentCount_eq : st'.sentCount = st.sentCount
  storeLvl_zero_z : storeLvl' z = 0
  storeLvl_outside : ∀ w, w ∉ (P.paddedDom d).erase z → storeLvl' w = 0
  storeLvl_le_bounds : ∀ w ∈ (P.paddedDom d).erase z, storeLvl w ≤ ℓ →
    1 ≤ storeLvl' w ∧ storeLvl' w ≤ ℓ
  storeLvl_gt_eq : ∀ w ∈ (P.paddedDom d).erase z, ℓ < storeLvl w → storeLvl' w = storeLvl w
  above_dom_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u, st'.nodeDom j hj1 hjd u = st.nodeDom j hj1 hjd u
  above_query_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u k, st'.nodeQuery scheme j hj1 hjd u k = st.nodeQuery scheme j hj1 hjd u k
  above_wait_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjd : j ≤ P.depth), ℓ < j →
    ∀ u, st'.nodeWait j hj2 hjd u = st.nodeWait j hj2 hjd u
  le_dom_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j)),
    st'.nodeDom j hj1 (hjℓ.trans hℓ) u =
      ((st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u).filter
        fun w => storeLvl' w = j).image (st.seeds.idAt j hj1 (hjℓ.trans hℓ))
  le_query_eq : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j))
    (w : Fin P.paddedUniv) (vw : Fin P.valBound),
    Function.update d z none w = some vw → st.seeds.nodeAt j (hjℓ.trans hℓ) w = u →
      storeLvl' w = j →
      st'.nodeQuery scheme j hj1 (hjℓ.trans hℓ) u (st.seeds.idAt j hj1 (hjℓ.trans hℓ) w) =
        some (st.seeds.quotAt j hj1 (hjℓ.trans hℓ) w, vw)
  le_inner_full : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjlt : j < P.depth), j ≤ ℓ →
    ∀ u, ((st'.inner j hj2 hjlt u).table.tableMeta.dom).card = P.tableCap j
  le_wait_dom_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j)),
    (st'.nodeWait j hj2 (hjℓ.trans hℓ) u).dom =
      ((st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u).filter
        fun w => storeLvl' w < j).image (st.seeds.idAt j (by omega) (hjℓ.trans hℓ))
  le_wait_lookup_eq : ∀ (j : ℕ) (hj2 : 2 ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes j))
    (w : Fin P.paddedUniv),
    w ∈ st.seeds.activeAt ((P.paddedDom d).erase z) j (hjℓ.trans hℓ) u → storeLvl' w < j →
      (st'.nodeWait j hj2 (hjℓ.trans hℓ) u).lookup
        (st.seeds.idAt j (by omega) (hjℓ.trans hℓ) w) =
        some (st.seeds.idAt (j - 1) (by omega) (by omega) w)

/-- **`Algorithm 3` correctness (`deleteAndGetQuotient_spec`)**: for any active key `z` at `(ℓ, u)`
with `storeLvl z ≤ ℓ` whose ancestors at levels `2 .. ℓ` strictly exceed `nLow j`,
`deleteAndGetQuotient` returns `(quotAt ℓ z, v_z)` and establishes `DeletePrefixPost` up to `ℓ`. -/
theorem deleteAndGetQuotient_spec
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) :
    ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
      (z : Fin P.paddedUniv) (vz : Fin P.valBound),
      d z = some vz →
      st.seeds.nodeAt ℓ hℓ z = u →
      storeLvl z ≤ ℓ →
      (∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ ℓ),
        P.nLow j <
          (st.seeds.activeAt (P.paddedDom d) j (hj.trans hℓ) (P.ancestorAt hj u)).card) →
      let res := st.deleteAndGetQuotient scheme ℓ h1 hℓ u (st.seeds.idAt ℓ h1 hℓ z)
      let out := res.2
      out.1 = st.seeds.quotAt ℓ h1 hℓ z ∧
      out.2 = vz ∧
      ∃ storeLvl' : Fin P.paddedUniv → ℕ,
        DeletePrefixPost scheme st res.1 d storeLvl storeLvl' ℓ hℓ z := by
  intro ℓ
  induction ℓ with
  | zero => intro h1; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro h1 hℓ u₁ z vz hdz hnz hslz _
      have hz_in : z ∈ P.paddedDom d := (P.mem_paddedDom_iff d z).mpr (by simp [hdz])
      have hslz1 : storeLvl z = 1 := by
        have := (hwf.storeLvl_bounds z hz_in).1; omega
      have hqz := hwf.query_eq_of_storeLvl 1 le_rfl hℓ u₁ z vz hdz hnz hslz1
      rw [nodeQuery_one] at hqz
      dsimp only [deleteAndGetQuotient]
      rw [hqz, Option.getD_some]
      refine ⟨rfl, rfl, Function.update storeLvl z 0, ?_⟩
      refine
        { seeds_eq := st.seeds_updateRoot_of_seed_eq _ _ rfl
          sentCount_eq := rfl
          storeLvl_zero_z := Function.update_self ..
          storeLvl_outside := fun w hw => by
            by_cases hwz : w = z
            · subst hwz; exact Function.update_self ..
            · rw [Function.update_of_ne hwz]
              exact hwf.storeLvl_outside w fun hwin => hw (mem_erase.mpr ⟨hwz, hwin⟩)
          storeLvl_le_bounds := fun w hw hle => by
            obtain ⟨hwz, hwin⟩ := mem_erase.mp hw
            rw [Function.update_of_ne hwz]
            exact ⟨(hwf.storeLvl_bounds w hwin).1, hle⟩
          storeLvl_gt_eq := fun w hw _ => Function.update_of_ne (mem_erase.mp hw).1 ..
          above_dom_eq := fun j hj1 hjd hgt u => by
            by_cases hlt' : j < P.depth
            · simp [nodeDom_inner _ hj1 (by omega) hlt' hjd, updateRoot]
            · have hd' : j = P.depth := by omega
              subst hd'; simp [updateRoot]
          above_query_eq := fun j hj1 hjd hgt u k => by
            by_cases hlt' : j < P.depth
            · rw [nodeQuery_inner _ _ hj1 (by omega) hlt' hjd,
                nodeQuery_inner _ _ hj1 (by omega) hlt' hjd]; rfl
            · have hd' : j = P.depth := by omega
              subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; rfl
          above_wait_eq := fun j hj2 hjd _ u => by
            by_cases hlt' : j < P.depth
            · simp [nodeWait_inner _ hj2 hlt' hjd, updateRoot]
            · have hd' : j = P.depth := by omega
              subst hd'; simp [updateRoot]
          le_dom_eq := fun j hj1 hjℓ u => by
            obtain rfl : j = 1 := by omega
            rw [nodeDom_one]
            have hd_old := hwf.dom_eq 1 le_rfl hℓ u
            rw [nodeDom_one] at hd_old
            dsimp only [updateRoot]
            by_cases hu : u = u₁
            · rw [hu] at hd_old ⊢
              rw [Function.update_self, StorageTable.dom_delete, hd_old]
              have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds le_rfl hℓ u₁
              have herase_img := image_erase_of_injOn
                (filter_subset (fun w => storeLvl w = 1) _) hinj
                (SeedAssignment.mem_activeAt_iff.mpr ⟨hz_in, hnz⟩)
              rw [herase_img]
              congr 1; ext w
              simp only [mem_erase, mem_filter, SeedAssignment.mem_activeAt_iff]
              by_cases hwz : w = z
              · subst hwz; simp
              · simp [hwz]
            · rw [Function.update_of_ne hu, hd_old]
              congr 1; ext w
              simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
              by_cases hwz : w = z
              · subst hwz
                have hnu : st.seeds.nodeAt 1 hℓ w ≠ u := fun h => hu (h.symm.trans hnz)
                simp [hnu]
              · simp [hwz]
          le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => by
            obtain rfl : j = 1 := by omega
            have hwz : w ≠ z := fun h => by subst h; simp at hdw
            rw [Function.update_of_ne hwz] at hdw hslw
            have hw_in : w ∈ P.paddedDom d := (P.mem_paddedDom_iff d w).mpr (by simp [hdw])
            have hq_old := hwf.query_eq_of_storeLvl 1 le_rfl hℓ u w vw hdw hnw hslw
            rw [nodeQuery_one] at hq_old ⊢
            dsimp only [updateRoot]
            by_cases hu : u = u₁
            · rw [hu] at hq_old hnw ⊢
              rw [Function.update_self, StorageTable.query_delete]
              have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds le_rfl hℓ u₁
              have hid_ne : st.seeds.idAt 1 hj1 _ w ≠ st.seeds.idAt 1 h1 hℓ z :=
                fun h => hwz (hinj (SeedAssignment.mem_activeAt_iff.mpr ⟨hw_in, hnw⟩)
                  (SeedAssignment.mem_activeAt_iff.mpr ⟨hz_in, hnz⟩) h)
              rw [Function.update_of_ne hid_ne, hq_old]
            · rw [Function.update_of_ne hu, hq_old]
          le_inner_full := fun j hj2 _ hjℓ => False.elim (by omega)
          le_wait_dom_eq := fun j hj2 hjℓ => False.elim (by omega)
          le_wait_lookup_eq := fun j hj2 hjℓ => False.elim (by omega) }
    | succ m =>
      intro h1 hℓ u_cur z vz hdz hnz hslz hloads
      have h2 : 2 ≤ m + 2 := by omega
      have h1_prev : 1 ≤ m + 1 := by omega
      have hlt_prev : m + 1 < P.depth := by omega
      let u_prev := P.parentNode (m + 1) u_cur
      let z_id := st.seeds.idAt (m + 2) h1 hℓ z
      have hz_in : z ∈ P.paddedDom d := (P.mem_paddedDom_iff d z).mpr (by simp [hdz])
      have hz_act : z ∈ st.seeds.activeAt (P.paddedDom d) (m + 2) hℓ u_cur :=
        SeedAssignment.mem_activeAt_iff.mpr ⟨hz_in, hnz⟩
      have hloads_prev : ∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ m + 1),
          P.nLow j < (st.seeds.activeAt (P.paddedDom d) j (hj.trans hlt_prev.le)
            (P.ancestorAt hj u_prev)).card := fun j hj2 hj => by
        rw [← P.ancestorAt_succ hj u_cur]
        exact hloads j hj2 (Nat.le_succ_of_le hj)
      let w_list := st.nodeWait (m + 2) h2 hℓ u_cur
      dsimp only
      rw [st.deleteAndGetQuotient_succ_succ scheme m h1 hℓ u_cur z_id]
      dsimp only
      rcases hlk : (st.nodeWait (m + 2) h2 hℓ u_cur).lookup z_id with _ | z_id_prev
      · -- Branch 2: `z` is NOT in `w_list`, so `storeLvl z = m + 2`
        have hz_not_wait : z_id ∉ w_list.dom :=
          mt (w_list.isSome_lookup_iff z_id).mpr (by simp [w_list, hlk])
        have hslz_eq : storeLvl z = m + 2 := by
          by_contra hne_lvl
          have hlt_lvl : storeLvl z < m + 2 := by omega
          have hmem_w : z_id ∈ w_list.dom := by
            dsimp only [w_list, z_id]
            rw [hwf.wait_dom_eq (m + 2) h2 hℓ u_cur]
            exact mem_image_of_mem _ (mem_filter.mpr ⟨hz_act, hlt_lvl⟩)
          exact hz_not_wait hmem_w
        have hqz := hwf.query_eq_of_storeLvl (m + 2) (by omega) hℓ u_cur z vz hdz hnz hslz_eq
        have hne_wait : w_list.dom.Nonempty := by
          apply Finset.card_pos.mp
          dsimp only [w_list]
          rw [card_nodeWait_dom_eq hwf h2 hℓ u_cur]
          have hload_cur := hloads (m + 2) h2 le_rfl
          rw [P.ancestorAt_refl] at hload_cur
          omega
        have hqz' : st.nodeQuery scheme (m + 2) (by omega) hℓ u_cur z_id =
            some (st.seeds.quotAt (m + 2) (by omega) hℓ z, vz) := hqz
        have hne_w' : (st.nodeWait (m + 2) h2 hℓ u_cur).dom.Nonempty := hne_wait
        dsimp only
        rw [hqz', Option.getD_some, dite_eq_left hne_w']
        dsimp only
        set popRes := w_list.pop hne_wait
        let y_id_cur := popRes.1.1
        let y_id_prev := popRes.1.2
        let wait' := popRes.2
        have hy_mem_w : y_id_cur ∈ w_list.dom := w_list.pop_fst_mem_dom hne_wait
        have hy_lk : w_list.lookup y_id_cur = some y_id_prev := w_list.lookup_pop_fst hne_wait
        have hw_dom := hwf.wait_dom_eq (m + 2) h2 hℓ u_cur
        change w_list.dom = _ at hw_dom
        rw [hw_dom] at hy_mem_w
        obtain ⟨y, hy_filt, hy_id_eq⟩ := mem_image.mp hy_mem_w
        obtain ⟨hy_act, hsly_lt⟩ := mem_filter.mp hy_filt
        obtain ⟨hy_in, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy_act
        obtain ⟨vy, hdy⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d y).mp hy_in)
        have hy_lk_expected := hwf.wait_lookup_eq (m + 2) h2 hℓ u_cur y hy_act hsly_lt
        change w_list.lookup (st.seeds.idAt (m + 2) _ hℓ y) = _ at hy_lk_expected
        rw [hy_id_eq, hy_lk] at hy_lk_expected
        have hy_id_prev_eq : st.seeds.idAt (m + 1) h1_prev hlt_prev.le y = y_id_prev :=
          (Option.some.inj hy_lk_expected).symm
        have hny_prev : st.seeds.nodeAt (m + 1) hlt_prev.le y = u_prev := by
          dsimp only [u_prev]; rw [← hny, st.seeds.parentNode_nodeAt hℓ y]
        have hyz : y ≠ z := fun h => by subst h; omega
        obtain ⟨hq_rec, hv_rec, storeLvl_y, hpost_y⟩ :=
          ih h1_prev hlt_prev.le u_prev y vy hdy hny_prev (by omega) hloads_prev
        rw [hy_id_prev_eq] at hq_rec hv_rec hpost_y
        set res_y := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev y_id_prev
        have hq_y_cur :
            (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res_y.2.1)).2.2 =
              st.seeds.quotAt (m + 2) (by omega) hℓ y := by
          rw [hq_rec, ← hy_id_prev_eq]
          exact stepCoordEquiv_quotAt st.seeds h1_prev hlt_prev u_cur y hny
        have hold_cur : z_id ∈ res_y.1.nodeDom (m + 2) (by omega) hℓ u_cur := by
          rw [hpost_y.above_dom_eq (m + 2) (by omega) hℓ (by omega) u_cur,
            hwf.dom_eq (m + 2) (by omega) hℓ u_cur]
          exact mem_image_of_mem _ (mem_filter.mpr ⟨hz_act, hslz_eq⟩)
        have hinj_cur := st.seeds.injOn_idAt_activeAt hwf.goodSeeds (by omega) hℓ u_cur
        have hy_not_dom : y_id_cur ∉ st.nodeDom (m + 2) (by omega) hℓ u_cur := by
          rw [hwf.dom_eq (m + 2) (by omega) hℓ u_cur, mem_image]
          rintro ⟨w', hw'_filt, hw'_eq⟩
          obtain ⟨hw'_act, hslw'⟩ := mem_filter.mp hw'_filt
          have hw'y : w' = y := hinj_cur hw'_act hy_act (hw'_eq.trans hy_id_eq.symm)
          subst hw'y; omega
        have hnew_cur : y_id_cur ∉ (res_y.1.nodeDom (m + 2) (by omega) hℓ u_cur).erase z_id := by
          rw [hpost_y.above_dom_eq (m + 2) (by omega) hℓ (by omega) u_cur]
          exact fun hm => hy_not_dom (mem_of_mem_erase hm)
        let storeLvl' := Function.update (Function.update storeLvl_y y (m + 2)) z 0
        refine ⟨rfl, rfl, storeLvl', ?_⟩
        set st_fin := res_y.1.replaceAtNode scheme (m + 2) h2 hℓ u_cur wait' z_id y_id_cur
          ((st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res_y.2.1)).2.2,
            res_y.2.2)
        have hsl_z_y : storeLvl_y z = m + 2 :=
          (hpost_y.storeLvl_gt_eq z (mem_erase.mpr ⟨hyz.symm, hz_in⟩) (by omega)).trans hslz_eq
        refine
          { seeds_eq := (res_y.1.seeds_replaceAtNode scheme h2 hℓ ..).trans hpost_y.seeds_eq
            sentCount_eq :=
              (res_y.1.sentCount_replaceAtNode scheme h2 hℓ ..).trans hpost_y.sentCount_eq
            storeLvl_zero_z := Function.update_self ..
            storeLvl_outside := fun w hw => by
              dsimp only [storeLvl']
              by_cases hwz : w = z
              · subst hwz; exact Function.update_self ..
              · rw [Function.update_of_ne hwz]
                have hw_not_in : w ∉ P.paddedDom d := fun hwin => hw (mem_erase.mpr ⟨hwz, hwin⟩)
                have hwy : w ≠ y := fun h => hw_not_in (h ▸ hy_in)
                rw [Function.update_of_ne hwy]
                exact hpost_y.storeLvl_outside w fun hm => hw_not_in (mem_of_mem_erase hm)
            storeLvl_le_bounds := fun w hw hle => by
              obtain ⟨hwz, hwin⟩ := mem_erase.mp hw
              dsimp only [storeLvl']
              rw [Function.update_of_ne hwz]
              by_cases hwy : w = y
              · subst hwy; rw [Function.update_self]; omega
              · rw [Function.update_of_ne hwy]
                have hwin_y : w ∈ (P.paddedDom d).erase y := mem_erase.mpr ⟨hwy, hwin⟩
                by_cases hle_prev : storeLvl w ≤ m + 1
                · have hb := hpost_y.storeLvl_le_bounds w hwin_y hle_prev
                  omega
                · rw [hpost_y.storeLvl_gt_eq w hwin_y (by omega)]; omega
            storeLvl_gt_eq := fun w hw hgt => by
              obtain ⟨hwz, hwin⟩ := mem_erase.mp hw
              have hwy : w ≠ y := fun h => by subst h; omega
              dsimp only [storeLvl']
              rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
              exact hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)
            above_dom_eq := fun j hj1 hjd hgt u => by
              have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
              exact (res_y.1.nodeDom_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                hj1 hjd u hne_j).trans (hpost_y.above_dom_eq j hj1 hjd (by omega) u)
            above_query_eq := fun j hj1 hjd hgt u k => by
              have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
              exact (res_y.1.nodeQuery_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur
                _ hj1 hjd u k hne_j).trans (hpost_y.above_query_eq j hj1 hjd (by omega) u k)
            above_wait_eq := fun j hj2 hjd hgt u => by
              have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
              exact (res_y.1.nodeWait_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                hj2 hjd u hne_j).trans (hpost_y.above_wait_eq j hj2 hjd (by omega) u)
            le_dom_eq := fun j hj1 hjℓ u => ?_
            le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => ?_
            le_inner_full := fun j hj2 hjlt hjℓ u => ?_
            le_wait_dom_eq := fun j hj2 hjℓ u => ?_
            le_wait_lookup_eq := fun j hj2 hjℓ u w hw hslw => ?_ }
        · by_cases hj_top : j = m + 2
          · subst hj_top
            by_cases hu : u = u_cur
            · rw [hu]
              dsimp only [st_fin]
              rw [res_y.1.nodeDom_replaceAtNode_same scheme hj1 h2 hℓ u_cur wait' z_id y_id_cur _
                hold_cur hnew_cur,
                hpost_y.above_dom_eq (m + 2) hj1 hℓ (by omega) u_cur,
                hwf.dom_eq (m + 2) hj1 hℓ u_cur]
              have hz_filt : z ∈ (st.seeds.activeAt (P.paddedDom d) (m + 2) hℓ u_cur).filter
                  (fun w => storeLvl w = m + 2) := mem_filter.mpr ⟨hz_act, hslz_eq⟩
              have herase_img := image_erase_of_injOn
                (filter_subset (fun w => storeLvl w = m + 2) _) hinj_cur hz_act
              rw [herase_img, ← hy_id_eq, ← image_insert]
              congr 1; ext w
              simp only [mem_insert, mem_erase, mem_filter, SeedAssignment.mem_activeAt_iff]
              by_cases hwz : w = z
              · rw [hwz]; simp [Ne.symm hyz]
              · by_cases hwy : w = y
                · rw [hwy]; simp [hy_in, hny, storeLvl', hyz]
                · have hsl_eq : storeLvl' w = m + 2 ↔ storeLvl w = m + 2 := by
                    by_cases hwin : w ∈ P.paddedDom d
                    · dsimp only [storeLvl']
                      rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
                      have hwin_y := mem_erase.mpr ⟨hwy, hwin⟩
                      by_cases hle_p : storeLvl w ≤ m + 1
                      · have hb := hpost_y.storeLvl_le_bounds w hwin_y hle_p
                        omega
                      · rw [hpost_y.storeLvl_gt_eq w hwin_y (by omega)]
                    · have h1' : storeLvl' w = 0 := by
                        dsimp only [storeLvl']
                        rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
                        exact hpost_y.storeLvl_outside w fun hm => hwin (mem_of_mem_erase hm)
                      rw [h1', hwf.storeLvl_outside w hwin]
                  simp [hwz, hwy, hsl_eq]
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              dsimp only [st_fin]
              rw [res_y.1.nodeDom_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                hj1 hℓ u hne_u,
                hpost_y.above_dom_eq (m + 2) hj1 hℓ (by omega) u,
                hwf.dom_eq (m + 2) hj1 hℓ u]
              congr 1; ext w
              simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
              by_cases hwz : w = z
              · rw [hwz]
                have hnu : st.seeds.nodeAt (m + 2) hℓ z ≠ u := fun h => hu (h.symm.trans hnz)
                simp [hnu]
              · by_cases hwy : w = y
                · rw [hwy]
                  have hnu : st.seeds.nodeAt (m + 2) hℓ y ≠ u := fun h => hu (h.symm.trans hny)
                  simp [hnu]
                · constructor
                  · rintro ⟨⟨hwin, hnw⟩, hslw⟩
                    refine ⟨⟨⟨hwz, hwin⟩, hnw⟩, ?_⟩
                    dsimp only [storeLvl']
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
                    exact hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega) |>.trans
                      hslw
                  · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hslw⟩
                    refine ⟨⟨hwin, hnw⟩, ?_⟩
                    dsimp only [storeLvl'] at hslw
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hslw
                    by_cases hle_p : storeLvl w ≤ m + 1
                    · have hb := hpost_y.storeLvl_le_bounds w (mem_erase.mpr ⟨hwy, hwin⟩) hle_p
                      omega
                    · rwa [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hslw
          · have hj_le_prev : j ≤ m + 1 := by omega
            have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_y.1.nodeDom_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
              hj1 (hjℓ.trans hℓ) u hne_j,
              hpost_y.le_dom_eq j hj1 hj_le_prev u]
            congr 1; ext w
            simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
            by_cases hwz : w = z
            · rw [hwz]; simp [hsl_z_y, show m + 2 ≠ j by omega]
            · by_cases hwy : w = y
              · rw [hwy]; simp [storeLvl', hyz, show m + 2 ≠ j by omega]
              · simp [storeLvl', hwz, hwy]
        · have hwz : w ≠ z := fun h => by subst h; simp at hdw
          rw [Function.update_of_ne hwz] at hdw
          have hwin : w ∈ P.paddedDom d := (P.mem_paddedDom_iff d w).mpr (by simp [hdw])
          by_cases hj_top : j = m + 2
          · subst hj_top
            by_cases hu : u = u_cur
            · rw [hu] at hnw ⊢
              dsimp only [st_fin]
              rw [res_y.1.nodeQuery_replaceAtNode_same scheme hj1 h2 hℓ u_cur wait' z_id y_id_cur
                _ _ hold_cur hnew_cur]
              by_cases hwy : w = y
              · rw [hwy] at hdw ⊢
                have hvw : vw = vy := Option.some.inj (hdw.symm.trans hdy)
                rw [hvw, hy_id_eq, Function.update_self, hq_y_cur, hv_rec]
              · have hne_new : st.seeds.idAt (m + 2) hj1 hℓ w ≠ y_id_cur := fun h =>
                  hwy (hinj_cur (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hy_act
                    (h.trans hy_id_eq.symm))
                have hne_old : st.seeds.idAt (m + 2) hj1 hℓ w ≠ z_id := fun h =>
                  hwz (hinj_cur (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hz_act h)
                rw [Function.update_of_ne hne_new, Function.update_of_ne hne_old,
                  hpost_y.above_query_eq (m + 2) hj1 hℓ (by omega) u_cur]
                dsimp only [storeLvl'] at hslw
                rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hslw
                have hslw_orig : storeLvl w = m + 2 := by
                  by_cases hle_p : storeLvl w ≤ m + 1
                  · have hb := hpost_y.storeLvl_le_bounds w (mem_erase.mpr ⟨hwy, hwin⟩) hle_p
                    omega
                  · rwa [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hslw
                exact hwf.query_eq_of_storeLvl (m + 2) hj1 hℓ u_cur w vw hdw hnw hslw_orig
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              have hwy : w ≠ y := fun h => hu (hnw.symm.trans (h ▸ hny))
              dsimp only [st_fin]
              rw [res_y.1.nodeQuery_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                hj1 hℓ u _ hne_u,
                hpost_y.above_query_eq (m + 2) hj1 hℓ (by omega) u]
              dsimp only [storeLvl'] at hslw
              rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hslw
              have hslw_orig : storeLvl w = m + 2 := by
                by_cases hle_p : storeLvl w ≤ m + 1
                · have hb := hpost_y.storeLvl_le_bounds w (mem_erase.mpr ⟨hwy, hwin⟩) hle_p
                  omega
                · rwa [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hslw
              exact hwf.query_eq_of_storeLvl (m + 2) hj1 hℓ u w vw hdw hnw hslw_orig
          · have hj_le_prev : j ≤ m + 1 := by omega
            have hwy : w ≠ y := fun h => by
              subst h; dsimp only [storeLvl'] at hslw
              rw [Function.update_of_ne hwz, Function.update_self] at hslw; omega
            dsimp only [storeLvl'] at hslw
            rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hslw
            have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_y.1.nodeQuery_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
              hj1 (hjℓ.trans hℓ) u _ hne_j]
            exact hpost_y.le_query_eq j hj1 hj_le_prev u w vw
              (by rw [Function.update_of_ne hwy]; exact hdw) hnw hslw
        · by_cases hj_top : j = m + 2
          · subst hj_top
            by_cases hu : u = u_cur
            · rw [hu]
              have hdom_fin := res_y.1.nodeDom_replaceAtNode_same scheme (by omega) h2 hℓ u_cur
                wait' z_id y_id_cur
                ((st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res_y.2.1)).2.2,
                  res_y.2.2) hold_cur hnew_cur
              rw [nodeDom_inner st_fin (by omega) hj2 hjlt hℓ] at hdom_fin
              rw [hdom_fin, card_insert_of_notMem hnew_cur, card_erase_of_mem hold_cur,
                hpost_y.above_dom_eq (m + 2) (by omega) hℓ (by omega) u_cur,
                nodeDom_inner st (by omega) hj2 hjlt hℓ,
                hwf.inner_full (m + 2) hj2 hjlt u_cur]
              have hpos : 1 ≤ (st.inner (m + 2) hj2 hjlt u_cur).table.tableMeta.dom.card := by
                rw [← nodeDom_inner st (by omega) hj2 hjlt hℓ]
                rw [← hpost_y.above_dom_eq (m + 2) (by omega) hℓ (by omega) u_cur]
                exact Finset.card_pos.mpr ⟨z_id, hold_cur⟩
              have hfull := hwf.inner_full (m + 2) hj2 hjlt u_cur
              omega
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              have hd := res_y.1.nodeDom_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id
                y_id_cur
                ((st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res_y.2.1)).2.2,
                  res_y.2.2) (by omega) hℓ u hne_u
              rw [hpost_y.above_dom_eq (m + 2) (by omega) hℓ (by omega) u,
                nodeDom_inner st_fin (by omega) hj2 hjlt hℓ,
                nodeDom_inner st (by omega) hj2 hjlt hℓ] at hd
              rw [hd, hwf.inner_full (m + 2) hj2 hjlt u]
          · have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            have hd := res_y.1.nodeDom_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id
              y_id_cur
              ((st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, y_id_prev, res_y.2.1)).2.2,
                res_y.2.2) (by omega) hjlt.le u hne_j
            rw [nodeDom_inner st_fin (by omega) hj2 hjlt hjlt.le,
              nodeDom_inner res_y.1 (by omega) hj2 hjlt hjlt.le] at hd
            rw [hd, hpost_y.le_inner_full j hj2 hjlt (by omega) u]
        · by_cases hj_top : j = m + 2
          · subst hj_top
            by_cases hu : u = u_cur
            · rw [hu]
              dsimp only [st_fin]
              rw [res_y.1.nodeWait_replaceAtNode_same scheme (by omega) h2 hℓ u_cur wait' z_id
                y_id_cur _ hold_cur hnew_cur]
              dsimp only [wait', popRes]
              rw [WaitingList.dom_pop_snd]
              change (st.nodeWait (m + 2) h2 hℓ u_cur).dom.erase y_id_cur = _
              rw [hwf.wait_dom_eq (m + 2) h2 hℓ u_cur, ← hy_id_eq]
              have herase_img := image_erase_of_injOn
                (filter_subset (fun w => storeLvl w < m + 2) _) hinj_cur hy_act
              rw [herase_img]
              congr 1; ext w
              simp only [mem_erase, mem_filter, SeedAssignment.mem_activeAt_iff]
              by_cases hwz : w = z
              · rw [hwz]; simp [hslz_eq]
              · by_cases hwy : w = y
                · rw [hwy]; simp [storeLvl', hyz]
                · constructor
                  · rintro ⟨_, ⟨hwin, hnw⟩, hlt_w⟩
                    refine ⟨⟨⟨hwz, hwin⟩, hnw⟩, ?_⟩
                    dsimp only [storeLvl']
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
                    have hb := hpost_y.storeLvl_le_bounds w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)
                    omega
                  · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hlt_w⟩
                    refine ⟨hwy, ⟨hwin, hnw⟩, ?_⟩
                    dsimp only [storeLvl'] at hlt_w
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hlt_w
                    by_contra hge
                    rw [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hlt_w
                    omega
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              dsimp only [st_fin]
              rw [res_y.1.nodeWait_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                h2 hℓ u hne_u,
                hpost_y.above_wait_eq (m + 2) h2 hℓ (by omega) u,
                hwf.wait_dom_eq (m + 2) h2 hℓ u]
              congr 1; ext w
              simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
              by_cases hwz : w = z
              · rw [hwz]; simp [hslz_eq]
              · by_cases hwy : w = y
                · rw [hwy]
                  have hnu : st.seeds.nodeAt (m + 2) hℓ y ≠ u := fun h => hu (h.symm.trans hny)
                  simp [hnu]
                · constructor
                  · rintro ⟨⟨hwin, hnw⟩, hlt_w⟩
                    refine ⟨⟨⟨hwz, hwin⟩, hnw⟩, ?_⟩
                    dsimp only [storeLvl']
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy]
                    have hb := hpost_y.storeLvl_le_bounds w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)
                    omega
                  · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hlt_w⟩
                    refine ⟨⟨hwin, hnw⟩, ?_⟩
                    dsimp only [storeLvl'] at hlt_w
                    rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hlt_w
                    by_contra hge
                    rw [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hlt_w
                    omega
          · have hj_le_prev : j ≤ m + 1 := by omega
            have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_y.1.nodeWait_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
              hj2 (hjℓ.trans hℓ) u hne_j,
              hpost_y.le_wait_dom_eq j hj2 hj_le_prev u]
            congr 1; ext w
            simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
            by_cases hwz : w = z
            · rw [hwz]; simp [hsl_z_y, show ¬ m + 2 < j by omega]
            · by_cases hwy : w = y
              · rw [hwy]; simp [storeLvl', hyz, show ¬ m + 2 < j by omega]
              · simp [storeLvl', hwz, hwy]
        · obtain ⟨hw_er, hnw⟩ := SeedAssignment.mem_activeAt_iff.mp hw
          obtain ⟨hwz, hwin⟩ := mem_erase.mp hw_er
          have hwy : w ≠ y := fun h => by
            subst h; dsimp only [storeLvl'] at hslw
            rw [Function.update_of_ne hwz, Function.update_self] at hslw; omega
          dsimp only [storeLvl'] at hslw
          rw [Function.update_of_ne hwz, Function.update_of_ne hwy] at hslw
          by_cases hj_top : j = m + 2
          · subst hj_top
            have hslw_orig : storeLvl w < m + 2 := by
              by_contra hge
              rw [hpost_y.storeLvl_gt_eq w (mem_erase.mpr ⟨hwy, hwin⟩) (by omega)] at hslw
              omega
            have hlk_old := hwf.wait_lookup_eq (m + 2) h2 hℓ u w
              (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hslw_orig
            by_cases hu : u = u_cur
            · rw [hu] at hnw hlk_old ⊢
              dsimp only [st_fin]
              rw [res_y.1.nodeWait_replaceAtNode_same scheme (by omega) h2 hℓ u_cur wait' z_id
                y_id_cur _ hold_cur hnew_cur]
              dsimp only [wait', popRes, w_list]
              rw [WaitingList.lookup_pop_snd]
              have hid_ne : st.seeds.idAt (m + 2) (by omega) hℓ w ≠ y_id_cur := fun h =>
                hwy (hinj_cur (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hy_act
                  (h.trans hy_id_eq.symm))
              rw [Function.update_of_ne hid_ne, hlk_old]
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              dsimp only [st_fin]
              rw [res_y.1.nodeWait_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
                h2 hℓ u hne_u,
                hpost_y.above_wait_eq (m + 2) h2 hℓ (by omega) u, hlk_old]
          · have hj_le_prev : j ≤ m + 1 := by omega
            have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_y.1.nodeWait_replaceAtNode_other scheme h2 hℓ u_cur wait' z_id y_id_cur _
              hj2 (hjℓ.trans hℓ) u hne_j]
            exact hpost_y.le_wait_lookup_eq j hj2 hj_le_prev u w
              (SeedAssignment.mem_activeAt_iff.mpr ⟨mem_erase.mpr ⟨hwy, hwin⟩, hnw⟩) hslw
      · -- Branch 1: `z` is in `w_list`, so `storeLvl z < m + 2`
        have hz_mem_w : z_id ∈ w_list.dom :=
          (w_list.isSome_lookup_iff z_id).mp (by simp [w_list, hlk])
        have hinj_cur := st.seeds.injOn_idAt_activeAt hwf.goodSeeds (by omega) hℓ u_cur
        have hslz_lt : storeLvl z < m + 2 := by
          have hw_dom := hwf.wait_dom_eq (m + 2) h2 hℓ u_cur
          change w_list.dom = _ at hw_dom
          rw [hw_dom] at hz_mem_w
          obtain ⟨w', hw'_filt, hw'_eq⟩ := mem_image.mp hz_mem_w
          obtain ⟨hw'_act, hw'_lt⟩ := mem_filter.mp hw'_filt
          have hw'z : w' = z := hinj_cur hw'_act hz_act hw'_eq
          exact hw'z ▸ hw'_lt
        have hlk_exp := hwf.wait_lookup_eq (m + 2) h2 hℓ u_cur z hz_act hslz_lt
        change w_list.lookup z_id = _ at hlk_exp
        rw [hlk] at hlk_exp
        have hz_prev_eq : st.seeds.idAt (m + 1) h1_prev hlt_prev.le z = z_id_prev :=
          (Option.some.inj hlk_exp).symm
        have hnz_prev : st.seeds.nodeAt (m + 1) hlt_prev.le z = u_prev := by
          dsimp only [u_prev]; rw [← hnz, st.seeds.parentNode_nodeAt hℓ z]
        obtain ⟨hq_rec, hv_rec, storeLvl', hpost_z⟩ :=
          ih h1_prev hlt_prev.le u_prev z vz hdz hnz_prev (by omega) hloads_prev
        rw [hz_prev_eq] at hq_rec hv_rec hpost_z
        set res_z := st.deleteAndGetQuotient scheme (m + 1) h1_prev hlt_prev.le u_prev z_id_prev
        have hq_z_cur :
            (st.seeds.stepCoordEquiv h1_prev hlt_prev (u_prev, z_id_prev, res_z.2.1)).2.2 =
              st.seeds.quotAt (m + 2) h1 hℓ z := by
          rw [hq_rec, ← hz_prev_eq]
          exact stepCoordEquiv_quotAt st.seeds h1_prev hlt_prev u_cur z hnz
        dsimp only
        refine ⟨hq_z_cur, hv_rec, storeLvl', ?_⟩
        set st_fin := res_z.1.removeWaitAtNode (m + 2) h2 hℓ u_cur z_id
        refine
          { seeds_eq := (res_z.1.seeds_removeWaitAtNode h2 hℓ ..).trans hpost_z.seeds_eq
            sentCount_eq :=
              (res_z.1.sentCount_removeWaitAtNode h2 hℓ ..).trans hpost_z.sentCount_eq
            storeLvl_zero_z := hpost_z.storeLvl_zero_z
            storeLvl_outside := hpost_z.storeLvl_outside
            storeLvl_le_bounds := fun w hw hle => by
              by_cases hle_p : storeLvl w ≤ m + 1
              · have hb := hpost_z.storeLvl_le_bounds w hw hle_p; omega
              · rw [hpost_z.storeLvl_gt_eq w hw (by omega)]; omega
            storeLvl_gt_eq := fun w hw hgt => hpost_z.storeLvl_gt_eq w hw (by omega)
            above_dom_eq := fun j hj1 hjd hgt u =>
              (res_z.1.nodeDom_removeWaitAtNode h2 hℓ u_cur z_id hj1 hjd u).trans
                (hpost_z.above_dom_eq j hj1 hjd (by omega) u)
            above_query_eq := fun j hj1 hjd hgt u k =>
              (res_z.1.nodeQuery_removeWaitAtNode scheme h2 hℓ u_cur z_id hj1 hjd u k).trans
                (hpost_z.above_query_eq j hj1 hjd (by omega) u k)
            above_wait_eq := fun j hj2 hjd hgt u => by
              have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
              exact (res_z.1.nodeWait_removeWaitAtNode_other h2 hℓ u_cur z_id hj2 hjd u
                hne_j).trans (hpost_z.above_wait_eq j hj2 hjd (by omega) u)
            le_dom_eq := fun j hj1 hjℓ u => by
              rw [res_z.1.nodeDom_removeWaitAtNode h2 hℓ u_cur z_id hj1 (hjℓ.trans hℓ) u]
              by_cases hj_top : j = m + 2
              · subst hj_top
                rw [hpost_z.above_dom_eq (m + 2) hj1 hℓ (by omega) u,
                  hwf.dom_eq (m + 2) hj1 hℓ u]
                congr 1; ext w
                simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
                by_cases hwz : w = z
                · rw [hwz]; simp [show storeLvl z ≠ m + 2 by omega]
                · constructor
                  · rintro ⟨⟨hwin, hnw⟩, hslw⟩
                    exact ⟨⟨⟨hwz, hwin⟩, hnw⟩,
                      (hpost_z.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)).trans hslw⟩
                  · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hslw⟩
                    refine ⟨⟨hwin, hnw⟩, ?_⟩
                    by_cases hle_p : storeLvl w ≤ m + 1
                    · have hb := hpost_z.storeLvl_le_bounds w (mem_erase.mpr ⟨hwz, hwin⟩) hle_p
                      omega
                    · rwa [hpost_z.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)] at hslw
              · exact hpost_z.le_dom_eq j hj1 (by omega) u
            le_query_eq := fun j hj1 hjℓ u w vw hdw hnw hslw => by
              rw [res_z.1.nodeQuery_removeWaitAtNode scheme h2 hℓ u_cur z_id hj1 (hjℓ.trans hℓ) u]
              by_cases hj_top : j = m + 2
              · subst hj_top
                have hwz : w ≠ z := fun h => by subst h; simp at hdw
                rw [Function.update_of_ne hwz] at hdw
                have hwin : w ∈ P.paddedDom d := (P.mem_paddedDom_iff d w).mpr (by simp [hdw])
                have hslw_orig : storeLvl w = m + 2 := by
                  by_cases hle_p : storeLvl w ≤ m + 1
                  · have hb := hpost_z.storeLvl_le_bounds w (mem_erase.mpr ⟨hwz, hwin⟩) hle_p
                    omega
                  · rwa [hpost_z.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)] at hslw
                rw [hpost_z.above_query_eq (m + 2) hj1 hℓ (by omega) u]
                exact hwf.query_eq_of_storeLvl (m + 2) hj1 hℓ u w vw hdw hnw hslw_orig
              · exact hpost_z.le_query_eq j hj1 (by omega) u w vw hdw hnw hslw
            le_inner_full := fun j hj2 hjlt hjℓ u => by
              have hd := res_z.1.nodeDom_removeWaitAtNode h2 hℓ u_cur z_id (by omega) hjlt.le u
              rw [nodeDom_inner st_fin (by omega) hj2 hjlt hjlt.le,
                nodeDom_inner res_z.1 (by omega) hj2 hjlt hjlt.le] at hd
              rw [hd]
              by_cases hj_top : j = m + 2
              · subst hj_top
                have hd2 := hpost_z.above_dom_eq (m + 2) (by omega) hjlt.le (by omega) u
                rw [nodeDom_inner res_z.1 (by omega) hj2 hjlt hjlt.le,
                  nodeDom_inner st (by omega) hj2 hjlt hjlt.le] at hd2
                rw [hd2, hwf.inner_full (m + 2) hj2 hjlt u]
              · exact hpost_z.le_inner_full j hj2 hjlt (by omega) u
            le_wait_dom_eq := fun j hj2 hjℓ u => ?_
            le_wait_lookup_eq := fun j hj2 hjℓ u w hw hslw => ?_ }
        · by_cases hj_top : j = m + 2
          · subst hj_top
            by_cases hu : u = u_cur
            · rw [hu]
              dsimp only [st_fin]
              rw [res_z.1.nodeWait_removeWaitAtNode_same h2 hℓ u_cur z_id,
                hpost_z.above_wait_eq (m + 2) h2 hℓ (by omega) u_cur,
                WaitingList.dom_remove, hwf.wait_dom_eq (m + 2) h2 hℓ u_cur]
              have herase_img := image_erase_of_injOn
                (filter_subset (fun w => storeLvl w < m + 2) _) hinj_cur hz_act
              rw [herase_img]
              congr 1; ext w
              simp only [mem_erase, mem_filter, SeedAssignment.mem_activeAt_iff]
              by_cases hwz : w = z
              · rw [hwz]; simp
              · constructor
                · rintro ⟨_, ⟨hwin, hnw⟩, hlt_w⟩
                  refine ⟨⟨⟨hwz, hwin⟩, hnw⟩, ?_⟩
                  have hb := hpost_z.storeLvl_le_bounds w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)
                  omega
                · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hlt_w⟩
                  refine ⟨hwz, ⟨hwin, hnw⟩, ?_⟩
                  by_contra hge
                  rw [hpost_z.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)] at hlt_w
                  omega
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              dsimp only [st_fin]
              rw [res_z.1.nodeWait_removeWaitAtNode_other h2 hℓ u_cur z_id h2 hℓ u hne_u,
                hpost_z.above_wait_eq (m + 2) h2 hℓ (by omega) u,
                hwf.wait_dom_eq (m + 2) h2 hℓ u]
              congr 1; ext w
              simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_erase]
              by_cases hwz : w = z
              · rw [hwz]
                have hnu : st.seeds.nodeAt (m + 2) hℓ z ≠ u := fun h => hu (h.symm.trans hnz)
                simp [hnu]
              · constructor
                · rintro ⟨⟨hwin, hnw⟩, hlt_w⟩
                  refine ⟨⟨⟨hwz, hwin⟩, hnw⟩, ?_⟩
                  have hb := hpost_z.storeLvl_le_bounds w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)
                  omega
                · rintro ⟨⟨⟨_, hwin⟩, hnw⟩, hlt_w⟩
                  refine ⟨⟨hwin, hnw⟩, ?_⟩
                  by_contra hge
                  rw [hpost_z.storeLvl_gt_eq w (mem_erase.mpr ⟨hwz, hwin⟩) (by omega)] at hlt_w
                  omega
          · have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_z.1.nodeWait_removeWaitAtNode_other h2 hℓ u_cur z_id hj2 (hjℓ.trans hℓ) u hne_j]
            exact hpost_z.le_wait_dom_eq j hj2 (by omega) u
        · by_cases hj_top : j = m + 2
          · subst hj_top
            obtain ⟨hw_er, hnw⟩ := SeedAssignment.mem_activeAt_iff.mp hw
            obtain ⟨hwz, hwin⟩ := mem_erase.mp hw_er
            have hslw_orig : storeLvl w < m + 2 := by
              by_contra hge
              rw [hpost_z.storeLvl_gt_eq w hw_er (by omega)] at hslw
              omega
            have hlk_old := hwf.wait_lookup_eq (m + 2) h2 hℓ u w
              (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hslw_orig
            by_cases hu : u = u_cur
            · rw [hu] at hnw hlk_old ⊢
              dsimp only [st_fin]
              rw [res_z.1.nodeWait_removeWaitAtNode_same h2 hℓ u_cur z_id,
                hpost_z.above_wait_eq (m + 2) h2 hℓ (by omega) u_cur,
                WaitingList.lookup_remove]
              have hid_ne : st.seeds.idAt (m + 2) (by omega) hℓ w ≠ z_id := fun h =>
                hwz (hinj_cur (SeedAssignment.mem_activeAt_iff.mpr ⟨hwin, hnw⟩) hz_act h)
              rw [Function.update_of_ne hid_ne, hlk_old]
            · have hne_u : ∀ h_eq : m + 2 = m + 2, h_eq ▸ u ≠ u_cur := fun _ => hu
              dsimp only [st_fin]
              rw [res_z.1.nodeWait_removeWaitAtNode_other h2 hℓ u_cur z_id h2 hℓ u hne_u,
                hpost_z.above_wait_eq (m + 2) h2 hℓ (by omega) u, hlk_old]
          · have hne_j : ∀ h_eq : j = m + 2, h_eq ▸ u ≠ u_cur := fun h_eq => by omega
            dsimp only [st_fin]
            rw [res_z.1.nodeWait_removeWaitAtNode_other h2 hℓ u_cur z_id hj2 (hjℓ.trans hℓ) u hne_j]
            exact hpost_z.le_wait_lookup_eq j hj2 (by omega) u w hw hslw

/-- Normal-path deletion of an active internal key `z ∈ P.paddedDom d`, invoking `Algorithm 3`
starting at the leaf `(depth, nodeAt depth z)` (`Section 5.3`, PDF p. 31 / printed p. 30). -/
noncomputable def normalDeleteMem
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (z : Fin P.paddedUniv) : P.TreeState :=
  (st.deleteAndGetQuotient scheme P.depth (Nat.one_le_of_lt P.two_le_depth) le_rfl
    (st.seeds.nodeAt P.depth le_rfl z)
    (st.seeds.idAt P.depth (Nat.one_le_of_lt P.two_le_depth) le_rfl z)).1

/-- **Normal-path deletion preserves `WellFormedPadded`** whenever `z ∈ P.paddedDom d` and all
current node seeds remain good on `(P.paddedDom d).erase z`. -/
theorem wellFormedPadded_normalDeleteMem
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {z : Fin P.paddedUniv}
    (hz : z ∈ P.paddedDom d)
    (hgood' : st.seeds.AllGoodSeeds ((P.paddedDom d).erase z)) :
    (st.normalDeleteMem scheme z).sentCount = st.sentCount ∧
    (st.normalDeleteMem scheme z).seeds = st.seeds ∧
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      (st.normalDeleteMem scheme z).WellFormedPadded scheme
        (Function.update d z none) storeLvl' := by
  obtain ⟨vz, hdz⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d z).mp hz)
  have h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  have hslz := (hwf.storeLvl_bounds z hz).2
  have hloads : ∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ P.depth),
      P.nLow j <
        (st.seeds.activeAt (P.paddedDom d) j hj
          (P.ancestorAt hj (st.seeds.nodeAt P.depth le_rfl z))).card := by
    intro j _ hj
    rw [st.seeds.ancestorAt_nodeAt hj le_rfl z]
    have hlo_er := (st.seeds.load_bounds_of_allGoodSeeds hgood' hj (st.seeds.nodeAt j hj z)).1
    have hact_er : st.seeds.activeAt ((P.paddedDom d).erase z) j hj (st.seeds.nodeAt j hj z) =
        (st.seeds.activeAt (P.paddedDom d) j hj (st.seeds.nodeAt j hj z)).erase z := by
      ext w
      simp [SeedAssignment.mem_activeAt_iff, mem_erase, and_assoc]
    have hz_act_j : z ∈ st.seeds.activeAt (P.paddedDom d) j hj (st.seeds.nodeAt j hj z) :=
      SeedAssignment.mem_activeAt_iff.mpr ⟨hz, rfl⟩
    rw [hact_er, card_erase_of_mem hz_act_j] at hlo_er
    have hpos : 1 ≤ (st.seeds.activeAt (P.paddedDom d) j hj (st.seeds.nodeAt j hj z)).card :=
      Finset.card_pos.mpr ⟨z, hz_act_j⟩
    omega
  obtain ⟨_, _, storeLvl', hpost⟩ :=
    deleteAndGetQuotient_spec hwf P.depth h1d le_rfl _ z vz hdz rfl hslz hloads
  have hdom_upd : P.paddedDom (Function.update d z none) = (P.paddedDom d).erase z :=
    P.paddedDom_update_none d z
  dsimp only [normalDeleteMem]
  refine ⟨hpost.sentCount_eq, hpost.seeds_eq, storeLvl', ?_⟩
  refine
    { goodSeeds := by rw [hpost.seeds_eq, hdom_upd]; exact hgood'
      storeLvl_bounds := fun w hw => by
        rw [hdom_upd] at hw
        exact hpost.storeLvl_le_bounds w hw
          (hwf.storeLvl_bounds w (mem_of_mem_erase hw)).2
      storeLvl_outside := fun w hw => by
        rw [hdom_upd] at hw
        exact hpost.storeLvl_outside w hw
      dom_eq := fun ℓ h1 hℓ u => by
        rw [hpost.seeds_eq, hdom_upd]
        exact hpost.le_dom_eq ℓ h1 hℓ u
      query_eq_of_storeLvl := fun ℓ h1 hℓ u w vw hdw hnw hslw => by
        rw [hpost.seeds_eq] at hnw ⊢
        exact hpost.le_query_eq ℓ h1 hℓ u w vw hdw hnw hslw
      inner_full := fun ℓ h2 hlt u =>
        hpost.le_inner_full ℓ h2 hlt hlt.le u
      wait_dom_eq := fun ℓ h2 hℓ u => by
        rw [hpost.seeds_eq, hdom_upd]
        exact hpost.le_wait_dom_eq ℓ h2 hℓ u
      wait_lookup_eq := fun ℓ h2 hℓ u w hw hslw => by
        rw [hpost.seeds_eq, hdom_upd] at hw
        rw [hpost.seeds_eq]
        exact hpost.le_wait_lookup_eq ℓ h2 hℓ u w hw hslw }

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
