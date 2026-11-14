/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeCore

/-!
# Root-to-Leaf Query and In-Place Payload Overwrite

This file formalizes deterministic root-to-leaf lookup (`rawQuery`, `query`) and in-place value
overwrite (`overwriteAtNode`, `rawOverwrite`) for the subconstant-redundancy dictionary tree of
Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant
Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 30–31 / printed pp. 29–30).

## Main definitions

* `TreeSchedule.TreeState.rawQuery`, `TreeSchedule.TreeState.query`: iterative root-to-leaf lookup.
* `TreeSchedule.TreeState.overwriteAtNode`, `TreeSchedule.TreeState.rawOverwrite`: in-place payload
  update of an active key.

## Main results

* `TreeSchedule.TreeState.rawQuery_eq`, `TreeSchedule.TreeState.query_eq_apply`: exact query
  correctness (rejecting false-positive ID collisions via global `levelCoordEquiv` bijectivity,
  `Footnote 10`).
* `TreeSchedule.TreeState.wellFormedPadded_rawOverwrite`: preservation of `WellFormedPadded` under
  in-place value updates.

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

/-! ## Section 1: Iterative root-to-leaf query (`rawQuery` and `query`) -/

/-- Iterative root-to-leaf query loop starting from `c : P.LevelCoord ℓ` (`Section 5.3`). -/
noncomputable def rawQueryLoop
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (c : P.LevelCoord ℓ) :
    Option (Fin P.valBound) :=
  match st.nodeQuery scheme ℓ h1 hℓ c.1 c.id with
  | some (q, v) =>
    if q == c.quot then some v
    else if hlt : ℓ < P.depth then
      st.rawQueryLoop scheme (ℓ + 1) (by omega) hlt (st.seeds.stepCoordEquiv h1 hlt c)
    else none
  | none =>
    if hlt : ℓ < P.depth then
      st.rawQueryLoop scheme (ℓ + 1) (by omega) hlt (st.seeds.stepCoordEquiv h1 hlt c)
    else none
termination_by P.depth - ℓ
decreasing_by all_goals omega

/-- Look up an internal key `x : Fin P.paddedUniv` along its root-to-leaf coordinate path. -/
noncomputable def rawQuery
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) : Option (Fin P.valBound) :=
  st.rawQueryLoop scheme 1 le_rfl (Nat.one_le_of_lt P.two_le_depth)
    (st.seeds.levelOneCoordEquiv x)

theorem nodeQuery_match_iff
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) :
    (match st.nodeQuery scheme ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x) (st.seeds.idAt ℓ h1 hℓ x) with
      | some (q, v) => if q == st.seeds.quotAt ℓ h1 hℓ x then some v else none
      | none => none) =
      if storeLvl x = ℓ then d x else none := by
  rcases hq : st.nodeQuery scheme ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x)
      (st.seeds.idAt ℓ h1 hℓ x) with _ | ⟨q, v⟩
  · simp only
    by_cases hsl : storeLvl x = ℓ
    · have hx_in : x ∈ P.paddedDom d := by
        by_contra hout
        have h0 := hwf.storeLvl_outside x hout
        omega
      obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d x).mp hx_in)
      have hq' := hwf.query_eq_of_storeLvl ℓ h1 hℓ _ x vx hvx rfl hsl
      rw [hq] at hq'; cases hq'
    · rw [ite_eq_right hsl]
  · simp only
    have hid_mem : st.seeds.idAt ℓ h1 hℓ x ∈ st.nodeDom ℓ h1 hℓ (st.seeds.nodeAt ℓ hℓ x) := by
      by_contra hnot
      have hnone := st.nodeQuery_eq_none_of_notMem scheme h1 hℓ _ hnot
      rw [hq] at hnone; cases hnone
    rw [hwf.dom_eq ℓ h1 hℓ] at hid_mem
    obtain ⟨y, hy_filt, hid_eq⟩ := mem_image.mp hid_mem
    obtain ⟨hy_act, hsl_y⟩ := mem_filter.mp hy_filt
    obtain ⟨hy_dom, hny⟩ := SeedAssignment.mem_activeAt_iff.mp hy_act
    obtain ⟨vy, hvy⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d y).mp hy_dom)
    have hqy := hwf.query_eq_of_storeLvl ℓ h1 hℓ _ y vy hvy hny hsl_y
    rw [hid_eq, hq] at hqy
    obtain ⟨hq_eq, hv_eq⟩ := Prod.mk.inj (Option.some.inj hqy)
    subst q; subst v
    by_cases hqx : st.seeds.quotAt ℓ h1 hℓ y == st.seeds.quotAt ℓ h1 hℓ x
    · rw [ite_eq_left hqx]
      have hq_yx : st.seeds.quotAt ℓ h1 hℓ y = st.seeds.quotAt ℓ h1 hℓ x := eq_of_beq hqx
      have hcoord_eq : st.seeds.levelCoordEquiv ℓ h1 hℓ y =
          st.seeds.levelCoordEquiv ℓ h1 hℓ x := by
        refine Prod.ext ?_ (Prod.ext hid_eq hq_yx)
        rw [st.seeds.levelCoordEquiv_fst, st.seeds.levelCoordEquiv_fst, hny]
      have hyx : y = x := (st.seeds.levelCoordEquiv ℓ h1 hℓ).injective hcoord_eq
      subst hyx
      rw [ite_eq_left hsl_y, hvy]
    · rw [ite_eq_right hqx]
      have hne_yx : y ≠ x := fun hyx => by subst hyx; simp at hqx
      have hsl_ne : storeLvl x ≠ ℓ := by
        intro hsl_x
        have hx_in : x ∈ P.paddedDom d := by
          by_contra hout; have := hwf.storeLvl_outside x hout; omega
        have hx_act : x ∈ st.seeds.activeAt (P.paddedDom d) ℓ hℓ (st.seeds.nodeAt ℓ hℓ x) :=
          SeedAssignment.mem_activeAt_iff.mpr ⟨hx_in, rfl⟩
        have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds h1 hℓ (st.seeds.nodeAt ℓ hℓ x)
        exact hne_yx (hinj hy_act hx_act hid_eq)
      rw [ite_eq_right hsl_ne]

/-- **Internal query correctness**: `st.rawQuery scheme x = d x` for every `x : Fin P.paddedUniv`
(both active and absent, `Section 5.3` & `Footnote 10`, PDF p. 30 / printed p. 29). -/
theorem rawQuery_eq
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) (x : Fin P.paddedUniv) :
    st.rawQuery scheme x = d x := by
  have hgen : ∀ (k m : ℕ), m + k = P.depth → (h1 : 1 ≤ m) → (hml : m ≤ P.depth) →
      st.rawQueryLoop scheme m h1 hml (st.seeds.levelCoordEquiv m h1 hml x) =
        if m ≤ storeLvl x then d x else none := by
    intro k
    induction k with
    | zero =>
      intro m hsum h1 hml
      obtain rfl : m = P.depth := by omega
      unfold rawQueryLoop
      have hm := nodeQuery_match_iff hwf h1 hml x
      have hc_eq : st.seeds.levelCoordEquiv P.depth h1 hml x =
          (st.seeds.nodeAt P.depth hml x, st.seeds.idAt P.depth h1 hml x,
            st.seeds.quotAt P.depth h1 hml x) :=
        Prod.ext (st.seeds.levelCoordEquiv_fst h1 hml x) rfl
      have hle_iff : P.depth ≤ storeLvl x ↔ storeLvl x = P.depth := by
        by_cases hxin : x ∈ P.paddedDom d
        · have := hwf.storeLvl_bounds x hxin; omega
        · have := hwf.storeLvl_outside x hxin; omega
      rw [hc_eq]; dsimp only [LevelCoord.id, LevelCoord.quot]
      rcases hq : st.nodeQuery scheme P.depth h1 hml (st.seeds.nodeAt P.depth hml x)
          (st.seeds.idAt P.depth h1 hml x) with _ | ⟨q, v⟩
      · rw [hq] at hm; simp only [dite_eq_right (lt_irrefl _), hle_iff] at hm ⊢; exact hm
      · rw [hq] at hm; simp only [dite_eq_right (lt_irrefl _), hle_iff] at hm ⊢; exact hm
    | succ k ih =>
      intro m hsum h1 hml
      have hlt : m < P.depth := by omega
      have hm := nodeQuery_match_iff hwf h1 hml x
      have hc1 := st.seeds.levelCoordEquiv_fst h1 hml x
      have hstep_coord : st.seeds.stepCoordEquiv h1 hlt
          (st.seeds.levelCoordEquiv m h1 hml x) =
          st.seeds.levelCoordEquiv (m + 1) (by omega) hlt x := by
        rw [st.seeds.levelCoordEquiv_succ h1 hlt, Equiv.trans_apply]
      have hrec : st.rawQueryLoop scheme (m + 1) (by omega) hlt
          (st.seeds.stepCoordEquiv h1 hlt (st.seeds.levelCoordEquiv m h1 hml x)) =
          if m + 1 ≤ storeLvl x then d x else none := by
        rw [hstep_coord]
        exact ih (m + 1) (by omega) (by omega) hlt
      unfold rawQueryLoop
      rw [hc1]
      change (match st.nodeQuery scheme m h1 hml (st.seeds.nodeAt m hml x)
          (st.seeds.idAt m h1 hml x) with
        | some (q, v) =>
          if q == st.seeds.quotAt m h1 hml x then some v
          else if hlt' : m < P.depth then
            st.rawQueryLoop scheme (m + 1) _ _
              (st.seeds.stepCoordEquiv h1 hlt' (st.seeds.levelCoordEquiv m h1 hml x))
          else none
        | none =>
          if hlt' : m < P.depth then
            st.rawQueryLoop scheme (m + 1) _ _
              (st.seeds.stepCoordEquiv h1 hlt' (st.seeds.levelCoordEquiv m h1 hml x))
          else none) = _
      rcases hq : st.nodeQuery scheme m h1 hml (st.seeds.nodeAt m hml x)
          (st.seeds.idAt m h1 hml x) with _ | ⟨q, v⟩
      · rw [hq] at hm; dsimp only at hm ⊢
        rw [dite_eq_left hlt, hrec]
        by_cases hsl_eq : storeLvl x = m
        · rw [ite_eq_left hsl_eq] at hm
          have hxin : x ∈ P.paddedDom d := by
            by_contra hout; have := hwf.storeLvl_outside x hout; omega
          have hsome := (P.mem_paddedDom_iff d x).mp hxin
          rw [← hm] at hsome; cases hsome
        · have hiff : (m + 1 ≤ storeLvl x) ↔ (m ≤ storeLvl x) := by omega
          simp [hiff]
      · rw [hq] at hm; dsimp only at hm ⊢
        by_cases hbeq : q == st.seeds.quotAt m h1 hml x
        · rw [ite_eq_left hbeq] at hm ⊢
          by_cases hsl_eq : storeLvl x = m
          · rw [ite_eq_left hsl_eq] at hm; rw [ite_eq_left (by omega), hm]
          · rw [ite_eq_right hsl_eq] at hm; cases hm
        · rw [ite_eq_right hbeq] at hm ⊢
          rw [dite_eq_left hlt, hrec]
          by_cases hsl_eq : storeLvl x = m
          · rw [ite_eq_left hsl_eq] at hm
            have hxin : x ∈ P.paddedDom d := by
              by_contra hout; have := hwf.storeLvl_outside x hout; omega
            have hsome := (P.mem_paddedDom_iff d x).mp hxin
            rw [← hm] at hsome; cases hsome
          · have hiff : (m + 1 ≤ storeLvl x) ↔ (m ≤ storeLvl x) := by omega
            simp [hiff]
  dsimp only [rawQuery]
  have h1 := hgen (P.depth - 1) 1 (by have := P.two_le_depth; omega) le_rfl
    (Nat.one_le_of_lt P.two_le_depth)
  rw [st.seeds.levelCoordEquiv_one] at h1
  rw [h1]
  by_cases hxin : x ∈ P.paddedDom d
  · rw [ite_eq_left (hwf.storeLvl_bounds x hxin).1]
  · rw [ite_eq_right (by rw [hwf.storeLvl_outside x hxin]; omega)]
    exact (Option.not_isSome_iff_eq_none.mp (mt (P.mem_paddedDom_iff d x).mpr hxin)).symm

/-- Deterministic external dictionary lookup `u : Fin P.univ → Option ℕ` (`Section 5.3`). -/
noncomputable def query
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) : Option ℕ :=
  (st.rawQuery scheme (P.embedReal u)).map Fin.val

/-- **External query correctness**: under `st.WellFormed scheme dict`, `st.query scheme u = dict u`
for every `u : Fin P.univ`. -/
theorem query_eq_apply
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u : Fin P.univ) :
    st.query scheme u = dict u := by
  obtain ⟨d, storeLvl, hm, hwfp⟩ := hwf
  dsimp only [query]
  rw [rawQuery_eq hwfp, hm.real_eq]

/-! ## Section 2: Uniform node overwrite and `rawOverwrite` -/

private def overwriteRootAt (st : P.TreeState) (u : Fin (P.numNodes 1))
    (k : Fin (2 ^ P.idBits 1)) (qv : Fin (P.quotUniv 1) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.roots u).table.tableMeta.dom then
    st.updateRoot u { (st.roots u) with table := (st.roots u).table.overwrite k qv hk }
  else st

private def overwriteInnerAt (st : P.TreeState) (L : ℕ) (h2 : 2 ≤ L) (hlt : L < P.depth)
    (u : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.inner L h2 hlt u).table.tableMeta.dom then
    st.updateInner L h2 hlt u
      { (st.inner L h2 hlt u) with table := (st.inner L h2 hlt u).table.overwrite k qv hk }
  else st

private def overwriteLeafAt
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin (P.numNodes P.depth)) (k : Fin (2 ^ P.idBits P.depth))
    (qv : Fin (P.quotUniv P.depth) × Fin P.valBound) : P.TreeState :=
  if hk : k ∈ (st.leaves u).dom then
    st.updateLeaf u ((st.leaves u).overwrite scheme k qv hk)
  else st

/-- Overwrite `(quot, val)` of an ID `k` at `(L, uL)` (`1 ≤ L ≤ depth`), acting as identity if
`k ∉ st.nodeDom L h1L hLL uL`. -/
def overwriteAtNode (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (L : ℕ) (_h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) : P.TreeState :=
  if h_one : L = 1 then
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (overwriteRootAt st) h_one.symm uL k qv
  else if hlt : L < P.depth then
    overwriteInnerAt st L (by omega) hlt uL k qv
  else
    have hd : L = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Fin (P.quotUniv m) × Fin P.valBound → P.TreeState)
      (overwriteLeafAt scheme st) hd.symm uL k qv

theorem seeds_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).seeds = st.seeds := by
  dsimp only [overwriteAtNode]
  by_cases h_one : L = 1
  · subst h_one; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]
    split_ifs with hk
    · exact st.seeds_updateRoot_of_seed_eq _ _ rfl
    · rfl
  · by_cases hlt : L < P.depth
    · rw [dite_eq_right h_one, dite_eq_left hlt]; dsimp only [overwriteInnerAt]
      split_ifs with hk
      · exact st.seeds_updateInner_of_seed_eq _ _ _ _ rfl
      · rfl
    · have hd : L = P.depth := by omega
      subst hd; rw [dite_eq_right h_one, dite_eq_right (lt_irrefl _)]; dsimp only [overwriteLeafAt]
      split_ifs with hk
      · exact st.seeds_updateLeaf_of_seed_eq _ _ rfl
      · rfl

theorem sentCount_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).sentCount = st.sentCount := by
  dsimp only [overwriteAtNode]
  by_cases h_one : L = 1
  · subst h_one; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]; split_ifs <;> rfl
  · by_cases hlt : L < P.depth
    · rw [dite_eq_right h_one, dite_eq_left hlt]; dsimp only [overwriteInnerAt]; split_ifs <;> rfl
    · have hd : L = P.depth := by omega
      subst hd; rw [dite_eq_right h_one, dite_eq_right (lt_irrefl _)]
      dsimp only [overwriteLeafAt]; split_ifs <;> rfl

theorem nodeDom_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeDom ℓ h1 hℓ u =
      st.nodeDom ℓ h1 hℓ u := by
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]
    split_ifs with hk
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; simp only [nodeDom_one, updateRoot]; by_cases hu : u = uL <;> simp [hu]
      · by_cases hlt' : ℓ < P.depth
        · simp [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateRoot]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; simp [updateRoot]
    · rfl
  · by_cases hLlt : L < P.depth
    · rw [dite_eq_right hL1, dite_eq_left hLlt]; dsimp only [overwriteInnerAt]
      split_ifs with hk
      · by_cases hℓ1 : ℓ = 1
        · subst hℓ1; simp [updateInner]
        · by_cases hlt' : ℓ < P.depth
          · simp only [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateInner]
            by_cases hℓL : ℓ = L
            · subst hℓL; rw [dite_eq_left rfl]; by_cases hu : u = uL <;> simp [hu]
            · rw [dite_eq_right hℓL]
          · have hd' : ℓ = P.depth := by omega
            subst hd'; simp [updateInner]
      · rfl
    · have hdL : L = P.depth := by omega
      subst hdL; rw [dite_eq_right hL1, dite_eq_right (lt_irrefl _)]; dsimp only [overwriteLeafAt]
      split_ifs with hk
      · by_cases hℓ1 : ℓ = 1
        · subst hℓ1; simp [updateLeaf]
        · by_cases hlt' : ℓ < P.depth
          · simp [nodeDom_inner _ h1 (by omega) hlt' hℓ, updateLeaf]
          · have hd' : ℓ = P.depth := by omega
            subst hd'; simp only [nodeDom_depth, updateLeaf]; by_cases hu : u = uL <;> simp [hu]
      · rfl

theorem nodeWait_overwriteAtNode
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeWait ℓ h2 hℓ u =
      st.nodeWait ℓ h2 hℓ u := by
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]
    split_ifs with hk
    · by_cases hlt' : ℓ < P.depth
      · simp [nodeWait_inner _ h2 hlt' hℓ, updateRoot]
      · have hd' : ℓ = P.depth := by omega
        subst hd'; simp [updateRoot]
    · rfl
  · by_cases hLlt : L < P.depth
    · rw [dite_eq_right hL1, dite_eq_left hLlt]; dsimp only [overwriteInnerAt]
      split_ifs with hk
      · by_cases hlt' : ℓ < P.depth
        · simp only [nodeWait_inner _ h2 hlt' hℓ, updateInner]
          by_cases hℓL : ℓ = L
          · subst hℓL; rw [dite_eq_left rfl]; by_cases hu : u = uL <;> simp [hu]
          · rw [dite_eq_right hℓL]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; simp [updateInner]
      · rfl
    · have hdL : L = P.depth := by omega
      subst hdL; rw [dite_eq_right hL1, dite_eq_right (lt_irrefl _)]; dsimp only [overwriteLeafAt]
      split_ifs with hk
      · by_cases hlt' : ℓ < P.depth
        · simp [nodeWait_inner _ h2 hlt' hℓ, updateLeaf]
        · have hd' : ℓ = P.depth := by omega
          subst hd'; simp only [nodeWait_depth, updateLeaf]
          by_cases hu : u = uL <;> simp [hu, LeafNode.overwrite, LeafNode.ofFixedEncoded]
      · rfl

theorem nodeQuery_overwriteAtNode_same
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k k' : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound) (hk : k ∈ st.nodeDom L h1L hLL uL) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeQuery scheme L h1L hLL uL k' =
      Function.update (st.nodeQuery scheme L h1L hLL uL) k (some qv) k' := by
  have hrhs : Function.update (st.nodeQuery scheme L h1L hLL uL) k (some qv) k' =
      if k' = k then some qv else st.nodeQuery scheme L h1L hLL uL k' := by
    by_cases hkk : k' = k <;> simp [hkk]
  rw [hrhs]
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1
    rw [nodeDom_one] at hk
    rw [dite_eq_left rfl, nodeQuery_one, nodeQuery_one]
    dsimp only [overwriteRootAt]
    rw [dite_eq_left hk]
    by_cases hkk : k' = k <;> simp [updateRoot, hkk]
  · by_cases hLlt : L < P.depth
    · have h2 : 2 ≤ L := by omega
      rw [nodeDom_inner st h1L h2 hLlt hLL] at hk
      rw [dite_eq_right hL1, dite_eq_left hLlt, nodeQuery_inner _ _ h1L h2 hLlt hLL,
        nodeQuery_inner _ _ h1L h2 hLlt hLL]
      dsimp only [overwriteInnerAt]
      rw [dite_eq_left hk]
      by_cases hkk : k' = k <;> simp [updateInner, hkk]
    · have hdL : L = P.depth := by omega
      subst hdL
      rw [nodeDom_depth] at hk
      rw [dite_eq_right hL1, dite_eq_right (lt_irrefl _), nodeQuery_depth, nodeQuery_depth]
      dsimp only [overwriteLeafAt]
      rw [dite_eq_left hk]
      by_cases hkk : k' = k <;> simp [updateLeaf, hkk]

theorem nodeQuery_overwriteAtNode_other
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {L : ℕ} (h1L : 1 ≤ L) (hLL : L ≤ P.depth)
    (uL : Fin (P.numNodes L)) (k : Fin (2 ^ P.idBits L))
    (qv : Fin (P.quotUniv L) × Fin P.valBound)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (k' : Fin (2 ^ P.idBits ℓ)) (hdiff : ∀ h_eq : ℓ = L, h_eq ▸ u ≠ uL) :
    (st.overwriteAtNode scheme L h1L hLL uL k qv).nodeQuery scheme ℓ h1 hℓ u k' =
      st.nodeQuery scheme ℓ h1 hℓ u k' := by
  dsimp only [overwriteAtNode]
  by_cases hL1 : L = 1
  · subst hL1; rw [dite_eq_left rfl]; dsimp only [overwriteRootAt]
    split_ifs with hk
    · by_cases hℓ1 : ℓ = 1
      · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; simp [updateRoot, hdiff rfl]
      · by_cases hlt' : ℓ < P.depth
        · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ,
            nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]; rfl
        · have hd' : ℓ = P.depth := by omega
          subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; rfl
    · rfl
  · by_cases hLlt : L < P.depth
    · rw [dite_eq_right hL1, dite_eq_left hLlt]; dsimp only [overwriteInnerAt]
      split_ifs with hk
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
      subst hdL; rw [dite_eq_right hL1, dite_eq_right (lt_irrefl _)]; dsimp only [overwriteLeafAt]
      split_ifs with hk
      · by_cases hℓ1 : ℓ = 1
        · subst hℓ1; rw [nodeQuery_one, nodeQuery_one]; rfl
        · by_cases hlt' : ℓ < P.depth
          · rw [nodeQuery_inner _ _ h1 (by omega) hlt' hℓ,
              nodeQuery_inner _ _ h1 (by omega) hlt' hℓ]; rfl
          · have hd' : ℓ = P.depth := by omega
            subst hd'; rw [nodeQuery_depth, nodeQuery_depth]; simp [updateLeaf, hdiff rfl]
      · rfl

/-- Overwrite loop scanning root-to-leaf for the stored level of an active key (`Section 5.3`). -/
noncomputable def rawOverwriteLoop
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (v_new : Fin P.valBound) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (c : P.LevelCoord ℓ) : P.TreeState :=
  match st.nodeQuery scheme ℓ h1 hℓ c.1 c.id with
  | some (q, _) =>
    if q == c.quot then
      st.overwriteAtNode scheme ℓ h1 hℓ c.1 c.id (q, v_new)
    else if hlt : ℓ < P.depth then
      st.rawOverwriteLoop scheme v_new (ℓ + 1) (by omega) hlt
        (st.seeds.stepCoordEquiv h1 hlt c)
    else st
  | none =>
    if hlt : ℓ < P.depth then
      st.rawOverwriteLoop scheme v_new (ℓ + 1) (by omega) hlt
        (st.seeds.stepCoordEquiv h1 hlt c)
    else st
termination_by P.depth - ℓ
decreasing_by all_goals omega

/-- Overwrite an active padded key `x ∈ P.paddedDom d` with `v_new : Fin P.valBound`. -/
noncomputable def rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) : P.TreeState :=
  st.rawOverwriteLoop scheme v_new 1 le_rfl (Nat.one_le_of_lt P.two_le_depth)
    (st.seeds.levelOneCoordEquiv x)

theorem sentCount_rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).sentCount = st.sentCount := by
  have hgen : ∀ (k m : ℕ), m + k = P.depth → (h1 : 1 ≤ m) → (hml : m ≤ P.depth) →
      ∀ c : P.LevelCoord m,
        (st.rawOverwriteLoop scheme v_new m h1 hml c).sentCount = st.sentCount := by
    intro k
    induction k with
    | zero =>
      intro m hsum h1 hml c
      obtain rfl : m = P.depth := by omega
      unfold rawOverwriteLoop
      split
      · split_ifs
        · exact st.sentCount_overwriteAtNode scheme h1 hml _ _ _
        · omega
        · rfl
      · rw [dite_eq_right (lt_irrefl _)]
    | succ k ih =>
      intro m hsum h1 hml c
      have hlt : m < P.depth := by omega
      unfold rawOverwriteLoop
      split
      · split_ifs
        · exact st.sentCount_overwriteAtNode scheme h1 hml _ _ _
        · exact ih (m + 1) (by omega) (by omega) hlt _
      · rw [dite_eq_left hlt]
        exact ih (m + 1) (by omega) (by omega) hlt _
  exact hgen (P.depth - 1) 1 (by have := P.two_le_depth; omega) le_rfl
    (Nat.one_le_of_lt P.two_le_depth) _

theorem seeds_rawOverwrite
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).seeds = st.seeds := by
  have hgen : ∀ (k m : ℕ), m + k = P.depth → (h1 : 1 ≤ m) → (hml : m ≤ P.depth) →
      ∀ c : P.LevelCoord m,
        (st.rawOverwriteLoop scheme v_new m h1 hml c).seeds = st.seeds := by
    intro k
    induction k with
    | zero =>
      intro m hsum h1 hml c
      obtain rfl : m = P.depth := by omega
      unfold rawOverwriteLoop
      split
      · split_ifs
        · exact st.seeds_overwriteAtNode scheme h1 hml _ _ _
        · omega
        · rfl
      · rw [dite_eq_right (lt_irrefl _)]
    | succ k ih =>
      intro m hsum h1 hml c
      have hlt : m < P.depth := by omega
      unfold rawOverwriteLoop
      split
      · split_ifs
        · exact st.seeds_overwriteAtNode scheme h1 hml _ _ _
        · exact ih (m + 1) (by omega) (by omega) hlt _
      · rw [dite_eq_left hlt]
        exact ih (m + 1) (by omega) (by omega) hlt _
  exact hgen (P.depth - 1) 1 (by have := P.two_le_depth; omega) le_rfl
    (Nat.one_le_of_lt P.two_le_depth) _

theorem wellFormedPadded_rawOverwrite
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {x : Fin P.paddedUniv}
    (hx : x ∈ P.paddedDom d) (v_new : Fin P.valBound) :
    (st.rawOverwrite scheme x v_new).WellFormedPadded scheme
      (Function.update d x (some v_new)) storeLvl := by
  have hdom_upd : P.paddedDom (Function.update d x (some v_new)) = P.paddedDom d := by
    rw [P.paddedDom_update_some, insert_eq_of_mem hx]
  obtain ⟨hlo_x, hhi_x⟩ := hwf.storeLvl_bounds x hx
  set L := storeLvl x
  let uL := st.seeds.nodeAt L hhi_x x
  let idL := st.seeds.idAt L hlo_x hhi_x x
  let qL := st.seeds.quotAt L hlo_x hhi_x x
  have hmemL : idL ∈ st.nodeDom L hlo_x hhi_x uL := by
    rw [hwf.dom_eq L hlo_x hhi_x uL]
    exact mem_image_of_mem _ (mem_filter.mpr ⟨SeedAssignment.mem_activeAt_iff.mpr ⟨hx, rfl⟩, rfl⟩)
  let st_target := st.overwriteAtNode scheme L hlo_x hhi_x uL idL (qL, v_new)
  have heq_target : st.rawOverwrite scheme x v_new = st_target := by
    obtain ⟨vx, hvx⟩ := Option.isSome_iff_exists.mp ((P.mem_paddedDom_iff d x).mp hx)
    have hgen : ∀ (k m : ℕ), m + k = L → (h1 : 1 ≤ m) → (hmL : m ≤ L) →
        st.rawOverwriteLoop scheme v_new m h1 (hmL.trans hhi_x)
          (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x) = st_target := by
      intro k
      induction k with
      | zero =>
        intro m hsum h1 hmL
        obtain rfl : m = L := by omega
        unfold rawOverwriteLoop
        have hc_eq : st.seeds.levelCoordEquiv L h1 hhi_x x = (uL, idL, qL) :=
          Prod.ext (st.seeds.levelCoordEquiv_fst h1 hhi_x x) rfl
        have hqL := hwf.query_eq_of_storeLvl L h1 hhi_x uL x vx hvx rfl rfl
        rw [hc_eq]
        change (match st.nodeQuery scheme L h1 (hmL.trans hhi_x) uL idL with
          | some (q, _) => if q == qL then _ else _
          | none => _) = _
        have hqL' : st.nodeQuery scheme L h1 (hmL.trans hhi_x) uL idL = some (qL, vx) := hqL
        rw [hqL']
        simp [st_target]
      | succ k ih =>
        intro m hsum h1 hmL
        have hm_lt_L : m < L := by omega
        have hm_lt_d : m < P.depth := hm_lt_L.trans_le hhi_x
        have hstep_coord : st.seeds.stepCoordEquiv h1 hm_lt_d
            (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x) =
            st.seeds.levelCoordEquiv (m + 1) (by omega) hm_lt_d x := by
          rw [st.seeds.levelCoordEquiv_succ h1 hm_lt_d, Equiv.trans_apply]
        have hnm := nodeQuery_match_iff hwf h1 (hmL.trans hhi_x) x
        rw [ite_eq_right (by omega : storeLvl x ≠ m)] at hnm
        have hc1 := st.seeds.levelCoordEquiv_fst h1 (hmL.trans hhi_x) x
        unfold rawOverwriteLoop
        rw [hc1]
        change (match st.nodeQuery scheme m h1 (hmL.trans hhi_x)
            (st.seeds.nodeAt m (hmL.trans hhi_x) x)
            (st.seeds.idAt m h1 (hmL.trans hhi_x) x) with
          | some (q, _) =>
            if q == st.seeds.quotAt m h1 (hmL.trans hhi_x) x then _
            else if hlt : m < P.depth then
              st.rawOverwriteLoop scheme v_new (m + 1) _ hlt
                (st.seeds.stepCoordEquiv h1 hlt
                  (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x))
            else st
          | none =>
            if hlt : m < P.depth then
              st.rawOverwriteLoop scheme v_new (m + 1) _ hlt
                (st.seeds.stepCoordEquiv h1 hlt
                  (st.seeds.levelCoordEquiv m h1 (hmL.trans hhi_x) x))
            else st) = _
        rcases hqm : st.nodeQuery scheme m h1 (hmL.trans hhi_x)
            (st.seeds.nodeAt m (hmL.trans hhi_x) x)
            (st.seeds.idAt m h1 (hmL.trans hhi_x) x) with _ | ⟨q, w⟩
        · dsimp only
          rw [dite_eq_left hm_lt_d, hstep_coord]
          exact ih (m + 1) (by omega) (by omega) (by omega)
        · rw [hqm] at hnm; dsimp only at hnm ⊢
          have hq_ne : ¬ (q == st.seeds.quotAt m h1 (hmL.trans hhi_x) x) := fun hb => by
            rw [ite_eq_left hb] at hnm; cases hnm
          rw [ite_eq_right hq_ne, dite_eq_left hm_lt_d, hstep_coord]
          exact ih (m + 1) (by omega) (by omega) (by omega)
    dsimp only [rawOverwrite]
    have h1 := hgen (L - 1) 1 (by omega) le_rfl hlo_x
    rwa [st.seeds.levelCoordEquiv_one] at h1
  rw [heq_target]
  have hseeds : st_target.seeds = st.seeds :=
    st.seeds_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new)
  refine
    { goodSeeds := by rw [hseeds, hdom_upd]; exact hwf.goodSeeds
      storeLvl_bounds := by rw [hdom_upd]; exact hwf.storeLvl_bounds
      storeLvl_outside := by rw [hdom_upd]; exact hwf.storeLvl_outside
      dom_eq := fun ℓ h1' hℓ' u => by
        rw [st.nodeDom_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h1' hℓ' u,
          hseeds, hdom_upd]
        exact hwf.dom_eq ℓ h1' hℓ' u
      query_eq_of_storeLvl := fun ℓ h1' hℓ' u y vy hdy hny hsly => ?_
      inner_full := fun ℓ h2' hlt' u => by
        have hd := st.nodeDom_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new)
          (by omega) hlt'.le u
        rw [nodeDom_inner _ _ h2' hlt' hlt'.le, nodeDom_inner _ _ h2' hlt' hlt'.le] at hd
        rw [hd]; exact hwf.inner_full ℓ h2' hlt' u
      wait_dom_eq := fun ℓ h2' hℓ' u => by
        rw [st.nodeWait_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h2' hℓ' u,
          hseeds, hdom_upd]
        exact hwf.wait_dom_eq ℓ h2' hℓ' u
      wait_lookup_eq := fun ℓ h2' hℓ' u y hy hsly => by
        rw [st.nodeWait_overwriteAtNode scheme hlo_x hhi_x uL idL (qL, v_new) h2' hℓ' u,
          hseeds]
        rw [hseeds, hdom_upd] at hy
        exact hwf.wait_lookup_eq ℓ h2' hℓ' u y hy hsly }
  rw [hseeds] at hny ⊢
  by_cases hyx : y = x
  · subst hyx
    rw [Function.update_self] at hdy
    have hvy : vy = v_new := (Option.some.inj hdy).symm
    subst hvy
    have hℓL : ℓ = L := hsly.symm
    subst hℓL; subst hny
    dsimp only [st_target]
    rw [st.nodeQuery_overwriteAtNode_same _ _ _ _ _ _ _ hmemL, Function.update_self]
  · rw [Function.update_of_ne hyx] at hdy
    have hy_in : y ∈ P.paddedDom d := (P.mem_paddedDom_iff d y).mpr (by simp [hdy])
    have hy_old := hwf.query_eq_of_storeLvl ℓ h1' hℓ' u y vy hdy hny hsly
    by_cases hsame : ∃ h_eq : ℓ = L, h_eq ▸ u = uL
    · obtain ⟨h_eq, hu_eq⟩ := hsame
      subst h_eq; subst hu_eq
      dsimp only [st_target]
      rw [st.nodeQuery_overwriteAtNode_same _ _ _ _ _ _ _ hmemL]
      have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds hlo_x hhi_x uL
      have hx_act : x ∈ st.seeds.activeAt (P.paddedDom d) L hhi_x uL :=
        SeedAssignment.mem_activeAt_iff.mpr ⟨hx, rfl⟩
      have hy_act : y ∈ st.seeds.activeAt (P.paddedDom d) L hhi_x uL :=
        SeedAssignment.mem_activeAt_iff.mpr ⟨hy_in, hny⟩
      have hid_ne : st.seeds.idAt L h1' hℓ' y ≠ idL := fun h => hyx (hinj hy_act hx_act h)
      rw [Function.update_of_ne hid_ne, hy_old]
    · push Not at hsame
      dsimp only [st_target]
      rw [st.nodeQuery_overwriteAtNode_other _ _ _ _ _ _ h1' hℓ' u _ hsame, hy_old]

end TreeSchedule.TreeState

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
