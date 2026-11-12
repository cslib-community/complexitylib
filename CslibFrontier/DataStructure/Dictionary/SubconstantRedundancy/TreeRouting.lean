/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSeeds

/-!
# Sentinel Padding and Bijective Multi-Level Coordinate Routing

This file formalizes the sentinel-padded key space (`Section 4, Footnote 5`, PDF p. 12 / printed
p. 11; `Section 5`, PDF p. 26 / printed p. 25), forest node ancestry, and bijective level-by-level
`(node, id, quot)` coordinate pipeline (`Sections 5.1 & 5.4`, PDF pp. 27, 32 / printed pp. 26, 31)
for the subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and
Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key* ([LiLiangYuZhou2024]).

## Main definitions

* `TreeSchedule.embedReal`, `TreeSchedule.sentinelKey`, `TreeSchedule.PaddedDict`: external and
  sentinel key embeddings into `Fin paddedUniv`.
* `TreeSchedule.childNodeEquiv`, `TreeSchedule.parentNode`, `TreeSchedule.ancestorAt`: forest node
  indexing and ancestor projections.
* `TreeSchedule.SeedAssignment`: per-node hash seed assignment `g_u` across `0 ≤ ℓ ≤ depth`, with
  bijections `levelCoordEquiv` and `stepCoordEquiv`.

## Main results

* `TreeSchedule.SeedAssignment.primCoordAt_congr_ancestors`: routed primitive IDs at level `ℓ`
  depend strictly on ancestor seeds at levels `< ℓ` (`Section 5.5`).
* `TreeSchedule.SeedAssignment.load_bounds_of_allGoodSeeds`,
  `TreeSchedule.SeedAssignment.injOn_idAt_activeAt`: load bounds and ID injectivity.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

private def fiberPermEquiv {α β : Type*} (perm : α → Equiv.Perm β)
    (hinv : ∀ a, Function.Involutive (perm a)) : Equiv.Perm (α × β) where
  toFun p := (p.1, perm p.1 p.2)
  invFun p := (p.1, perm p.1 p.2)
  left_inv p := Prod.ext rfl (hinv p.1 p.2)
  right_inv p := Prod.ext rfl (hinv p.1 p.2)

@[simp] private theorem fiberPermEquiv_apply {α β : Type*} (perm : α → Equiv.Perm β)
    (hinv : ∀ a, Function.Involutive (perm a)) (p : α × β) :
    fiberPermEquiv perm hinv p = (p.1, perm p.1 p.2) := rfl

@[simp] private theorem prodAssoc_symm_apply {α β γ : Type*} (x : α × β × γ) :
    (Equiv.prodAssoc α β γ).symm x = ((x.1, x.2.1), x.2.2) := rfl

namespace TreeSchedule

variable (P : TreeSchedule)

instance instSubsingletonFinNumNodesZero : Subsingleton (Fin (P.numNodes 0)) :=
  ⟨fun a b => Fin.ext (by have := a.isLt; have := b.isLt; simp [numNodes_zero] at *; omega)⟩

/-! ## Section 1: Sentinel-padded key universe and external dictionary correspondence -/

theorem univ_add_cap_le_paddedUniv : P.univ + P.cap ≤ P.paddedUniv := P.univ_le_padded

/-- Embed an external dictionary key `u : Fin P.univ` into `Fin P.paddedUniv`. -/
@[expose] def embedReal (u : Fin P.univ) : Fin P.paddedUniv :=
  ⟨u.val, u.isLt.trans_le ((Nat.le_add_right P.univ P.cap).trans P.univ_le_padded)⟩

theorem embedReal_injective : Function.Injective P.embedReal := fun u₁ u₂ h =>
  Fin.ext (by simpa only [embedReal] using congrArg Fin.val h)

/-- `i`-th sentinel padding key `P.univ + i` in `Fin P.paddedUniv` (`Section 4, Footnote 5`,
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 12 / printed p. 11). -/
@[expose] def sentinelKey (i : Fin P.cap) : Fin P.paddedUniv :=
  ⟨P.univ + i.val, (Nat.add_lt_add_left i.isLt P.univ).trans_le P.univ_le_padded⟩

theorem sentinelKey_injective : Function.Injective P.sentinelKey := fun i₁ i₂ h =>
  Fin.ext (Nat.add_left_cancel (by simpa only [sentinelKey] using congrArg Fin.val h))

theorem embedReal_ne_sentinelKey (u : Fin P.univ) (i : Fin P.cap) :
    P.embedReal u ≠ P.sentinelKey i := fun h => by
  have hv := congrArg Fin.val h; dsimp only [embedReal, sentinelKey] at hv; have := u.isLt; omega

/-- Internal padded dictionary mapping `Fin P.paddedUniv` to bounded values `Fin P.valBound`. -/
abbrev PaddedDict : Type := Fin P.paddedUniv → Option (Fin P.valBound)

/-- Active key domain `{x : Fin P.paddedUniv | (d x).isSome}` of a `PaddedDict`. -/
@[expose] def paddedDom (d : P.PaddedDict) : Finset (Fin P.paddedUniv) :=
  Finset.univ.filter fun x => (d x).isSome

@[simp] theorem mem_paddedDom_iff (d : P.PaddedDict) (x : Fin P.paddedUniv) :
    x ∈ P.paddedDom d ↔ (d x).isSome := by simp [paddedDom]

@[simp] theorem paddedDom_update_some (d : P.PaddedDict) (x : Fin P.paddedUniv)
    (v : Fin P.valBound) :
    P.paddedDom (Function.update d x (some v)) = Insert.insert x (P.paddedDom d) := by
  ext y; by_cases h : y = x <;> simp [h]

@[simp] theorem paddedDom_update_none (d : P.PaddedDict) (x : Fin P.paddedUniv) :
    P.paddedDom (Function.update d x none) = (P.paddedDom d).erase x := by
  ext y; by_cases h : y = x <;> simp [h]

/-- Correspondence between an internal sentinel-padded dictionary `d`, active sentinel count
`sentCount ≤ P.cap`, and external `dict : Dictionary.State P.univ`. -/
structure MatchesExternal (d : P.PaddedDict) (sentCount : ℕ)
    (dict : Dictionary.State P.univ) : Prop where
  sentCount_le : sentCount ≤ P.cap
  card_lo : P.cap - 1 ≤ (P.paddedDom d).card
  card_hi : (P.paddedDom d).card ≤ P.cap
  real_eq : ∀ u : Fin P.univ, (d (P.embedReal u)).map Fin.val = dict u
  sentinel_eq : ∀ x : Fin P.paddedUniv, P.univ ≤ x.val →
    d x = if x.val < P.univ + sentCount then some ⟨0, P.val_pos⟩ else none

/-- Canonical empty-dictionary padded state containing all `P.cap` sentinel keys with value `0`. -/
@[expose]
def initPaddedDict : P.PaddedDict := fun x =>
  if P.univ ≤ x.val ∧ x.val < P.univ + P.cap then some ⟨0, P.val_pos⟩ else none

theorem paddedDom_eq_disjUnion {d : P.PaddedDict} {sentCount : ℕ}
    {dict : Dictionary.State P.univ} (hm : P.MatchesExternal d sentCount dict) :
    P.paddedDom d =
      (Dictionary.dom dict).map ⟨P.embedReal, P.embedReal_injective⟩ ∪
        ((Finset.range sentCount).attach.map
          ⟨fun i => P.sentinelKey ⟨i.1, (Finset.mem_range.mp i.2).trans_le hm.sentCount_le⟩,
            fun _ _ h => Subtype.ext (congrArg Fin.val (P.sentinelKey_injective h))⟩) := by
  ext x
  simp only [mem_paddedDom_iff, mem_union, mem_map, mem_attach, true_and,
    Function.Embedding.coeFn_mk]
  by_cases hx : x.val < P.univ
  · let u : Fin P.univ := ⟨x.val, hx⟩
    have hxu : P.embedReal u = x := Fin.ext rfl
    constructor
    · intro hsome
      left
      refine ⟨u, ?_, hxu⟩
      simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u, hxu,
        Option.isSome_map]
      exact hsome
    · rintro (⟨u', hu', rfl⟩ | ⟨⟨i, hi⟩, hseq⟩)
      · simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u',
          Option.isSome_map] at hu'
        exact hu'
      · have hv : P.univ + i = x.val := congrArg Fin.val hseq
        omega
  · have hge : P.univ ≤ x.val := not_lt.mp hx
    rw [hm.sentinel_eq x hge]
    constructor
    · intro hsome
      split_ifs at hsome with hlt
      · right
        refine ⟨⟨x.val - P.univ, Finset.mem_range.mpr (by omega)⟩, ?_⟩
        change P.sentinelKey ⟨x.val - P.univ, _⟩ = x
        apply Fin.ext
        dsimp only [sentinelKey]
        omega
      · simp at hsome
    · rintro (⟨u', _, rfl⟩ | ⟨⟨i, hi⟩, hseq⟩)
      · exact absurd u'.isLt (not_lt.mpr hge)
      · have hi_lt : i < sentCount := Finset.mem_range.mp hi
        have hv : P.univ + i = x.val := congrArg Fin.val hseq
        rw [ite_eq_left (by omega)]
        rfl

theorem card_paddedDom_eq {d : P.PaddedDict} {sentCount : ℕ}
    {dict : Dictionary.State P.univ} (hm : P.MatchesExternal d sentCount dict) :
    (P.paddedDom d).card = (Dictionary.dom dict).card + sentCount := by
  rw [P.paddedDom_eq_disjUnion hm, card_union_of_disjoint]
  · simp [card_map, card_attach, Finset.card_range]
  · rw [Finset.disjoint_left]
    rintro x hx₁ hx₂
    obtain ⟨u, _, rfl⟩ := mem_map.mp hx₁
    obtain ⟨⟨i, _⟩, _, hseq⟩ := mem_map.mp hx₂
    exact P.embedReal_ne_sentinelKey u _ hseq.symm

theorem matchesExternal_valuesBounded {d : P.PaddedDict} {sentCount : ℕ}
    {dict : Dictionary.State P.univ} (hm : P.MatchesExternal d sentCount dict) :
    Dictionary.ValuesBounded P.valBound dict := by
  intro u v hdu
  rw [← hm.real_eq u] at hdu
  rcases h : d (P.embedReal u) with _ | w
  · simp [h] at hdu
  · simp only [h, Option.map_some, Option.some.injEq] at hdu
    exact hdu ▸ w.isLt

theorem matchesExternal_card_dom_le {d : P.PaddedDict} {sentCount : ℕ}
    {dict : Dictionary.State P.univ} (hm : P.MatchesExternal d sentCount dict) :
    (Dictionary.dom dict).card ≤ P.cap := by
  have hc := P.card_paddedDom_eq hm
  have hhi := hm.card_hi
  omega

theorem paddedDom_initPaddedDict :
    P.paddedDom P.initPaddedDict =
      (Finset.univ : Finset (Fin P.cap)).map ⟨P.sentinelKey, P.sentinelKey_injective⟩ := by
  ext x
  simp only [mem_paddedDom_iff, initPaddedDict, mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hs
    split_ifs at hs with h
    · refine ⟨⟨x.val - P.univ, by omega⟩, ?_⟩
      ext; dsimp only [sentinelKey]; omega
    · simp at hs
  · rintro ⟨i, rfl⟩
    have hcond : P.univ ≤ (P.sentinelKey i).val ∧ (P.sentinelKey i).val < P.univ + P.cap := by
      dsimp only [sentinelKey]; exact ⟨by omega, by omega⟩
    rw [ite_eq_left hcond]
    rfl

theorem matchesExternal_initPaddedDict :
    P.MatchesExternal P.initPaddedDict P.cap (Dictionary.empty P.univ) where
  sentCount_le := le_rfl
  card_lo := by rw [P.paddedDom_initPaddedDict, card_map, card_univ, Fintype.card_fin]; omega
  card_hi := by rw [P.paddedDom_initPaddedDict, card_map, card_univ, Fintype.card_fin]
  real_eq u := by
    dsimp only [initPaddedDict, embedReal]
    rw [ite_eq_right (fun h => absurd u.isLt (not_lt.mpr h.1))]
    rfl
  sentinel_eq x hge := by
    dsimp only [initPaddedDict]
    by_cases hlt : x.val < P.univ + P.cap
    · rw [ite_eq_left ⟨hge, hlt⟩, ite_eq_left hlt]
    · rw [ite_eq_right (fun h => hlt h.2), ite_eq_right hlt]

/-! ## Section 2: Forest node indexing and ancestor topology -/

/-- Equivalence `(parent, branch) ≃ child` between level `ℓ` and level `ℓ + 1`. -/
def childNodeEquiv (ℓ : ℕ) :
    Fin (P.numNodes ℓ) × Fin (2 ^ P.branchBits ℓ) ≃ Fin (P.numNodes (ℓ + 1)) :=
  finProdFinEquiv.trans (finCongr (P.numNodes_succ ℓ).symm)

/-- Parent node of `u : Fin (P.numNodes (ℓ + 1))` at level `ℓ`. -/
def parentNode (ℓ : ℕ) (u : Fin (P.numNodes (ℓ + 1))) : Fin (P.numNodes ℓ) :=
  ((P.childNodeEquiv ℓ).symm u).1

/-- Branch index `b ∈ Fin (2 ^ branchBits ℓ)` of `u : Fin (P.numNodes (ℓ + 1))` under its parent. -/
def childBranch (ℓ : ℕ) (u : Fin (P.numNodes (ℓ + 1))) : Fin (2 ^ P.branchBits ℓ) :=
  ((P.childNodeEquiv ℓ).symm u).2

@[simp]
theorem childNodeEquiv_parent_branch (ℓ : ℕ) (u : Fin (P.numNodes (ℓ + 1))) :
    P.childNodeEquiv ℓ (P.parentNode ℓ u, P.childBranch ℓ u) = u :=
  (P.childNodeEquiv ℓ).apply_symm_apply u

@[simp]
theorem parentNode_childNodeEquiv (ℓ : ℕ) (p : Fin (P.numNodes ℓ))
    (b : Fin (2 ^ P.branchBits ℓ)) :
    P.parentNode ℓ (P.childNodeEquiv ℓ (p, b)) = p := by
  simp [parentNode]

@[simp]
theorem childBranch_childNodeEquiv (ℓ : ℕ) (p : Fin (P.numNodes ℓ))
    (b : Fin (2 ^ P.branchBits ℓ)) :
    P.childBranch ℓ (P.childNodeEquiv ℓ (p, b)) = b := by
  simp [childBranch]

/-- Ancestor of a level-`ℓ` node `u` at any level `j ≤ ℓ`. -/
def ancestorAt : ∀ {j ℓ : ℕ}, j ≤ ℓ → Fin (P.numNodes ℓ) → Fin (P.numNodes j)
  | _, 0, hj, u => by
    obtain rfl : _ = 0 := Nat.eq_zero_of_le_zero hj
    exact u
  | j, ℓ + 1, hj, u =>
    if h : j = ℓ + 1 then h ▸ u
    else ancestorAt (Nat.le_of_lt_succ (lt_of_le_of_ne hj h)) (P.parentNode ℓ u)

@[simp]
theorem ancestorAt_refl {ℓ : ℕ} (u : Fin (P.numNodes ℓ)) :
    P.ancestorAt (le_rfl : ℓ ≤ ℓ) u = u := by
  cases ℓ with
  | zero => rfl
  | succ _ => simp [ancestorAt]

theorem ancestorAt_succ {j ℓ : ℕ} (hj : j ≤ ℓ) (u : Fin (P.numNodes (ℓ + 1))) :
    P.ancestorAt (Nat.le_succ_of_le hj) u = P.ancestorAt hj (P.parentNode ℓ u) := by
  dsimp only [ancestorAt]; rw [dite_eq_right (by omega)]

theorem ancestorAt_trans {i j ℓ : ℕ} (hij : i ≤ j) (hjℓ : j ≤ ℓ) (u : Fin (P.numNodes ℓ)) :
    P.ancestorAt hij (P.ancestorAt hjℓ u) = P.ancestorAt (hij.trans hjℓ) u := by
  induction ℓ generalizing j with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hjℓ; obtain rfl := Nat.eq_zero_of_le_zero hij; rfl
  | succ m ih =>
    by_cases hjm : j = m + 1
    · subst hjm; simp
    · have hj_le : j ≤ m := Nat.le_of_lt_succ (lt_of_le_of_ne hjℓ hjm)
      rw [P.ancestorAt_succ hj_le, P.ancestorAt_succ (hij.trans hj_le), ih hij hj_le]

/-! ## Section 3: Seed assignments and bijective coordinate pipeline -/

/-- Level-`ℓ` routed `(node, primitiveId)` coordinate (`0 ≤ ℓ ≤ depth`). -/
abbrev PrimCoord (ℓ : ℕ) : Type :=
  Fin (P.numNodes ℓ) × P.PrimId ℓ

/-- Level-`ℓ` routed `(node, compressedId, quotient)` coordinate (`1 ≤ ℓ ≤ depth`). -/
abbrev LevelCoord (ℓ : ℕ) : Type :=
  Fin (P.numNodes ℓ) × Fin (2 ^ P.idBits ℓ) × Fin (P.quotUniv ℓ)
/-- Node component of `c : P.LevelCoord ℓ`. -/
abbrev LevelCoord.node {P : TreeSchedule} {ℓ : ℕ} (c : P.LevelCoord ℓ) : Fin (P.numNodes ℓ) := c.1
/-- Compressed-ID component of `c : P.LevelCoord ℓ`. -/
abbrev LevelCoord.id {P : TreeSchedule} {ℓ : ℕ} (c : P.LevelCoord ℓ) : Fin (2 ^ P.idBits ℓ) := c.2.1
/-- Quotient component of `c : P.LevelCoord ℓ`. -/
abbrev LevelCoord.quot {P : TreeSchedule} {ℓ : ℕ} (c : P.LevelCoord ℓ) : Fin (P.quotUniv ℓ) := c.2.2

/-- Full-forest hash seed assignment storing `g_u : P.NodeSeed ℓ` at every node `0 ≤ ℓ ≤ depth`. -/
@[ext] structure SeedAssignment (P : TreeSchedule) where
  /-- Per-node hash seed `g_u` at `(ℓ, u)`. -/
  seed : ∀ (ℓ : ℕ), ℓ ≤ P.depth → Fin (P.numNodes ℓ) → P.NodeSeed ℓ

/-- Equivalence `Fin P.paddedUniv ≃ P.PrimCoord 0` at the top router (`numNodes 0 = 1`). -/
def paddedToPrimZeroEquiv : Fin P.paddedUniv ≃ P.PrimCoord 0 :=
  have hp : P.paddedUniv = 2 ^ P.branchBits 0 * P.routerRightUniv 0 := by
    dsimp only [paddedUniv, branchFactor, routerRightUniv]
    rw [ite_eq_left rfl, Nat.mul_assoc]
  ((finCongr hp).trans (FeistelPerm.mixedDomainEquiv (P.branchBits 0) (P.routerRightUniv 0))).trans
    { toFun := fun y => (⟨0, P.numNodes_pos 0⟩, y)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun ⟨u, _⟩ => Prod.ext (Subsingleton.elim _ u) rfl }

namespace SeedAssignment

variable {P : TreeSchedule}

/-- Top-level routing bijection `PrimCoord 0 ≃ PrimCoord 1` via `topSeed = seeds.seed 0 _ 0`. -/
noncomputable def primZeroToOneEquiv (seeds : P.SeedAssignment) :
    P.PrimCoord 0 ≃ P.PrimCoord 1 :=
  let h0 : 0 < P.depth := Nat.lt_of_lt_of_le Nat.zero_lt_two P.two_le_depth
  have hr : P.routerRightUniv 0 = 2 ^ P.idBits 1 * P.idCompRightUniv 1 := rfl
  (fiberPermEquiv (α := Fin (P.numNodes 0))
    (β := Fin (2 ^ P.branchBits 0) × Fin (P.routerRightUniv 0))
    (fun u₀ => P.routerPerm 0 (P.routerSeedOfNodeSeed h0 (seeds.seed 0 (Nat.zero_le _) u₀)))
    (fun _ => P.routerPerm_involutive 0 _)).trans
    ((Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (P.childNodeEquiv 0)
        ((finCongr hr).trans
          (FeistelPerm.mixedDomainEquiv (P.idBits 1) (P.idCompRightUniv 1)))))

theorem primZeroToOneEquiv_congr {s₁ s₂ : P.SeedAssignment} (p : P.PrimCoord 0)
    (hs : s₁.seed 0 (Nat.zero_le _) p.1 = s₂.seed 0 (Nat.zero_le _) p.1) :
    s₁.primZeroToOneEquiv p = s₂.primZeroToOneEquiv p := by
  unfold primZeroToOneEquiv
  simp only [Equiv.trans_apply, fiberPermEquiv_apply, hs]

theorem primZeroToOneEquiv_fst (seeds : P.SeedAssignment) (p : P.PrimCoord 0) :
    (seeds.primZeroToOneEquiv p).1 =
      P.childNodeEquiv 0 (p.1, FeistelPerm.feistelHead
        (P.routerRound 0 (P.routerSeedOfNodeSeed
          (Nat.lt_of_lt_of_le Nat.zero_lt_two P.two_le_depth)
          (seeds.seed 0 (Nat.zero_le _) p.1))) p.2) := by
  unfold primZeroToOneEquiv
  simp only [Equiv.trans_apply, fiberPermEquiv_apply, routerPerm_apply, FeistelPerm.feistelPair,
    prodAssoc_symm_apply, Equiv.prodCongr_apply, Prod.map_fst]

/-- Level-1 ID compression bijection `PrimCoord 1 ≃ LevelCoord 1`. -/
noncomputable def primOneToCoordOneEquiv (seeds : P.SeedAssignment) :
    P.PrimCoord 1 ≃ P.LevelCoord 1 :=
  fiberPermEquiv (α := Fin (P.numNodes 1))
    (β := Fin (2 ^ P.idBits 1) × Fin (P.idCompRightUniv 1))
    (fun u₁ => FeistelPerm.idCompressorPerm (P.idBits 1) (P.idCompRightUniv 1)
      (P.idSeedOfNodeSeed (seeds.seed 1 (Nat.one_le_of_lt P.two_le_depth) u₁)))
    (fun _ => FeistelPerm.idCompressorPerm_involutive _ _ _)

theorem primOneToCoordOneEquiv_apply (seeds : P.SeedAssignment) (p : P.PrimCoord 1) :
    seeds.primOneToCoordOneEquiv p =
      (p.1, FeistelPerm.feistelPair
        (FeistelPerm.idCompressorRound (P.idBits 1) (P.idCompRightUniv 1)
          (P.idSeedOfNodeSeed (seeds.seed 1 (Nat.one_le_of_lt P.two_le_depth) p.1))) p.2) := by
  change fiberPermEquiv (α := Fin (P.numNodes 1))
      (β := Fin (2 ^ P.idBits 1) × Fin (P.idCompRightUniv 1))
      (fun u₁ => FeistelPerm.idCompressorPerm (P.idBits 1) (P.idCompRightUniv 1)
        (P.idSeedOfNodeSeed (seeds.seed 1 (Nat.one_le_of_lt P.two_le_depth) u₁)))
      (fun _ => FeistelPerm.idCompressorPerm_involutive _ _ _) p = _
  rw [fiberPermEquiv_apply, FeistelPerm.idCompressorPerm_apply]

/-- Full level-1 coordinate bijection `Fin P.paddedUniv ≃ P.LevelCoord 1`. -/
noncomputable def levelOneCoordEquiv (seeds : P.SeedAssignment) :
    Fin P.paddedUniv ≃ P.LevelCoord 1 :=
  P.paddedToPrimZeroEquiv.trans (seeds.primZeroToOneEquiv.trans seeds.primOneToCoordOneEquiv)

/-- Child-routing bijection `(u_m, x_id_m) ≃ (u_{m + 1}, prim_{m + 1})` on edge `m → m + 1`
(`1 ≤ m < depth`). -/
noncomputable def routeIdToPrimEquiv (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) :
    (Fin (P.numNodes m) × Fin (2 ^ P.idBits m)) ≃ P.PrimCoord (m + 1) :=
  have hsL : P.branchBits m ≤ P.idBits m := by
    have := P.idBits_step_le m h1 hm; omega
  have hsId : P.idBits (m + 1) ≤ P.idBits m - P.branchBits m := by
    have := P.idBits_step_le m h1 hm; omega
  have hRight : 2 ^ (P.idBits m - P.branchBits m) = P.routerRightUniv m := by
    dsimp only [routerRightUniv]; rw [ite_eq_right (by omega)]
  have hComp : 2 ^ (P.idBits m - P.branchBits m - P.idBits (m + 1)) =
      P.idCompRightUniv (m + 1) := by
    dsimp only [idCompRightUniv, remBits]; rw [ite_eq_right (by omega)]; rfl
  let splitIn : (Fin (P.numNodes m) × Fin (2 ^ P.idBits m)) ≃
      (Fin (P.numNodes m) × (Fin (2 ^ P.branchBits m) × Fin (P.routerRightUniv m))) :=
    Equiv.prodCongr (Equiv.refl _)
      ((FeistelPerm.bitDomainEquiv hsL).trans (Equiv.prodCongr (Equiv.refl _) (finCongr hRight)))
  let permMid := fiberPermEquiv (α := Fin (P.numNodes m))
    (β := Fin (2 ^ P.branchBits m) × Fin (P.routerRightUniv m))
    (fun u_m => P.routerPerm m (P.routerSeedOfNodeSeed hm (seeds.seed m hm.le u_m)))
    (fun u_m => P.routerPerm_involutive m _)
  let splitOut : (Fin (P.numNodes m) × (Fin (2 ^ P.branchBits m) × Fin (P.routerRightUniv m))) ≃
      P.PrimCoord (m + 1) :=
    (Equiv.prodAssoc _ _ _).symm.trans
      (Equiv.prodCongr (P.childNodeEquiv m)
        ((finCongr hRight.symm).trans
          ((FeistelPerm.bitDomainEquiv hsId).trans
            (Equiv.prodCongr (Equiv.refl _) (finCongr hComp)))))
  splitIn.trans (permMid.trans splitOut)

theorem routeIdToPrimEquiv_congr {s₁ s₂ : P.SeedAssignment} {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) (p : Fin (P.numNodes m) × Fin (2 ^ P.idBits m))
    (hs : s₁.seed m hm.le p.1 = s₂.seed m hm.le p.1) :
    s₁.routeIdToPrimEquiv h1 hm p = s₂.routeIdToPrimEquiv h1 hm p := by
  unfold routeIdToPrimEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, fiberPermEquiv_apply, hs]

theorem routeIdToPrimEquiv_fst (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) (hsL : P.branchBits m ≤ P.idBits m)
    (hRight : 2 ^ (P.idBits m - P.branchBits m) = P.routerRightUniv m)
    (p : Fin (P.numNodes m) × Fin (2 ^ P.idBits m)) :
    (seeds.routeIdToPrimEquiv h1 hm p).1 =
      P.childNodeEquiv m (p.1, FeistelPerm.feistelHead
        (P.routerRound m (P.routerSeedOfNodeSeed hm (seeds.seed m hm.le p.1)))
        ((FeistelPerm.bitDomainEquiv hsL p.2).1,
          finCongr hRight (FeistelPerm.bitDomainEquiv hsL p.2).2)) := by
  unfold routeIdToPrimEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, fiberPermEquiv_apply, routerPerm_apply, FeistelPerm.feistelPair,
    prodAssoc_symm_apply]
  rfl

/-- Level-`(m + 1)` ID compression bijection
`PrimCoord (m + 1) ≃ Fin (numNodes (m + 1)) × Fin (2 ^ idBits (m + 1)) × Fin (2 ^ remBits m)`. -/
noncomputable def primSuccToIdRemEquiv (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) :
    P.PrimCoord (m + 1) ≃
      Fin (P.numNodes (m + 1)) × Fin (2 ^ P.idBits (m + 1)) × Fin (2 ^ P.remBits m) :=
  have hComp : P.idCompRightUniv (m + 1) = 2 ^ P.remBits m := by
    dsimp only [idCompRightUniv]; rw [ite_eq_right (by omega)]; rfl
  (fiberPermEquiv (α := Fin (P.numNodes (m + 1)))
    (β := Fin (2 ^ P.idBits (m + 1)) × Fin (P.idCompRightUniv (m + 1)))
    (fun u_next => FeistelPerm.idCompressorPerm (P.idBits (m + 1)) (P.idCompRightUniv (m + 1))
      (P.idSeedOfNodeSeed (seeds.seed (m + 1) hm u_next)))
    (fun u_next => FeistelPerm.idCompressorPerm_involutive _ _ _)).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (finCongr hComp)))

/-- Quotient-remainder merge equivalence
`Fin (quotUniv m) × Fin (2 ^ remBits m) ≃ Fin (quotUniv (m + 1))` for `1 ≤ m`. -/
def quotMergeEquiv {m : ℕ} (h1 : 1 ≤ m) :
    Fin (P.quotUniv m) × Fin (2 ^ P.remBits m) ≃ Fin (P.quotUniv (m + 1)) :=
  finProdFinEquiv.trans (finCongr (P.quotUniv_succ_of_pos h1).symm)

/-- Single-edge coordinate bijection `LevelCoord m ≃ LevelCoord (m + 1)` (`1 ≤ m < depth`,
`Section 5.1` & `Algorithm 3` Line 14). -/
noncomputable def stepCoordEquiv (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) :
    P.LevelCoord m ≃ P.LevelCoord (m + 1) where
  toFun := fun (u_m, id_m, q_m) =>
    let prim_next := seeds.routeIdToPrimEquiv h1 hm (u_m, id_m)
    let ir := seeds.primSuccToIdRemEquiv h1 hm prim_next
    let ir2 := ir.2
    (ir.1, ir2.1, quotMergeEquiv h1 (q_m, ir2.2))
  invFun := fun (u_next, id_next, q_next) =>
    let qr := (quotMergeEquiv (P := P) h1).symm q_next
    let prim_next := (seeds.primSuccToIdRemEquiv h1 hm).symm (u_next, id_next, qr.2)
    let uid := (seeds.routeIdToPrimEquiv h1 hm).symm prim_next
    (uid.1, uid.2, qr.1)
  left_inv := fun (u_m, id_m, q_m) => by simp [Prod.mk.eta]
  right_inv := fun (u_next, id_next, q_next) => by
    rcases hqr : (quotMergeEquiv (P := P) h1).symm q_next with ⟨q_m, rem_m⟩
    have hq_eq : quotMergeEquiv (P := P) h1 (q_m, rem_m) = q_next := by
      rw [← hqr, Equiv.apply_symm_apply]
    simp [hqr, hq_eq]

@[simp] theorem stepCoordEquiv_apply (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m)
    (hm : m < P.depth) (c : P.LevelCoord m) :
    seeds.stepCoordEquiv h1 hm c =
      let prim_next := seeds.routeIdToPrimEquiv h1 hm (c.node, c.id)
      let ir := seeds.primSuccToIdRemEquiv h1 hm prim_next
      let ir2 := ir.2
      (ir.1, ir2.1, quotMergeEquiv h1 (c.quot, ir2.2)) := by rfl

/-- Multi-level coordinate bijection `Fin P.paddedUniv ≃ P.LevelCoord ℓ` for `1 ≤ ℓ ≤ depth`. -/
noncomputable def levelCoordEquiv (seeds : P.SeedAssignment) :
    ∀ (ℓ : ℕ), 1 ≤ ℓ → ℓ ≤ P.depth → (Fin P.paddedUniv ≃ P.LevelCoord ℓ)
  | 0, h1, _ => False.elim (by omega)
  | 1, _, _ => seeds.levelOneCoordEquiv
  | m + 2, _, hℓ =>
    (seeds.levelCoordEquiv (m + 1) (by omega) (by omega)).trans
      (seeds.stepCoordEquiv (by omega) (by omega))

@[simp] theorem levelCoordEquiv_one (seeds : P.SeedAssignment) :
    seeds.levelCoordEquiv 1 le_rfl (Nat.one_le_of_lt P.two_le_depth) = seeds.levelOneCoordEquiv :=
  by rfl

theorem levelCoordEquiv_succ (seeds : P.SeedAssignment) {m : ℕ} (h1 : 1 ≤ m) (hm : m < P.depth) :
    seeds.levelCoordEquiv (m + 1) (by omega) hm =
      (seeds.levelCoordEquiv m h1 hm.le).trans (seeds.stepCoordEquiv h1 hm) := by
  cases m with | zero => omega | succ _ => rfl

/-- Routed `(node, primId)` coordinate of `x : Fin P.paddedUniv` at level `0 ≤ ℓ ≤ depth`. -/
noncomputable def primCoordAt (seeds : P.SeedAssignment) :
    ∀ (ℓ : ℕ), ℓ ≤ P.depth → Fin P.paddedUniv → P.PrimCoord ℓ
  | 0, _, x => P.paddedToPrimZeroEquiv x
  | 1, _, x => seeds.primZeroToOneEquiv (P.paddedToPrimZeroEquiv x)
  | m + 2, _, x =>
    let c := seeds.levelCoordEquiv (m + 1) (by omega) (by omega) x
    seeds.routeIdToPrimEquiv (by omega) (by omega) (c.node, c.id)

/-- Node reached by `x : Fin P.paddedUniv` at level `0 ≤ ℓ ≤ depth`. -/
@[expose] noncomputable def nodeAt (seeds : P.SeedAssignment) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) : Fin (P.numNodes ℓ) := (seeds.primCoordAt ℓ hℓ x).1

/-- Compressed `I_ℓ`-bit ID of `x : Fin P.paddedUniv` at level `1 ≤ ℓ ≤ depth`. -/
@[expose] noncomputable def idAt (seeds : P.SeedAssignment) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) : Fin (2 ^ P.idBits ℓ) := (seeds.levelCoordEquiv ℓ h1 hℓ x).id

/-- Quotient `x_quot^[ℓ]` of `x : Fin P.paddedUniv` at level `1 ≤ ℓ ≤ depth`. -/
@[expose] noncomputable def quotAt (seeds : P.SeedAssignment) (ℓ : ℕ) (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.depth) (x : Fin P.paddedUniv) : Fin (P.quotUniv ℓ) :=
  (seeds.levelCoordEquiv ℓ h1 hℓ x).quot

theorem levelCoordEquiv_fst (seeds : P.SeedAssignment) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) : (seeds.levelCoordEquiv ℓ h1 hℓ x).1 = seeds.nodeAt ℓ hℓ x := by
  rcases ℓ with _ | _ | _ <;> [omega; rfl; rfl]

theorem idAt_succ_eq_idCompressorHead (seeds : P.SeedAssignment) {k : ℕ} (hk : k + 1 ≤ P.depth)
    (x : Fin P.paddedUniv) :
    seeds.idAt (k + 1) (by omega) hk x =
      FeistelPerm.idCompressorHead (P.idBits (k + 1)) (P.idCompRightUniv (k + 1))
        (P.idSeedOfNodeSeed (seeds.seed (k + 1) hk (seeds.nodeAt (k + 1) hk x)))
        (seeds.primCoordAt (k + 1) hk x).2 := by
  rw [FeistelPerm.idCompressorHead_apply]
  cases k with
  | zero =>
    unfold idAt levelCoordEquiv levelOneCoordEquiv primCoordAt nodeAt
    rw [Equiv.trans_apply, Equiv.trans_apply, primOneToCoordOneEquiv_apply]
    rfl
  | succ m =>
    unfold idAt levelCoordEquiv primCoordAt nodeAt
    rw [Equiv.trans_apply, stepCoordEquiv_apply]
    unfold primSuccToIdRemEquiv
    simp only [Equiv.trans_apply, fiberPermEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst,
      Prod.map_snd, Equiv.refl_apply, FeistelPerm.idCompressorPerm_apply]
    rfl

/-! ## Section 4: Routed key sets, ancestor-only dependence, and `AllGoodSeeds` invariants -/

theorem parentNode_nodeAt (seeds : P.SeedAssignment) {ℓ : ℕ} (hℓ : ℓ + 1 ≤ P.depth)
    (x : Fin P.paddedUniv) :
    P.parentNode ℓ (seeds.nodeAt (ℓ + 1) hℓ x) = seeds.nodeAt ℓ (by omega) x := by
  cases ℓ with
  | zero =>
    exact Subsingleton.elim _ _
  | succ m =>
    have hc : (seeds.levelCoordEquiv (m + 1) (by omega) (by omega) x).1 =
        seeds.nodeAt (m + 1) (by omega) x := seeds.levelCoordEquiv_fst (by omega) (by omega) x
    change P.parentNode (m + 1)
      (seeds.routeIdToPrimEquiv (by omega) (by omega)
        ((seeds.levelCoordEquiv (m + 1) (by omega) (by omega) x).1,
          (seeds.levelCoordEquiv (m + 1) (by omega) (by omega) x).2.1)).1 =
      seeds.nodeAt (m + 1) (by omega) x
    dsimp only [routeIdToPrimEquiv, fiberPermEquiv]
    simp [hc]

theorem ancestorAt_nodeAt (seeds : P.SeedAssignment) {j ℓ : ℕ} (hjℓ : j ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (x : Fin P.paddedUniv) :
    P.ancestorAt hjℓ (seeds.nodeAt ℓ hℓ x) = seeds.nodeAt j (hjℓ.trans hℓ) x := by
  induction ℓ with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hjℓ
    rfl
  | succ m ih =>
    by_cases hjm : j = m + 1
    · subst hjm; simp
    · have hj_le : j ≤ m := Nat.le_of_lt_succ (lt_of_le_of_ne hjℓ hjm)
      rw [P.ancestorAt_succ hj_le, seeds.parentNode_nodeAt hℓ, ih hj_le (by omega)]

/-- Subset of `S : Finset (Fin P.paddedUniv)` routed to node `u` at level `ℓ`. -/
@[expose]
noncomputable def activeAt (seeds : P.SeedAssignment) (S : Finset (Fin P.paddedUniv)) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) : Finset (Fin P.paddedUniv) :=
  S.filter fun x => seeds.nodeAt ℓ hℓ x = u

@[simp]
theorem mem_activeAt_iff {seeds : P.SeedAssignment} {S : Finset (Fin P.paddedUniv)} {ℓ : ℕ}
    {hℓ : ℓ ≤ P.depth} {u : Fin (P.numNodes ℓ)} {x : Fin P.paddedUniv} :
    x ∈ seeds.activeAt S ℓ hℓ u ↔ x ∈ S ∧ seeds.nodeAt ℓ hℓ x = u :=
  mem_filter

theorem activeAt_subset_ancestor (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    {j ℓ : ℕ} (hjℓ : j ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    seeds.activeAt S ℓ hℓ u ⊆ seeds.activeAt S j (hjℓ.trans hℓ) (P.ancestorAt hjℓ u) := by
  intro x hx
  rcases mem_activeAt_iff.mp hx with ⟨hxS, hnode⟩
  exact mem_activeAt_iff.mpr ⟨hxS, by rw [← hnode, seeds.ancestorAt_nodeAt]⟩

theorem activeAt_zero (seeds : P.SeedAssignment) (S : Finset (Fin P.paddedUniv))
    (u₀ : Fin (P.numNodes 0)) :
    seeds.activeAt S 0 (Nat.zero_le _) u₀ = S := by
  ext x
  simp only [mem_activeAt_iff, and_iff_left_iff_imp]
  exact fun _ => Subsingleton.elim _ _

/-- Primitive-ID finset `S_prim` arriving at node `u` at level `ℓ` (`Section 5.5`). -/
@[expose]
noncomputable def primSetAt (seeds : P.SeedAssignment) (S : Finset (Fin P.paddedUniv)) (ℓ : ℕ)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) : Finset (P.PrimId ℓ) :=
  (seeds.activeAt S ℓ hℓ u).image fun x => (seeds.primCoordAt ℓ hℓ x).2

/-- **Ancestor-only dependence (`Section 5.5` crucial property for `Claim 5.4` & `Lemma 5.3`)**:
if two seed assignments `s₁, s₂` agree at all strict ancestors `(j, ancestorAt hj u)` (`j < ℓ`) of
`u`, then `s₁` and `s₂` route the exact same keys to `u` with the exact same primitive IDs. -/
theorem primCoordAt_congr_ancestors {s₁ s₂ : P.SeedAssignment} {ℓ : ℕ} (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ))
    (hanc : ∀ (j : ℕ) (hj : j < ℓ),
      s₁.seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u) =
        s₂.seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u))
    (x : Fin P.paddedUniv) :
    (s₁.nodeAt ℓ hℓ x = u ↔ s₂.nodeAt ℓ hℓ x = u) ∧
      (s₁.nodeAt ℓ hℓ x = u → s₁.primCoordAt ℓ hℓ x = s₂.primCoordAt ℓ hℓ x) := by
  induction ℓ with
  | zero =>
    exact ⟨⟨fun _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩, fun _ => rfl⟩
  | succ m ih =>
    let u_m := P.parentNode m u
    have hanc_m : ∀ (j : ℕ) (hj : j < m),
        s₁.seed j (hj.le.trans (by omega)) (P.ancestorAt hj.le u_m) =
          s₂.seed j (hj.le.trans (by omega)) (P.ancestorAt hj.le u_m) := fun j hj => by
      rw [← P.ancestorAt_succ hj.le u]; exact hanc j (Nat.lt_succ_of_lt hj)
    obtain ⟨hiff_m, heq_m⟩ := ih (by omega) u_m hanc_m
    have hseed_m : s₁.seed m (by omega) u_m = s₂.seed m (by omega) u_m := by
      have htr : u_m = P.ancestorAt (Nat.le_succ m) u := by
        rw [P.ancestorAt_succ le_rfl, P.ancestorAt_refl]
      rw [htr]; exact hanc m (Nat.lt_succ_self m)
    cases m with
    | zero =>
      have hp_eq : s₁.primCoordAt 1 hℓ x = s₂.primCoordAt 1 hℓ x :=
        primZeroToOneEquiv_congr _ (by rw [Subsingleton.elim (P.paddedToPrimZeroEquiv x).1 u_m,
          hseed_m])
      exact ⟨by dsimp only [nodeAt]; rw [hp_eq], fun _ => hp_eq⟩
    | succ k =>
      have hstep : ∀ (a b : P.SeedAssignment),
          a.nodeAt (k + 1) (by omega) x = u_m →
          a.primCoordAt (k + 1) (by omega) x = b.primCoordAt (k + 1) (by omega) x →
          a.seed (k + 1) (by omega) u_m = b.seed (k + 1) (by omega) u_m →
          a.primCoordAt (k + 2) hℓ x = b.primCoordAt (k + 2) hℓ x := by
        intro a b hna hpab hsab
        have hnb : b.nodeAt (k + 1) (by omega) x = u_m := by
          dsimp only [nodeAt] at hna ⊢; rw [← hpab, hna]
        have hid_ab : a.idAt (k + 1) (by omega) (by omega) x =
            b.idAt (k + 1) (by omega) (by omega) x := by
          rw [a.idAt_succ_eq_idCompressorHead (by omega) x,
            b.idAt_succ_eq_idCompressorHead (by omega) x, hna, hnb, hsab, hpab]
        have hc1_a := a.levelCoordEquiv_fst (by omega : 1 ≤ k + 1) (by omega) x
        have hc1_b := b.levelCoordEquiv_fst (by omega : 1 ≤ k + 1) (by omega) x
        change a.routeIdToPrimEquiv (by omega) (by omega)
            ((a.levelCoordEquiv (k + 1) (by omega) (by omega) x).1,
              a.idAt (k + 1) (by omega) (by omega) x) =
          b.routeIdToPrimEquiv (by omega) (by omega)
            ((b.levelCoordEquiv (k + 1) (by omega) (by omega) x).1,
              b.idAt (k + 1) (by omega) (by omega) x)
        rw [hc1_a, hc1_b, hna, hnb, hid_ab]
        exact routeIdToPrimEquiv_congr _ _ _ hsab
      refine ⟨⟨fun h1 => ?_, fun h2 => ?_⟩, fun h1 => ?_⟩
      · have hm1 : s₁.nodeAt (k + 1) (by omega) x = u_m := by
          rw [← s₁.parentNode_nodeAt hℓ x, h1]
        exact congrArg Prod.fst (hstep s₁ s₂ hm1 (heq_m hm1) hseed_m).symm |>.trans h1
      · have hm2 : s₂.nodeAt (k + 1) (by omega) x = u_m := by
          rw [← s₂.parentNode_nodeAt hℓ x, h2]
        have hm1 := hiff_m.mpr hm2
        exact congrArg Prod.fst (hstep s₁ s₂ hm1 (heq_m hm1) hseed_m) |>.trans h2
      · have hm1 : s₁.nodeAt (k + 1) (by omega) x = u_m := by
          rw [← s₁.parentNode_nodeAt hℓ x, h1]
        exact hstep s₁ s₂ hm1 (heq_m hm1) hseed_m

theorem primSetAt_congr_ancestors {s₁ s₂ : P.SeedAssignment} (S : Finset (Fin P.paddedUniv))
    {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hanc : ∀ (j : ℕ) (hj : j < ℓ),
      s₁.seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u) =
        s₂.seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u)) :
    s₁.primSetAt S ℓ hℓ u = s₂.primSetAt S ℓ hℓ u := by
  have hact : s₁.activeAt S ℓ hℓ u = s₂.activeAt S ℓ hℓ u := by
    ext x
    simp only [mem_activeAt_iff, (primCoordAt_congr_ancestors hℓ u hanc x).1]
  dsimp only [primSetAt]
  rw [hact]
  refine Finset.image_congr fun x hx => ?_
  have hnx : s₂.nodeAt ℓ hℓ x = u := (mem_activeAt_iff.mp hx).2
  have hn1 : s₁.nodeAt ℓ hℓ x = u := (primCoordAt_congr_ancestors hℓ u hanc x).1.mpr hnx
  exact congrArg Prod.snd ((primCoordAt_congr_ancestors hℓ u hanc x).2 hn1)

/-- Level-`ℓ` coordinate congruence when `s₁, s₂` agree along `(0 .. ℓ)` of `u`'s path. -/
theorem levelCoordEquiv_congr_ancestors {s₁ s₂ : P.SeedAssignment} {ℓ : ℕ} (h1 : 1 ≤ ℓ)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (hanc : ∀ (j : ℕ) (hj : j ≤ ℓ),
      s₁.seed j (hj.trans hℓ) (P.ancestorAt hj u) =
        s₂.seed j (hj.trans hℓ) (P.ancestorAt hj u))
    (x : Fin P.paddedUniv) (hnx : s₁.nodeAt ℓ hℓ x = u) :
    s₁.levelCoordEquiv ℓ h1 hℓ x = s₂.levelCoordEquiv ℓ h1 hℓ x := by
  induction ℓ with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      have hprim := (primCoordAt_congr_ancestors hℓ u (fun j hj => hanc j hj.le) x).2 hnx
      have hs1 : s₁.seed 1 hℓ u = s₂.seed 1 hℓ u := by simpa using hanc 1 le_rfl
      have hn2 : s₂.nodeAt 1 hℓ x = u := by
        dsimp only [nodeAt] at hnx ⊢; rw [← hprim, hnx]
      simp only [levelCoordEquiv, levelOneCoordEquiv, primOneToCoordOneEquiv, Equiv.trans_apply]
      change (s₁.nodeAt 1 hℓ x, FeistelPerm.idCompressorPerm (P.idBits 1) (P.idCompRightUniv 1)
          (P.idSeedOfNodeSeed (s₁.seed 1 hℓ (s₁.nodeAt 1 hℓ x))) (s₁.primCoordAt 1 hℓ x).2) =
        (s₂.nodeAt 1 hℓ x, FeistelPerm.idCompressorPerm (P.idBits 1) (P.idCompRightUniv 1)
          (P.idSeedOfNodeSeed (s₂.seed 1 hℓ (s₂.nodeAt 1 hℓ x))) (s₂.primCoordAt 1 hℓ x).2)
      rw [hnx, hn2, hs1, hprim]
    | succ k =>
      have hm_lt : k + 1 < P.depth := by omega
      let u_m := P.parentNode (k + 1) u
      have hanc_m : ∀ (j : ℕ) (hj : j ≤ k + 1),
          s₁.seed j (hj.trans hm_lt.le) (P.ancestorAt hj u_m) =
            s₂.seed j (hj.trans hm_lt.le) (P.ancestorAt hj u_m) := fun j hj => by
        rw [(P.ancestorAt_succ hj u).symm]; exact hanc j (Nat.le_succ_of_le hj)
      have hnx_m : s₁.nodeAt (k + 1) hm_lt.le x = u_m := by
        rw [← s₁.parentNode_nodeAt hℓ x, hnx]
      have heq_m := ih (by omega) hm_lt.le u_m hanc_m hnx_m
      have hprim := (primCoordAt_congr_ancestors hℓ u (fun j hj => hanc j hj.le) x).2 hnx
      have hn2 : s₂.nodeAt (k + 2) hℓ x = u :=
        (primCoordAt_congr_ancestors hℓ u (fun j hj => hanc j hj.le) x).1.mp hnx
      have hs_cur : s₁.seed (k + 2) hℓ u = s₂.seed (k + 2) hℓ u := by
        simpa using hanc (k + 2) le_rfl
      change ((s₁.levelCoordEquiv (k + 1) (by omega) hm_lt.le).trans
          (s₁.stepCoordEquiv (by omega) hm_lt)) x =
        ((s₂.levelCoordEquiv (k + 1) (by omega) hm_lt.le).trans
          (s₂.stepCoordEquiv (by omega) hm_lt)) x
      simp only [Equiv.trans_apply, stepCoordEquiv_apply]
      have hqm : (s₁.levelCoordEquiv (k + 1) (by omega) hm_lt.le x).2.2 =
          (s₂.levelCoordEquiv (k + 1) (by omega) hm_lt.le x).2.2 := by rw [heq_m]
      change (let ir := s₁.primSuccToIdRemEquiv (by omega) hm_lt (s₁.primCoordAt (k + 2) hℓ x);
          (ir.1, ir.2.1, quotMergeEquiv (by omega)
            ((s₁.levelCoordEquiv (k + 1) (by omega) hm_lt.le x).2.2, ir.2.2))) =
        (let ir := s₂.primSuccToIdRemEquiv (by omega) hm_lt (s₂.primCoordAt (k + 2) hℓ x);
          (ir.1, ir.2.1, quotMergeEquiv (by omega)
            ((s₂.levelCoordEquiv (k + 1) (by omega) hm_lt.le x).2.2, ir.2.2)))
      rw [hqm]
      unfold primSuccToIdRemEquiv
      simp only [Equiv.trans_apply, fiberPermEquiv_apply, Equiv.prodCongr_apply, Prod.map_fst,
        Prod.map_snd, Equiv.refl_apply]
      have hp1 : (s₁.primCoordAt (k + 2) hℓ x).1 = u := hnx
      have hp2 : (s₂.primCoordAt (k + 2) hℓ x).1 = u := hn2
      rw [hp1, hp2, hs_cur, hprim]

/-- Global seed-goodness invariant on an active padded set `S`: `#S ∈ [nLow 0, nHigh 0]` and
every node `(ℓ, u)` (`0 ≤ ℓ ≤ depth`) satisfies `IsGoodNodeSeed` on `primSetAt S ℓ hℓ u`. -/
@[expose]
def AllGoodSeeds (seeds : P.SeedAssignment) (S : Finset (Fin P.paddedUniv)) : Prop :=
  (P.nLow 0 ≤ #S ∧ #S ≤ P.nHigh 0) ∧
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
      P.IsGoodNodeSeed ℓ (seeds.seed ℓ hℓ u) (seeds.primSetAt S ℓ hℓ u)

/-- Ancestor-local routing invariants at `(ℓ, u)`: whenever `#S ∈ [nLow 0, nHigh 0]` and every
strict ancestor `j < ℓ` of `u` satisfies `IsGoodNodeSeed`, `(primCoordAt ℓ hℓ ·).2` is injective on
`activeAt S ℓ hℓ u`, `nLow ℓ ≤ #(activeAt S ℓ hℓ u) ≤ nHigh ℓ`, and (if `u`'s seed is good) `idAt ℓ`
is injective on `activeAt S ℓ hℓ u`. -/
theorem ancestorsGood_invariants (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hcard0 : P.nLow 0 ≤ #S ∧ #S ≤ P.nHigh 0) :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
      (∀ (j : ℕ) (hj : j < ℓ),
        P.IsGoodNodeSeed j (seeds.seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u))
          (seeds.primSetAt S j (hj.le.trans hℓ) (P.ancestorAt hj.le u))) →
      Set.InjOn (fun x => (seeds.primCoordAt ℓ hℓ x).2) (seeds.activeAt S ℓ hℓ u) ∧
      (P.nLow ℓ ≤ #(seeds.activeAt S ℓ hℓ u) ∧ #(seeds.activeAt S ℓ hℓ u) ≤ P.nHigh ℓ) ∧
      (P.IsGoodNodeSeed ℓ (seeds.seed ℓ hℓ u) (seeds.primSetAt S ℓ hℓ u) →
        ∀ h1 : 1 ≤ ℓ, Set.InjOn (seeds.idAt ℓ h1 hℓ) (seeds.activeAt S ℓ hℓ u)) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro hℓ u₀ _
    have hinj0 : Set.InjOn (fun x => (seeds.primCoordAt 0 hℓ x).2) (seeds.activeAt S 0 hℓ u₀) :=
      fun x _ y _ hxy => P.paddedToPrimZeroEquiv.injective (Prod.ext (Subsingleton.elim _ _) hxy)
    exact ⟨hinj0, by rw [seeds.activeAt_zero S u₀]; exact hcard0, fun _ h1 => False.elim (by omega)⟩
  | succ m ih =>
    intro hℓ u_next hanc
    let u_m := P.parentNode m u_next
    let b_m := P.childBranch m u_next
    have hanc_m : ∀ (j : ℕ) (hj : j < m),
        P.IsGoodNodeSeed j (seeds.seed j (hj.le.trans (by omega)) (P.ancestorAt hj.le u_m))
          (seeds.primSetAt S j (hj.le.trans (by omega)) (P.ancestorAt hj.le u_m)) := fun j hj => by
      have heq : P.ancestorAt hj.le u_m = P.ancestorAt (Nat.le_succ_of_le hj.le) u_next :=
        (P.ancestorAt_succ hj.le u_next).symm
      rw [heq]; exact hanc j (Nat.lt_succ_of_lt hj)
    have hgm : P.IsGoodNodeSeed m (seeds.seed m (by omega) u_m)
        (seeds.primSetAt S m (by omega) u_m) := by
      have heq : u_m = P.ancestorAt (Nat.le_succ m) u_next := by
        rw [P.ancestorAt_succ le_rfl, P.ancestorAt_refl]
      rw [heq]; exact hanc m (Nat.lt_succ_self m)
    obtain ⟨_, _, hinj_id_m_imp⟩ := ih (by omega) u_m hanc_m
    have hinj_id_m_opt := hinj_id_m_imp hgm
    cases m with
    | zero =>
      have hinj1 : Set.InjOn (fun x => (seeds.primCoordAt 1 hℓ x).2)
          (seeds.activeAt S 1 hℓ u_next) := by
        intro x hx y hy hxy
        have hnx : (seeds.primCoordAt 1 hℓ x).1 = u_next := (mem_activeAt_iff.mp hx).2
        have hny : (seeds.primCoordAt 1 hℓ y).1 = u_next := (mem_activeAt_iff.mp hy).2
        exact (P.paddedToPrimZeroEquiv.trans seeds.primZeroToOneEquiv).injective
          (Prod.ext (hnx.trans hny.symm) hxy)
      have hg0 := hgm
      rcases hs0 : seeds.seed 0 (Nat.zero_le _) u_m with ⟨r₀⟩
      rw [hs0] at hg0
      dsimp only [IsGoodNodeSeed] at hg0
      have hbl_bounds := hg0 b_m
      have hcard_eq : #(seeds.activeAt S 1 hℓ u_next) =
          FeistelPerm.bucketLoad (P.routerRound 0 r₀)
            (seeds.primSetAt S 0 (Nat.zero_le _) u_m) b_m := by
        let f0 : Fin P.paddedUniv → P.PrimId 0 := fun x => (seeds.primCoordAt 0 (Nat.zero_le _) x).2
        have hf0_inj : Set.InjOn f0 (seeds.activeAt S 0 (Nat.zero_le _) u_m) := fun x _ y _ hxy =>
          P.paddedToPrimZeroEquiv.injective (Prod.ext (Subsingleton.elim _ _) hxy)
        have hset0 : seeds.activeAt S 1 hℓ u_next =
            (seeds.activeAt S 0 (Nat.zero_le _) u_m).filter fun x =>
              FeistelPerm.feistelHead (P.routerRound 0 r₀) (f0 x) = b_m := by
          ext x
          simp only [mem_filter, mem_activeAt_iff]
          have hu0x : seeds.nodeAt 0 (Nat.zero_le _) x = u_m := Subsingleton.elim _ _
          have hp0 : (P.paddedToPrimZeroEquiv x).1 = u_m := Subsingleton.elim _ _
          constructor
          · rintro ⟨hxS, hnode1⟩
            refine ⟨⟨hxS, hu0x⟩, ?_⟩
            have hb : P.childBranch 0 (seeds.nodeAt 1 hℓ x) = b_m :=
              congrArg (P.childBranch 0) hnode1
            change P.childBranch 0 (seeds.primZeroToOneEquiv (P.paddedToPrimZeroEquiv x)).1 = b_m
              at hb
            rw [seeds.primZeroToOneEquiv_fst, P.childBranch_childNodeEquiv, hp0, hs0] at hb
            exact hb
          · rintro ⟨⟨hxS, _⟩, hhead⟩
            refine ⟨hxS, ?_⟩
            change (seeds.primZeroToOneEquiv (P.paddedToPrimZeroEquiv x)).1 = u_next
            rw [seeds.primZeroToOneEquiv_fst, hp0, hs0]
            change P.childNodeEquiv 0
              (u_m, FeistelPerm.feistelHead (P.routerRound 0 r₀) (f0 x)) = u_next
            rw [hhead, P.childNodeEquiv_parent_branch]
        rw [hset0, ← card_image_of_injOn (hf0_inj.mono (filter_subset _ _))]
        dsimp only [FeistelPerm.bucketLoad, primSetAt]
        rw [Finset.filter_image]
      refine ⟨hinj1, hcard_eq ▸ hbl_bounds, fun hg1 _ => ?_⟩
      have hhead_inj : Set.InjOn
          (FeistelPerm.idCompressorHead (P.idBits 1) (P.idCompRightUniv 1)
            (P.idSeedOfNodeSeed (seeds.seed 1 hℓ u_next)))
          (seeds.primSetAt S 1 hℓ u_next : Set (P.PrimId 1)) := by
        rcases hs1 : seeds.seed 1 hℓ u_next with _ | ⟨_, idS, _⟩ | ⟨_, idS⟩
        · rw [hs1] at hg1; exact hg1.1
        · rw [hs1] at hg1; exact hg1
      intro x hx y hy hxy
      have hnx : seeds.nodeAt 1 hℓ x = u_next := (mem_activeAt_iff.mp hx).2
      have hny : seeds.nodeAt 1 hℓ y = u_next := (mem_activeAt_iff.mp hy).2
      rw [seeds.idAt_succ_eq_idCompressorHead hℓ x, seeds.idAt_succ_eq_idCompressorHead hℓ y,
        hnx, hny] at hxy
      exact hinj1 hx hy (hhead_inj (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy)
    | succ k =>
      have h1_m : 1 ≤ k + 1 := by omega
      have hlt_m : k + 1 < P.depth := by omega
      have hinj_id_m := hinj_id_m_opt h1_m
      have hinj_prim_next : Set.InjOn (fun x => (seeds.primCoordAt (k + 2) hℓ x).2)
          (seeds.activeAt S (k + 2) hℓ u_next) := by
        intro x hx y hy hxy
        have hnx : (seeds.primCoordAt (k + 2) hℓ x).1 = u_next := (mem_activeAt_iff.mp hx).2
        have hny : (seeds.primCoordAt (k + 2) hℓ y).1 = u_next := (mem_activeAt_iff.mp hy).2
        have heq_p : seeds.primCoordAt (k + 2) hℓ x = seeds.primCoordAt (k + 2) hℓ y :=
          Prod.ext (hnx.trans hny.symm) hxy
        have hanc_eq : P.ancestorAt (Nat.le_succ (k + 1)) u_next = u_m := by
          rw [P.ancestorAt_succ le_rfl, P.ancestorAt_refl]
        have hx_m : x ∈ seeds.activeAt S (k + 1) hlt_m.le u_m :=
          hanc_eq ▸ seeds.activeAt_subset_ancestor (Nat.le_succ (k + 1)) hℓ u_next hx
        have hy_m : y ∈ seeds.activeAt S (k + 1) hlt_m.le u_m :=
          hanc_eq ▸ seeds.activeAt_subset_ancestor (Nat.le_succ (k + 1)) hℓ u_next hy
        have hinj_route := (seeds.routeIdToPrimEquiv h1_m hlt_m).injective heq_p
        exact hinj_id_m hx_m hy_m (congrArg Prod.snd hinj_route)
      rcases hsm : seeds.seed (k + 1) hlt_m.le u_m with _ | ⟨_, idS_m, r_m⟩ | ⟨hge, _⟩
      · rw [hsm] at hgm
        dsimp only [IsGoodNodeSeed] at hgm
        have hsL : P.branchBits (k + 1) ≤ P.idBits (k + 1) := by
          have := P.idBits_step_le (k + 1) h1_m hlt_m; omega
        have hbl_bounds := hgm.2 b_m
        let f_emb : Fin P.paddedUniv →
            Fin (2 ^ P.branchBits (k + 1)) × Fin (P.routerRightUniv (k + 1)) :=
          fun x => FeistelPerm.bitDomainEquiv hsL (seeds.idAt (k + 1) h1_m hlt_m.le x)
        have hf_inj : Set.InjOn f_emb (seeds.activeAt S (k + 1) hlt_m.le u_m) := fun x hx y hy h =>
          hinj_id_m hx hy ((FeistelPerm.bitDomainEquiv hsL).injective h)
        let S_id := ((seeds.primSetAt S (k + 1) hlt_m.le u_m).image
          (FeistelPerm.idCompressorHead (P.idBits (k + 1)) (P.idCompRightUniv (k + 1))
            idS_m)).map
          (FeistelPerm.bitDomainEquiv (s := P.branchBits (k + 1)) (L := P.idBits (k + 1))
            hsL).toEmbedding
        have hSid_eq : S_id = (seeds.activeAt S (k + 1) hlt_m.le u_m).image f_emb := by
          simp only [S_id, primSetAt, Finset.map_eq_image, Finset.image_image]
          refine Finset.image_congr fun x hx => ?_
          have hnx : seeds.nodeAt (k + 1) hlt_m.le x = u_m := (mem_activeAt_iff.mp hx).2
          simp only [Function.comp_apply, Equiv.toEmbedding_apply, f_emb]
          rw [seeds.idAt_succ_eq_idCompressorHead hlt_m.le x, hnx, hsm]
          rfl
        have hcard_eq : #(seeds.activeAt S (k + 2) hℓ u_next) =
            FeistelPerm.bucketLoad (P.routerRound (k + 1) r_m) S_id b_m := by
          have hset_eq : (seeds.activeAt S (k + 2) hℓ u_next) =
              (seeds.activeAt S (k + 1) hlt_m.le u_m).filter fun x =>
                FeistelPerm.feistelHead (P.routerRound (k + 1) r_m) (f_emb x) = b_m := by
            ext x
            simp only [mem_activeAt_iff, mem_filter]
            have hc1 := seeds.levelCoordEquiv_fst h1_m hlt_m.le x
            constructor
            · rintro ⟨hxS, hnode2⟩
              have hpm : seeds.nodeAt (k + 1) hlt_m.le x = u_m := by
                rw [← seeds.parentNode_nodeAt hℓ x, hnode2]
              refine ⟨⟨hxS, hpm⟩, ?_⟩
              have hb : P.childBranch (k + 1) (seeds.nodeAt (k + 2) hℓ x) = b_m :=
                congrArg (P.childBranch (k + 1)) hnode2
              change P.childBranch (k + 1)
                (seeds.routeIdToPrimEquiv h1_m hlt_m
                  ((seeds.levelCoordEquiv (k + 1) h1_m hlt_m.le x).1,
                    seeds.idAt (k + 1) h1_m hlt_m.le x)).1 = b_m at hb
              rw [seeds.routeIdToPrimEquiv_fst h1_m hlt_m hsL rfl, P.childBranch_childNodeEquiv,
                hc1, hpm, hsm] at hb
              exact hb
            · rintro ⟨⟨hxS, hpm⟩, hhead⟩
              refine ⟨hxS, ?_⟩
              change (seeds.routeIdToPrimEquiv h1_m hlt_m
                  ((seeds.levelCoordEquiv (k + 1) h1_m hlt_m.le x).1,
                    seeds.idAt (k + 1) h1_m hlt_m.le x)).1 = u_next
              rw [seeds.routeIdToPrimEquiv_fst h1_m hlt_m hsL rfl, hc1, hpm, hsm]
              change P.childNodeEquiv (k + 1)
                (u_m, FeistelPerm.feistelHead (P.routerRound (k + 1) r_m) (f_emb x)) = u_next
              rw [hhead, P.childNodeEquiv_parent_branch]
          rw [hset_eq, ← card_image_of_injOn (hf_inj.mono (filter_subset _ _))]
          dsimp only [FeistelPerm.bucketLoad]
          rw [hSid_eq, Finset.filter_image]
        refine ⟨hinj_prim_next, hcard_eq ▸ hbl_bounds, fun hg_next _ => ?_⟩
        have hhead_inj : Set.InjOn
            (FeistelPerm.idCompressorHead (P.idBits (k + 2)) (P.idCompRightUniv (k + 2))
              (P.idSeedOfNodeSeed (seeds.seed (k + 2) hℓ u_next)))
            (seeds.primSetAt S (k + 2) hℓ u_next : Set (P.PrimId (k + 2))) := by
          rcases hsn : seeds.seed (k + 2) hℓ u_next with _ | ⟨_, idSn, _⟩ | ⟨_, idSn⟩
          · rw [hsn] at hg_next; exact hg_next.1
          · rw [hsn] at hg_next; exact hg_next
        intro x hx y hy hxy
        have hnx : seeds.nodeAt (k + 2) hℓ x = u_next := (mem_activeAt_iff.mp hx).2
        have hny : seeds.nodeAt (k + 2) hℓ y = u_next := (mem_activeAt_iff.mp hy).2
        rw [seeds.idAt_succ_eq_idCompressorHead hℓ x, seeds.idAt_succ_eq_idCompressorHead hℓ y,
          hnx, hny] at hxy
        exact hinj_prim_next hx hy
          (hhead_inj (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) hxy)
      · exact False.elim (hge hlt_m)

theorem allGoodSeeds_invariants (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hgood : seeds.AllGoodSeeds S) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    Set.InjOn (fun x => (seeds.primCoordAt ℓ hℓ x).2) (seeds.activeAt S ℓ hℓ u) ∧
    (P.nLow ℓ ≤ #(seeds.activeAt S ℓ hℓ u) ∧ #(seeds.activeAt S ℓ hℓ u) ≤ P.nHigh ℓ) ∧
    (∀ h1 : 1 ≤ ℓ, Set.InjOn (seeds.idAt ℓ h1 hℓ) (seeds.activeAt S ℓ hℓ u)) :=
  let ⟨h1, h2, h3⟩ := seeds.ancestorsGood_invariants hgood.1 ℓ hℓ u
    fun j hj => hgood.2 j (hj.le.trans hℓ) (P.ancestorAt hj.le u)
  ⟨h1, h2, h3 (hgood.2 ℓ hℓ u)⟩

theorem card_primSetAt_eq (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hgood : seeds.AllGoodSeeds S) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    #(seeds.primSetAt S ℓ hℓ u) = #(seeds.activeAt S ℓ hℓ u) :=
  card_image_of_injOn (seeds.allGoodSeeds_invariants hgood ℓ hℓ u).1

theorem load_bounds_of_allGoodSeeds (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hgood : seeds.AllGoodSeeds S) {ℓ : ℕ} (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    P.nLow ℓ ≤ #(seeds.activeAt S ℓ hℓ u) ∧ #(seeds.activeAt S ℓ hℓ u) ≤ P.nHigh ℓ :=
  (seeds.allGoodSeeds_invariants hgood ℓ hℓ u).2.1

theorem injOn_idAt_activeAt (seeds : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hgood : seeds.AllGoodSeeds S) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) :
    Set.InjOn (seeds.idAt ℓ h1 hℓ) (seeds.activeAt S ℓ hℓ u) :=
  (seeds.allGoodSeeds_invariants hgood ℓ hℓ u).2.2 h1

end SeedAssignment

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
