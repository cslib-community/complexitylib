/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.StorageNode
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeRouting

/-!
# Multi-Level Dictionary Tree State, Section 5.6 Metadata, and Subtree Capacity Laws

This file defines the pure multi-level state `TreeState`, uniform node accessors, Section 5.6 DFS
subtree metadata extraction, the `WellFormedPadded` / `WellFormed` representation invariants, and
exact subtree/waiting-list/root capacity laws for the subconstant-redundancy dictionary tree of
Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant
Wasted Bits per Key* ([LiLiangYuZhou2024, Sections 5.2 and 5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 27–30 and 35–36 /
printed pp. 26–29 and 34–35).

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.takeFinset`: canonical `m`-element prefix
  subset of a `Finset` in `LinearOrder`.
* `LeafNode.dom`, `LeafNode.query`, `LeafNode.ofFinset`, `LeafNode.overwrite`, `LeafNode.replace`:
  typed `(quot, val)` interface over `Minimap.FixedEncoded`.
* `TreeSchedule.TreeState`: multi-level forest state with Section 5.6 `dfsSubtreeMeta` projection.
* `TreeSchedule.TreeState.WellFormedPadded`, `TreeSchedule.TreeState.WellFormed`: multi-level seed,
  capacity, storage-level partition, and waiting-list invariants.

## Main results

* `TreeSchedule.TreeState.subtree_stored_card_eq_nLow`: every level-`ℓ` (`2 ≤ ℓ ≤ depth`) subtree
  stores `nLow ℓ` keys in total.
* `TreeSchedule.TreeState.card_nodeWait_dom_eq`, `TreeSchedule.TreeState.card_root_dom_add_eq`,
  `TreeSchedule.TreeState.rootKeyCount_le_rootValPoolCap`: exact waiting-list and root-pool
  capacity conservation laws.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

/-- Canonical `m`-element prefix subset of `A : Finset α` when `m ≤ #A`. -/
noncomputable def takeFinset {α : Type*} [LinearOrder α] (A : Finset α) (m : ℕ) (hm : m ≤ #A) :
    Finset α :=
  (Finset.range m).attach.map
    ⟨fun (i : { x : ℕ // x ∈ Finset.range m }) =>
        (A.orderEmbOfFin rfl) ⟨i.1, (Finset.mem_range.mp i.2).trans_le hm⟩,
      fun _ _ h => Subtype.ext (congrArg Fin.val ((A.orderEmbOfFin rfl).injective h))⟩

theorem takeFinset_subset {α : Type*} [LinearOrder α] (A : Finset α) (m : ℕ) (hm : m ≤ #A) :
    takeFinset A m hm ⊆ A := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := mem_map.mp hx
  exact A.orderEmbOfFin_mem rfl _

@[simp]
theorem card_takeFinset {α : Type*} [LinearOrder α] (A : Finset α) (m : ℕ) (hm : m ≤ #A) :
    #(takeFinset A m hm) = m := by
  simp [takeFinset, card_map, card_attach, Finset.card_range]

namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Typed `(quot, val)` interface on `LeafNode` -/

/-- Active `I_depth`-bit ID set stored in a fixed-capacity `LeafNode`. -/
abbrev LeafNode.dom {P : TreeSchedule} (ln : P.LeafNode) : Finset (Fin (2 ^ P.idBits P.depth)) :=
  Minimap.activeSet ln.toFixedEncoded

theorem LeafNode.card_dom {P : TreeSchedule} (ln : P.LeafNode) :
    ln.dom.card = P.nLow P.depth :=
  Minimap.card_activeSet ln.toFixedEncoded

/-- Look up `(quot, val)` of `k` in a `LeafNode` using `scheme`. -/
@[expose]
def LeafNode.query {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode) (k : Fin (2 ^ P.idBits P.depth)) :
    Option (Fin (P.quotUniv P.depth) × Fin P.valBound) :=
  (Minimap.queryFin scheme ln.toFixedEncoded k).map finProdFinEquiv.symm

theorem LeafNode.query_eq_none_of_notMem {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode) {k : Fin (2 ^ P.idBits P.depth)} (hk : k ∉ ln.dom) :
    ln.query scheme k = none := by
  dsimp only [LeafNode.query]
  rw [Minimap.queryFin_of_notMem scheme ln.toFixedEncoded hk]
  rfl

private theorem option_map_val_inj {X : ℕ} {o₁ o₂ : Option (Fin X)}
    (h : o₁.map Fin.val = o₂.map Fin.val) : o₁ = o₂ := by
  rcases o₁ with _ | a <;> rcases o₂ with _ | b
  · rfl
  · simp at h
  · simp at h
  · simp only [Option.map_some, Option.some.injEq] at h
    exact congrArg some (Fin.ext h)

private theorem leafOfFinset_valuesBounded {P : TreeSchedule}
    (S : Finset (Fin (2 ^ P.idBits P.depth)))
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) :
    Dictionary.ValuesBounded (P.quotUniv P.depth * P.valBound)
      (fun k => if k ∈ S then some (finProdFinEquiv (f k)).val else none) := by
  intro k v hkv
  dsimp only at hkv
  split_ifs at hkv with hk
  exact (Option.some.inj hkv) ▸ (finProdFinEquiv (f k)).isLt

private theorem leafOfFinset_card_dom {P : TreeSchedule}
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) :
    (Dictionary.dom (fun k => if k ∈ S then some (finProdFinEquiv (f k)).val else none)).card =
      P.nLow P.depth := by
  have hd : Dictionary.dom (fun k =>
      if k ∈ S then some (finProdFinEquiv (f k)).val else none) = S := by
    ext k; by_cases hk : k ∈ S <;> simp [Dictionary.dom, hk]
  exact hd.symm ▸ hS

/-- Bulk-encode a `LeafNode` from an exact `nLow depth`-subset `S` and payload map `f`. -/
def LeafNode.ofFinset {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) : P.LeafNode :=
  LeafNode.ofFixedEncoded P seed wait
    (Minimap.encode le_rfl scheme
      (fun k => if k ∈ S then some (finProdFinEquiv (f k)).val else none)
      (leafOfFinset_valuesBounded S f) (leafOfFinset_card_dom S hS f))

@[simp]
private theorem toFixedEncoded_ofFixedEncoded {P : TreeSchedule} (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (enc : Minimap.FixedEncoded (2 ^ P.idBits P.depth) (P.nLow P.depth)
      (P.quotUniv P.depth * P.valBound)) :
    (LeafNode.ofFixedEncoded P seed wait enc).toFixedEncoded = enc := by
  cases enc; rfl

@[simp]
theorem LeafNode.seed_ofFinset {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) :
    (LeafNode.ofFinset scheme seed wait S hS f).leafMeta.seed = seed := by
  rfl

@[simp]
theorem LeafNode.wait_ofFinset {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) :
    (LeafNode.ofFinset scheme seed wait S hS f).leafMeta.wait = wait := by
  rfl

@[simp]
theorem LeafNode.dom_ofFinset {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound) :
    (LeafNode.ofFinset scheme seed wait S hS f).dom = S := by
  unfold LeafNode.dom LeafNode.ofFinset
  rw [toFixedEncoded_ofFixedEncoded, Minimap.activeSet_encode]
  ext k; by_cases hk : k ∈ S <;> simp [Dictionary.dom, hk]

@[simp]
theorem LeafNode.query_ofFinset {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (S : Finset (Fin (2 ^ P.idBits P.depth))) (hS : S.card = P.nLow P.depth)
    (f : Fin (2 ^ P.idBits P.depth) → Fin (P.quotUniv P.depth) × Fin P.valBound)
    (k : Fin (2 ^ P.idBits P.depth)) :
    (LeafNode.ofFinset scheme seed wait S hS f).query scheme k =
      if k ∈ S then some (f k) else none := by
  have hfin : Minimap.queryFin scheme (LeafNode.ofFinset scheme seed wait S hS f).toFixedEncoded k =
      if k ∈ S then some (finProdFinEquiv (f k)) else none := by
    apply option_map_val_inj
    unfold LeafNode.ofFinset
    rw [toFixedEncoded_ofFixedEncoded]
    change Minimap.query scheme _ k = _
    rw [Minimap.query_encode]
    by_cases hk : k ∈ S <;> simp [hk]
  dsimp only [LeafNode.query]
  rw [hfin]
  by_cases hk : k ∈ S <;> simp [hk]

/-- Overwrite `(quot, val)` of an active key `k ∈ ln.dom` in place (`LeafNode`). -/
@[expose]
def LeafNode.overwrite {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode) (k : Fin (2 ^ P.idBits P.depth))
    (qv : Fin (P.quotUniv P.depth) × Fin P.valBound) (hk : k ∈ ln.dom) : P.LeafNode :=
  let packed := finProdFinEquiv qv
  LeafNode.ofFixedEncoded P ln.leafMeta.seed ln.leafMeta.wait
    (Minimap.overwrite le_rfl scheme ln.toFixedEncoded k packed.val packed.isLt hk)

@[simp]
theorem LeafNode.dom_overwrite {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode) (k : Fin (2 ^ P.idBits P.depth))
    (qv : Fin (P.quotUniv P.depth) × Fin P.valBound) (hk : k ∈ ln.dom) :
    (ln.overwrite scheme k qv hk).dom = ln.dom := by
  unfold LeafNode.dom LeafNode.overwrite
  rw [toFixedEncoded_ofFixedEncoded]
  exact Minimap.activeSet_overwrite le_rfl scheme ln.toFixedEncoded k _ _ hk

@[simp]
theorem LeafNode.query_overwrite {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode) (k : Fin (2 ^ P.idBits P.depth))
    (qv : Fin (P.quotUniv P.depth) × Fin P.valBound) (hk : k ∈ ln.dom)
    (k' : Fin (2 ^ P.idBits P.depth)) :
    (ln.overwrite scheme k qv hk).query scheme k' =
      Function.update (ln.query scheme) k (some qv) k' := by
  let packed := finProdFinEquiv qv
  have hfin : Minimap.queryFin scheme (ln.overwrite scheme k qv hk).toFixedEncoded k' =
      Function.update (Minimap.queryFin scheme ln.toFixedEncoded) k (some packed) k' := by
    apply option_map_val_inj
    unfold LeafNode.overwrite
    rw [toFixedEncoded_ofFixedEncoded]
    change Minimap.query scheme _ k' = _
    rw [Minimap.query_overwrite]
    by_cases heq : k' = k <;> simp [heq, Minimap.query, packed]
  unfold LeafNode.query
  rw [hfin]
  by_cases heq : k' = k <;> simp [heq, packed]

/-- Replace `k_old ∈ ln.dom` with `(k_new, qv_new)` (`Algorithm 3` Branch 2 at a leaf) while
simultaneously updating the leaf's waiting list to `wait'`. -/
@[expose]
def LeafNode.replace {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode)
    (wait' : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (k_old k_new : Fin (2 ^ P.idBits P.depth))
    (qv_new : Fin (P.quotUniv P.depth) × Fin P.valBound)
    (hold : k_old ∈ ln.dom) (hnew : k_new ∉ ln.dom.erase k_old) : P.LeafNode :=
  let packed := finProdFinEquiv qv_new
  LeafNode.ofFixedEncoded P ln.leafMeta.seed wait'
    (Minimap.replace scheme ln.toFixedEncoded k_old k_new packed.val packed.isLt hold hnew)

@[simp]
theorem LeafNode.dom_replace {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode)
    (wait' : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (k_old k_new : Fin (2 ^ P.idBits P.depth))
    (qv_new : Fin (P.quotUniv P.depth) × Fin P.valBound)
    (hold : k_old ∈ ln.dom) (hnew : k_new ∉ ln.dom.erase k_old) :
    (ln.replace scheme wait' k_old k_new qv_new hold hnew).dom =
      Insert.insert k_new (ln.dom.erase k_old) := by
  unfold LeafNode.dom LeafNode.replace
  rw [toFixedEncoded_ofFixedEncoded]
  exact Minimap.activeSet_replace scheme ln.toFixedEncoded k_old k_new _ _ hold hnew

@[simp]
theorem LeafNode.query_replace {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ln : P.LeafNode)
    (wait' : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (k_old k_new : Fin (2 ^ P.idBits P.depth))
    (qv_new : Fin (P.quotUniv P.depth) × Fin P.valBound)
    (hold : k_old ∈ ln.dom) (hnew : k_new ∉ ln.dom.erase k_old)
    (k' : Fin (2 ^ P.idBits P.depth)) :
    (ln.replace scheme wait' k_old k_new qv_new hold hnew).query scheme k' =
      Function.update (Function.update (ln.query scheme) k_old none) k_new (some qv_new) k' := by
  let packed := finProdFinEquiv qv_new
  have hfin : Minimap.queryFin scheme
      (ln.replace scheme wait' k_old k_new qv_new hold hnew).toFixedEncoded k' =
      Function.update
        (Function.update (Minimap.queryFin scheme ln.toFixedEncoded) k_old none)
        k_new (some packed) k' := by
    apply option_map_val_inj
    unfold LeafNode.replace
    rw [toFixedEncoded_ofFixedEncoded]
    change Minimap.query scheme _ k' = _
    rw [Minimap.query_replace]
    by_cases hn : k' = k_new
    · subst hn; simp [packed]
    · by_cases ho : k' = k_old
      · subst ho; simp [hn]
      · simp [hn, ho, Minimap.query]
  unfold LeafNode.query
  rw [hfin]
  by_cases hn : k' = k_new
  · subst hn; simp [packed]
  · by_cases ho : k' = k_old
    · subst ho; simp [hn]
    · simp [hn, ho]

/-! ## Section 2: `TreeState`, uniform node accessors, and Section 5.6 subtree metadata -/

/-- Pure multi-level forest state of the Section 5 subconstant-redundancy dictionary tree. -/
structure TreeState (P : TreeSchedule) where
  /-- Top-level (`ℓ = 0`) child-router seed `g_{r_0}`. -/
  topSeed : P.NodeSeed 0
  /-- Level-1 root nodes (`u ∈ Fin (N_1)`). -/
  roots : Fin (P.numNodes 1) → P.RootNode
  /-- Inner-level storage nodes (`2 ≤ ℓ < depth`, `u ∈ Fin (N_ℓ)`). -/
  inner : ∀ (ℓ : ℕ), 2 ≤ ℓ → ℓ < P.depth → Fin (P.numNodes ℓ) → P.InnerNode ℓ
  /-- Leaf minimap nodes (`ℓ = depth`, `u ∈ Fin (N_depth)`). -/
  leaves : Fin (P.numNodes P.depth) → P.LeafNode
  /-- Active sentinel padding count (`#(dom dict) + sentCount ∈ {cap - 1, cap}`). -/
  sentCount : ℕ

namespace TreeState

variable {P : TreeSchedule}

/-- Extract the full-forest `SeedAssignment` stored inside `st : P.TreeState`. -/
def seeds (st : P.TreeState) : P.SeedAssignment where
  seed ℓ hℓ u :=
    if h0 : ℓ = 0 then
      Eq.ndrec (motive := fun m => P.NodeSeed m) st.topSeed h0.symm
    else if h1 : ℓ = 1 then
      Eq.ndrec (motive := fun m => Fin (P.numNodes m) → P.NodeSeed m)
        (fun u' => (st.roots u').seed) h1.symm u
    else if hlt : ℓ < P.depth then
      (st.inner ℓ (by omega) hlt u).seed
    else
      have hd : ℓ = P.depth := by omega
      Eq.ndrec (motive := fun m => Fin (P.numNodes m) → P.NodeSeed m)
        (fun u' => (st.leaves u').leafMeta.seed) hd.symm u

@[simp]
theorem seeds_zero (st : P.TreeState) (hℓ : 0 ≤ P.depth) (u : Fin (P.numNodes 0)) :
    st.seeds.seed 0 hℓ u = st.topSeed := by
  simp [seeds]

@[simp]
theorem seeds_one (st : P.TreeState) (hℓ : 1 ≤ P.depth) (u : Fin (P.numNodes 1)) :
    st.seeds.seed 1 hℓ u = (st.roots u).seed := by
  dsimp only [seeds]
  rw [dite_eq_right (by omega), dite_eq_left rfl]

@[simp]
theorem seeds_inner (st : P.TreeState) {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    st.seeds.seed ℓ hℓ u = (st.inner ℓ h2 hlt u).seed := by
  dsimp only [seeds]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left hlt]

@[simp]
theorem seeds_depth (st : P.TreeState) (hℓ : P.depth ≤ P.depth)
    (u : Fin (P.numNodes P.depth)) :
    st.seeds.seed P.depth hℓ u = (st.leaves u).leafMeta.seed := by
  have h2 := P.two_le_depth
  dsimp only [seeds]
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (lt_irrefl _)]

/-- Active `I_ℓ`-bit ID domain stored directly at node `(ℓ, u)` (`1 ≤ ℓ ≤ depth`). -/
def nodeDom (st : P.TreeState) (ℓ : ℕ) (_h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) : Finset (Fin (2 ^ P.idBits ℓ)) :=
  if h_one : ℓ = 1 then
    Eq.ndrec (motive := fun m => Fin (P.numNodes m) → Finset (Fin (2 ^ P.idBits m)))
      (fun u' => (st.roots u').table.tableMeta.dom) h_one.symm u
  else if hlt : ℓ < P.depth then
    (st.inner ℓ (by omega) hlt u).table.tableMeta.dom
  else
    have hd : ℓ = P.depth := by omega
    Eq.ndrec (motive := fun m => Fin (P.numNodes m) → Finset (Fin (2 ^ P.idBits m)))
      (fun u' => (st.leaves u').dom) hd.symm u

@[simp]
theorem nodeDom_one (st : P.TreeState) (h1 : 1 ≤ 1) (hℓ : 1 ≤ P.depth)
    (u : Fin (P.numNodes 1)) :
    st.nodeDom 1 h1 hℓ u = (st.roots u).table.tableMeta.dom := by
  dsimp only [nodeDom]; rw [dite_eq_left rfl]

@[simp]
theorem nodeDom_inner (st : P.TreeState) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : 2 ≤ ℓ)
    (hlt : ℓ < P.depth) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    st.nodeDom ℓ h1 hℓ u = (st.inner ℓ h2 hlt u).table.tableMeta.dom := by
  dsimp only [nodeDom]; rw [dite_eq_right (by omega), dite_eq_left hlt]

@[simp]
theorem nodeDom_depth (st : P.TreeState) (h1 : 1 ≤ P.depth) (hℓ : P.depth ≤ P.depth)
    (u : Fin (P.numNodes P.depth)) :
    st.nodeDom P.depth h1 hℓ u = (st.leaves u).dom := by
  have h2 := P.two_le_depth
  dsimp only [nodeDom]; rw [dite_eq_right (by omega), dite_eq_right (lt_irrefl _)]

/-- Look up `(quot, val)` at node `(ℓ, u)` (`1 ≤ ℓ ≤ depth`) for compressed ID `k`. -/
def nodeQuery (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (ℓ : ℕ) (_h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) (k : Fin (2 ^ P.idBits ℓ)) :
    Option (Fin (P.quotUniv ℓ) × Fin P.valBound) :=
  if h_one : ℓ = 1 then
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Option (Fin (P.quotUniv m) × Fin P.valBound))
      (fun u' k' => (st.roots u').table.query k') h_one.symm u k
  else if hlt : ℓ < P.depth then
    (st.inner ℓ (by omega) hlt u).table.query k
  else
    have hd : ℓ = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) → Fin (2 ^ P.idBits m) →
        Option (Fin (P.quotUniv m) × Fin P.valBound))
      (fun u' k' => (st.leaves u').query scheme k') hd.symm u k

@[simp]
theorem nodeQuery_one (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (h1 : 1 ≤ 1) (hℓ : 1 ≤ P.depth) (u : Fin (P.numNodes 1))
    (k : Fin (2 ^ P.idBits 1)) :
    st.nodeQuery scheme 1 h1 hℓ u k = (st.roots u).table.query k := by
  dsimp only [nodeQuery]; rw [dite_eq_left rfl]

@[simp]
theorem nodeQuery_inner (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) (k : Fin (2 ^ P.idBits ℓ)) :
    st.nodeQuery scheme ℓ h1 hℓ u k = (st.inner ℓ h2 hlt u).table.query k := by
  dsimp only [nodeQuery]; rw [dite_eq_right (by omega), dite_eq_left hlt]

@[simp]
theorem nodeQuery_depth (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (h1 : 1 ≤ P.depth) (hℓ : P.depth ≤ P.depth)
    (u : Fin (P.numNodes P.depth)) (k : Fin (2 ^ P.idBits P.depth)) :
    st.nodeQuery scheme P.depth h1 hℓ u k = (st.leaves u).query scheme k := by
  have h2 := P.two_le_depth
  dsimp only [nodeQuery]; rw [dite_eq_right (by omega), dite_eq_right (lt_irrefl _)]

theorem nodeQuery_eq_none_of_notMem
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) {k : Fin (2 ^ P.idBits ℓ)} (hk : k ∉ st.nodeDom ℓ h1 hℓ u) :
    st.nodeQuery scheme ℓ h1 hℓ u k = none := by
  by_cases h_one : ℓ = 1
  · subst h_one
    rw [nodeDom_one] at hk
    rw [nodeQuery_one]
    exact Option.not_isSome_iff_eq_none.mp (mt ((st.roots u).table.isSome_query_iff k).mp hk)
  · by_cases hlt : ℓ < P.depth
    · have h2 : 2 ≤ ℓ := by omega
      rw [nodeDom_inner st h1 h2 hlt hℓ] at hk
      rw [nodeQuery_inner scheme st h1 h2 hlt hℓ]
      exact Option.not_isSome_iff_eq_none.mp
        (mt ((st.inner ℓ h2 hlt u).table.isSome_query_iff k).mp hk)
    · have hd : ℓ = P.depth := by omega
      subst hd
      rw [nodeDom_depth] at hk
      rw [nodeQuery_depth]
      exact LeafNode.query_eq_none_of_notMem scheme (st.leaves u) hk

/-- Waiting list at node `(ℓ, u)` (`2 ≤ ℓ ≤ depth`). -/
def nodeWait (st : P.TreeState) (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) : WaitingList (P.idBits ℓ) (P.idBits (ℓ - 1)) (P.waitCap ℓ) :=
  if hlt : ℓ < P.depth then
    (st.inner ℓ h2 hlt u).wait
  else
    have hd : ℓ = P.depth := by omega
    Eq.ndrec
      (motive := fun m => Fin (P.numNodes m) →
        WaitingList (P.idBits m) (P.idBits (m - 1)) (P.waitCap m))
      (fun u' => (st.leaves u').leafMeta.wait) hd.symm u

@[simp]
theorem nodeWait_inner (st : P.TreeState) {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth)
    (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    st.nodeWait ℓ h2 hℓ u = (st.inner ℓ h2 hlt u).wait := by
  dsimp only [nodeWait]; rw [dite_eq_left hlt]

@[simp]
theorem nodeWait_depth (st : P.TreeState) (h2 : 2 ≤ P.depth) (hℓ : P.depth ≤ P.depth)
    (u : Fin (P.numNodes P.depth)) :
    st.nodeWait P.depth h2 hℓ u = (st.leaves u).leafMeta.wait := by
  dsimp only [nodeWait]; rw [dite_eq_right (lt_irrefl _)]

/-- Update a single root node `u₀` in `st`. -/
@[expose]
def updateRoot (st : P.TreeState) (u₀ : Fin (P.numNodes 1)) (nd : P.RootNode) : P.TreeState :=
  { st with roots := Function.update st.roots u₀ nd }

/-- Update a single inner node `(ℓ₀, u₀)` (`2 ≤ ℓ₀ < depth`) in `st`. -/
@[expose]
def updateInner (st : P.TreeState) (ℓ₀ : ℕ) (h2₀ : 2 ≤ ℓ₀) (hlt₀ : ℓ₀ < P.depth)
    (u₀ : Fin (P.numNodes ℓ₀)) (nd : P.InnerNode ℓ₀) : P.TreeState :=
  { st with
    inner := fun ℓ h2 hlt u =>
      if hℓ : ℓ = ℓ₀ then
        Eq.ndrec (motive := fun m => Fin (P.numNodes m) → P.InnerNode m)
          (Function.update (st.inner ℓ₀ h2₀ hlt₀) u₀ nd) hℓ.symm u
      else st.inner ℓ h2 hlt u }

/-- Update a single leaf node `u₀` in `st`. -/
@[expose]
def updateLeaf (st : P.TreeState) (u₀ : Fin (P.numNodes P.depth)) (ln : P.LeafNode) :
    P.TreeState :=
  { st with leaves := Function.update st.leaves u₀ ln }

theorem seeds_updateRoot_of_seed_eq (st : P.TreeState) (u₀ : Fin (P.numNodes 1))
    (nd : P.RootNode) (hs : nd.seed = (st.roots u₀).seed) :
    (st.updateRoot u₀ nd).seeds = st.seeds := by
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0; simp [updateRoot]
  · by_cases h1 : ℓ = 1
    · subst h1
      simp only [seeds_one, updateRoot]
      by_cases hu : u = u₀
      · subst hu; simp [hs]
      · simp [hu]
    · by_cases hlt : ℓ < P.depth
      · simp [seeds_inner _ (by omega) hlt hℓ, updateRoot]
      · have hd : ℓ = P.depth := by omega
        subst hd; simp [updateRoot]

theorem seeds_updateInner_of_seed_eq (st : P.TreeState) {ℓ₀ : ℕ} (h2₀ : 2 ≤ ℓ₀)
    (hlt₀ : ℓ₀ < P.depth) (u₀ : Fin (P.numNodes ℓ₀)) (nd : P.InnerNode ℓ₀)
    (hs : nd.seed = (st.inner ℓ₀ h2₀ hlt₀ u₀).seed) :
    (st.updateInner ℓ₀ h2₀ hlt₀ u₀ nd).seeds = st.seeds := by
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0; simp [updateInner]
  · by_cases h1 : ℓ = 1
    · subst h1; simp [updateInner]
    · by_cases hlt : ℓ < P.depth
      · simp only [seeds_inner _ (by omega) hlt hℓ, updateInner]
        by_cases hℓ_eq : ℓ = ℓ₀
        · subst hℓ_eq
          rw [dite_eq_left rfl]
          by_cases hu : u = u₀
          · subst hu; simp [hs]
          · simp [hu]
        · rw [dite_eq_right hℓ_eq]
      · have hd : ℓ = P.depth := by omega
        subst hd; simp [updateInner]

theorem seeds_updateLeaf_of_seed_eq (st : P.TreeState) (u₀ : Fin (P.numNodes P.depth))
    (ln : P.LeafNode) (hs : ln.leafMeta.seed = (st.leaves u₀).leafMeta.seed) :
    (st.updateLeaf u₀ ln).seeds = st.seeds := by
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0; simp [updateLeaf]
  · by_cases h1 : ℓ = 1
    · subst h1; simp [updateLeaf]
    · by_cases hlt : ℓ < P.depth
      · simp [seeds_inner _ (by omega) hlt hℓ, updateLeaf]
      · have hd : ℓ = P.depth := by omega
        subst hd
        simp only [seeds_depth, updateLeaf]
        by_cases hu : u = u₀
        · subst hu; simp [hs]
        · simp [hu]

/-- Tagged node metadata item (`Section 5.6`, PDF pp. 35–36 / printed pp. 34–35) for DFS pre-order
subtree metadata packing in Word-RAM M4. -/
inductive NodeMetaItem (P : TreeSchedule) : Type
  | root : P.RootMeta → NodeMetaItem P
  | inner (ℓ : ℕ) : P.InnerMeta ℓ → NodeMetaItem P
  | leaf : P.LeafMeta → NodeMetaItem P
  deriving DecidableEq

/-- Project the Section 5.6 metadata of node `(ℓ, u)` (`1 ≤ ℓ ≤ depth`), excluding inner/root
`(quot, val)` payload arrays and leaf spillover memory slots. -/
def nodeMeta (st : P.TreeState) (ℓ : ℕ) (_h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) : NodeMetaItem P :=
  if h_one : ℓ = 1 then
    .root (st.roots (h_one ▸ u)).toMeta
  else if hlt : ℓ < P.depth then
    .inner ℓ (st.inner ℓ (by omega) hlt u).toMeta
  else
    have hd : ℓ = P.depth := by omega
    .leaf (st.leaves (hd ▸ u)).leafMeta

/-- DFS pre-order metadata traversal of the subtree rooted at `(ℓ, u)` (`1 ≤ ℓ ≤ depth`), matching
`Section 5.6` contiguous subtree metadata blocks (`ℓ ≥ 2`). -/
def dfsSubtreeMeta (st : P.TreeState) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) : List (NodeMetaItem P) :=
  let head := st.nodeMeta ℓ h1 hℓ u
  if hlt : ℓ < P.depth then
    head :: (List.finRange (2 ^ P.branchBits ℓ)).flatMap fun b =>
      st.dfsSubtreeMeta (ℓ + 1) (by omega) hlt (P.childNodeEquiv ℓ (u, b))
  else
    [head]
termination_by P.depth - ℓ
decreasing_by omega

theorem dfsSubtreeMeta_nonempty (st : P.TreeState) {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) :
    st.dfsSubtreeMeta ℓ h1 hℓ u ≠ [] := by
  unfold dfsSubtreeMeta
  split_ifs <;> simp

/-- Total number of keys currently stored in level-1 root tables across all `N_1` roots. -/
def rootKeyCount (st : P.TreeState) : ℕ :=
  ∑ u : Fin (P.numNodes 1), (st.roots u).table.tableMeta.dom.card

/-! ## Section 3: `WellFormedPadded`, `WellFormed`, and exact subtree capacity laws -/

/-- Internal multi-level representation invariant on `st : P.TreeState` with respect to a
sentinel-padded dictionary `d : P.PaddedDict` and per-key storage-level map
`storeLvl : Fin P.paddedUniv → ℕ` (`Sections 5.2–5.5`). -/
structure WellFormedPadded
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (d : P.PaddedDict) (storeLvl : Fin P.paddedUniv → ℕ) : Prop where
  goodSeeds : st.seeds.AllGoodSeeds (P.paddedDom d)
  storeLvl_bounds : ∀ x ∈ P.paddedDom d, 1 ≤ storeLvl x ∧ storeLvl x ≤ P.depth
  storeLvl_outside : ∀ x, x ∉ P.paddedDom d → storeLvl x = 0
  dom_eq : ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
    st.nodeDom ℓ h1 hℓ u =
      ((st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun x => storeLvl x = ℓ).image
        (st.seeds.idAt ℓ h1 hℓ)
  query_eq_of_storeLvl : ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (x : Fin P.paddedUniv) (v : Fin P.valBound),
    d x = some v → st.seeds.nodeAt ℓ hℓ x = u → storeLvl x = ℓ →
      st.nodeQuery scheme ℓ h1 hℓ u (st.seeds.idAt ℓ h1 hℓ x) =
        some (st.seeds.quotAt ℓ h1 hℓ x, v)
  inner_full : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)),
    ((st.inner ℓ h2 hlt u).table.tableMeta.dom).card = P.tableCap ℓ
  wait_dom_eq : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
    (st.nodeWait ℓ h2 hℓ u).dom =
      ((st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun x => storeLvl x < ℓ).image
        (st.seeds.idAt ℓ (by omega) hℓ)
  wait_lookup_eq : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (x : Fin P.paddedUniv),
    x ∈ st.seeds.activeAt (P.paddedDom d) ℓ hℓ u → storeLvl x < ℓ →
      (st.nodeWait ℓ h2 hℓ u).lookup (st.seeds.idAt ℓ (by omega) hℓ x) =
        some (st.seeds.idAt (ℓ - 1) (by omega) (by omega) x)

/-- External representation invariant coupling `st : P.TreeState` to
`dict : Dictionary.State P.univ` via sentinel padding (`Section 4, Footnote 5` & `Section 5.2`). -/
@[expose]
def WellFormed (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (dict : Dictionary.State P.univ) : Prop :=
  ∃ (d : P.PaddedDict) (storeLvl : Fin P.paddedUniv → ℕ),
    P.MatchesExternal d st.sentCount dict ∧
    st.WellFormedPadded scheme d storeLvl

theorem WellFormed.valuesBounded
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict) :
    Dictionary.ValuesBounded P.valBound dict := by
  obtain ⟨d, _, hm, _⟩ := hwf
  exact P.matchesExternal_valuesBounded hm

theorem WellFormed.card_dom_le
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict) :
    (Dictionary.dom dict).card ≤ P.cap := by
  obtain ⟨d, _, hm, _⟩ := hwf
  exact P.matchesExternal_card_dom_le hm

/-- Active keys routed to `(ℓ, u)` partition disjointly across its `2 ^ branchBits ℓ` children. -/
theorem activeAt_filter_card_eq_sum_children (seeds : P.SeedAssignment)
    (S : Finset (Fin P.paddedUniv)) {ℓ : ℕ} (hlt : ℓ < P.depth)
    (u : Fin (P.numNodes ℓ)) (p : Fin P.paddedUniv → Prop) [DecidablePred p] :
    ((seeds.activeAt S ℓ hlt.le u).filter p).card =
      ∑ b : Fin (2 ^ P.branchBits ℓ),
        ((seeds.activeAt S (ℓ + 1) hlt (P.childNodeEquiv ℓ (u, b))).filter p).card := by
  have hpart : (seeds.activeAt S ℓ hlt.le u).filter p =
      Finset.univ.biUnion fun b : Fin (2 ^ P.branchBits ℓ) =>
        (seeds.activeAt S (ℓ + 1) hlt (P.childNodeEquiv ℓ (u, b))).filter p := by
    ext x
    simp only [mem_filter, SeedAssignment.mem_activeAt_iff, mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hxS, hnu⟩, hpx⟩
      refine ⟨P.childBranch ℓ (seeds.nodeAt (ℓ + 1) hlt x), ⟨hxS, ?_⟩, hpx⟩
      rw [← hnu, ← seeds.parentNode_nodeAt hlt x, P.childNodeEquiv_parent_branch]
    · rintro ⟨b, ⟨hxS, hnc⟩, hpx⟩
      refine ⟨⟨hxS, ?_⟩, hpx⟩
      rw [← seeds.parentNode_nodeAt hlt x, hnc, P.parentNode_childNodeEquiv]
  rw [hpart, card_biUnion]
  intro b₁ _ b₂ _ hne
  change Disjoint _ _
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have hn₁ := (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx₁).1).2
  have hn₂ := (SeedAssignment.mem_activeAt_iff.mp (mem_filter.mp hx₂).1).2
  have hceq := hn₁.symm.trans hn₂
  exact hne (congrArg Prod.snd ((P.childNodeEquiv ℓ).injective hceq))

/-- Every node `(ℓ, u)` at level `2 ≤ ℓ ≤ depth` stores **identically `P.nLow ℓ` keys** in its
subtree (`storeLvl x ≥ ℓ`). -/
theorem subtree_stored_card_eq_nLow
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) :
    ((st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun x => ℓ ≤ storeLvl x).card =
      P.nLow ℓ := by
  have hgen : ∀ (k m : ℕ), m + k = P.depth → (hm2 : 2 ≤ m) → (hml : m ≤ P.depth) →
      ∀ (u' : Fin (P.numNodes m)),
        ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
          fun x => m ≤ storeLvl x).card = P.nLow m := by
    intro k
    induction k with
    | zero =>
      intro m hsum hm2 hml u'
      obtain rfl : m = P.depth := by omega
      have h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
      have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds h1d le_rfl u'
      have hfeq : ((st.seeds.activeAt (P.paddedDom d) P.depth hml u').filter
          fun x => P.depth ≤ storeLvl x) =
          (st.seeds.activeAt (P.paddedDom d) P.depth hml u').filter
            fun x => storeLvl x = P.depth := by
        refine filter_congr fun x hx => ?_
        have hbd := hwf.storeLvl_bounds x (SeedAssignment.mem_activeAt_iff.mp hx).1
        omega
      have hdom := hwf.dom_eq P.depth h1d hml u'
      rw [nodeDom_depth] at hdom
      rw [hfeq, ← card_image_of_injOn (hinj.mono (filter_subset _ _)), ← hdom, LeafNode.card_dom]
    | succ k ih =>
      intro m hsum hm2 hml u'
      have hmlt : m < P.depth := by omega
      have h1m : 1 ≤ m := by omega
      have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds h1m hml u'
      have hsplit : ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
          fun x => m ≤ storeLvl x) =
          ((st.seeds.activeAt (P.paddedDom d) m hml u').filter fun x => storeLvl x = m) ∪
          ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
            fun x => m + 1 ≤ storeLvl x) := by
        ext x
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨hx, hle⟩
          by_cases he : storeLvl x = m
          · exact Or.inl ⟨hx, he⟩
          · exact Or.inr ⟨hx, by omega⟩
        · rintro (⟨hx, he⟩ | ⟨hx, hge⟩) <;> exact ⟨hx, by omega⟩
      have hdisj : Disjoint
          ((st.seeds.activeAt (P.paddedDom d) m hml u').filter fun x => storeLvl x = m)
          ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
            fun x => m + 1 ≤ storeLvl x) := by
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        have h1 := (mem_filter.mp hx₁).2
        have h2' := (mem_filter.mp hx₂).2
        omega
      have hcur : ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
          fun x => storeLvl x = m).card = P.tableCap m := by
        have hdom := hwf.dom_eq m h1m hml u'
        rw [nodeDom_inner st h1m hm2 hmlt hml] at hdom
        rw [← card_image_of_injOn (hinj.mono (filter_subset _ _)), ← hdom,
          hwf.inner_full m hm2 hmlt u']
      have hchildren : ((st.seeds.activeAt (P.paddedDom d) m hml u').filter
          fun x => m + 1 ≤ storeLvl x).card = P.branchFactor m * P.nLow (m + 1) := by
        rw [activeAt_filter_card_eq_sum_children st.seeds (P.paddedDom d) hmlt u']
        have hchild_eq : ∀ b : Fin (2 ^ P.branchBits m),
            ((st.seeds.activeAt (P.paddedDom d) (m + 1) hmlt
              (P.childNodeEquiv m (u', b))).filter fun x => m + 1 ≤ storeLvl x).card =
              P.nLow (m + 1) :=
          fun b => ih (m + 1) (by omega) (by omega) hmlt (P.childNodeEquiv m (u', b))
        simp only [hchild_eq, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, branchFactor]
      have hcap_eq : P.tableCap m + P.branchFactor m * P.nLow (m + 1) = P.nLow m := by
        dsimp only [tableCap, nLow, branchFactor]
        rw [ite_eq_right (by omega), ite_eq_left hmlt, ite_eq_right (by omega),
          ite_eq_right (by omega)]
        have hle := P.inner_cap_le m hm2 hmlt
        omega
      rw [hsplit, card_union_of_disjoint hdisj, hcur, hchildren, hcap_eq]
  exact hgen (P.depth - ℓ) ℓ (by omega) h2 hℓ u

/-- Exact waiting-list cardinality identity at any node `(ℓ, u)` (`2 ≤ ℓ ≤ depth`):
`#(nodeWait ℓ u).dom = #(activeAt ℓ u) - nLow ℓ`. -/
theorem card_nodeWait_dom_eq
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) :
    (st.nodeWait ℓ h2 hℓ u).dom.card =
      (st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).card - P.nLow ℓ := by
  have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds (by omega) hℓ u
  rw [hwf.wait_dom_eq ℓ h2 hℓ u, card_image_of_injOn (hinj.mono (filter_subset _ _))]
  have hpart := card_filter_add_card_filter_not
    (s := st.seeds.activeAt (P.paddedDom d) ℓ hℓ u) (p := fun x => storeLvl x < ℓ)
  have hnot : ((st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun x => ¬ storeLvl x < ℓ) =
      (st.seeds.activeAt (P.paddedDom d) ℓ hℓ u).filter fun x => ℓ ≤ storeLvl x := by
    refine filter_congr fun x _ => by omega
  rw [hnot, subtree_stored_card_eq_nLow hwf h2 hℓ u] at hpart
  omega

/-- Exact root storage-table cardinality identity at any root `u₁` (`ℓ = 1`):
`#(roots u₁).table.tableMeta.dom + B_1 * nLow 2 = #(activeAt 1 u₁)`. -/
theorem card_root_dom_add_eq
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) (u₁ : Fin (P.numNodes 1)) :
    (st.roots u₁).table.tableMeta.dom.card + P.branchFactor 1 * P.nLow 2 =
      (st.seeds.activeAt (P.paddedDom d) 1 (Nat.one_le_of_lt P.two_le_depth) u₁).card := by
  have h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  have h1lt : 1 < P.depth := P.two_le_depth
  have hinj := st.seeds.injOn_idAt_activeAt hwf.goodSeeds le_rfl h1d u₁
  have hdom := hwf.dom_eq 1 le_rfl h1d u₁
  rw [nodeDom_one] at hdom
  have hroot_card : (st.roots u₁).table.tableMeta.dom.card =
      ((st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).filter fun x => storeLvl x = 1).card := by
    rw [hdom, card_image_of_injOn (hinj.mono (filter_subset _ _))]
  have hpart := card_filter_add_card_filter_not
    (s := st.seeds.activeAt (P.paddedDom d) 1 h1d u₁) (p := fun x => storeLvl x = 1)
  have hnot : ((st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).filter fun x => ¬ storeLvl x = 1) =
      (st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).filter fun x => 2 ≤ storeLvl x := by
    refine filter_congr fun x hx => ?_
    have hbd := hwf.storeLvl_bounds x (SeedAssignment.mem_activeAt_iff.mp hx).1
    omega
  rw [hnot, activeAt_filter_card_eq_sum_children st.seeds (P.paddedDom d) h1lt u₁
    (fun x => 2 ≤ storeLvl x)] at hpart
  have hchild : ∀ b : Fin (2 ^ P.branchBits 1),
      ((st.seeds.activeAt (P.paddedDom d) 2 P.two_le_depth
        (P.childNodeEquiv 1 (u₁, b))).filter fun x => 2 ≤ storeLvl x).card = P.nLow 2 :=
    fun b => subtree_stored_card_eq_nLow hwf le_rfl P.two_le_depth _
  rw [Finset.sum_congr rfl fun b _ => hchild b, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul] at hpart
  rwa [← hroot_card] at hpart

/-- Active keys stored across all `N_1` root tables never exceed `P.rootValPoolCap`. -/
theorem rootKeyCount_le_rootValPoolCap
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) :
    st.rootKeyCount ≤ P.rootValPoolCap := by
  have h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  let u₀ : Fin (P.numNodes 0) := ⟨0, P.numNodes_pos 0⟩
  have hsum_act : ∑ u₁ : Fin (P.numNodes 1),
      (st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).card = (P.paddedDom d).card := by
    have h0 := activeAt_filter_card_eq_sum_children st.seeds (P.paddedDom d)
      (Nat.lt_of_lt_of_le Nat.zero_lt_two P.two_le_depth) u₀ (fun _ => True)
    rw [st.seeds.activeAt_zero, filter_true_of_mem (fun _ _ => trivial)] at h0
    rw [h0]
    have hbij : ∑ p : Fin (P.numNodes 0) × Fin (2 ^ P.branchBits 0),
        (st.seeds.activeAt (P.paddedDom d) 1 h1d (P.childNodeEquiv 0 p)).card =
        ∑ u₁ : Fin (P.numNodes 1), (st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).card :=
      Fintype.sum_equiv (P.childNodeEquiv 0)
        (fun p => (st.seeds.activeAt (P.paddedDom d) 1 h1d (P.childNodeEquiv 0 p)).card)
        (fun u₁ => (st.seeds.activeAt (P.paddedDom d) 1 h1d u₁).card) (fun _ => rfl)
    rw [← hbij, Fintype.sum_prod_type]
    have huniv0 : (Finset.univ : Finset (Fin (P.numNodes 0))) = {u₀} := by
      ext v
      rw [Subsingleton.elim v u₀]
      exact ⟨fun _ => mem_singleton_self u₀, fun _ => Finset.mem_univ u₀⟩
    rw [huniv0, sum_singleton]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [filter_true_of_mem (fun _ _ => trivial)]
  have hsum_roots : st.rootKeyCount + P.numNodes 2 * P.nLow 2 = (P.paddedDom d).card := by
    dsimp only [rootKeyCount]
    have h1 := Finset.sum_congr (rfl : (Finset.univ : Finset (Fin (P.numNodes 1))) = Finset.univ)
      fun u₁ _ => card_root_dom_add_eq hwf u₁
    rw [Finset.sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
      ← mul_assoc, ← P.numNodes_succ 1, hsum_act] at h1
    exact h1
  have hhi : (P.paddedDom d).card ≤ P.cap := by
    have := hwf.goodSeeds.1.2
    simpa [nHigh] using this
  dsimp only [rootValPoolCap]
  omega


end TreeState

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
