/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSeeds

/-!
# Subconstant-Redundancy Pure Storage Nodes and Metadata Separation

This file formalizes the pure node-level storage structures and Section 5.6 metadata-versus-payload
separation for the multi-level dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and
Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Sections 5.2 and 5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 27–30 and 35–36 /
printed pp. 26–29 and 34–35), re-exporting the regime-switched hash-seed spaces and concentration
theorems from `NodeSeeds`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.WaitingList`: bounded waiting list of pairs
  `(x_id^[ℓ], x_id^[ℓ - 1])` (`Section 5.2`, capacity `waitCap ℓ = 2 * delta ℓ`).
* `StorageTableMeta`, `StorageTable`: inner and root storage tables separating `StorageTableMeta`
  (`Section 5.6` ID-only slot locator `locateSlot`, bit budget `succinctTableMetaBits`, though
  modeled as a map with ~`m · 2^I` states without an explicit bit-packing encoding) from
  `(quot, val)` payload slots.
* `TreeSchedule.LeafMeta`, `TreeSchedule.LeafNode`, `TreeSchedule.InnerMeta`,
  `TreeSchedule.InnerNode`, `TreeSchedule.RootMeta`, `TreeSchedule.RootNode`: leaf
  (`Minimap.FixedEncoded`), inner, and root node representations with explicit metadata projections
  (`toMeta`, `LeafMeta.locateSlot`) for DFS metadata packing.

## Main results

* `WaitingList.lookup_push`, `WaitingList.lookup_remove`, `WaitingList.lookup_pop_snd`: exact
  `Function.update` equations for waiting-list operations (`Algorithm 3`).
* `StorageTable.query_overwrite`, `StorageTable.query_insert`, `StorageTable.query_delete`,
  `StorageTable.query_replace`, `StorageTable.query_ofFinset`: exact `Function.update` equations for
  storage-table operations.
* `TreeSchedule.rootKeys_le_rootValPoolCap`: active root values across all `N_1` roots never exceed
  `rootValPoolCap` (`TreeState.rootKeyCount_le_rootValPoolCap`).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
* [M. Pătrașcu, *Succincter*][Patrascu2008]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 3: Pure waiting lists, storage tables, and Section 5.6 metadata separation -/

/-- Bounded waiting list storing up to `cap` pairs `(x_id^[ℓ], x_id^[ℓ - 1])` with distinct first
components ([LiLiangYuZhou2024, Section 5.2];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 28 / printed p. 27). -/
structure WaitingList (I_cur I_prev cap : ℕ) where
  /-- Ordered `(currentId, parentId)` pairs currently held in the waiting list. -/
  entries : List (Fin (2 ^ I_cur) × Fin (2 ^ I_prev))
  len_le : entries.length ≤ cap
  nodup_fst : (entries.map Prod.fst).Nodup
  deriving DecidableEq

namespace WaitingList

variable {I_cur I_prev cap : ℕ}

/-- Active level-`ℓ` ID set present in `w`. -/
def dom (w : WaitingList I_cur I_prev cap) : Finset (Fin (2 ^ I_cur)) :=
  (w.entries.map Prod.fst).toFinset

theorem mem_dom_iff (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) :
    k ∈ w.dom ↔ k ∈ w.entries.map Prod.fst :=
  List.mem_toFinset

theorem card_dom (w : WaitingList I_cur I_prev cap) :
    w.dom.card = w.entries.length := by
  rw [dom, List.toFinset_card_of_nodup w.nodup_fst, List.length_map]

theorem card_dom_le (w : WaitingList I_cur I_prev cap) :
    w.dom.card ≤ cap :=
  w.card_dom ▸ w.len_le

/-- Empty waiting list. -/
def empty (I_cur I_prev cap : ℕ) : WaitingList I_cur I_prev cap where
  entries := []
  len_le := Nat.zero_le cap
  nodup_fst := List.nodup_nil

@[simp]
theorem dom_empty : (empty I_cur I_prev cap).dom = ∅ := by rfl

/-- Look up the parent ID `x_id^[ℓ - 1]` associated with `k : Fin (2 ^ I_cur)`. -/
def lookup (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) :
    Option (Fin (2 ^ I_prev)) :=
  (w.entries.find? fun p => p.1 == k).map Prod.snd

@[simp]
theorem lookup_empty (k : Fin (2 ^ I_cur)) :
    (empty I_cur I_prev cap).lookup k = none := by rfl

private theorem lookup_list_of_nodup :
    ∀ {l : List (Fin (2 ^ I_cur) × Fin (2 ^ I_prev))},
      (l.map Prod.fst).Nodup →
      ∀ {p : Fin (2 ^ I_cur) × Fin (2 ^ I_prev)}, p ∈ l →
        ((l.find? fun q => q.1 == p.1).map Prod.snd) = some p.2
  | [], _, _, hp => nomatch hp
  | q :: qs, hnd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hmem
    · simp [List.find?]
    · have hne : (q.1 == p.1) = false :=
        beq_eq_false_iff_ne.mpr fun h => hnd.1 (h ▸ List.mem_map_of_mem hmem)
      simp only [List.find?, hne, Option.map]
      exact lookup_list_of_nodup hnd.2 hmem

theorem lookup_eq_some_iff (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur))
    (v : Fin (2 ^ I_prev)) :
    w.lookup k = some v ↔ (k, v) ∈ w.entries := by
  constructor
  · intro h
    dsimp only [lookup] at h
    rcases hfind : w.entries.find? (fun p => p.1 == k) with _ | p
    · rw [hfind] at h; cases h
    · rw [hfind] at h
      have hmem := List.mem_of_find?_eq_some hfind
      have heq : p.1 = k := beq_iff_eq.mp <|
        List.find?_some (p := fun q : Fin (2 ^ I_cur) × Fin (2 ^ I_prev) => q.1 == k) hfind
      have hv : p.2 = v := Option.some.inj h
      rwa [← heq, ← hv]
  · exact lookup_list_of_nodup w.nodup_fst

theorem isSome_lookup_iff (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) :
    (w.lookup k).isSome ↔ k ∈ w.dom := by
  rw [w.mem_dom_iff, List.mem_map]
  rcases h : w.lookup k with _ | v
  · constructor
    · intro hs; cases hs
    · rintro ⟨⟨k', v'⟩, hmem, rfl⟩
      have := (w.lookup_eq_some_iff k' v').mpr hmem
      rw [h] at this; cases this
  · constructor
    · intro _; exact ⟨(k, v), (w.lookup_eq_some_iff k v).mp h, rfl⟩
    · intro _; rfl

/-- Push a fresh `(k, prev)` pair onto `w`. -/
def push (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) (prev : Fin (2 ^ I_prev))
    (hlen : w.entries.length + 1 ≤ cap) (hk : k ∉ w.dom) :
    WaitingList I_cur I_prev cap where
  entries := (k, prev) :: w.entries
  len_le := by simpa only [List.length_cons] using hlen
  nodup_fst := by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨mt (w.mem_dom_iff k).mpr hk, w.nodup_fst⟩

@[simp]
theorem dom_push (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur))
    (prev : Fin (2 ^ I_prev)) (hlen : w.entries.length + 1 ≤ cap) (hk : k ∉ w.dom) :
    (w.push k prev hlen hk).dom = insert k w.dom := by
  simp [dom, push]

@[simp]
theorem lookup_push (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur))
    (prev : Fin (2 ^ I_prev)) (hlen : w.entries.length + 1 ≤ cap) (hk : k ∉ w.dom)
    (k' : Fin (2 ^ I_cur)) :
    (w.push k prev hlen hk).lookup k' = Function.update w.lookup k (some prev) k' := by
  by_cases hkk : k' = k
  · subst k'
    dsimp only [lookup, push]
    simp [List.find?]
  · rw [Function.update_of_ne hkk]
    have hne : (k == k') = false := beq_eq_false_iff_ne.mpr (Ne.symm hkk)
    dsimp only [lookup, push]
    simp [List.find?, hne]

/-- Remove `k` (if present) from `w` (`Algorithm 3`, Branch 1). -/
def remove (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) :
    WaitingList I_cur I_prev cap where
  entries := w.entries.filter fun p => p.1 != k
  len_le := (List.length_filter_le _ _).trans w.len_le
  nodup_fst := by
    have hsub : ((w.entries.filter fun p => p.1 != k).map Prod.fst).Sublist
        (w.entries.map Prod.fst) :=
      (List.filter_sublist).map Prod.fst
    exact w.nodup_fst.sublist hsub

@[simp]
theorem dom_remove (w : WaitingList I_cur I_prev cap) (k : Fin (2 ^ I_cur)) :
    (w.remove k).dom = w.dom.erase k := by
  ext k'
  simp only [mem_dom_iff, remove, List.mem_map, List.mem_filter, bne_iff_ne, mem_erase]
  constructor
  · rintro ⟨p, ⟨hp, hne⟩, rfl⟩
    exact ⟨hne, ⟨p, hp, rfl⟩⟩
  · rintro ⟨hne, ⟨p, hp, rfl⟩⟩
    exact ⟨p, ⟨hp, hne⟩, rfl⟩

@[simp]
theorem lookup_remove (w : WaitingList I_cur I_prev cap) (k k' : Fin (2 ^ I_cur)) :
    (w.remove k).lookup k' = Function.update w.lookup k none k' := by
  by_cases hkk : k' = k
  · subst k'
    rw [Function.update_self]
    by_contra hsome
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hsome
    have hmem := ((w.remove k).lookup_eq_some_iff k v).mp hv
    simp [remove] at hmem
  · rw [Function.update_of_ne hkk]
    rcases h : w.lookup k' with _ | v
    · by_contra hsome
      obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp hsome
      have hmem := ((w.remove k).lookup_eq_some_iff k' v').mp hv'
      have hmem0 : (k', v') ∈ w.entries := (List.mem_filter.mp hmem).1
      have := (w.lookup_eq_some_iff k' v').mpr hmem0
      rw [h] at this; cases this
    · have hmem0 := (w.lookup_eq_some_iff k' v).mp h
      have hmem1 : (k', v) ∈ (w.remove k).entries :=
        List.mem_filter.mpr ⟨hmem0, bne_iff_ne.mpr hkk⟩
      exact ((w.remove k).lookup_eq_some_iff k' v).mpr hmem1

/-- Pop the head entry `(y_id^[ℓ], y_id^[ℓ - 1])` of a nonempty waiting list (`Algorithm 3`,
Branch 2). -/
def pop (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty) :
    (Fin (2 ^ I_cur) × Fin (2 ^ I_prev)) × WaitingList I_cur I_prev cap :=
  have hlen : w.entries ≠ [] := by
    intro hemp
    rcases hne with ⟨x, hx⟩
    rw [w.mem_dom_iff, hemp] at hx
    cases hx
  let hd := w.entries.head hlen
  (hd, w.remove hd.1)

/-- Popped `(currentId, parentId)` pair returned by `w.pop hne`. -/
abbrev popEntry (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty) :
    Fin (2 ^ I_cur) × Fin (2 ^ I_prev) :=
  (w.pop hne).1

theorem pop_fst_mem_dom (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty) :
    (w.popEntry hne).1 ∈ w.dom := by
  dsimp only [popEntry, pop]
  have hlen : w.entries ≠ [] := by
    intro hemp; rcases hne with ⟨x, hx⟩; rw [w.mem_dom_iff, hemp] at hx; cases hx
  exact (w.mem_dom_iff _).mpr (List.mem_map_of_mem (List.head_mem hlen))

theorem lookup_pop_fst (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty) :
    w.lookup (w.popEntry hne).1 = some (w.popEntry hne).2 := by
  dsimp only [popEntry, pop]
  have hlen : w.entries ≠ [] := by
    intro hemp; rcases hne with ⟨x, hx⟩; rw [w.mem_dom_iff, hemp] at hx; cases hx
  exact (w.lookup_eq_some_iff _ _).mpr (List.head_mem hlen)

@[simp]
theorem dom_pop_snd (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty) :
    (w.pop hne).2.dom = w.dom.erase (w.popEntry hne).1 :=
  w.dom_remove _

@[simp]
theorem lookup_pop_snd (w : WaitingList I_cur I_prev cap) (hne : w.dom.Nonempty)
    (k : Fin (2 ^ I_cur)) :
    (w.pop hne).2.lookup k = Function.update w.lookup (w.popEntry hne).1 none k :=
  w.lookup_remove _ k

/-- Build a waiting list from a finite set `S` (`#S ≤ cap`) and parent-ID map `f`. -/
noncomputable def ofFinset (S : Finset (Fin (2 ^ I_cur))) (hS : S.card ≤ cap)
    (f : Fin (2 ^ I_cur) → Fin (2 ^ I_prev)) : WaitingList I_cur I_prev cap where
  entries := (S.sort (· ≤ ·)).map fun k => (k, f k)
  len_le := by rw [List.length_map, Finset.length_sort]; exact hS
  nodup_fst := by
    rw [List.map_map, Function.comp_def]
    simpa only [List.map_id'] using S.sort_nodup (· ≤ ·)

@[simp]
theorem dom_ofFinset (S : Finset (Fin (2 ^ I_cur))) (hS : S.card ≤ cap)
    (f : Fin (2 ^ I_cur) → Fin (2 ^ I_prev)) :
    (ofFinset S hS f).dom = S := by
  ext k
  simp [dom, ofFinset]

@[simp]
theorem lookup_ofFinset (S : Finset (Fin (2 ^ I_cur))) (hS : S.card ≤ cap)
    (f : Fin (2 ^ I_cur) → Fin (2 ^ I_prev)) (k : Fin (2 ^ I_cur)) :
    (ofFinset S hS f).lookup k = if k ∈ S then some (f k) else none := by
  by_cases hk : k ∈ S
  · rw [ite_eq_left hk]
    refine ((ofFinset S hS f).lookup_eq_some_iff k (f k)).mpr ?_
    simp [ofFinset, hk]
  · rw [ite_eq_right hk]
    by_contra hsome
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hsome
    have hmem := ((ofFinset S hS f).lookup_eq_some_iff k v).mp hv
    simp [ofFinset, hk] at hmem

end WaitingList

/-- Pure storage-table ID metadata on `Fin (2 ^ I)` with `m` slots (`Section 5.6` metadata
component of `SuccinctBucket`, matching the intended bit budget `succinctTableMetaBits I m`,
though modeled here as a slot-assignment structure with ~`m · 2^I` states rather than packed to
that bit budget by an explicit encoding). -/
structure StorageTableMeta (I m : ℕ) where
  /-- Slot-to-active-ID assignment across the `m` table slots. -/
  slots : Fin m → Option (Fin (2 ^ I))
  inj_slots : ∀ i j k, slots i = some k → slots j = some k → i = j
  deriving DecidableEq

namespace StorageTableMeta

variable {I m : ℕ}

/-- Metadata-only slot locator (`Section 5.6`): returns `some i` iff key `k` occupies slot `i`,
without inspecting quotient or value payloads. -/
def locateSlot (tm : StorageTableMeta I m) (k : Fin (2 ^ I)) : Option (Fin m) :=
  Fin.find? fun i => tm.slots i == some k

theorem locateSlot_eq_some_iff (tm : StorageTableMeta I m) (k : Fin (2 ^ I)) (i : Fin m) :
    tm.locateSlot k = some i ↔ tm.slots i = some k := by
  dsimp only [locateSlot]
  constructor
  · intro h
    exact eq_of_beq (Fin.eq_true_of_find?_eq_some (p := fun j => tm.slots j == some k) h)
  · intro hi
    cases hfind : Fin.find? (fun j => tm.slots j == some k) with
    | some j =>
      have hj := eq_of_beq (Fin.eq_true_of_find?_eq_some (p := fun j => tm.slots j == some k) hfind)
      rw [tm.inj_slots j i k hj hi]
    | none =>
      have hfalse := Fin.find?_eq_none_iff.mp hfind i
      simp [hi] at hfalse

/-- Active ID set represented in `tm`. -/
def dom (tm : StorageTableMeta I m) : Finset (Fin (2 ^ I)) :=
  univ.filter fun k => (tm.locateSlot k).isSome

theorem mem_dom_iff (tm : StorageTableMeta I m) (k : Fin (2 ^ I)) :
    k ∈ tm.dom ↔ ∃ i : Fin m, tm.slots i = some k := by
  simp only [dom, mem_filter, mem_univ, true_and, Option.isSome_iff_exists,
    tm.locateSlot_eq_some_iff]

theorem isSome_locateSlot_iff (tm : StorageTableMeta I m) (k : Fin (2 ^ I)) :
    (tm.locateSlot k).isSome ↔ k ∈ tm.dom := by
  simp [dom]

theorem card_dom_le (tm : StorageTableMeta I m) : tm.dom.card ≤ m := by
  have hsub : tm.dom ⊆ univ.biUnion fun i : Fin m => (tm.slots i).toFinset := by
    intro k hk
    obtain ⟨i, hi⟩ := (tm.mem_dom_iff k).mp hk
    exact mem_biUnion.mpr ⟨i, mem_univ i, Option.mem_toFinset.mpr hi⟩
  calc tm.dom.card ≤ (univ.biUnion fun i : Fin m => (tm.slots i).toFinset).card :=
        card_le_card hsub
    _ ≤ ∑ i : Fin m, (tm.slots i).toFinset.card := card_biUnion_le
    _ ≤ ∑ _i : Fin m, 1 := sum_le_sum fun i _ => by cases tm.slots i <;> simp
    _ = m := by simp

theorem exists_free_slot (tm : StorageTableMeta I m) (hlt : tm.dom.card < m) :
    ∃ i : Fin m, tm.slots i = none := by
  by_contra hno
  push Not at hno
  have hsome : ∀ i : Fin m, ∃ k, tm.slots i = some k := fun i =>
    Option.ne_none_iff_exists'.mp (hno i)
  choose f hf using hsome
  have hinj : Function.Injective f := fun i j hij =>
    tm.inj_slots i j (f j) (hij ▸ hf i) (hf j)
  have hmap : (univ.map ⟨f, hinj⟩) ⊆ tm.dom := by
    intro k hk
    rcases mem_map.mp hk with ⟨i, _, rfl⟩
    exact (tm.mem_dom_iff (f i)).mpr ⟨i, hf i⟩
  have hle : m ≤ tm.dom.card := by
    simpa only [card_map, card_univ, Fintype.card_fin] using card_le_card hmap
  omega

/-- Empty storage-table metadata. -/
def empty (I m : ℕ) : StorageTableMeta I m where
  slots := fun _ => none
  inj_slots := fun _ _ _ h => nomatch h

@[simp]
theorem dom_empty : (empty I m).dom = ∅ := by
  ext k; simp [mem_dom_iff, empty]

@[simp]
theorem locateSlot_empty (k : Fin (2 ^ I)) : (empty I m).locateSlot k = none := by
  rcases h : (empty I m).locateSlot k with _ | i
  · rfl
  · exact nomatch ((empty I m).locateSlot_eq_some_iff k i |>.mp h)

end StorageTableMeta

/-- Inner or root storage table separating `tableMeta : StorageTableMeta I m` (`Section 5.6`
metadata) from `payload : Fin m → Fin Q × Fin V` (`(quot, val)` payload slots). -/
structure StorageTable (I m Q V : ℕ) where
  /-- Active-ID slot metadata separated from payload values (`Section 5.6`). -/
  tableMeta : StorageTableMeta I m
  /-- Per-slot `(quotient, value)` payload array. -/
  payload : Fin m → Fin Q × Fin V
  deriving DecidableEq

namespace StorageTable

variable {I m Q V : ℕ}

/-- Look up `(quot, val)` for `k : Fin (2 ^ I)` via metadata-only `locateSlot` followed by a single
payload-slot read. -/
def query (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) : Option (Fin Q × Fin V) :=
  (tbl.tableMeta.locateSlot k).map tbl.payload

theorem isSome_query_iff (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) :
    (tbl.query k).isSome ↔ k ∈ tbl.tableMeta.dom := by
  simp [query, tbl.tableMeta.isSome_locateSlot_iff]

/-- Empty storage table (given `1 ≤ Q` and `1 ≤ V`). -/
def empty (I m : ℕ) {Q V : ℕ} (hQ : 1 ≤ Q) (hV : 1 ≤ V) : StorageTable I m Q V where
  tableMeta := StorageTableMeta.empty I m
  payload := fun _ => (⟨0, hQ⟩, ⟨0, hV⟩)

@[simp]
theorem dom_empty {Q V : ℕ} (hQ : 1 ≤ Q) (hV : 1 ≤ V) :
    (empty I m hQ hV).tableMeta.dom = ∅ :=
  StorageTableMeta.dom_empty

@[simp]
theorem query_empty {Q V : ℕ} (hQ : 1 ≤ Q) (hV : 1 ≤ V) (k : Fin (2 ^ I)) :
    (empty I m hQ hV).query k = none := by
  simp [query, empty]

/-- Overwrite the `(quot, val)` payload of an existing key `k ∈ tbl.tableMeta.dom` in place,
leaving `tableMeta` unchanged. -/
def overwrite (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) (qv : Fin Q × Fin V)
    (hk : k ∈ tbl.tableMeta.dom) : StorageTable I m Q V :=
  let i₀ := (tbl.tableMeta.locateSlot k).get (tbl.tableMeta.isSome_locateSlot_iff k |>.mpr hk)
  { tableMeta := tbl.tableMeta
    payload := Function.update tbl.payload i₀ qv }

@[simp]
theorem tableMeta_overwrite (tbl : StorageTable I m Q V) (k : Fin (2 ^ I))
    (qv : Fin Q × Fin V) (hk : k ∈ tbl.tableMeta.dom) :
    (tbl.overwrite k qv hk).tableMeta = tbl.tableMeta := by rfl

@[simp]
theorem query_overwrite (tbl : StorageTable I m Q V) (k : Fin (2 ^ I))
    (qv : Fin Q × Fin V) (hk : k ∈ tbl.tableMeta.dom) (k' : Fin (2 ^ I)) :
    (tbl.overwrite k qv hk).query k' = Function.update tbl.query k (some qv) k' := by
  have hsome := (tbl.tableMeta.isSome_locateSlot_iff k).mpr hk
  let i₀ := (tbl.tableMeta.locateSlot k).get hsome
  have hloc₀ : tbl.tableMeta.locateSlot k = some i₀ := (Option.some_get hsome).symm
  have hsl₀ : tbl.tableMeta.slots i₀ = some k :=
    (tbl.tableMeta.locateSlot_eq_some_iff k i₀).mp hloc₀
  by_cases hkk : k' = k
  · subst k'
    change Option.map (Function.update tbl.payload i₀ qv) (tbl.tableMeta.locateSlot k) =
      Function.update tbl.query k (some qv) k
    rw [hloc₀, Option.map_some, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hkk]
    dsimp only [query, overwrite]
    rcases hloc : tbl.tableMeta.locateSlot k' with _ | j
    · rfl
    · have hsl_j := (tbl.tableMeta.locateSlot_eq_some_iff k' j).mp hloc
      have hj_ne : j ≠ i₀ := fun hji => hkk (Option.some.inj (hsl_j.symm.trans (hji ▸ hsl₀)))
      rw [Option.map_some, Option.map_some, Function.update_of_ne hj_ne]

private def freeSlot (tm : StorageTableMeta I m) (hlt : tm.dom.card < m) : Fin m :=
  match h : Fin.find? (fun i => (tm.slots i).isNone) with
  | some i => i
  | none =>
    False.elim <| by
      obtain ⟨j, hj⟩ := tm.exists_free_slot hlt
      have := Fin.find?_eq_none_iff.mp h j
      simp [hj] at this

private theorem slots_freeSlot (tm : StorageTableMeta I m) (hlt : tm.dom.card < m) :
    tm.slots (freeSlot tm hlt) = none := by
  dsimp only [freeSlot]
  split
  · next i h =>
    exact Option.isNone_iff_eq_none.mp
      (Fin.eq_true_of_find?_eq_some (p := fun j => (tm.slots j).isNone) h)
  · contradiction

/-- Insert a fresh key `k ∉ tbl.tableMeta.dom` when `tbl.tableMeta.dom.card < m` (used at root
nodes `ℓ = 1`). -/
def insert (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) (qv : Fin Q × Fin V)
    (hlt : tbl.tableMeta.dom.card < m) (hk : k ∉ tbl.tableMeta.dom) :
    StorageTable I m Q V :=
  let i₀ := freeSlot tbl.tableMeta hlt
  { tableMeta :=
      { slots := Function.update tbl.tableMeta.slots i₀ (some k)
        inj_slots := fun i j k' hi hj => by
          by_cases hii : i = i₀ <;> by_cases hjj : j = i₀
          · exact hii.trans hjj.symm
          · subst hii
            rw [Function.update_self] at hi
            rw [Function.update_of_ne hjj] at hj
            have hmem : k' ∈ tbl.tableMeta.dom := (tbl.tableMeta.mem_dom_iff k').mpr ⟨j, hj⟩
            exact False.elim (hk (Option.some.inj hi ▸ hmem))
          · subst hjj
            rw [Function.update_self] at hj
            rw [Function.update_of_ne hii] at hi
            have hmem : k' ∈ tbl.tableMeta.dom := (tbl.tableMeta.mem_dom_iff k').mpr ⟨i, hi⟩
            exact False.elim (hk (Option.some.inj hj ▸ hmem))
          · rw [Function.update_of_ne hii] at hi
            rw [Function.update_of_ne hjj] at hj
            exact tbl.tableMeta.inj_slots i j k' hi hj }
    payload := Function.update tbl.payload i₀ qv }

@[simp]
theorem dom_insert (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) (qv : Fin Q × Fin V)
    (hlt : tbl.tableMeta.dom.card < m) (hk : k ∉ tbl.tableMeta.dom) :
    (tbl.insert k qv hlt hk).tableMeta.dom = Insert.insert k tbl.tableMeta.dom := by
  let i₀ := freeSlot tbl.tableMeta hlt
  have hi₀_none : tbl.tableMeta.slots i₀ = none := slots_freeSlot tbl.tableMeta hlt
  ext k'
  rw [StorageTableMeta.mem_dom_iff, mem_insert, StorageTableMeta.mem_dom_iff]
  dsimp only [insert]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i₀
    · subst hji; rw [Function.update_self] at hj; left; exact (Option.some.inj hj).symm
    · rw [Function.update_of_ne hji] at hj; right; exact ⟨j, hj⟩
  · rintro (rfl | ⟨j, hj⟩)
    · exact ⟨i₀, Function.update_self ..⟩
    · have hji : j ≠ i₀ := fun h => by rw [h, hi₀_none] at hj; cases hj
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

@[simp]
theorem query_insert (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) (qv : Fin Q × Fin V)
    (hlt : tbl.tableMeta.dom.card < m) (hk : k ∉ tbl.tableMeta.dom) (k' : Fin (2 ^ I)) :
    (tbl.insert k qv hlt hk).query k' = Function.update tbl.query k (some qv) k' := by
  let i₀ := freeSlot tbl.tableMeta hlt
  have hi₀_none : tbl.tableMeta.slots i₀ = none := slots_freeSlot tbl.tableMeta hlt
  let tbl' := tbl.insert k qv hlt hk
  by_cases hkk : k' = k
  · subst k'
    have hloc' : tbl'.tableMeta.locateSlot k = some i₀ :=
      (tbl'.tableMeta.locateSlot_eq_some_iff k i₀).mpr (Function.update_self ..)
    dsimp only [query]
    rw [hloc', Option.map_some, Function.update_self]
    dsimp only [tbl', insert]
    rw [Function.update_self]
  · rw [Function.update_of_ne hkk]
    dsimp only [query]
    rcases hloc : tbl.tableMeta.locateSlot k' with _ | j
    · have hloc' : tbl'.tableMeta.locateSlot k' = none := by
        rcases hl : tbl'.tableMeta.locateSlot k' with _ | j'
        · rfl
        · have hsj := (tbl'.tableMeta.locateSlot_eq_some_iff k' j').mp hl
          dsimp only [tbl', insert] at hsj
          by_cases hji : j' = i₀
          · subst hji; rw [Function.update_self] at hsj
            exact absurd (Option.some.inj hsj).symm hkk
          · rw [Function.update_of_ne hji] at hsj
            have := (tbl.tableMeta.locateSlot_eq_some_iff k' j').mpr hsj
            rw [hloc] at this; cases this
      rw [hloc']; rfl
    · have hsj := (tbl.tableMeta.locateSlot_eq_some_iff k' j).mp hloc
      have hji : j ≠ i₀ := fun h => by rw [h, hi₀_none] at hsj; cases hsj
      have hloc' : tbl'.tableMeta.locateSlot k' = some j :=
        (tbl'.tableMeta.locateSlot_eq_some_iff k' j).mpr
          (by dsimp only [tbl', insert]; rw [Function.update_of_ne hji]; exact hsj)
      rw [hloc', Option.map_some, Option.map_some]
      dsimp only [tbl', insert]
      rw [Function.update_of_ne hji]

/-- Delete `k` from `tbl` (used at root nodes `ℓ = 1`). -/
def delete (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) : StorageTable I m Q V where
  tableMeta :=
    { slots := fun i => if tbl.tableMeta.slots i == some k then none else tbl.tableMeta.slots i
      inj_slots := fun i j k' hi hj => by
        split_ifs at hi with h1
        split_ifs at hj with h2
        exact tbl.tableMeta.inj_slots i j k' hi hj }
  payload := tbl.payload

@[simp]
theorem dom_delete (tbl : StorageTable I m Q V) (k : Fin (2 ^ I)) :
    (tbl.delete k).tableMeta.dom = tbl.tableMeta.dom.erase k := by
  ext k'
  simp only [StorageTableMeta.mem_dom_iff, delete, mem_erase]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with h
    have hne : k' ≠ k := fun hkk => by subst k'; exact absurd (beq_iff_eq.mpr hi) (by simp [h])
    exact ⟨hne, i, hi⟩
  · rintro ⟨hne, i, hi⟩
    refine ⟨i, ?_⟩
    have hbeq : (tbl.tableMeta.slots i == some k) = false := by
      rw [hi]; exact beq_eq_false_iff_ne.mpr (fun h => hne (Option.some.inj h))
    rw [ite_eq_right (by simp [hbeq])]
    exact hi

@[simp]
theorem query_delete (tbl : StorageTable I m Q V) (k k' : Fin (2 ^ I)) :
    (tbl.delete k).query k' = Function.update tbl.query k none k' := by
  by_cases hkk : k' = k
  · subst k'
    rw [Function.update_self]
    dsimp only [query]
    rcases hl : (tbl.delete k).tableMeta.locateSlot k with _ | i
    · rfl
    · have hi := ((tbl.delete k).tableMeta.locateSlot_eq_some_iff k i).mp hl
      dsimp only [delete] at hi
      split_ifs at hi with h
      exact absurd (beq_iff_eq.mpr hi) (by simp [h])
  · rw [Function.update_of_ne hkk]
    dsimp only [query]
    rcases hl : tbl.tableMeta.locateSlot k' with _ | i
    · have hl' : (tbl.delete k).tableMeta.locateSlot k' = none := by
        rcases h2 : (tbl.delete k).tableMeta.locateSlot k' with _ | j
        · rfl
        · have hj := ((tbl.delete k).tableMeta.locateSlot_eq_some_iff k' j).mp h2
          dsimp only [delete] at hj
          split_ifs at hj
          have := (tbl.tableMeta.locateSlot_eq_some_iff k' j).mpr hj
          rw [hl] at this; cases this
      rw [hl']; rfl
    · have hi := (tbl.tableMeta.locateSlot_eq_some_iff k' i).mp hl
      have hl' : (tbl.delete k).tableMeta.locateSlot k' = some i := by
        refine ((tbl.delete k).tableMeta.locateSlot_eq_some_iff k' i).mpr ?_
        dsimp only [delete]
        have hbeq : (tbl.tableMeta.slots i == some k) = false := by
          rw [hi]; exact beq_eq_false_iff_ne.mpr (fun h => hkk (Option.some.inj h))
        rw [ite_eq_right (by simp [hbeq])]
        exact hi
      rw [hl']
      rfl

/-- Replace an active key `k_old ∈ tbl.tableMeta.dom` with `(k_new, qv_new)` in the freed slot
(`Algorithm 3`, Branch 2 at inner nodes `2 ≤ ℓ < depth`). -/
def replace (tbl : StorageTable I m Q V) (k_old k_new : Fin (2 ^ I)) (qv_new : Fin Q × Fin V)
    (hold : k_old ∈ tbl.tableMeta.dom) (hnew : k_new ∉ tbl.tableMeta.dom.erase k_old) :
    StorageTable I m Q V :=
  let hsome := (tbl.tableMeta.isSome_locateSlot_iff k_old).mpr hold
  let i₀ := (tbl.tableMeta.locateSlot k_old).get hsome
  { tableMeta :=
      { slots := Function.update tbl.tableMeta.slots i₀ (some k_new)
        inj_slots := fun i j k' hi hj => by
          have hsl₀ : tbl.tableMeta.slots i₀ = some k_old :=
            (tbl.tableMeta.locateSlot_eq_some_iff k_old i₀).mp (Option.some_get hsome).symm
          by_cases hii : i = i₀ <;> by_cases hjj : j = i₀
          · exact hii.trans hjj.symm
          · subst hii
            rw [Function.update_self] at hi
            rw [Function.update_of_ne hjj] at hj
            have hne_old : k' ≠ k_old := fun hk =>
              hjj (tbl.tableMeta.inj_slots j i₀ k_old (hk ▸ hj) hsl₀)
            have hmem : k' ∈ tbl.tableMeta.dom.erase k_old :=
              mem_erase.mpr ⟨hne_old, (tbl.tableMeta.mem_dom_iff k').mpr ⟨j, hj⟩⟩
            exact False.elim (hnew (Option.some.inj hi ▸ hmem))
          · subst hjj
            rw [Function.update_self] at hj
            rw [Function.update_of_ne hii] at hi
            have hne_old : k' ≠ k_old := fun hk =>
              hii (tbl.tableMeta.inj_slots i i₀ k_old (hk ▸ hi) hsl₀)
            have hmem : k' ∈ tbl.tableMeta.dom.erase k_old :=
              mem_erase.mpr ⟨hne_old, (tbl.tableMeta.mem_dom_iff k').mpr ⟨i, hi⟩⟩
            exact False.elim (hnew (Option.some.inj hj ▸ hmem))
          · rw [Function.update_of_ne hii] at hi
            rw [Function.update_of_ne hjj] at hj
            exact tbl.tableMeta.inj_slots i j k' hi hj }
    payload := Function.update tbl.payload i₀ qv_new }

@[simp]
theorem dom_replace (tbl : StorageTable I m Q V) (k_old k_new : Fin (2 ^ I))
    (qv_new : Fin Q × Fin V) (hold : k_old ∈ tbl.tableMeta.dom)
    (hnew : k_new ∉ tbl.tableMeta.dom.erase k_old) :
    (tbl.replace k_old k_new qv_new hold hnew).tableMeta.dom =
      Insert.insert k_new (tbl.tableMeta.dom.erase k_old) := by
  have hsome := (tbl.tableMeta.isSome_locateSlot_iff k_old).mpr hold
  let i₀ := (tbl.tableMeta.locateSlot k_old).get hsome
  have hsl₀ : tbl.tableMeta.slots i₀ = some k_old :=
    (tbl.tableMeta.locateSlot_eq_some_iff k_old i₀).mp (Option.some_get hsome).symm
  ext k'
  simp only [StorageTableMeta.mem_dom_iff, replace, mem_insert, mem_erase]
  constructor
  · rintro ⟨j, hj⟩
    by_cases hji : j = i₀
    · subst hji; rw [Function.update_self] at hj; left; exact (Option.some.inj hj).symm
    · rw [Function.update_of_ne hji] at hj
      right
      exact ⟨fun hk => hji (tbl.tableMeta.inj_slots j i₀ k_old (hk ▸ hj) hsl₀), j, hj⟩
  · rintro (rfl | ⟨hne, j, hj⟩)
    · exact ⟨i₀, Function.update_self ..⟩
    · have hji : j ≠ i₀ := fun h => hne (Option.some.inj (hj.symm.trans (h ▸ hsl₀)))
      exact ⟨j, by rw [Function.update_of_ne hji]; exact hj⟩

@[simp]
theorem query_replace (tbl : StorageTable I m Q V) (k_old k_new : Fin (2 ^ I))
    (qv_new : Fin Q × Fin V) (hold : k_old ∈ tbl.tableMeta.dom)
    (hnew : k_new ∉ tbl.tableMeta.dom.erase k_old) (k' : Fin (2 ^ I)) :
    (tbl.replace k_old k_new qv_new hold hnew).query k' =
      Function.update (Function.update tbl.query k_old none) k_new (some qv_new) k' := by
  have hsome := (tbl.tableMeta.isSome_locateSlot_iff k_old).mpr hold
  let i₀ := (tbl.tableMeta.locateSlot k_old).get hsome
  have hsl₀ : tbl.tableMeta.slots i₀ = some k_old :=
    (tbl.tableMeta.locateSlot_eq_some_iff k_old i₀).mp (Option.some_get hsome).symm
  let tbl' := tbl.replace k_old k_new qv_new hold hnew
  by_cases hnew_eq : k' = k_new
  · subst k'
    have hl' : tbl'.tableMeta.locateSlot k_new = some i₀ :=
      (tbl'.tableMeta.locateSlot_eq_some_iff k_new i₀).mpr (Function.update_self ..)
    dsimp only [query]
    rw [hl', Option.map_some, Function.update_self]
    dsimp only [tbl', replace]
    rw [Function.update_self]
  · rw [Function.update_of_ne hnew_eq]
    by_cases hold_eq : k' = k_old
    · subst k'
      rw [Function.update_self]
      dsimp only [query]
      have hl' : tbl'.tableMeta.locateSlot k_old = none := by
        rcases hl : tbl'.tableMeta.locateSlot k_old with _ | j
        · rfl
        · have hj := (tbl'.tableMeta.locateSlot_eq_some_iff k_old j).mp hl
          dsimp only [tbl', replace] at hj
          by_cases hji : j = i₀
          · subst hji; rw [Function.update_self] at hj
            exact absurd (Option.some.inj hj).symm hnew_eq
          · rw [Function.update_of_ne hji] at hj
            exact absurd (tbl.tableMeta.inj_slots j i₀ k_old hj hsl₀) hji
      rw [hl']
      rfl
    · rw [Function.update_of_ne hold_eq]
      dsimp only [query]
      rcases hl : tbl.tableMeta.locateSlot k' with _ | j
      · have hl' : tbl'.tableMeta.locateSlot k' = none := by
          rcases hl2 : tbl'.tableMeta.locateSlot k' with _ | j'
          · rfl
          · have hj := (tbl'.tableMeta.locateSlot_eq_some_iff k' j').mp hl2
            dsimp only [tbl', replace] at hj
            by_cases hji : j' = i₀
            · subst hji; rw [Function.update_self] at hj
              exact absurd (Option.some.inj hj).symm hnew_eq
            · rw [Function.update_of_ne hji] at hj
              have := (tbl.tableMeta.locateSlot_eq_some_iff k' j').mpr hj
              rw [hl] at this; cases this
        rw [hl']; rfl
      · have hsj := (tbl.tableMeta.locateSlot_eq_some_iff k' j).mp hl
        have hji : j ≠ i₀ := fun h => hold_eq (Option.some.inj (hsj.symm.trans (h ▸ hsl₀)))
        have hl' : tbl'.tableMeta.locateSlot k' = some j :=
          (tbl'.tableMeta.locateSlot_eq_some_iff k' j).mpr
            (by dsimp only [tbl', replace]; rw [Function.update_of_ne hji]; exact hsj)
        rw [hl', Option.map_some, Option.map_some]
        dsimp only [tbl', replace]
        rw [Function.update_of_ne hji]

/-- Bulk-initialize a storage table from `S : Finset (Fin (2 ^ I))` (`#S ≤ m`) and `f`
(`Algorithm 4` `Rehash`). -/
noncomputable def ofFinset (S : Finset (Fin (2 ^ I))) (_hS : S.card ≤ m)
    (hQ : 1 ≤ Q) (hV : 1 ≤ V) (f : Fin (2 ^ I) → Fin Q × Fin V) : StorageTable I m Q V :=
  let iso := S.orderIsoOfFin rfl
  { tableMeta :=
      { slots := fun i => if hi : i.val < S.card then some (iso ⟨i.val, hi⟩).1 else none
        inj_slots := fun i j k hi hj => by
          split_ifs at hi with hlt_i
          split_ifs at hj with hlt_j
          have hk_eq := (Option.some.inj hi).trans (Option.some.inj hj).symm
          have heq := iso.injective (Subtype.ext hk_eq)
          exact Fin.ext (congrArg (fun x : Fin S.card => x.val) heq) }
    payload := fun i =>
      if hi : i.val < S.card then f (iso ⟨i.val, hi⟩).1 else (⟨0, hQ⟩, ⟨0, hV⟩) }

@[simp]
theorem dom_ofFinset (S : Finset (Fin (2 ^ I))) (hS : S.card ≤ m)
    (hQ : 1 ≤ Q) (hV : 1 ≤ V) (f : Fin (2 ^ I) → Fin Q × Fin V) :
    (ofFinset S hS hQ hV f).tableMeta.dom = S := by
  ext k
  rw [StorageTableMeta.mem_dom_iff]
  dsimp only [ofFinset]
  constructor
  · rintro ⟨i, hi⟩
    split_ifs at hi with hlt
    exact (Option.some.inj hi) ▸ ((S.orderIsoOfFin rfl) ⟨i.val, hlt⟩).2
  · intro hk
    let idx := (S.orderIsoOfFin rfl).symm ⟨k, hk⟩
    refine ⟨⟨idx.val, idx.isLt.trans_le hS⟩, ?_⟩
    simp [idx.isLt, idx]

@[simp]
theorem query_ofFinset (S : Finset (Fin (2 ^ I))) (hS : S.card ≤ m)
    (hQ : 1 ≤ Q) (hV : 1 ≤ V) (f : Fin (2 ^ I) → Fin Q × Fin V) (k : Fin (2 ^ I)) :
    (ofFinset S hS hQ hV f).query k = if k ∈ S then some (f k) else none := by
  set tbl := ofFinset S hS hQ hV f
  by_cases hk : k ∈ S
  · rw [ite_eq_left hk]
    let idx := (S.orderIsoOfFin rfl).symm ⟨k, hk⟩
    let i : Fin m := ⟨idx.val, idx.isLt.trans_le hS⟩
    have hl : tbl.tableMeta.locateSlot k = some i := by
      refine (tbl.tableMeta.locateSlot_eq_some_iff k i).mpr ?_
      dsimp only [tbl, ofFinset, i]
      simp [idx.isLt, idx]
    dsimp only [query]
    rw [hl, Option.map_some]
    dsimp only [tbl, ofFinset, i]
    simp [idx.isLt, idx]
  · rw [ite_eq_right hk]
    rcases hl : tbl.tableMeta.locateSlot k with _ | i
    · simp [query, hl]
    · have hmem : k ∈ tbl.tableMeta.dom := (tbl.tableMeta.mem_dom_iff k).mpr
        ⟨i, (tbl.tableMeta.locateSlot_eq_some_iff k i).mp hl⟩
      rw [dom_ofFinset] at hmem
      exact absurd hmem hk

end StorageTable

namespace TreeSchedule

variable (P : TreeSchedule)

/-- Leaf metadata (`Section 5.6`): hash seed `g_u`, waiting list, and `Minimap` subset/spillover
header, decoupled from `nLow depth` payload slots. -/
structure LeafMeta where
  /-- Per-node hash seed at `ℓ = depth`. -/
  seed : P.NodeSeed P.depth
  /-- Leaf waiting list of capacity `waitCap depth`. -/
  wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth)
  /-- `Minimap` subset, spillover, and round header index. -/
  header : Fin (Minimap.headerUniv (2 ^ P.idBits P.depth) (P.nLow P.depth)
    (P.quotUniv P.depth * P.valBound) (P.nLow P.depth))
  deriving DecidableEq

/-- Metadata-only leaf slot locator (`Section 5.6` & `Lemma 3.7`): returns `some (spill, slotIdx)`
without inspecting leaf payload slots. -/
def LeafMeta.locateSlot
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (lm : P.LeafMeta) (k : Fin (2 ^ P.idBits P.depth)) :
    Option (Fin (Spillover.spillUniv (P.quotUniv P.depth * P.valBound) (P.nLow P.depth)) ×
      Fin (P.nLow P.depth)) :=
  Minimap.lookupHeader scheme lm.header k

/-- Leaf node (`ℓ = depth`) combining `LeafMeta` with `nLow depth` spillover memory slots
(`Minimap.FixedEncoded`). -/
structure LeafNode where
  /-- Leaf metadata (`seed`, `wait`, and `Minimap` header). -/
  leafMeta : P.LeafMeta
  /-- Fixed-capacity `nLow depth` spillover memory slots. -/
  slots : Fin (P.nLow P.depth) →
    Fin (2 ^ Spillover.memBits (P.quotUniv P.depth * P.valBound) (P.nLow P.depth))
  deriving DecidableEq

/-- Underlying `Minimap.FixedEncoded` representation of a `LeafNode`. -/
@[expose]
def LeafNode.toFixedEncoded (ln : P.LeafNode) :
    Minimap.FixedEncoded (2 ^ P.idBits P.depth) (P.nLow P.depth)
      (P.quotUniv P.depth * P.valBound) where
  header := ln.leafMeta.header
  slots := ln.slots

/-- Construct a `LeafNode` from `seed`, `wait`, and a `Minimap.FixedEncoded` state. -/
@[expose]
def LeafNode.ofFixedEncoded (seed : P.NodeSeed P.depth)
    (wait : WaitingList (P.idBits P.depth) (P.idBits (P.depth - 1)) (P.waitCap P.depth))
    (enc : Minimap.FixedEncoded (2 ^ P.idBits P.depth) (P.nLow P.depth)
      (P.quotUniv P.depth * P.valBound)) : P.LeafNode where
  leafMeta := { seed := seed, wait := wait, header := enc.header }
  slots := enc.slots

/-- Inner-node metadata (`2 ≤ ℓ < depth`, `Section 5.6`): hash seed, waiting list, and
`StorageTableMeta` (independent of `quotUniv ℓ` and `valBound`). -/
structure InnerMeta (ℓ : ℕ) where
  /-- Per-node hash seed at level `ℓ`. -/
  seed : P.NodeSeed ℓ
  /-- Waiting list of capacity `waitCap ℓ`. -/
  wait : WaitingList (P.idBits ℓ) (P.idBits (ℓ - 1)) (P.waitCap ℓ)
  /-- Active-ID slot metadata of the node's storage table. -/
  tableMeta : StorageTableMeta (P.idBits ℓ) (P.tableCap ℓ)
  deriving DecidableEq

/-- Inner node (`2 ≤ ℓ < depth`) combining `InnerMeta` with `tableCap ℓ` `(quot, val)` payload
slots. -/
structure InnerNode (ℓ : ℕ) where
  /-- Per-node hash seed at level `ℓ`. -/
  seed : P.NodeSeed ℓ
  /-- Waiting list of capacity `waitCap ℓ`. -/
  wait : WaitingList (P.idBits ℓ) (P.idBits (ℓ - 1)) (P.waitCap ℓ)
  /-- Full storage table (`tableMeta` + `(quot, val)` payload). -/
  table : StorageTable (P.idBits ℓ) (P.tableCap ℓ) (P.quotUniv ℓ) P.valBound
  deriving DecidableEq

/-- Project `InnerNode` to its Section 5.6 metadata `InnerMeta`. -/
def InnerNode.toMeta {ℓ : ℕ} (nd : P.InnerNode ℓ) : P.InnerMeta ℓ where
  seed := nd.seed
  wait := nd.wait
  tableMeta := nd.table.tableMeta

/-- Root-node metadata (`ℓ = 1`, `Section 5.6`): hash seed and `StorageTableMeta` (no waiting list
at `ℓ = 1`). -/
structure RootMeta where
  /-- Per-node hash seed at `ℓ = 1`. -/
  seed : P.NodeSeed 1
  /-- Active-ID slot metadata of the root storage table. -/
  tableMeta : StorageTableMeta (P.idBits 1) (P.tableCap 1)
  deriving DecidableEq

/-- Root node (`ℓ = 1`), storing `(quot, val)` inline via `StorageTable` in the pure tree model
(while the Section 5 layout bit budget arithmetic in `BitBudget.lean` accounts for a shared root
value pool). -/
structure RootNode where
  /-- Per-node hash seed at `ℓ = 1`. -/
  seed : P.NodeSeed 1
  /-- Full root storage table (`tableMeta` + `(quot, val)` payload). -/
  table : StorageTable (P.idBits 1) (P.tableCap 1) (P.quotUniv 1) P.valBound
  deriving DecidableEq

/-- Project `RootNode` to its Section 5.6 metadata `RootMeta`. -/
def RootNode.toMeta (nd : P.RootNode) : P.RootMeta where
  seed := nd.seed
  tableMeta := nd.table.tableMeta

/-- When all leaf minimaps (`nLow depth` keys each) and inner storage tables (`tableCap ℓ` keys
each) are at full capacity and total active keys `totalActive ≤ cap`, total keys stored across all
`N_1` root tables never exceed `P.rootValPoolCap`. -/
theorem rootKeys_le_rootValPoolCap {rootKeys totalActive : ℕ}
    (hpart : P.numNodes P.depth * P.nLow P.depth +
      (∑ ℓ ∈ Finset.Ico 2 P.depth, P.numNodes ℓ * P.tableCap ℓ) + rootKeys = totalActive)
    (hcap : totalActive ≤ P.cap) :
    rootKeys ≤ P.rootValPoolCap := by
  rw [P.leaf_add_inner_slots_eq] at hpart
  dsimp only [rootValPoolCap]
  omega

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
