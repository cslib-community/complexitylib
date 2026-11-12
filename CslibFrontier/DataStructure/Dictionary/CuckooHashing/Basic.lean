/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Ring

/-!
# Pure cuckoo tables, displacement, and replay

This module defines the pure two-table cuckoo model used by the graph analysis and the Word-RAM
implementation. It has no dependency on a machine model. The table scale and eviction cap are the
parameters used by the quantitative analysis; `SlotEntry`, `PureTable`, `WellPlaced`, `pureEvict`,
and `pureReplay` describe table contents and insertion-order replay independently of memory layout.

`GoodForSet` requires successful replay for every duplicate-free insertion order in a set.
`cuckooWalkRounds` is the supremum of the displacement rounds over every `ValidPlacement` of that
set and every allocation index. These are original strengthened sufficient notions inspired by
Pagh and Rodler [PaghRodler2004], Section 2.3 (8 December 2003 manuscript, pp. 6–10): Lemma 1 on
p. 7 concerns the distinct-subsequence structure of displacement walks, Eq. (3) on p. 9 bounds
expected displacement iterations, and pp. 9–10 analyze rehashing. The chosen sub-table size
`2 ^ tableBits n_max ≥ 32 * max n_max 4` is a stronger load condition than their
`m ≥ (1 + ε) n`.

## Main definitions

* `tableBits`, `tableSize`, `maxEvictions`, `cuckooK`: table scale, eviction cap, and required
  independence level.
* `SlotEntry`, `PureTable`, `WellPlaced`, `lookupEntry`, `pureEvictRound`, `pureEvict`,
  `pureReplay`:
  pure two-table state, lookup, displacement, and replay.
* `GoodForSet`, `ValidPlacement`, `cuckooWalkRounds`, `survivingSeeds`: uniform replay goodness,
  worst-case walk counts, and the set of successful replay seeds.

## Main results

* `pureReplay_append_singleton`, `pureReplay_lookupEntry_of_mem`: incremental insertion agrees
  with replay, and lookup recovers the inserted key's allocation index.
* `survivingSeeds_append_subset`, `mem_survivingSeeds_of_goodForSet`: surviving replay seeds shrink
  on insertion, and set-level goodness implies successful replay.
* `pureReplay_isSome_of_length_le_two`: replay of at most two keys succeeds for every hash pair
  with a positive eviction cap.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, pp. 6–10).
-/

public section

namespace Cslib.DataStructure.Dictionary.CuckooHashing

open scoped Finset

/-! ### Section 1: Table scale and eviction cap parameters -/

/-- Sub-table bit-width `M = ⌈log₂ (32 * max n_max 4)⌉`, ensuring each of the two cuckoo sub-tables
has size `m = 2 ^ M ≥ 32 * max n_max 4`. -/
@[expose]
def tableBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (32 * max n_max 4)

/-- Sub-table capacity `m = 2 ^ tableBits n_max`. -/
@[expose]
def tableSize (n_max : ℕ) : ℕ :=
  2 ^ tableBits n_max

/-- Maximum number of two-table cuckoo displacement rounds `6 * (⌈log₂ max(n_max, 2)⌉ + 2)` before
triggering a full-table rehash. -/
@[expose]
def maxEvictions (n_max : ℕ) : ℕ :=
  6 * (Nat.clog 2 (max n_max 2) + 2)

theorem seven_le_tableBits (n_max : ℕ) : 7 ≤ tableBits n_max := by
  unfold tableBits
  have h128 : 128 ≤ 32 * max n_max 4 := by omega
  have h7 : Nat.clog 2 128 = 7 := by decide
  rw [← h7]
  exact Nat.clog_mono_right 2 h128

theorem two_le_tableBits (n_max : ℕ) : 2 ≤ tableBits n_max := by
  have := seven_le_tableBits n_max
  omega

theorem tableBits_pos (n_max : ℕ) : 0 < tableBits n_max := by
  have := seven_le_tableBits n_max
  omega

theorem tableBits_le (n_max : ℕ) : tableBits n_max ≤ Nat.clog 2 (max n_max 4) + 5 := by
  unfold tableBits
  refine Nat.clog_le_of_le_pow ?_
  calc 32 * max n_max 4
      ≤ 32 * 2 ^ Nat.clog 2 (max n_max 4) :=
        Nat.mul_le_mul_left 32 (Nat.le_pow_clog (by decide) _)
    _ = 2 ^ (Nat.clog 2 (max n_max 4) + 5) := by ring

theorem thirtyTwo_mul_max_le_tableSize (n_max : ℕ) :
    32 * max n_max 4 ≤ tableSize n_max := by
  unfold tableSize tableBits
  exact Nat.le_pow_clog (by decide) _

theorem four_mul_max_le_tableSize (n_max : ℕ) :
    max (4 * n_max) 4 ≤ tableSize n_max :=
  le_trans (by omega) (thirtyTwo_mul_max_le_tableSize n_max)

theorem four_mul_le_tableSize (n_max : ℕ) : 4 * n_max ≤ tableSize n_max :=
  le_trans (le_max_left _ _) (four_mul_max_le_tableSize n_max)

theorem four_le_tableSize (n_max : ℕ) : 4 ≤ tableSize n_max :=
  le_trans (le_max_right _ _) (four_mul_max_le_tableSize n_max)

theorem tableSize_pos (n_max : ℕ) : 0 < tableSize n_max := by
  have := four_le_tableSize n_max
  omega

theorem tableSize_le_sixtyFour_mul_max (n_max : ℕ) :
    tableSize n_max ≤ 64 * max n_max 4 := by
  have h1 : tableBits n_max ≤ Nat.log 2 (max n_max 4) + 6 := by
    have hle := tableBits_le n_max
    have hclog : Nat.clog 2 (max n_max 4) ≤ Nat.log 2 (max n_max 4) + 1 :=
      Nat.clog_le_of_le_pow (le_of_lt (Nat.lt_pow_succ_log_self (by decide) _))
    omega
  calc tableSize n_max
      = 2 ^ tableBits n_max := rfl
    _ ≤ 2 ^ (Nat.log 2 (max n_max 4) + 6) := Nat.pow_le_pow_right (by decide) h1
    _ = 64 * 2 ^ Nat.log 2 (max n_max 4) := by ring
    _ ≤ 64 * max n_max 4 := Nat.mul_le_mul_left 64 (Nat.pow_log_le_self 2 (by omega))

theorem eighteen_le_maxEvictions (n_max : ℕ) : 18 ≤ maxEvictions n_max := by
  unfold maxEvictions
  have h1 : 1 ≤ Nat.clog 2 (max n_max 2) := by
    have h2 : 2 ≤ max n_max 2 := le_max_right _ _
    have hc : Nat.clog 2 2 = 1 := by decide
    rw [← hc]
    exact Nat.clog_mono_right 2 h2
  omega

theorem maxEvictions_pos (n_max : ℕ) : 0 < maxEvictions n_max := by
  have := eighteen_le_maxEvictions n_max
  omega

theorem maxEvictions_le_thirtyTwo_mul_max (n_max : ℕ) :
    maxEvictions n_max ≤ 32 * max n_max 4 := by
  have hclog : Nat.clog 2 (max n_max 2) ≤ max n_max 2 :=
    (Nat.clog_le_iff_le_pow (by decide)).mpr (Nat.le_of_lt (max n_max 2).lt_two_pow_self)
  unfold maxEvictions
  omega

theorem maxEvictions_le_tableSize (n_max : ℕ) :
    maxEvictions n_max ≤ tableSize n_max :=
  le_trans (maxEvictions_le_thirtyTwo_mul_max n_max) (thirtyTwo_mul_max_le_tableSize n_max)

/-- Independence parameter `k = 2 * maxEvictions n_max + 2` required by the two-table cuckoo hashing
analysis on eviction walks of length up to `maxEvictions n_max`. -/
@[expose]
def cuckooK (n_max : ℕ) : ℕ :=
  2 * maxEvictions n_max + 2

theorem thirtyEight_le_cuckooK (n_max : ℕ) : 38 ≤ cuckooK n_max := by
  have := eighteen_le_maxEvictions n_max
  unfold cuckooK
  omega

/-! ### Section 2: Pure two-table cuckoo displacement and replay model -/

/-- A stored slot entry in one of the two cuckoo sub-tables, recording a key `key : Fin U` and its
allocation index `idx : ℕ` in the insertion-order arrays `insKeys` / `insVals`. -/
structure SlotEntry (U : ℕ) where
  /-- Stored dictionary key. -/
  key : Fin U
  /-- Index into `insKeys` and `insVals`. -/
  idx : ℕ
  deriving DecidableEq, Repr

/-- Pure state of the two cuckoo sub-tables `T₁` and `T₂`, each of size `m`. -/
structure PureTable (U m : ℕ) where
  /-- First cuckoo sub-table `T₁`. -/
  t1 : Fin m → Option (SlotEntry U)
  /-- Second cuckoo sub-table `T₂`. -/
  t2 : Fin m → Option (SlotEntry U)

/-- The empty cuckoo table pair in which every slot of `T₁` and `T₂` is `none`. -/
@[expose]
def PureTable.empty (U m : ℕ) : PureTable U m where
  t1 := fun _ => none
  t2 := fun _ => none

/-- Entry `e` occupies some slot of `T₁` or `T₂`. -/
@[expose]
def EntryIn {U m : ℕ} (tbl : PureTable U m) (e : SlotEntry U) : Prop :=
  (∃ i, tbl.t1 i = some e) ∨ (∃ i, tbl.t2 i = some e)

/-- Key `k` is present in some slot of `T₁` or `T₂`. -/
@[expose]
def HasKey {U m : ℕ} (tbl : PureTable U m) (k : Fin U) : Prop :=
  ∃ e, EntryIn tbl e ∧ e.key = k

/-- Well-placed cuckoo table invariant under hash pair `(h₁, h₂)`:
every entry in `T₁` sits at its `h₁`-home slot, every entry in `T₂` sits at its `h₂`-home slot,
and no key appears simultaneously in both `T₁` and `T₂`. -/
structure WellPlaced {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (tbl : PureTable U m) : Prop where
  /-- Every entry in `T₁` is stored at index `h₁ e.key`. -/
  t1_home : ∀ i e, tbl.t1 i = some e → h₁ e.key = i
  /-- Every entry in `T₂` is stored at index `h₂ e.key`. -/
  t2_home : ∀ i e, tbl.t2 i = some e → h₂ e.key = i
  /-- No key is present in both `T₁` and `T₂`. -/
  disjoint_keys : ∀ i₁ i₂ e₁ e₂, tbl.t1 i₁ = some e₁ → tbl.t2 i₂ = some e₂ → e₁.key ≠ e₂.key

theorem wellPlaced_empty {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    WellPlaced h₁ h₂ (PureTable.empty U m) where
  t1_home := by intro _ _ h; cases h
  t2_home := by intro _ _ h; cases h
  disjoint_keys := by intro _ _ _ _ h _; cases h

@[simp]
theorem not_entryIn_empty {U m : ℕ} (e : SlotEntry U) :
    ¬ EntryIn (PureTable.empty U m) e := by
  rintro (⟨i, h⟩ | ⟨i, h⟩) <;> cases h

@[simp]
theorem not_hasKey_empty {U m : ℕ} (k : Fin U) :
    ¬ HasKey (PureTable.empty U m) k := by
  rintro ⟨e, h, _⟩
  exact not_entryIn_empty e h

/-- Two-probe cuckoo lookup for key `u`: probes `T₁[h₁ u]` first, then `T₂[h₂ u]`. -/
@[expose]
def lookupEntry {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (tbl : PureTable U m) (u : Fin U) :
    Option (SlotEntry U) :=
  match tbl.t1 (h₁ u) with
  | some e₁ =>
    if e₁.key = u then some e₁
    else
      match tbl.t2 (h₂ u) with
      | some e₂ => if e₂.key = u then some e₂ else none
      | none => none
  | none =>
    match tbl.t2 (h₂ u) with
    | some e₂ => if e₂.key = u then some e₂ else none
    | none => none

theorem WellPlaced.entryIn_iff_home {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    (hwp : WellPlaced h₁ h₂ tbl) (e : SlotEntry U) :
    EntryIn tbl e ↔ tbl.t1 (h₁ e.key) = some e ∨ tbl.t2 (h₂ e.key) = some e := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · left; rw [hwp.t1_home i e hi]; exact hi
    · right; rw [hwp.t2_home i e hi]; exact hi
  · rintro (h | h)
    · exact Or.inl ⟨h₁ e.key, h⟩
    · exact Or.inr ⟨h₂ e.key, h⟩

theorem WellPlaced.entry_unique_of_key_eq {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    (hwp : WellPlaced h₁ h₂ tbl) {e₁ e₂ : SlotEntry U}
    (h₁in : EntryIn tbl e₁) (h₂in : EntryIn tbl e₂) (hk : e₁.key = e₂.key) :
    e₁ = e₂ := by
  rcases (hwp.entryIn_iff_home e₁).mp h₁in with ht1 | ht2 <;>
    rcases (hwp.entryIn_iff_home e₂).mp h₂in with hs1 | hs2
  · rw [hk] at ht1
    exact Option.some.inj (ht1.symm.trans hs1)
  · exfalso
    exact hwp.disjoint_keys _ _ _ _ ht1 hs2 hk
  · exfalso
    exact hwp.disjoint_keys _ _ _ _ hs1 ht2 hk.symm
  · rw [hk] at ht2
    exact Option.some.inj (ht2.symm.trans hs2)

theorem WellPlaced.lookupEntry_eq_some_iff {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    (hwp : WellPlaced h₁ h₂ tbl) (u : Fin U) (e : SlotEntry U) :
    lookupEntry h₁ h₂ tbl u = some e ↔ EntryIn tbl e ∧ e.key = u := by
  rw [hwp.entryIn_iff_home]
  unfold lookupEntry
  have hsecond :
      (match tbl.t2 (h₂ u) with
        | some e₂ => if e₂.key = u then some e₂ else none
        | none => none) = some e →
        (tbl.t1 (h₁ e.key) = some e ∨ tbl.t2 (h₂ e.key) = some e) ∧ e.key = u := by
    cases ht2 : tbl.t2 (h₂ u) with
    | none => intro h; cases h
    | some e₂ =>
      dsimp only
      split_ifs with hk₂
      · intro h; injection h with h; subst h; exact ⟨Or.inr (by rw [hk₂]; exact ht2), hk₂⟩
      · intro h; cases h
  constructor
  · cases ht1 : tbl.t1 (h₁ u) with
    | none => exact hsecond
    | some e₁ =>
      dsimp only
      split_ifs with hk₁
      · intro h; injection h with h; subst h; exact ⟨Or.inl (by rw [hk₁]; exact ht1), hk₁⟩
      · exact hsecond
  · rintro ⟨ht | ht, rfl⟩
    · rw [ht]; simp
    · rw [ht]
      cases ht1 : tbl.t1 (h₁ e.key) with
      | none => simp
      | some e₁ =>
        have hne : e₁.key ≠ e.key := hwp.disjoint_keys _ _ _ _ ht1 ht
        simp [hne]

theorem WellPlaced.lookupEntry_eq_none_iff {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    (hwp : WellPlaced h₁ h₂ tbl) (u : Fin U) :
    lookupEntry h₁ h₂ tbl u = none ↔ ¬ HasKey tbl u := by
  rw [Option.eq_none_iff_forall_not_mem]
  constructor
  · intro hall ⟨e, hin, hk⟩
    exact hall e ((hwp.lookupEntry_eq_some_iff u e).mpr ⟨hin, hk⟩)
  · intro hno e he
    exact hno ⟨e, (hwp.lookupEntry_eq_some_iff u e).mp he⟩

/-- Place entry `e` into `T₁[h₁ e.key]`, returning the updated table and any displaced entry. -/
@[expose]
def putT1 {U m : ℕ} (h₁ : Fin U → Fin m) (tbl : PureTable U m) (e : SlotEntry U) :
    PureTable U m × Option (SlotEntry U) :=
  let i₁ := h₁ e.key
  ({ tbl with t1 := Function.update tbl.t1 i₁ (some e) }, tbl.t1 i₁)

/-- Place entry `e` into `T₂[h₂ e.key]`, returning the updated table and any displaced entry. -/
@[expose]
def putT2 {U m : ℕ} (h₂ : Fin U → Fin m) (tbl : PureTable U m) (e : SlotEntry U) :
    PureTable U m × Option (SlotEntry U) :=
  let i₂ := h₂ e.key
  ({ tbl with t2 := Function.update tbl.t2 i₂ (some e) }, tbl.t2 i₂)

/-- One two-table displacement round: places `e` in `T₁[h₁ e.key]`; if that slot was occupied by
`e₁`, places `e₁` in `T₂[h₂ e₁.key]` and returns any entry displaced from `T₂`. -/
@[expose]
def pureEvictRound {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (tbl : PureTable U m) (e : SlotEntry U) :
    PureTable U m × Option (SlotEntry U) :=
  match (putT1 h₁ tbl e).2 with
  | none => ((putT1 h₁ tbl e).1, none)
  | some e₁ => putT2 h₂ (putT1 h₁ tbl e).1 e₁

theorem putT1_wellPlaced {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m} {e : SlotEntry U}
    (hwp : WellPlaced h₁ h₂ tbl) (hno : ¬ HasKey tbl e.key) :
    WellPlaced h₁ h₂ (putT1 h₁ tbl e).1 where
  t1_home := by
    intro i d hd
    dsimp only [putT1] at hd
    by_cases hi : i = h₁ e.key
    · subst hi
      rw [Function.update_self] at hd
      injection hd with hd
      subst hd; rfl
    · rw [Function.update_of_ne hi] at hd
      exact hwp.t1_home i d hd
  t2_home := hwp.t2_home
  disjoint_keys := by
    intro i₁ i₂ e₁ e₂ ht1 ht2
    dsimp only [putT1] at ht1 ht2
    by_cases hi₁ : i₁ = h₁ e.key
    · subst hi₁
      rw [Function.update_self] at ht1
      injection ht1 with ht1; subst ht1
      intro heq
      exact hno ⟨e₂, Or.inr ⟨i₂, ht2⟩, heq.symm⟩
    · rw [Function.update_of_ne hi₁] at ht1
      exact hwp.disjoint_keys i₁ i₂ e₁ e₂ ht1 ht2

theorem putT1_entryIn_none {U m : ℕ} {h₁ : Fin U → Fin m} {tbl : PureTable U m}
    {e : SlotEntry U} (hold : (putT1 h₁ tbl e).2 = none) (d : SlotEntry U) :
    EntryIn (putT1 h₁ tbl e).1 d ↔ EntryIn tbl d ∨ d = e := by
  have ht1_none : tbl.t1 (h₁ e.key) = none := hold
  dsimp only [EntryIn, putT1]
  rw [Function.exists_update_iff tbl.t1 (a := h₁ e.key) (b := some e)
    (p := fun _ slot => slot = some d), Option.some.injEq]
  constructor
  · rintro ((hd | ⟨i, _, hi⟩) | hi)
    · exact Or.inr hd.symm
    · exact Or.inl (Or.inl ⟨i, hi⟩)
    · exact Or.inl (Or.inr hi)
  · rintro ((⟨i, hi⟩ | hi) | hd)
    · have hie : i ≠ h₁ e.key := by
        intro h; subst h; rw [ht1_none] at hi; cases hi
      exact Or.inl (Or.inr ⟨i, hie, hi⟩)
    · exact Or.inr hi
    · exact Or.inl (Or.inl hd.symm)

theorem putT1_some_spec {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    {e e₁ : SlotEntry U} (hwp : WellPlaced h₁ h₂ tbl) (hno : ¬ HasKey tbl e.key)
    (hold : (putT1 h₁ tbl e).2 = some e₁) :
    ¬ HasKey (putT1 h₁ tbl e).1 e₁.key ∧
      (∀ d, EntryIn (putT1 h₁ tbl e).1 d ∨ d = e₁ ↔ EntryIn tbl d ∨ d = e) := by
  have ht1_some : tbl.t1 (h₁ e.key) = some e₁ := hold
  have hhome₁ : h₁ e₁.key = h₁ e.key := hwp.t1_home (h₁ e.key) e₁ ht1_some
  have hne_key : e₁.key ≠ e.key := by
    intro heq
    exact hno ⟨e₁, Or.inl ⟨h₁ e.key, ht1_some⟩, heq⟩
  refine ⟨?_, fun d => ?_⟩
  · rintro ⟨d, (⟨i, hi⟩ | ⟨i, hi⟩), hdk⟩
    · dsimp only [putT1] at hi
      by_cases hie : i = h₁ e.key
      · subst hie; rw [Function.update_self] at hi
        injection hi with hi; subst hi
        exact hne_key hdk.symm
      · rw [Function.update_of_ne hie] at hi
        have hi_eq := hwp.t1_home i d hi
        rw [hdk, hhome₁] at hi_eq
        exact hie hi_eq.symm
    · exact hwp.disjoint_keys (h₁ e.key) i e₁ d ht1_some hi hdk.symm
  · dsimp only [EntryIn, putT1]
    rw [Function.exists_update_iff tbl.t1 (a := h₁ e.key) (b := some e)
      (p := fun _ slot => slot = some d), Option.some.injEq]
    constructor
    · rintro (((hd | ⟨i, _, hi⟩) | hi) | hd)
      · exact Or.inr hd.symm
      · exact Or.inl (Or.inl ⟨i, hi⟩)
      · exact Or.inl (Or.inr hi)
      · subst hd
        exact Or.inl (Or.inl ⟨h₁ e.key, ht1_some⟩)
    · rintro ((⟨i, hi⟩ | hi) | hd)
      · by_cases hie : i = h₁ e.key
        · subst hie; rw [ht1_some] at hi; exact Or.inr (Option.some.inj hi).symm
        · exact Or.inl (Or.inl (Or.inr ⟨i, hie, hi⟩))
      · exact Or.inl (Or.inr hi)
      · exact Or.inl (Or.inl (Or.inl hd.symm))

theorem putT2_wellPlaced {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m} {e : SlotEntry U}
    (hwp : WellPlaced h₁ h₂ tbl) (hno : ¬ HasKey tbl e.key) :
    WellPlaced h₁ h₂ (putT2 h₂ tbl e).1 where
  t1_home := hwp.t1_home
  t2_home := by
    intro i d hd
    dsimp only [putT2] at hd
    by_cases hi : i = h₂ e.key
    · subst hi; rw [Function.update_self] at hd
      injection hd with hd; subst hd; rfl
    · rw [Function.update_of_ne hi] at hd
      exact hwp.t2_home i d hd
  disjoint_keys := by
    intro i₁ i₂ e₁ e₂ ht1 ht2
    dsimp only [putT2] at ht1 ht2
    by_cases hi₂ : i₂ = h₂ e.key
    · subst hi₂; rw [Function.update_self] at ht2
      injection ht2 with ht2; subst ht2
      intro heq
      exact hno ⟨e₁, Or.inl ⟨i₁, ht1⟩, heq⟩
    · rw [Function.update_of_ne hi₂] at ht2
      exact hwp.disjoint_keys i₁ i₂ e₁ e₂ ht1 ht2

theorem putT2_entryIn_none {U m : ℕ} {h₂ : Fin U → Fin m} {tbl : PureTable U m}
    {e : SlotEntry U} (hold : (putT2 h₂ tbl e).2 = none) (d : SlotEntry U) :
    EntryIn (putT2 h₂ tbl e).1 d ↔ EntryIn tbl d ∨ d = e := by
  have ht2_none : tbl.t2 (h₂ e.key) = none := hold
  dsimp only [EntryIn, putT2]
  rw [Function.exists_update_iff tbl.t2 (a := h₂ e.key) (b := some e)
    (p := fun _ slot => slot = some d), Option.some.injEq]
  constructor
  · rintro (hi | (hd | ⟨i, _, hi⟩))
    · exact Or.inl (Or.inl hi)
    · exact Or.inr hd.symm
    · exact Or.inl (Or.inr ⟨i, hi⟩)
  · rintro ((hi | ⟨i, hi⟩) | hd)
    · exact Or.inl hi
    · have hie : i ≠ h₂ e.key := by
        intro h; subst h; rw [ht2_none] at hi; cases hi
      exact Or.inr (Or.inr ⟨i, hie, hi⟩)
    · exact Or.inr (Or.inl hd.symm)

theorem putT2_some_spec {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {tbl : PureTable U m}
    {e e₂ : SlotEntry U} (hwp : WellPlaced h₁ h₂ tbl) (hno : ¬ HasKey tbl e.key)
    (hold : (putT2 h₂ tbl e).2 = some e₂) :
    ¬ HasKey (putT2 h₂ tbl e).1 e₂.key ∧
      (∀ d, EntryIn (putT2 h₂ tbl e).1 d ∨ d = e₂ ↔ EntryIn tbl d ∨ d = e) := by
  have ht2_some : tbl.t2 (h₂ e.key) = some e₂ := hold
  have hhome₂ : h₂ e₂.key = h₂ e.key := hwp.t2_home (h₂ e.key) e₂ ht2_some
  have hne_key : e₂.key ≠ e.key := by
    intro heq
    exact hno ⟨e₂, Or.inr ⟨h₂ e.key, ht2_some⟩, heq⟩
  refine ⟨?_, fun d => ?_⟩
  · rintro ⟨d, (⟨i, hi⟩ | ⟨i, hi⟩), hdk⟩
    · exact hwp.disjoint_keys i (h₂ e.key) d e₂ hi ht2_some hdk
    · dsimp only [putT2] at hi
      by_cases hie : i = h₂ e.key
      · subst hie; rw [Function.update_self] at hi
        injection hi with hi; subst hi
        exact hne_key hdk.symm
      · rw [Function.update_of_ne hie] at hi
        have hi_eq := hwp.t2_home i d hi
        rw [hdk, hhome₂] at hi_eq
        exact hie hi_eq.symm
  · dsimp only [EntryIn, putT2]
    rw [Function.exists_update_iff tbl.t2 (a := h₂ e.key) (b := some e)
      (p := fun _ slot => slot = some d), Option.some.injEq]
    constructor
    · rintro ((hi | (hd | ⟨i, _, hi⟩)) | hd)
      · exact Or.inl (Or.inl hi)
      · exact Or.inr hd.symm
      · exact Or.inl (Or.inr ⟨i, hi⟩)
      · subst hd
        exact Or.inl (Or.inr ⟨h₂ e.key, ht2_some⟩)
    · rintro ((hi | ⟨i, hi⟩) | hd)
      · exact Or.inl (Or.inl hi)
      · by_cases hie : i = h₂ e.key
        · subst hie; rw [ht2_some] at hi; exact Or.inr (Option.some.inj hi).symm
        · exact Or.inl (Or.inr (Or.inr ⟨i, hie, hi⟩))
      · exact Or.inl (Or.inr (Or.inl hd.symm))

/-- Run up to `fuel` two-table cuckoo displacement rounds starting with displaced entry `e`. -/
@[expose]
def pureEvict {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    ℕ → PureTable U m → SlotEntry U → Option (PureTable U m)
  | 0, _, _ => none
  | fuel + 1, tbl, e =>
    match pureEvictRound h₁ h₂ tbl e with
    | (tbl', none) => some tbl'
    | (tbl', some e') => pureEvict h₁ h₂ fuel tbl' e'

/-- Number of displacement rounds executed by `pureEvict` before either settling or exhausting
`fuel`. -/
@[expose]
def evictRounds {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    ℕ → PureTable U m → SlotEntry U → ℕ
  | 0, _, _ => 0
  | fuel + 1, tbl, e =>
    match pureEvictRound h₁ h₂ tbl e with
    | (_, none) => 1
    | (tbl', some e') => 1 + evictRounds h₁ h₂ fuel tbl' e'

theorem evictRounds_le {U m : ℕ} (h₁ h₂ : Fin U → Fin m) :
    ∀ (fuel : ℕ) (tbl : PureTable U m) (e : SlotEntry U),
      evictRounds h₁ h₂ fuel tbl e ≤ fuel
  | 0, _, _ => le_rfl
  | fuel + 1, tbl, e => by
    unfold evictRounds
    cases h : pureEvictRound h₁ h₂ tbl e with
    | mk tbl' oe =>
      cases oe with
      | none => dsimp only; omega
      | some e' =>
        dsimp only
        have ih := evictRounds_le h₁ h₂ fuel tbl' e'
        omega

theorem pureEvict_spec {U m : ℕ} {h₁ h₂ : Fin U → Fin m} :
    ∀ (fuel : ℕ) {tbl tbl' : PureTable U m} {e : SlotEntry U},
      WellPlaced h₁ h₂ tbl → ¬ HasKey tbl e.key →
      pureEvict h₁ h₂ fuel tbl e = some tbl' →
      WellPlaced h₁ h₂ tbl' ∧ (∀ d, EntryIn tbl' d ↔ EntryIn tbl d ∨ d = e)
  | 0, _, _, _, _, _, h => by cases h
  | fuel + 1, tbl, tbl', e, hwp, hno, hev => by
    unfold pureEvict pureEvictRound at hev
    have hwp₁ : WellPlaced h₁ h₂ (putT1 h₁ tbl e).1 := putT1_wellPlaced hwp hno
    cases hold₁ : (putT1 h₁ tbl e).2 with
    | none =>
      rw [hold₁] at hev
      injection hev with hev; subst hev
      exact ⟨hwp₁, putT1_entryIn_none hold₁⟩
    | some e₁ =>
      rw [hold₁] at hev
      dsimp only at hev
      obtain ⟨hno₁, hent₁⟩ := putT1_some_spec hwp hno hold₁
      have hwp₂ : WellPlaced h₁ h₂ (putT2 h₂ (putT1 h₁ tbl e).1 e₁).1 :=
        putT2_wellPlaced hwp₁ hno₁
      cases hold₂ : (putT2 h₂ (putT1 h₁ tbl e).1 e₁).2 with
      | none =>
        have hpair : putT2 h₂ (putT1 h₁ tbl e).1 e₁ =
            ((putT2 h₂ (putT1 h₁ tbl e).1 e₁).1, none) := Prod.ext rfl hold₂
        rw [hpair] at hev
        injection hev with hev; subst hev
        refine ⟨hwp₂, fun d => ?_⟩
        rw [putT2_entryIn_none hold₂ d, hent₁ d]
      | some e₂ =>
        have hpair : putT2 h₂ (putT1 h₁ tbl e).1 e₁ =
            ((putT2 h₂ (putT1 h₁ tbl e).1 e₁).1, some e₂) := Prod.ext rfl hold₂
        rw [hpair] at hev
        obtain ⟨hno₂, hent₂⟩ := putT2_some_spec hwp₁ hno₁ hold₂
        obtain ⟨hwp', hent'⟩ := pureEvict_spec fuel hwp₂ hno₂ hev
        refine ⟨hwp', fun d => ?_⟩
        rw [hent' d, hent₂ d, hent₁ d]

/-- Replay a list of distinct inserted keys `ks` in exact insertion order starting from
`PureTable.empty`. -/
@[expose]
def pureReplay {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (ks : List (Fin U)) :
    Option (PureTable U m) :=
  ks.zipIdx.foldlM (fun tbl p => pureEvict h₁ h₂ maxLoop tbl ⟨p.1, p.2⟩) (PureTable.empty U m)

@[simp]
theorem pureReplay_nil {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) :
    pureReplay h₁ h₂ maxLoop [] = some (PureTable.empty U m) := rfl

theorem pureReplay_append_singleton {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (ks : List (Fin U)) (u : Fin U) :
    pureReplay h₁ h₂ maxLoop (ks ++ [u]) =
      (pureReplay h₁ h₂ maxLoop ks).bind
        (fun tbl => pureEvict h₁ h₂ maxLoop tbl ⟨u, ks.length⟩) := by
  simp [pureReplay, List.zipIdx_append, List.foldlM_append]

private theorem foldlM_zipIdx_spec {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ} :
    ∀ (ks : List (Fin U)) (start : ℕ) {tbl₀ tbl : PureTable U m},
      WellPlaced h₁ h₂ tbl₀ →
      ks.Nodup →
      (∀ u ∈ ks, ¬ HasKey tbl₀ u) →
      (ks.zipIdx start).foldlM (fun t p => pureEvict h₁ h₂ maxLoop t ⟨p.1, p.2⟩) tbl₀ = some tbl →
      WellPlaced h₁ h₂ tbl ∧
        (∀ d, EntryIn tbl d ↔ EntryIn tbl₀ d ∨ (d.key, d.idx) ∈ ks.zipIdx start)
  | [], _, tbl₀, tbl, hwp₀, _, _, hfold => by
    injection hfold with h; subst h
    simp [hwp₀]
  | u :: ks, start, tbl₀, tbl, hwp₀, hnodup, hdisj, hfold => by
    simp only [List.zipIdx_cons, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at hfold
    obtain ⟨tbl₁, hev₁, hfold⟩ := hfold
    rw [List.nodup_cons] at hnodup
    have hno_u : ¬ HasKey tbl₀ u := hdisj u (List.mem_cons_self ..)
    obtain ⟨hwp₁, hent₁⟩ := pureEvict_spec maxLoop hwp₀ hno_u hev₁
    have hdisj₁ : ∀ w ∈ ks, ¬ HasKey tbl₁ w := by
      intro w hw ⟨d, hdin, hdk⟩
      rw [hent₁ d] at hdin
      rcases hdin with hdin₀ | rfl
      · exact hdisj w (List.mem_cons_of_mem u hw) ⟨d, hdin₀, hdk⟩
      · dsimp only at hdk
        subst hdk
        exact hnodup.1 hw
    obtain ⟨hwp, hent⟩ := foldlM_zipIdx_spec ks (start + 1) hwp₁ hnodup.2 hdisj₁ hfold
    refine ⟨hwp, fun d => ?_⟩
    rw [hent d, hent₁ d, List.zipIdx_cons, List.mem_cons]
    have heq : (d = ⟨u, start⟩) ↔ (d.key, d.idx) = (u, start) := by
      cases d; simp
    rw [heq, or_assoc]

theorem pureReplay_spec {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl) :
    WellPlaced h₁ h₂ tbl ∧
      (∀ d : SlotEntry U, EntryIn tbl d ↔ (d.key, d.idx) ∈ ks.zipIdx) := by
  obtain ⟨hwp, hent⟩ := foldlM_zipIdx_spec ks 0 (wellPlaced_empty h₁ h₂) hnodup
    (fun u _ => not_hasKey_empty u) hrep
  refine ⟨hwp, fun d => ?_⟩
  rw [hent d]
  simp

theorem pureReplay_hasKey_iff {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl) (u : Fin U) :
    HasKey tbl u ↔ u ∈ ks := by
  obtain ⟨_, hent⟩ := pureReplay_spec hnodup hrep
  constructor
  · rintro ⟨d, hdin, rfl⟩
    rw [hent, List.mem_zipIdx_iff_getElem?] at hdin
    exact List.mem_of_getElem? hdin
  · intro hu
    obtain ⟨idx, hlt, hget⟩ := List.mem_iff_getElem.mp hu
    refine ⟨⟨u, idx⟩, ?_, rfl⟩
    rw [hent, List.mem_zipIdx_iff_getElem?]
    simp [hlt, hget]

theorem pureReplay_lookupEntry_of_mem {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl)
    {idx : ℕ} (hlt : idx < ks.length) :
    lookupEntry h₁ h₂ tbl ks[idx] = some ⟨ks[idx], idx⟩ := by
  obtain ⟨hwp, hent⟩ := pureReplay_spec hnodup hrep
  rw [hwp.lookupEntry_eq_some_iff]
  refine ⟨?_, rfl⟩
  rw [hent, List.mem_zipIdx_iff_getElem?]
  simp [hlt]

theorem pureReplay_lookupEntry_of_notMem {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl)
    {u : Fin U} (hu : u ∉ ks) :
    lookupEntry h₁ h₂ tbl u = none := by
  obtain ⟨hwp, _⟩ := pureReplay_spec hnodup hrep
  rw [hwp.lookupEntry_eq_none_iff, pureReplay_hasKey_iff hnodup hrep]
  exact hu

/-! ### Section 3: Set-monotone cuckoo goodness, walk bounds, and conditional-uniform invariance -/

/-- Original strengthened sufficient goodness predicate: a hash pair `(h₁, h₂)` is good for key set
`S` with cap `maxLoop` if replaying every duplicate-free (`Nodup`) key list `ks` with `ks ⊆ S`
succeeds within `maxLoop` displacement rounds per insertion. -/
@[expose]
def GoodForSet {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (S : Finset (Fin U)) : Prop :=
  ∀ ks : List (Fin U), ks.Nodup → (∀ u ∈ ks, u ∈ S) →
    (pureReplay h₁ h₂ maxLoop ks).isSome

theorem GoodForSet.mono {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {S S' : Finset (Fin U)} (hsub : S ⊆ S') (hgood : GoodForSet h₁ h₂ maxLoop S') :
    GoodForSet h₁ h₂ maxLoop S :=
  fun ks hnodup hks => hgood ks hnodup fun u hu => hsub (hks u hu)

@[simp]
theorem goodForSet_empty {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) :
    GoodForSet h₁ h₂ maxLoop ∅ := by
  intro ks _ hks
  cases ks with
  | nil => simp
  | cons u _ => exfalso; exact Finset.notMem_empty u (hks u (List.mem_cons_self ..))

/-- Pure predicate that `tbl` is well-placed under `(h₁, h₂)` and every key in `tbl` belongs to
`S`. -/
@[expose]
def ValidPlacement {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (S : Finset (Fin U))
    (tbl : PureTable U m) : Prop :=
  WellPlaced h₁ h₂ tbl ∧ ∀ u, HasKey tbl u → u ∈ S

theorem pureReplay_validPlacement {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {S : Finset (Fin U)} {tbl : PureTable U m}
    (hnodup : ks.Nodup) (hsub : ∀ u ∈ ks, u ∈ S)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl) :
    ValidPlacement h₁ h₂ S tbl := by
  refine ⟨(pureReplay_spec hnodup hrep).1, fun u hu => ?_⟩
  exact hsub u ((pureReplay_hasKey_iff hnodup hrep u).mp hu)

/-- Original strengthened worst-case displacement round count: supremum (`sSup`) of `evictRounds`
to insert `u` over all `ValidPlacement`s of `S` under `(h₁, h₂)` with cap `maxLoop`. -/
@[expose]
noncomputable def cuckooWalkRounds {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (S : Finset (Fin U)) (u : Fin U) : ℕ :=
  sSup {r : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ S tbl ∧
    ∃ idx : ℕ, r = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩}

private theorem bddAbove_cuckooWalkRounds_set {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (S : Finset (Fin U)) (u : Fin U) :
    BddAbove {r : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ S tbl ∧
      ∃ idx : ℕ, r = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩} := by
  refine ⟨maxLoop, ?_⟩
  rintro r ⟨tbl, _, idx, rfl⟩
  exact evictRounds_le h₁ h₂ maxLoop tbl ⟨u, idx⟩

theorem evictRounds_le_cuckooWalkRounds {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {S : Finset (Fin U)} {tbl : PureTable U m} (hvp : ValidPlacement h₁ h₂ S tbl)
    (u : Fin U) (idx : ℕ) :
    evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩ ≤ cuckooWalkRounds h₁ h₂ maxLoop S u :=
  le_csSup (bddAbove_cuckooWalkRounds_set h₁ h₂ maxLoop S u) ⟨tbl, hvp, idx, rfl⟩

/-- `cuckooWalkRounds` is at most any common bound on the `evictRounds` of the valid placements
it ranges over (the supremum of the empty set is `0`). -/
private theorem cuckooWalkRounds_le_of_forall {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {S : Finset (Fin U)} {u : Fin U} {B : ℕ}
    (h : ∀ tbl, ValidPlacement h₁ h₂ S tbl → ∀ idx, evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩ ≤ B) :
    cuckooWalkRounds h₁ h₂ maxLoop S u ≤ B := by
  unfold cuckooWalkRounds
  refine csSup_le' ?_
  rintro r ⟨tbl, hvp, idx, rfl⟩
  exact h tbl hvp idx

theorem cuckooWalkRounds_le_maxLoop {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (S : Finset (Fin U)) (u : Fin U) :
    cuckooWalkRounds h₁ h₂ maxLoop S u ≤ maxLoop :=
  cuckooWalkRounds_le_of_forall fun tbl _ idx => evictRounds_le h₁ h₂ maxLoop tbl ⟨u, idx⟩

/-- In any valid placement of a key set `S` of cardinality at most `1`, if `T₁` contains an entry
`e₁`, then every slot of `T₂` is empty (by key disjointness between `T₁` and `T₂`). -/
theorem t2_eq_none_of_validPlacement_card_le_one {U m : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {tbl : PureTable U m} (hvp : ValidPlacement h₁ h₂ S tbl)
    (hcard : S.card ≤ 1) {i₁ : Fin m} {e₁ : SlotEntry U} (ht1 : tbl.t1 i₁ = some e₁)
    (i₂ : Fin m) : tbl.t2 i₂ = none := by
  cases ht2 : tbl.t2 i₂ with
  | none => rfl
  | some e₂ =>
    exfalso
    have he1 : e₁.key ∈ S := hvp.2 e₁.key ⟨e₁, Or.inl ⟨i₁, ht1⟩, rfl⟩
    have he2 : e₂.key ∈ S := hvp.2 e₂.key ⟨e₂, Or.inr ⟨i₂, ht2⟩, rfl⟩
    have heq : e₁.key = e₂.key := Finset.card_le_one_iff.mp hcard he1 he2
    exact hvp.1.disjoint_keys i₁ i₂ e₁ e₂ ht1 ht2 heq

/-- In any valid placement of a key set `S` of cardinality at most `1`, a single two-table
displacement round `pureEvictRound` always terminates without displacing an entry from `T₂`. -/
theorem pureEvictRound_snd_eq_none_of_card_le_one {U m : ℕ} {h₁ h₂ : Fin U → Fin m}
    {S : Finset (Fin U)} {tbl : PureTable U m} (hvp : ValidPlacement h₁ h₂ S tbl)
    (hcard : S.card ≤ 1) (e : SlotEntry U) :
    (pureEvictRound h₁ h₂ tbl e).2 = none := by
  unfold pureEvictRound
  cases hold₁ : (putT1 h₁ tbl e).2 with
  | none => rfl
  | some e₁ =>
    have ht1 : tbl.t1 (h₁ e.key) = some e₁ := hold₁
    exact t2_eq_none_of_validPlacement_card_le_one hvp hcard ht1 (h₂ e₁.key)

/-- Whenever `S.card ≤ 1`, inserting any key `u` into any valid placement of `S` completes in at
most `1` displacement round for every hash pair `(h₁, h₂)`. -/
theorem cuckooWalkRounds_le_one_of_card_le_one {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    {S : Finset (Fin U)} (hcard : S.card ≤ 1) (u : Fin U) :
    cuckooWalkRounds h₁ h₂ maxLoop S u ≤ 1 := by
  refine cuckooWalkRounds_le_of_forall fun tbl hvp idx => ?_
  cases maxLoop with
  | zero => exact Nat.zero_le _
  | succ k =>
    unfold evictRounds
    cases h : pureEvictRound h₁ h₂ tbl ⟨u, idx⟩ with
    | mk tbl' oe =>
      have hoe : oe = none := by
        have := pureEvictRound_snd_eq_none_of_card_le_one hvp hcard ⟨u, idx⟩
        rw [h] at this
        exact this
      subst hoe
      exact le_rfl

/-- Inserting into a valid placement of the empty set takes at most one displacement round. -/
theorem cuckooWalkRounds_empty {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (u : Fin U) :
    cuckooWalkRounds h₁ h₂ maxLoop ∅ u ≤ 1 :=
  cuckooWalkRounds_le_one_of_card_le_one h₁ h₂ maxLoop (by simp) u

/-- Finset of hash seeds `θ : Θ` under which insertion-order replay
`pureReplay (h₁ θ) (h₂ θ) maxLoop ks` succeeds without exhausting the displacement cap `maxLoop`. -/
@[expose]
noncomputable def survivingSeeds {Θ : Type*} [Fintype Θ] {U m : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (maxLoop : ℕ) (ks : List (Fin U)) : Finset Θ :=
  open scoped Classical in
  Finset.univ.filter fun θ => (pureReplay (h₁ θ) (h₂ θ) maxLoop ks).isSome

@[simp]
theorem mem_survivingSeeds {Θ : Type*} [Fintype Θ] {U m : ℕ}
    {h₁ h₂ : Θ → Fin U → Fin m} {maxLoop : ℕ} {ks : List (Fin U)} {θ : Θ} :
    θ ∈ survivingSeeds h₁ h₂ maxLoop ks ↔ (pureReplay (h₁ θ) (h₂ θ) maxLoop ks).isSome := by
  classical
  simp [survivingSeeds]

@[simp]
theorem survivingSeeds_nil {Θ : Type*} [Fintype Θ] {U m : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (maxLoop : ℕ) :
    survivingSeeds h₁ h₂ maxLoop [] = Finset.univ := by
  ext θ
  simp

theorem survivingSeeds_append_subset {Θ : Type*} [Fintype Θ] {U m : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (maxLoop : ℕ) (ks : List (Fin U)) (u : Fin U) :
    survivingSeeds h₁ h₂ maxLoop (ks ++ [u]) ⊆ survivingSeeds h₁ h₂ maxLoop ks := by
  intro θ hθ
  rw [mem_survivingSeeds, pureReplay_append_singleton] at hθ
  rw [mem_survivingSeeds]
  cases h : pureReplay (h₁ θ) (h₂ θ) maxLoop ks with
  | none => simp [h] at hθ
  | some _ => rfl

theorem mem_survivingSeeds_of_goodForSet {Θ : Type*} [Fintype Θ] {U m : ℕ}
    {h₁ h₂ : Θ → Fin U → Fin m} {maxLoop : ℕ} {ks : List (Fin U)} {S : Finset (Fin U)} {θ : Θ}
    (hnodup : ks.Nodup) (hsub : ∀ u ∈ ks, u ∈ S)
    (hgood : GoodForSet (h₁ θ) (h₂ θ) maxLoop S) :
    θ ∈ survivingSeeds h₁ h₂ maxLoop ks := by
  rw [mem_survivingSeeds]
  exact hgood ks hnodup hsub

/-- When `ks` has length at most `1` and `0 < maxLoop`, `pureReplay` succeeds for every hash pair
`(h₁, h₂)` in a single probe into `T₁`. -/
theorem pureReplay_isSome_of_length_le_one {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    {maxLoop : ℕ} (hloop : 0 < maxLoop) {ks : List (Fin U)} (hlen : ks.length ≤ 1) :
    (pureReplay h₁ h₂ maxLoop ks).isSome := by
  cases ks with
  | nil => simp
  | cons u rest =>
    cases rest with
    | nil =>
      cases maxLoop with
      | zero => omega
      | succ k =>
        simp [pureReplay, pureEvict, pureEvictRound, putT1, PureTable.empty]
    | cons v _ =>
      simp only [List.length_cons] at hlen
      omega

/-- When `ks` has length at most `2` and `0 < maxLoop`, `pureReplay` succeeds for every hash pair
`(h₁, h₂)` in at most `1` displacement round per key: the first key lands in `T₁`, and even if the
second key collides with the first in `T₁`, the displaced first key lands in `T₂`, which is
empty. -/
theorem pureReplay_isSome_of_length_le_two {U m : ℕ} (h₁ h₂ : Fin U → Fin m)
    {maxLoop : ℕ} (hloop : 0 < maxLoop) {ks : List (Fin U)} (hlen : ks.length ≤ 2) :
    (pureReplay h₁ h₂ maxLoop ks).isSome := by
  cases ks with
  | nil => simp
  | cons u rest =>
    cases rest with
    | nil => exact pureReplay_isSome_of_length_le_one h₁ h₂ hloop (by simp)
    | cons v rest₂ =>
      cases rest₂ with
      | nil =>
        have hrep₁ : (pureReplay h₁ h₂ maxLoop [u]).isSome :=
          pureReplay_isSome_of_length_le_one h₁ h₂ hloop (by simp)
        obtain ⟨tbl₁, htbl₁⟩ := Option.isSome_iff_exists.mp hrep₁
        have hvp₁ : ValidPlacement h₁ h₂ {u} tbl₁ :=
          pureReplay_validPlacement (List.nodup_singleton u)
            (fun x hx => by simp only [List.mem_singleton] at hx; simp [hx]) htbl₁
        have hcard₁ : ({u} : Finset (Fin U)).card ≤ 1 := by simp
        have hround := pureEvictRound_snd_eq_none_of_card_le_one hvp₁ hcard₁ ⟨v, 1⟩
        change (pureReplay h₁ h₂ maxLoop ([u] ++ [v])).isSome
        rw [pureReplay_append_singleton, htbl₁]
        dsimp only [Option.bind_eq_bind, Option.bind_some, List.length_singleton]
        cases maxLoop with
        | zero => omega
        | succ k =>
          unfold pureEvict
          cases hr : pureEvictRound h₁ h₂ tbl₁ ⟨v, 1⟩ with
          | mk tbl₂ oe =>
            rw [hr] at hround
            dsimp only at hround
            subst hround
            rfl
      | cons w _ =>
        simp only [List.length_cons] at hlen
        omega

end Cslib.DataStructure.Dictionary.CuckooHashing
