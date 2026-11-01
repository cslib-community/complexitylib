/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Hashing.KWise
public import Complexity.Algorithms.WordRAM.Hashing.Tabulation
public import Complexity.Computability.WordRAM.RegisterFrame
public import Complexity.DataStructure.HashFamily.WordRAM.DoubleTabulation
public import Complexity.Probability.PMF.Bind
public import Complexity.Probability.PMF.Map
public import Complexity.Probability.PMF.UniformSubset
public import Complexity.Probability.Uniform
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Cuckoo hash family, pure replay semantics, and regime-switched Word-RAM hashing

This module develops the pure displacement and replay model of Pagh and Rodler's two-table cuckoo
hashing scheme [PaghRodler2004] together with the regime-switched Word-RAM hash pair
`(evalHash1 c_exp n_max U M, evalHash2 c_exp n_max U M)` combining
`Cslib.Algorithms.WordRAM.Hashing.KWise` (`k = 2 * maxEvictions n_max + 2` for
`n_max < doubleTabThreshold c_exp`) and Mikkel Thorup's double tabulation
(`Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation`, [Thorup2013], for
`doubleTabThreshold c_exp ≤ n_max`).

## Primary-source mapping

* **Pagh and Rodler [PaghRodler2004]:** R. Pagh and F. F. Rodler, *"Cuckoo Hashing"*, author-hosted
  journal manuscript (8 December 2003, published in *Journal of Algorithms* 51(2):122–144, 2004),
  **Section 2.3 ("Analysis", manuscript pp. 6–10)**: **Lemma 1** (manuscript p. 7,
  distinct-subsequence structure of displacement walks when the cuckoo graph contains no component
  with more than one cycle), **Eq. (3) on manuscript p. 9** (expected displacement iterations
  `O(1)`), and **manuscript pp. 9–10** (rehash probability and amortized rebuild analysis in two
  tables of size `m ≥ (1 + ε) n`, where `m = 2 ^ M ≥ 32 * max n_max 4` here).
* **Thorup [Thorup2013]:** M. Thorup, *"Simple Tabulation, Fast Expanders, Double Tabulation, and
  High Independence"*, *Proc. 54th IEEE FOCS*, 2013, pp. 90–99 (`arXiv:1311.3121v2`, pp. 4–5,
  11–13), providing high-probability `(2 * maxEvictions n_max + 2)`-wise independence via double
  tabulation in the large-`n_max` regime `doubleTabThreshold c_exp ≤ n_max`.
* **Sufficient cuckoo hash pair interface (`IsCuckooHashPair`):** `GoodForSet`, `cuckooWalkRounds`,
  and `IsCuckooHashPair` capture the replay properties used by the Word-RAM cuckoo hash table:
  `GoodForSet` quantifies over every duplicate-free (`Nodup`) sublist/insertion order in `S`,
  `cuckooWalkRounds` takes the supremum (`sSup`) over all `ValidPlacement`s of `S`, and
  `rehash_prob_le_half` / `step_rehash_prob_le` package the whole-set `≤ 1 / 2` and incremental
  one-step `≤ C_reh / (max n_max 1 * max MaxLoop 1)` replay failure bounds over the
  oblivious-adversary model (`Dictionary.spec U V n_max`). These bounds are proved unconditionally
  across all `n_max : ℕ` (`C_walk = 3`, `C_reh = 4`) whenever `U ≤ max n_max 4 ^ c_exp` in
  `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_provableFamily`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.tableBits`, `tableSize`, `maxEvictions`:
  sub-table bit-width `M = ⌈log₂ (32 * max n_max 4)⌉`, sub-table size `m = 2 ^ M`, and eviction cap
  `MaxLoop = 6 (⌈log₂ max(n_max, 2)⌉ + 2)`.
* `SlotEntry`, `PureTable`, `WellPlaced`, `lookupEntry`, `pureEvictRound`, `pureEvict`,
  `pureReplay`: pure two-table cuckoo displacement and insertion-order replay model.
* `GoodForSet`, `survivingSeeds`, `cuckooWalkRounds`, `IsCuckooHashPair`, `IsCuckooHashFamily`:
  cuckoo hash family interface for expected displacement rounds and rehash probability.
* `Seed`, `seedLaw`, `evalHash1`, `evalHash2`: regime-switched seed space and hash pair
  (proven to satisfy `IsCuckooHashFamily` in
  `Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_provableFamily`).
* `HashPairRep`, `initTableHashPairCode`, `resampleHashPairCode`, `evalHash1Code`, `evalHash2Code`:
  two-block Word-RAM layout and programs realizing `(evalHash1, evalHash2)` in `O_{c_exp}(1)`
  instructions and `O_{c_exp}(n_max + 1)` words of space across all `n_max : ℕ`.

## Main results

* `pureReplay_append_singleton`, `pureReplay_lookupEntry_of_mem`: incremental eviction from the
  replayed table coincides with full replay of `ks ++ [u]`, and `lookupEntry` recovers the exact
  index of every inserted key in `O(1)` probes.
* `survivingSeeds_append_subset`, `mem_survivingSeeds_of_goodForSet`: monotonicity of surviving
  replay seeds across insertions (combined with `Cslib.Probability.PMF.unifOn_rehash_eq` and
  `Cslib.Probability.PMF.uniformOfFinset_le_two_mul_uniformOfFintype` from
  `Complexity/Probability/PMF/UniformSubset.lean`).
* `isCuckooHashPair_le_two`: reusable hash-pair-independent `n_max ≤ 2` instance (`C_walk = 1`,
  `C_reh = 0`) requiring no independence assumption, with `IsCuckooHashPair.mono_consts`
  providing monotonicity in `(C_walk, C_reh)`.
* `initTableHashPairCode_execWithin`, `resampleHashPairCode_execRand`, `evalHash1Code_execWithin`,
  `evalHash2Code_execWithin`, `hashPairSpace_le`, `evalHashSteps_le`: Word-RAM correctness,
  `O_{c_exp}(n_max + 1)` space bound, and `O_{c_exp}(1)` evaluation step bound across all
  `n_max : ℕ`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Analysis", pp. 6–10: Lemma 1 on p. 7, Eq. (3) on p. 9, and rehash
  analysis on pp. 9–10).
* [M. Thorup, "Simple tabulation, fast expanders, double tabulation, and high
  independence"][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, pp. 4–5, 11–13).
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed.][MitzenmacherUpfal2017]
* [J. L. Carter and M. N. Wegman, "Universal classes of hash functions"][CarterWegman1979]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing

open Cslib.WordRAM
open Cslib.Probability
open Cslib.Probability.PMF
open Cslib.Algorithms.WordRAM.Hashing
open scoped ENNReal Finset

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
  constructor
  · cases ht1 : tbl.t1 (h₁ u) with
    | none =>
      cases ht2 : tbl.t2 (h₂ u) with
      | none => intro h; cases h
      | some e₂ =>
        dsimp only
        split_ifs with hk₂
        · intro h; injection h with h; subst h; exact ⟨Or.inr (by rw [hk₂]; exact ht2), hk₂⟩
        · intro h; cases h
    | some e₁ =>
      dsimp only
      split_ifs with hk₁
      · intro h; injection h with h; subst h; exact ⟨Or.inl (by rw [hk₁]; exact ht1), hk₁⟩
      · cases ht2 : tbl.t2 (h₂ u) with
        | none => intro h; cases h
        | some e₂ =>
          dsimp only
          split_ifs with hk₂
          · intro h; injection h with h; subst h; exact ⟨Or.inr (by rw [hk₂]; exact ht2), hk₂⟩
          · intro h; cases h
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
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · dsimp only [putT1] at hi
      by_cases hie : i = h₁ e.key
      · subst hie; rw [Function.update_self] at hi
        injection hi with hi; exact Or.inr hi.symm
      · rw [Function.update_of_ne hie] at hi
        exact Or.inl (Or.inl ⟨i, hi⟩)
    · exact Or.inl (Or.inr ⟨i, hi⟩)
  · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
    · left
      have hie : i ≠ h₁ e.key := by
        intro h; subst h; rw [ht1_none] at hi; cases hi
      refine ⟨i, ?_⟩
      dsimp only [putT1]
      rw [Function.update_of_ne hie]
      exact hi
    · exact Or.inr ⟨i, hi⟩
    · subst hd
      left
      refine ⟨h₁ d.key, ?_⟩
      dsimp only [putT1]
      rw [Function.update_self]

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
  · constructor
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
      · dsimp only [putT1] at hi
        by_cases hie : i = h₁ e.key
        · subst hie; rw [Function.update_self] at hi
          injection hi with hi; exact Or.inr hi.symm
        · rw [Function.update_of_ne hie] at hi
          exact Or.inl (Or.inl ⟨i, hi⟩)
      · exact Or.inl (Or.inr ⟨i, hi⟩)
      · subst hd
        exact Or.inl (Or.inl ⟨h₁ e.key, ht1_some⟩)
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
      · by_cases hie : i = h₁ e.key
        · subst hie; rw [ht1_some] at hi; injection hi with hi; exact Or.inr hi.symm
        · refine Or.inl (Or.inl ⟨i, ?_⟩)
          dsimp only [putT1]
          rw [Function.update_of_ne hie]
          exact hi
      · exact Or.inl (Or.inr ⟨i, hi⟩)
      · subst hd
        refine Or.inl (Or.inl ⟨h₁ d.key, ?_⟩)
        dsimp only [putT1]
        rw [Function.update_self]

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
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact Or.inl (Or.inl ⟨i, hi⟩)
    · dsimp only [putT2] at hi
      by_cases hie : i = h₂ e.key
      · subst hie; rw [Function.update_self] at hi
        injection hi with hi; exact Or.inr hi.symm
      · rw [Function.update_of_ne hie] at hi
        exact Or.inl (Or.inr ⟨i, hi⟩)
  · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
    · exact Or.inl ⟨i, hi⟩
    · right
      have hie : i ≠ h₂ e.key := by
        intro h; subst h; rw [ht2_none] at hi; cases hi
      refine ⟨i, ?_⟩
      dsimp only [putT2]
      rw [Function.update_of_ne hie]
      exact hi
    · subst hd
      right
      refine ⟨h₂ d.key, ?_⟩
      dsimp only [putT2]
      rw [Function.update_self]

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
  · constructor
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
      · exact Or.inl (Or.inl ⟨i, hi⟩)
      · dsimp only [putT2] at hi
        by_cases hie : i = h₂ e.key
        · subst hie; rw [Function.update_self] at hi
          injection hi with hi; exact Or.inr hi.symm
        · rw [Function.update_of_ne hie] at hi
          exact Or.inl (Or.inr ⟨i, hi⟩)
      · subst hd
        exact Or.inl (Or.inr ⟨h₂ e.key, ht2_some⟩)
    · rintro ((⟨i, hi⟩ | ⟨i, hi⟩) | hd)
      · exact Or.inl (Or.inl ⟨i, hi⟩)
      · by_cases hie : i = h₂ e.key
        · subst hie; rw [ht2_some] at hi; injection hi with hi; exact Or.inr hi.symm
        · refine Or.inl (Or.inr ⟨i, ?_⟩)
          dsimp only [putT2]
          rw [Function.update_of_ne hie]
          exact hi
      · subst hd
        refine Or.inl (Or.inr ⟨h₂ d.key, ?_⟩)
        dsimp only [putT2]
        rw [Function.update_self]

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

theorem cuckooWalkRounds_le_maxLoop {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (S : Finset (Fin U)) (u : Fin U) :
    cuckooWalkRounds h₁ h₂ maxLoop S u ≤ maxLoop := by
  unfold cuckooWalkRounds
  by_cases hne : ({r : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ S tbl ∧
      ∃ idx : ℕ, r = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩}).Nonempty
  · refine csSup_le hne ?_
    rintro r ⟨tbl, _, idx, rfl⟩
    exact evictRounds_le h₁ h₂ maxLoop tbl ⟨u, idx⟩
  · rw [ Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

theorem cuckooWalkRounds_empty {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (u : Fin U) :
    cuckooWalkRounds h₁ h₂ maxLoop ∅ u ≤ 1 := by
  unfold cuckooWalkRounds
  by_cases hne : ({r : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ ∅ tbl ∧
      ∃ idx : ℕ, r = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩}).Nonempty
  · refine csSup_le hne ?_
    rintro r ⟨tbl, hvp, idx, rfl⟩
    cases maxLoop with
    | zero => exact Nat.zero_le _
    | succ k =>
      have ht1 : tbl.t1 (h₁ u) = none := by
        cases h : tbl.t1 (h₁ u) with
        | none => rfl
        | some e =>
          exfalso
          exact Finset.notMem_empty e.key (hvp.2 e.key ⟨e, Or.inl ⟨h₁ u, h⟩, rfl⟩)
      simp [evictRounds, pureEvictRound, putT1, ht1]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

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
  unfold cuckooWalkRounds
  by_cases hne : ({r : ℕ | ∃ tbl : PureTable U m, ValidPlacement h₁ h₂ S tbl ∧
      ∃ idx : ℕ, r = evictRounds h₁ h₂ maxLoop tbl ⟨u, idx⟩}).Nonempty
  · refine csSup_le hne ?_
    rintro r ⟨tbl, hvp, idx, rfl⟩
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
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, csSup_empty]
    exact Nat.zero_le _

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

/-! ### Section 4: Regime-switched cuckoo hash pair (`trinomialPolyHash` + `doubleTabHash`) -/

/-- Independence parameter `k = 2 * maxEvictions n_max + 2` required by the two-table cuckoo hashing
analysis on eviction walks of length up to `maxEvictions n_max`. -/
@[expose]
def cuckooK (n_max : ℕ) : ℕ :=
  2 * maxEvictions n_max + 2

theorem thirtyEight_le_cuckooK (n_max : ℕ) : 38 ≤ cuckooK n_max := by
  have := eighteen_le_maxEvictions n_max
  unfold cuckooK
  omega

open Cslib.DataStructure.HashFamily.WordRAM

/-- Regime-indexed seed space for the unconditional cuckoo hash pair:
- When `reg = true` (`n_max < doubleTabThreshold c_exp`), two independent
  `(2 * maxEvictions n_max + 2)`-wise independent trinomial polynomial seeds
  `Fin k → Fin (2 ^ (2 * 3 ^ trinomialStep U M))`.
- When `reg = false` (`doubleTabThreshold c_exp ≤ n_max`), two independent double-tabulation seed
  pairs `DoubleTabTopSeed c d b × DoubleTabBotSeed d b M` with
  `c = DoubleTabulation.provableC c_exp`, `d = DoubleTabulation.provableD c_exp`, and
  `b = DoubleTabulation.provableB n_max`. -/
@[expose]
def SeedAux (reg : Bool) (c_exp n_max U M : ℕ) : Type :=
  match reg with
  | true =>
    let k := 2 * maxEvictions n_max + 2
    (Fin k → Fin (2 ^ (2 * 3 ^ trinomialStep U M))) ×
      (Fin k → Fin (2 ^ (2 * 3 ^ trinomialStep U M)))
  | false =>
    let c := DoubleTabulation.provableC c_exp
    let d := DoubleTabulation.provableD c_exp
    let b := DoubleTabulation.provableB n_max
    (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M) ×
      (DoubleTabTopSeed c d b × DoubleTabBotSeed d b M)

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Fintype (SeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SeedAux] <;> infer_instance

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Nonempty (SeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SeedAux] <;> infer_instance

instance (c d b : ℕ) : DecidableEq (DoubleTabTopSeed c d b) :=
  inferInstanceAs (DecidableEq (Fin c → Fin d → Fin (2 ^ b) → Fin (2 ^ b)))

instance (d b M : ℕ) : DecidableEq (DoubleTabBotSeed d b M) :=
  inferInstanceAs (DecidableEq (Fin d → Fin (2 ^ b) → Fin (2 ^ M)))

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    DecidableEq (SeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SeedAux] <;> infer_instance

/-- Regime-indexed first cuckoo hash function. -/
@[expose]
noncomputable def evalHash1Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun (seed₁, _) =>
    trinomialPolyHash (trinomialStep U M) (2 * maxEvictions n_max + 2) U M seed₁
  | false => fun ((top₁, bottom₁), _) =>
    doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) U M top₁ bottom₁

/-- Regime-indexed second cuckoo hash function. -/
@[expose]
noncomputable def evalHash2Aux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun (_, seed₂) =>
    trinomialPolyHash (trinomialStep U M) (2 * maxEvictions n_max + 2) U M seed₂
  | false => fun (_, (top₂, bottom₂)) =>
    doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) U M top₂ bottom₂

/-- Seed space for the regime-switched cuckoo hash pair (`trinomialPolyHash` below
`doubleTabThreshold c_exp`, `doubleTabHash` at or above `doubleTabThreshold c_exp`). -/
abbrev Seed (c_exp n_max U M : ℕ) : Type :=
  SeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Uniform seed distribution over `Seed c_exp n_max U M`. -/
@[expose]
noncomputable def seedLaw (c_exp n_max U M : ℕ) : PMF (Seed c_exp n_max U M) :=
  PMF.uniformOfFintype (Seed c_exp n_max U M)

/-- First cuckoo hash function `h₁(u)` of the regime-switched cuckoo hash pair. -/
@[expose]
noncomputable def evalHash1 {c_exp n_max U M : ℕ} :
    Seed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  evalHash1Aux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Second cuckoo hash function `h₂(u)` of the regime-switched cuckoo hash pair. -/
@[expose]
noncomputable def evalHash2 {c_exp n_max U M : ℕ} :
    Seed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  evalHash2Aux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- **General cuckoo hash pair interface (`IsCuckooHashPair`)**:
an original strengthened sufficient assumption bundle inspired by Pagh and Rodler [PaghRodler2004]
(8 December 2003 manuscript, Section 2.3 "Analysis", pp. 6–10), asserting over a
seed distribution `μ : PMF Θ` and hash pair `h₁ h₂ : Θ → Fin U → Fin m`:
1. (`expected_walk_le`): for any set `S` of fewer than `n_max` keys and absent key `u ∉ S`, the
   expected number of worst-case displacement rounds `cuckooWalkRounds` (`sSup` over all
   `ValidPlacement`s of `S`) is at most `C_walk` (cf. [PaghRodler2004], §2.3, Lemma 1 on manuscript
   p. 7 and Eq. (3) on manuscript p. 9);
2. (`rehash_prob_le_half`): for any set `S` of at most `n_max` keys, the probability that `θ ∼ μ`
   fails `GoodForSet` (all `Nodup` sublists in `S`) is at most `1 / 2` (so each rehash attempt
   succeeds with probability at least `1 / 2` and the surviving seed set has measure at least
   `1 / 2`); and
3. (`step_rehash_prob_le`): for any insertion-order prefix `ks` of fewer than `n_max` distinct keys
   and new key `u ∉ ks`, the one-step incremental failure probability that `θ ∼ μ` survives
   `pureReplay (h₁ θ) (h₂ θ) MaxLoop ks` yet fails `pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])`
   is at most `C_reh / (max n_max 1 * max MaxLoop 1)` (cf. [PaghRodler2004], §2.3, manuscript
   pp. 9–10). -/
structure IsCuckooHashPair {Θ : Type*} (μ : PMF Θ) {U m : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (n_max MaxLoop C_walk C_reh : ℕ) : Prop where
  /-- Expected displacement rounds per new-key insertion is at most `C_walk`. -/
  expected_walk_le : ∀ (S : Finset (Fin U)) (u : Fin U), S.card < n_max → u ∉ S →
    (∑' θ : Θ, μ θ * (cuckooWalkRounds (h₁ θ) (h₂ θ) MaxLoop S u : ℝ≥0∞)) ≤ C_walk
  /-- Whole-set rehash failure probability on any key set `S` of size `≤ n_max` is at most
  `1 / 2`. -/
  rehash_prob_le_half : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
    μ.toOuterMeasure {θ : Θ | ¬ GoodForSet (h₁ θ) (h₂ θ) MaxLoop S} ≤ 1 / 2
  /-- One-step incremental rehash probability when appending a new key `u ∉ ks` to a duplicate-free
  key list `ks` of length `< n_max` is at most `C_reh / (max n_max 1 * max MaxLoop 1)`. -/
  step_rehash_prob_le : ∀ (ks : List (Fin U)) (u : Fin U),
    ks.Nodup → ks.length < n_max → u ∉ ks →
    μ.toOuterMeasure
      {θ : Θ | (pureReplay (h₁ θ) (h₂ θ) MaxLoop ks).isSome ∧
        (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isNone} ≤
      (C_reh : ℝ≥0∞) / ((max n_max 1 : ℝ≥0∞) * (max MaxLoop 1 : ℝ≥0∞))

/-- Monotonicity of `IsCuckooHashPair` in the constants `C_walk` and `C_reh`. -/
theorem IsCuckooHashPair.mono_consts {Θ : Type*} {μ : PMF Θ} {U m : ℕ}
    {h₁ h₂ : Θ → Fin U → Fin m}
    {n_max MaxLoop C_walk C_walk' C_reh C_reh' : ℕ}
    (hp : IsCuckooHashPair μ h₁ h₂ n_max MaxLoop C_walk C_reh)
    (hw : C_walk ≤ C_walk') (hr : C_reh ≤ C_reh') :
    IsCuckooHashPair μ h₁ h₂ n_max MaxLoop C_walk' C_reh' where
  expected_walk_le S u hS hu :=
    (hp.expected_walk_le S u hS hu).trans (by exact_mod_cast hw)
  rehash_prob_le_half := hp.rehash_prob_le_half
  step_rehash_prob_le ks u hnodup hlen hu :=
    (hp.step_rehash_prob_le ks u hnodup hlen hu).trans
      (ENNReal.div_le_div_right (by exact_mod_cast hr) _)

/-- Specialization of `IsCuckooHashPair` to the regime-switched cuckoo hash pair
`(evalHash1, evalHash2)` over `seedLaw c_exp n_max U M`.
Proved unconditionally for every `n_max : ℕ` (`C_walk = 3`, `C_reh = 4`) whenever
`U ≤ max n_max 4 ^ c_exp` and `32 * max n_max 4 ≤ 2 ^ M` via
`Cslib.Algorithms.Lean.CuckooHashing.isCuckooHashPair_provableFamily`. -/
abbrev IsCuckooHashFamily (c_exp U n_max M MaxLoop C_walk C_reh : ℕ) : Prop :=
  IsCuckooHashPair (seedLaw c_exp n_max U M) evalHash1 evalHash2 n_max MaxLoop C_walk C_reh

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

/-- Reusable hash-pair-independent `IsCuckooHashPair` instance for `n_max ≤ 2` and `0 < MaxLoop`
(`C_walk = 1`, `C_reh = 0`) over any seed distribution `μ` and arbitrary hash pair `(h₁, h₂)`
(without any independence assumption): inserting up to `2` keys into two tables `T₁, T₂` always
completes in `1` round with zero rehashes (even if both keys collide in `T₁`, the displaced first
key is placed into an empty slot of `T₂`). -/
theorem isCuckooHashPair_le_two {Θ : Type*} (μ : PMF Θ) {U m n_max MaxLoop : ℕ}
    (h₁ h₂ : Θ → Fin U → Fin m) (hn : n_max ≤ 2) (hloop : 0 < MaxLoop) :
    IsCuckooHashPair μ h₁ h₂ n_max MaxLoop 1 0 where
  expected_walk_le S u hcard _ := by
    have hcard1 : S.card ≤ 1 := by omega
    calc (∑' θ : Θ, μ θ * (cuckooWalkRounds (h₁ θ) (h₂ θ) MaxLoop S u : ℝ≥0∞))
      _ ≤ ∑' θ : Θ, μ θ * (1 : ℝ≥0∞) := by
          gcongr with θ
          exact_mod_cast cuckooWalkRounds_le_one_of_card_le_one (h₁ θ) (h₂ θ) MaxLoop hcard1 u
      _ = ((1 : ℕ) : ℝ≥0∞) := by
          simp only [mul_one, PMF.tsum_coe, Nat.cast_one]
  rehash_prob_le_half S hcard := by
    have hgood : ∀ θ : Θ, GoodForSet (h₁ θ) (h₂ θ) MaxLoop S := by
      intro θ ks hnodup hsub
      have hlen : ks.length ≤ 2 := by
        have h1 : ks.toFinset ⊆ S := fun x hx => hsub x (List.mem_toFinset.mp hx)
        have h2 : ks.toFinset.card ≤ S.card := Finset.card_le_card h1
        rw [List.card_toFinset, List.dedup_eq_self.mpr hnodup] at h2
        omega
      exact pureReplay_isSome_of_length_le_two _ _ hloop hlen
    have hempty : {θ : Θ | ¬ GoodForSet (h₁ θ) (h₂ θ) MaxLoop S} = ∅ := by
      ext θ; simp [hgood θ]
    rw [hempty]
    simp
  step_rehash_prob_le ks u _ hlen _ := by
    have hlen' : (ks ++ [u]).length ≤ 2 := by simp; omega
    have hsome : ∀ θ : Θ, (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isSome :=
      fun θ => pureReplay_isSome_of_length_le_two _ _ hloop hlen'
    have hempty :
        {θ : Θ | (pureReplay (h₁ θ) (h₂ θ) MaxLoop ks).isSome ∧
          (pureReplay (h₁ θ) (h₂ θ) MaxLoop (ks ++ [u])).isNone} = ∅ := by
      ext θ
      simp [Option.isNone_iff_eq_none, Option.ne_none_iff_isSome.mpr (hsome θ)]
    rw [hempty]
    simp

/-! ### Section 5: Two-block Word-RAM hash pair representation and programs -/

open Cslib.Algorithms.WordRAM.Hashing Cslib.DataStructure.HashFamily.WordRAM

/-- Word-RAM memory footprint of a single regime-switched hash instance (`h₁` or `h₂`). -/
@[expose]
def singleHashSpace (c_exp n_max : ℕ) : ℕ :=
  DoubleTabulation.provableSpace c_exp (cuckooK n_max) n_max

/-- Word-RAM memory footprint of the two-block hash pair `(h₁, h₂)` at `hashBase`:
`singleHashSpace c_exp n_max` words at `hashBase` for `h₁` followed by
`singleHashSpace c_exp n_max` words at `hash2Base hashBase c_exp n_max` for `h₂`. -/
@[expose]
def hashPairSpace (c_exp n_max : ℕ) : ℕ :=
  2 * singleHashSpace c_exp n_max

/-- Base address of the second hash instance `h₂`. -/
@[expose]
def hash2Base (hashBase c_exp n_max : ℕ) : ℕ :=
  hashBase + singleHashSpace c_exp n_max

theorem le_singleHashSpace (c_exp n_max : ℕ) :
    47 ≤ singleHashSpace c_exp n_max := by
  dsimp only [singleHashSpace, DoubleTabulation.provableSpace]
  split_ifs
  · dsimp only [KWise.space, KWise.spaceFromB]
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    omega
  · dsimp only [DoubleTabulation.space]
    have hc : 2 ≤ DoubleTabulation.provableC c_exp := by
      dsimp only [DoubleTabulation.provableC]; omega
    have hd : 16 ≤ DoubleTabulation.provableD c_exp := by
      dsimp only [DoubleTabulation.provableD, DoubleTabulation.provableC]; omega
    have hb : 2 ≤ 2 ^ DoubleTabulation.provableB n_max := by
      have h1 := DoubleTabulation.one_le_provableB n_max
      exact Nat.le_self_pow (by omega) 2
    have hcd : 48 ≤ (DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp := by
      nlinarith
    nlinarith

theorem le_hashPairSpace (c_exp n_max : ℕ) :
    49 ≤ hashPairSpace c_exp n_max := by
  have := le_singleHashSpace c_exp n_max
  dsimp only [hashPairSpace]
  omega

/-- Constant upper bound `24 * doubleTabMinB c_exp + 26` on `cuckooK n_max` throughout the small
regime `n_max < doubleTabThreshold c_exp`. -/
@[expose]
def cuckooKBound (c_exp : ℕ) : ℕ :=
  24 * doubleTabMinB c_exp + 26

theorem cuckooK_le_cuckooKBound_of_lt {c_exp n_max : ℕ}
    (hlt : n_max < doubleTabThreshold c_exp) :
    cuckooK n_max ≤ cuckooKBound c_exp := by
  have hb_pos : 1 ≤ doubleTabMinB c_exp := by
    rw [doubleTabMinB_eq]
    have hbase : 1 ≤ 24 * (2 * max c_exp 1) + 8 := by omega
    have hsq : 1 ≤ (24 * (2 * max c_exp 1) + 8) ^ 2 := Nat.one_le_pow 2 _ hbase
    omega
  have hpow_ge_2 : 2 ≤ 2 ^ (2 * doubleTabMinB c_exp) := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (2 * doubleTabMinB c_exp) := Nat.pow_le_pow_right (by decide) (by omega)
  have hmax_le : max n_max 2 ≤ 2 ^ (2 * doubleTabMinB c_exp) := by
    rw [← doubleTabThreshold_eq]
    exact max_le (le_of_lt hlt) (by rw [doubleTabThreshold_eq]; exact hpow_ge_2)
  have hclog : Nat.clog 2 (max n_max 2) ≤ 2 * doubleTabMinB c_exp :=
    Nat.clog_le_of_le_pow hmax_le
  dsimp only [cuckooK, maxEvictions, cuckooKBound]
  omega

theorem singleHashSpace_le_provableSpace_cuckooKBound (c_exp n_max : ℕ) :
    singleHashSpace c_exp n_max ≤
      DoubleTabulation.provableSpace c_exp (cuckooKBound c_exp) n_max := by
  dsimp only [singleHashSpace, DoubleTabulation.provableSpace]
  split_ifs with h
  · dsimp only [KWise.space, KWise.spaceFromB]
    have hk := cuckooK_le_cuckooKBound_of_lt h
    omega
  · exact le_rfl

/-- Explicit `O_{c_exp}(1)` linear-space factor for `hashPairSpace c_exp n_max`. -/
@[expose]
def hashPairSpaceFactor (c_exp : ℕ) : ℕ :=
  2 * DoubleTabulation.provableSpaceFactor c_exp (cuckooKBound c_exp)

/-- **All-`n_max` linear space bound for `hashPairSpace` (`O_{c_exp}(n_max + 1)`)**. -/
theorem hashPairSpace_le (c_exp n_max : ℕ) :
    hashPairSpace c_exp n_max ≤ hashPairSpaceFactor c_exp * (n_max + 1) := by
  dsimp only [hashPairSpace, hashPairSpaceFactor]
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left 2
    ((singleHashSpace_le_provableSpace_cuckooKBound c_exp n_max).trans
      (DoubleTabulation.provableSpace_le c_exp (cuckooKBound c_exp) n_max))

/-- Regime-indexed deterministic table representation for a single hash block at `base`. -/
@[expose]
def SingleTableRepAux (reg : Bool) (base n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  match reg with
  | true => KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) mem
  | false => True

/-- Deterministic table representation for a single hash block at `base`. -/
@[expose]
def SingleTableRep (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  SingleTableRepAux (decide (n_max < doubleTabThreshold c_exp)) base n_max U M mem

/-- Deterministic table representation invariant for the two-block hash pair at `hashBase`. -/
@[expose]
def HashPairTableRep (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  SingleTableRep hashBase c_exp n_max U M mem ∧
  SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M mem

/-- Regime-indexed seed representation for the two-block hash pair at `hashBase`. -/
@[expose]
def HashPairSeedRepAux (reg : Bool) (hashBase c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → (ℕ → ℕ) → Prop :=
  match reg with
  | true => fun (θ₁, θ₂) mem =>
    KWise.SeedRep hashBase U M (cuckooK n_max) θ₁ mem ∧
    KWise.SeedRep (hash2Base hashBase c_exp n_max) U M (cuckooK n_max) θ₂ mem
  | false => fun (θ₁, θ₂) mem =>
    DoubleTabulation.SeedRep hashBase
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M θ₁ mem ∧
    DoubleTabulation.SeedRep (hash2Base hashBase c_exp n_max)
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M θ₂ mem

/-- Seed representation invariant for `θ : Seed c_exp n_max U M` at `hashBase`. -/
@[expose]
def HashPairSeedRep (hashBase c_exp n_max U M : ℕ)
    (θ : Seed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  HashPairSeedRepAux (decide (n_max < doubleTabThreshold c_exp)) hashBase c_exp n_max U M θ mem

/-- Full representation invariant for the hash pair `(h₁, h₂)` at `hashBase`. -/
@[expose]
def HashPairRep (hashBase c_exp n_max U M : ℕ)
    (θ : Seed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  HashPairTableRep hashBase c_exp n_max U M mem ∧
  HashPairSeedRep hashBase c_exp n_max U M θ mem

/-- Regime-indexed seed extraction from memory at `hashBase`. -/
@[expose]
def extractSeedAux (reg : Bool) (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SeedAux reg c_exp n_max U M :=
  match reg with
  | true =>
    (KWise.extractSeeds hashBase U M (cuckooK n_max) mem,
     KWise.extractSeeds (hash2Base hashBase c_exp n_max) U M (cuckooK n_max) mem)
  | false =>
    (DoubleTabulation.extractSeed hashBase
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M mem,
     DoubleTabulation.extractSeed (hash2Base hashBase c_exp n_max)
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M mem)

/-- Extract the full cuckoo hash seed `Seed c_exp n_max U M` from memory at `hashBase`. -/
@[expose]
def extractSeed (hashBase c_exp n_max U M : ℕ) (mem : ℕ → ℕ) : Seed c_exp n_max U M :=
  extractSeedAux (decide (n_max < doubleTabThreshold c_exp)) hashBase c_exp n_max U M mem

private theorem extractSeeds_eq_of_seedRep {base U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {mem : ℕ → ℕ}
    (hseed : KWise.SeedRep base U M k c mem) :
    KWise.extractSeeds base U M k mem = c := by
  funext j
  ext
  dsimp only [KWise.extractSeeds, Tabulation.extractSlice]
  rw [hseed j, Tabulation.extractWord_val_of_lt (c j).isLt]

private theorem extractSeed_eq_of_doubleTabSeedRep {base c d b M : ℕ}
    {θ : DoubleTabTopSeed c d b × DoubleTabBotSeed d b M} {mem : ℕ → ℕ}
    (hseed : DoubleTabulation.SeedRep base c d b M θ mem) :
    DoubleTabulation.extractSeed base c d b M mem = θ := by
  rcases θ with ⟨T₁, T₂⟩
  rcases hseed with ⟨h1, h2⟩
  dsimp only [DoubleTabulation.extractSeed]
  congr 1
  · funext i j ch
    ext
    rw [DoubleTabulation.extractTop_apply, h1 i j ch,
      Tabulation.extractWord_val_of_lt (T₁ i j ch).isLt]
  · funext j y
    ext
    rw [DoubleTabulation.extractBot_apply, h2 j y,
      Tabulation.extractWord_val_of_lt (T₂ j y).isLt]

theorem extractSeed_eq_of_HashPairSeedRep {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem) :
    extractSeed hashBase c_exp n_max U M mem = θ := by
  unfold Seed extractSeed HashPairSeedRep at *
  revert θ hseed
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro ⟨θ₁, θ₂⟩ ⟨h1, h2⟩
  · exact Prod.ext (extractSeed_eq_of_doubleTabSeedRep h1) (extractSeed_eq_of_doubleTabSeedRep h2)
  · exact Prod.ext (extractSeeds_eq_of_seedRep h1) (extractSeeds_eq_of_seedRep h2)

theorem SingleTableRep.congr_of_footprint {base c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : SingleTableRep base c_exp n_max U M mem)
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    SingleTableRep base c_exp n_max U M mem' := by
  unfold SingleTableRep at *
  revert htab
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro htab
  · trivial
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    rcases htab with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
    refine ⟨(hm _ (by omega) (by omega)).trans h0,
      (hm _ (by omega) (by omega)).trans h1,
      (hm _ (by omega) (by omega)).trans h2,
      (hm _ (by omega) (by omega)).trans h3,
      (hm _ (by omega) (by omega)).trans h4,
      (hm _ (by omega) (by omega)).trans h5,
      (hm _ (by omega) (by omega)).trans h6,
      (hm _ (by omega) (by omega)).trans h7,
      fun idx hidx => (hm _ (by omega) (by omega)).trans (hcl idx hidx)⟩

theorem SingleTableRep.of_copy_from_hashBase {hashBase c_exp n_max U M : ℕ} {mem : ℕ → ℕ}
    (htab : SingleTableRep hashBase c_exp n_max U M mem)
    (hcopy : ∀ j < singleHashSpace c_exp n_max,
      mem (hash2Base hashBase c_exp n_max + j) = mem (hashBase + j)) :
    SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M mem := by
  unfold SingleTableRep at *
  revert htab
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro htab
  · trivial
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hk := thirtyEight_le_cuckooK n_max
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    rcases htab with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun idx hidx => ?_⟩
    · simpa using (hcopy 0 (by omega)).trans (by simpa using h0)
    · exact (hcopy 1 (by omega)).trans h1
    · exact (hcopy 2 (by omega)).trans h2
    · exact (hcopy 3 (by omega)).trans h3
    · exact (hcopy 4 (by omega)).trans h4
    · exact (hcopy 5 (by omega)).trans h5
    · exact (hcopy 6 (by omega)).trans h6
    · exact (hcopy 7 (by omega)).trans h7
    · rw [show hash2Base hashBase c_exp n_max + 8 + cuckooK n_max + idx =
            hash2Base hashBase c_exp n_max + (8 + cuckooK n_max + idx) by omega,
          hcopy (8 + cuckooK n_max + idx) (by omega),
          show hashBase + (8 + cuckooK n_max + idx) = hashBase + 8 + cuckooK n_max + idx by omega]
      exact hcl idx hidx

theorem HashPairTableRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : HashPairTableRep hashBase c_exp n_max U M mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairTableRep hashBase c_exp n_max U M mem' :=
  ⟨htab.1.congr_of_footprint (fun a hge hlt =>
    hm a hge (by dsimp only [hashPairSpace]; omega)),
   htab.2.congr_of_footprint (fun a hge hlt =>
    hm a (by dsimp only [hash2Base] at hge; omega)
      (by dsimp only [hash2Base, hashPairSpace] at hlt ⊢; omega))⟩

private theorem kwiseSeedRep_congr_of_footprint {base U M k : ℕ}
    {c : Fin k → Fin (2 ^ trinomialDeg U M)} {mem mem' : ℕ → ℕ}
    (hseed : KWise.SeedRep base U M k c mem)
    (hm : ∀ a, base ≤ a → a < base + 8 + k → mem' a = mem a) :
    KWise.SeedRep base U M k c mem' :=
  fun j => (hm (base + 8 + j.val) (by omega) (by have := j.isLt; omega)).trans (hseed j)

theorem HashPairSeedRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairSeedRep hashBase c_exp n_max U M θ mem' := by
  unfold Seed HashPairSeedRep at *
  revert θ hseed
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro ⟨θ₁, θ₂⟩ ⟨h1, h2⟩
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hge]
    exact ⟨h1.congr_mem (fun a ha1 ha2 =>
        hm a ha1 (by dsimp only [hashPairSpace]; omega)),
      h2.congr_mem (fun a ha1 ha2 =>
        hm a (by dsimp only [hash2Base] at ha1; omega)
          (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega))⟩
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    exact ⟨kwiseSeedRep_congr_of_footprint h1 (fun a ha1 ha2 =>
        hm a ha1 (by dsimp only [hashPairSpace]; omega)),
      kwiseSeedRep_congr_of_footprint h2 (fun a ha1 ha2 =>
        hm a (by dsimp only [hash2Base] at ha1; omega)
          (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega))⟩

theorem HashPairRep.congr_of_footprint {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hrep : HashPairRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    HashPairRep hashBase c_exp n_max U M θ mem' :=
  ⟨hrep.1.congr_of_footprint hm, hrep.2.congr_of_footprint hm⟩

theorem HashPairRep.congr_of_ge_hashBase {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hrep : HashPairRep hashBase c_exp n_max U M θ mem)
    (hm : ∀ a, hashBase ≤ a → mem' a = mem a) :
    HashPairRep hashBase c_exp n_max U M θ mem' :=
  hrep.congr_of_footprint (fun a hge _ => hm a hge)

private theorem extractSeeds_congr_of_footprint {base U M k : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, base ≤ a → a < base + 8 + k → mem' a = mem a) :
    KWise.extractSeeds base U M k mem' = KWise.extractSeeds base U M k mem := by
  funext j
  dsimp only [KWise.extractSeeds, Tabulation.extractSlice]
  rw [hm (base + 8 + j.val) (by omega) (by have := j.isLt; omega)]

theorem extractSeed_congr_of_footprint {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, hashBase ≤ a → a < hashBase + hashPairSpace c_exp n_max → mem' a = mem a) :
    extractSeed hashBase c_exp n_max U M mem' = extractSeed hashBase c_exp n_max U M mem := by
  unfold Seed extractSeed
  cases h : decide (n_max < doubleTabThreshold c_exp)
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hge]
    dsimp only [extractSeedAux]
    exact Prod.ext
      (DoubleTabulation.extractSeed_congr_mem (fun a ha1 ha2 =>
        hm a ha1 (by dsimp only [hashPairSpace]; omega)))
      (DoubleTabulation.extractSeed_congr_mem (fun a ha1 ha2 =>
        hm a (by dsimp only [hash2Base] at ha1; omega)
          (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega)))
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + (2 * maxEvictions n_max + 2) + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    dsimp only [extractSeedAux]
    exact Prod.ext
      (extractSeeds_congr_of_footprint (fun a ha1 ha2 =>
        hm a ha1 (by dsimp only [hashPairSpace]; omega)))
      (extractSeeds_congr_of_footprint (fun a ha1 ha2 =>
        hm a (by dsimp only [hash2Base] at ha1; omega)
          (by dsimp only [hash2Base, hashPairSpace] at ha2 ⊢; omega)))

theorem extractSeed_congr_of_ge_hashBase {hashBase c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, hashBase ≤ a → mem' a = mem a) :
    extractSeed hashBase c_exp n_max U M mem' = extractSeed hashBase c_exp n_max U M mem :=
  extractSeed_congr_of_footprint (fun a hge _ => hm a hge)

/-- Injective register map embedding `Data 18` into `Data 19`. -/
@[expose]
def cast18To19 : Fin 18 → Fin 19 :=
  Fin.castLE (by decide : 18 ≤ 19)

theorem injective_cast18To19 : Function.Injective cast18To19 :=
  Fin.castLE_injective _

/-- Injective register map embedding `Data 12` into `Data 19`. -/
@[expose]
def cast12To19 : Fin 12 → Fin 19 :=
  Fin.castLE (by decide : 12 ≤ 19)

theorem injective_cast12To19 : Function.Injective cast12To19 :=
  Fin.castLE_injective _

/-- Body of `copyWordsLoop`: copies one word from `[reg 3]` to `[reg 4]` and increments both
pointers by `reg 6 = 1`. -/
@[expose]
def copyWordsBody : Code .exact 19 :=
  .seq (.op (.load 7 3))
  (.seq (.op (.store 4 7))
  (.seq (.op (.exactBin .add 3 3 6))
        (.op (.exactBin .add 4 4 6))))

/-- Word-slice copy loop `while reg 4 < reg 5 do copyWordsBody`. -/
@[expose]
def copyWordsLoop : Code .exact 19 :=
  .loop (.lt 4 5) copyWordsBody

theorem copyWordsLoop_exec {w : ℕ} (len src dst : ℕ) {x : Data 19}
    (hsrc : x.regs 3 = src) (hdst : x.regs 4 = dst)
    (hend : x.regs 5 = dst + len) (hone : x.regs 6 = 1)
    (hdisj : src + len ≤ dst) (hfit_end : Fits w (dst + len)) :
    ∃ y : Data 19,
      Exec w copyWordsLoop x y (6 * len + 2) ∧
      (∀ r : Fin 19, r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 7 → y.regs r = x.regs r) ∧
      (∀ j < len, y.mem (dst + j) = x.mem (src + j)) ∧
      (∀ a, (a < dst ∨ dst + len ≤ a) → y.mem a = x.mem a) := by
  induction len generalizing src dst x with
  | zero =>
    have hc : ¬ (Cond.lt (4 : Fin 19) 5).Holds x := by
      simp [Cond.Holds, hdst, hend]
    exact ⟨x, Exec.loop_exit hc, fun _ _ => rfl, fun _ hj => by omega, fun _ _ => rfl⟩
  | succ len ih =>
    have hc : (Cond.lt (4 : Fin 19) 5).Holds x := by
      simp [Cond.Holds, hdst, hend]
    have hfit_src1 : Fits w (src + 1) := hfit_end.of_le (by omega)
    have hfit_dst1 : Fits w (dst + 1) := hfit_end.of_le (by omega)
    set s1 := x.set 7 (x.mem src)
    have e1 : Exec w (.op (.load 7 3) : Code .exact 19) x s1 1 := by
      simpa +decide [s1, hsrc] using (Exec.load (B := .exact) (w := w) (d := 7) (a := 3) (x := x))
    set s2 := s1.write dst (x.mem src)
    have e2 : Exec w (.op (.store 4 7) : Code .exact 19) s1 s2 1 := by
      simpa +decide [s2, s1, hdst] using
        (Exec.store (B := .exact) (w := w) (a := 4) (s := 7) (x := s1))
    set s3 := s2.set 3 (src + 1)
    have e3 : Exec w (.op (.exactBin .add 3 3 6) : Code .exact 19) s2 s3 1 :=
      ExactLog.exec_exactBin (by simp +decide [s2, s1, hsrc, hone]) hfit_src1
    set s4 := s3.set 4 (dst + 1)
    have e4 : Exec w (.op (.exactBin .add 4 4 6) : Code .exact 19) s3 s4 1 :=
      ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, hdst, hone]) hfit_dst1
    have hbody : Exec w copyWordsBody x s4 4 := e1.seq (e2.seq (e3.seq e4))
    obtain ⟨y, hrec, hy_regs, hy_copy, hy_frame⟩ :=
      ih (src + 1) (dst + 1) (x := s4)
        (by simp +decide [s4, s3])
        (by simp +decide [s4])
        (by simp +decide [s4, s3, s2, s1, hend]; omega)
        (by simp +decide [s4, s3, s2, s1, hone])
        (by omega)
        (by rwa [show dst + 1 + len = dst + (len + 1) by omega])
    have hiter := Exec.loop_iter hc hbody hrec
    refine ⟨y, ?_, ?_, ?_, ?_⟩
    · simpa only [copyWordsLoop, show 4 + (6 * len + 2) + 2 = 6 * (len + 1) + 2 by ring] using
        hiter
    · intro r ⟨hr3, hr4, hr7⟩
      rw [hy_regs r ⟨hr3, hr4, hr7⟩]
      dsimp only [s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne hr4, Function.update_of_ne hr3, Function.update_of_ne hr7]
    · intro j hj
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [Nat.add_zero, Nat.add_zero, hy_frame dst (Or.inl (by omega))]
        simp [s4, s3, s2, Data.write]
      · have h1 := hy_copy (j - 1) (by omega)
        rw [show dst + 1 + (j - 1) = dst + j by omega,
          show src + 1 + (j - 1) = src + j by omega] at h1
        rw [h1]
        dsimp only [s4, s3, s2, s1, Data.write, Data.set]
        rw [Function.update_of_ne (by omega)]
    · intro a ha
      rw [hy_frame a (ha.imp (by omega) (by omega))]
      dsimp only [s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne (by omega)]

/-- Setup block preparing `copyWordsLoop` to duplicate
`[hashBase, hashBase + singleHashSpace c_exp n_max)` into
`[hash2Base hashBase c_exp n_max, hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max)`. -/
@[expose]
def copyTableSetup (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.copy 3 0))
  (.seq (.op (.const 4 (singleHashSpace c_exp n_max)))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 (singleHashSpace c_exp n_max)))
  (.seq (.op (.exactBin .add 5 4 5))
        (.op (.const 6 1))))))

/-- Deterministic table-initialization program for the two-block hash pair at `hashBase`:
in the small-`n_max` regime `n_max < doubleTabThreshold c_exp`, initializes the `KWise` lookup table
at `hashBase` and copies it to `hash2Base hashBase c_exp n_max`; in the large-`n_max` regime,
executes a 1-instruction no-op (`SingleTableRep` is `True`). -/
@[expose]
def initTableHashPairCode (c_exp n_max : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    .seq ((KWise.initTableCode (cuckooK n_max)).rename cast18To19)
    (.seq (copyTableSetup c_exp n_max) copyWordsLoop)
  else
    .op (.copy 0 0)

/-- Instruction bound for `initTableHashPairCode`. -/
@[expose]
def initTableHashPairSteps (c_exp n_max U M : ℕ) : ℕ :=
  KWise.initTableSteps n_max U M + 6 * singleHashSpace c_exp n_max + 8

theorem initTableHashPairCode_execWithin {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = n_max)
    (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ∃ y : Data 19,
      ExecWithin w (initTableHashPairCode c_exp n_max) x y
        (initTableHashPairSteps c_exp n_max U M) ∧
      HashPairTableRep hashBase c_exp n_max U M y.mem ∧
      y.regs 0 = hashBase ∧
      (∀ a, (a < hashBase ∨ hashBase + hashPairSpace c_exp n_max ≤ a) → y.mem a = x.mem a) := by
  unfold initTableHashPairCode
  split_ifs with hlt
  · have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hle_sp := le_singleHashSpace c_exp n_max
    have hfit_kw : Fits w (hashBase + KWise.space n_max (cuckooK n_max)) :=
      hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_1 : Fits w 1 := hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
    have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
    have hfit_end : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
      hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
    obtain ⟨y_kw, ⟨t_kw, ht_kw, he_kw⟩, htab_kw, hy_kw0, hy_kw_out⟩ :=
      KWise.initTableCode_execWithin (w := w) (base := hashBase) (n_max := n_max)
        (U := U) (M := M) (k := cuckooK n_max) (x := x.comap cast18To19)
        (by simp +decide [cast18To19, Data.comap, h0])
        (by simp +decide [cast18To19, Data.comap, h1])
        (by simp +decide [cast18To19, Data.comap, h2])
        (by simp +decide [cast18To19, Data.comap, h3])
        hfit_kw hfit_n hfit_U hfit_q
    set d1 := y_kw.extend cast18To19 x
    have he_kw' : Exec w ((KWise.initTableCode (cuckooK n_max)).rename cast18To19) x d1 t_kw :=
      he_kw.rename injective_cast18To19
    have hd1_0 : d1.regs 0 = hashBase := by
      change ((y_kw.extend cast18To19 x).comap cast18To19).regs 0 = hashBase
      rw [Data.comap_extend injective_cast18To19, hy_kw0]
    have hd1_mem : d1.mem = y_kw.mem := rfl
    set s1 := d1.set 3 hashBase
    have es1 : Exec w (.op (.copy 3 0) : Code .exact 19) d1 s1 1 := by
      simpa +decide [s1, hd1_0] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 0) (x := d1))
    set s2 := s1.set 4 (singleHashSpace c_exp n_max)
    have es2 : Exec w (.op (.const 4 (singleHashSpace c_exp n_max)) : Code .exact 19) s1 s2 1 :=
      Exec.const hfit_sh
    set s3 := s2.set 4 (hash2Base hashBase c_exp n_max)
    have es3 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 19) s2 s3 1 :=
      ExactLog.exec_exactBin (by simp +decide [s2, s1, hd1_0, hash2Base]) hfit_h2
    set s4 := s3.set 5 (singleHashSpace c_exp n_max)
    have es4 : Exec w (.op (.const 5 (singleHashSpace c_exp n_max)) : Code .exact 19) s3 s4 1 :=
      Exec.const hfit_sh
    set s5 := s4.set 5 (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max)
    have es5 : Exec w (.op (.exactBin .add 5 4 5) : Code .exact 19) s4 s5 1 :=
      ExactLog.exec_exactBin (by simp +decide [s4, s3]) hfit_end
    set s6 := s5.set 6 1
    have es6 : Exec w (.op (.const 6 1) : Code .exact 19) s5 s6 1 := Exec.const hfit_1
    have esetup : Exec w (copyTableSetup c_exp n_max) d1 s6 6 :=
      es1.seq (es2.seq (es3.seq (es4.seq (es5.seq es6))))
    obtain ⟨y, ecopy, hy_regs, hy_copy, hy_frame⟩ :=
      copyWordsLoop_exec (w := w) (singleHashSpace c_exp n_max) hashBase
        (hash2Base hashBase c_exp n_max) (x := s6)
        (by simp +decide [s6, s5, s4, s3, s2, s1])
        (by simp +decide [s6, s5, s4, s3])
        (by simp +decide [s6, s5])
        (by simp +decide [s6])
        (by dsimp only [hash2Base]; omega)
        hfit_end
    have hall := he_kw'.seq (esetup.seq ecopy)
    have hy0 : y.regs 0 = hashBase := by
      rw [hy_regs 0 ⟨by decide, by decide, by decide⟩]
      simp +decide [s6, s5, s4, s3, s2, s1, hd1_0]
    have htab1_d1 : SingleTableRep hashBase c_exp n_max U M d1.mem := by
      unfold SingleTableRep
      rw [decide_eq_true hlt]
      exact htab_kw
    have htab1_y : SingleTableRep hashBase c_exp n_max U M y.mem :=
      htab1_d1.congr_of_footprint (fun a ha1 ha2 =>
        hy_frame a (Or.inl (by dsimp only [hash2Base]; omega)))
    have htab2_y : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M y.mem :=
      htab1_y.of_copy_from_hashBase (fun j hj => by
        rw [hy_copy j hj, hy_frame (hashBase + j) (Or.inl (by dsimp only [hash2Base]; omega))])
    refine ⟨y, ⟨t_kw + (6 + (6 * singleHashSpace c_exp n_max + 2)),
      by dsimp only [initTableHashPairSteps]; omega, hall⟩,
      ⟨htab1_y, htab2_y⟩, hy0, fun a ha => ?_⟩
    have ha_copy : a < hash2Base hashBase c_exp n_max ∨
        hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a := by
      dsimp only [hash2Base, hashPairSpace] at ha ⊢
      exact ha.imp (by omega) (by omega)
    have ha_kw : a < hashBase ∨ hashBase + KWise.space n_max (cuckooK n_max) ≤ a := by
      dsimp only [hashPairSpace] at ha
      exact ha.imp id (by omega)
    exact (hy_frame a ha_copy).trans (hy_kw_out a ha_kw)
  · refine ⟨x.set 0 (x.regs 0),
      ⟨1, by dsimp only [initTableHashPairSteps]; omega, Exec.copy⟩,
      ?_, by simp +decide [h0], fun _ _ => rfl⟩
    unfold HashPairTableRep SingleTableRep
    rw [decide_eq_false hlt]
    exact ⟨trivial, trivial⟩

/-- Regime-indexed seed type for a single hash block (`h₁` or `h₂`). -/
@[expose]
def SingleSeedAux (reg : Bool) (c_exp n_max U M : ℕ) : Type :=
  match reg with
  | true => Fin (cuckooK n_max) → Fin (2 ^ trinomialDeg U M)
  | false =>
    DoubleTabTopSeed (DoubleTabulation.provableC c_exp)
      (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) ×
    DoubleTabBotSeed (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) M

/-- Seed type for a single regime-switched hash block (`h₁` or `h₂`). -/
abbrev SingleSeed (c_exp n_max U M : ℕ) : Type :=
  SingleSeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Fintype (SingleSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SingleSeedAux] <;> infer_instance

instance (reg : Bool) (c_exp n_max U M : ℕ) :
    Nonempty (SingleSeedAux reg c_exp n_max U M) := by
  cases reg <;> dsimp [SingleSeedAux] <;> infer_instance

/-- Regime-indexed seed representation for a single hash block at `base`. -/
@[expose]
def SingleSeedRepAux (reg : Bool) (base c_exp n_max U M : ℕ) :
    SingleSeedAux reg c_exp n_max U M → (ℕ → ℕ) → Prop :=
  match reg with
  | true => fun θ mem => KWise.SeedRep base U M (cuckooK n_max) θ mem
  | false => fun θ mem =>
    DoubleTabulation.SeedRep base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M θ mem

/-- Seed representation for a single regime-switched hash block at `base`. -/
@[expose]
def SingleSeedRep (base c_exp n_max U M : ℕ)
    (θ : SingleSeed c_exp n_max U M) (mem : ℕ → ℕ) : Prop :=
  SingleSeedRepAux (decide (n_max < doubleTabThreshold c_exp)) base c_exp n_max U M θ mem

/-- Regime-indexed seed extraction for a single hash block at `base`. -/
@[expose]
def extractSingleSeedAux (reg : Bool) (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SingleSeedAux reg c_exp n_max U M :=
  match reg with
  | true => KWise.extractSeeds base U M (cuckooK n_max) mem
  | false =>
    DoubleTabulation.extractSeed base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M mem

/-- Extract the seed of a single regime-switched hash block at `base`. -/
@[expose]
def extractSingleSeed (base c_exp n_max U M : ℕ) (mem : ℕ → ℕ) :
    SingleSeed c_exp n_max U M :=
  extractSingleSeedAux (decide (n_max < doubleTabThreshold c_exp)) base c_exp n_max U M mem

theorem SingleSeedRep.congr_of_footprint {base c_exp n_max U M : ℕ}
    {θ : SingleSeed c_exp n_max U M} {mem mem' : ℕ → ℕ}
    (hseed : SingleSeedRep base c_exp n_max U M θ mem)
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    SingleSeedRep base c_exp n_max U M θ mem' := by
  unfold SingleSeed SingleSeedRep at *
  revert θ hseed
  cases h : decide (n_max < doubleTabThreshold c_exp) <;> intro θ hseed
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hge]
    exact hseed.congr_mem (fun a ha1 ha2 => hm a ha1 (by omega))
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    exact kwiseSeedRep_congr_of_footprint hseed (fun a ha1 ha2 => hm a ha1 (by omega))

theorem extractSingleSeed_congr_of_footprint {base c_exp n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (hm : ∀ a, base ≤ a → a < base + singleHashSpace c_exp n_max → mem' a = mem a) :
    extractSingleSeed base c_exp n_max U M mem' = extractSingleSeed base c_exp n_max U M mem := by
  unfold SingleSeed extractSingleSeed
  cases h : decide (n_max < doubleTabThreshold c_exp)
  · have hge : ¬ (n_max < doubleTabThreshold c_exp) := of_decide_eq_false h
    have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hge]
    exact DoubleTabulation.extractSeed_congr_mem (fun a ha1 ha2 => hm a ha1 (by omega))
  · have hlt : n_max < doubleTabThreshold c_exp := of_decide_eq_true h
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    exact extractSeeds_congr_of_footprint (fun a ha1 ha2 => hm a ha1 (by omega))

private theorem hashPairSeedRep_extractSeed_of_single {hashBase c_exp n_max U M : ℕ}
    {mem : ℕ → ℕ}
    (h1 : SingleSeedRep hashBase c_exp n_max U M
      (extractSingleSeed hashBase c_exp n_max U M mem) mem)
    (h2 : SingleSeedRep (hash2Base hashBase c_exp n_max) c_exp n_max U M
      (extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M mem) mem) :
    HashPairSeedRep hashBase c_exp n_max U M (extractSeed hashBase c_exp n_max U M mem) mem := by
  unfold HashPairSeedRep extractSeed SingleSeedRep extractSingleSeed at *
  revert h1 h2
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro h1 h2 <;> exact ⟨h1, h2⟩

/-- Shifts `reg 0` (`base`) forward by `singleHashSpace c_exp n_max` (`hashBase → hash2Base`)
using scratch register `15`. -/
@[expose]
def shiftToHash2BaseCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 (singleHashSpace c_exp n_max)))
       (.op (.exactBin .add 0 0 15))

/-- Closed-form machine state after `shiftToHash2BaseCode c_exp n_max`. -/
@[expose]
def shiftToHash2BaseData (hashBase c_exp n_max : ℕ) (x : Data 19) : Data 19 :=
  (x.set 15 (singleHashSpace c_exp n_max)).set 0 (hash2Base hashBase c_exp n_max)

/-- Shifts `reg 0` (`base`) back by `singleHashSpace c_exp n_max` (`hash2Base → hashBase`)
using scratch register `15`. -/
@[expose]
def unshiftFromHash2BaseCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 (singleHashSpace c_exp n_max)))
       (.op (.exactBin .sub 0 0 15))

/-- Closed-form machine state after `unshiftFromHash2BaseCode c_exp n_max`. -/
@[expose]
def unshiftFromHash2BaseData (hashBase c_exp n_max : ℕ) (x : Data 19) : Data 19 :=
  (x.set 15 (singleHashSpace c_exp n_max)).set 0 hashBase

theorem shiftToHash2BaseCode_exec {w hashBase c_exp n_max : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    Exec w (shiftToHash2BaseCode c_exp n_max) x
      (shiftToHash2BaseData hashBase c_exp n_max x) 2 := by
  have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  have e1 : Exec w (.op (.const 15 (singleHashSpace c_exp n_max)) : Code .exact 19)
      x (x.set 15 (singleHashSpace c_exp n_max)) 1 :=
    Exec.const hfit_sh
  have e2 : Exec w (.op (.exactBin .add 0 0 15) : Code .exact 19)
      (x.set 15 (singleHashSpace c_exp n_max))
      (shiftToHash2BaseData hashBase c_exp n_max x) 1 :=
    ExactLog.exec_exactBin (by simp +decide [h0, hash2Base]) hfit_h2
  exact e1.seq e2

theorem unshiftFromHash2BaseCode_exec {w hashBase c_exp n_max : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hash2Base hashBase c_exp n_max)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    Exec w (unshiftFromHash2BaseCode c_exp n_max) x
      (unshiftFromHash2BaseData hashBase c_exp n_max x) 2 := by
  have hfit_sh : Fits w (singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hfit_hb : Fits w hashBase :=
    hfit_space.of_le (by omega)
  have e1 : Exec w (.op (.const 15 (singleHashSpace c_exp n_max)) : Code .exact 19)
      x (x.set 15 (singleHashSpace c_exp n_max)) 1 :=
    Exec.const hfit_sh
  have e2 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19)
      (x.set 15 (singleHashSpace c_exp n_max))
      (unshiftFromHash2BaseData hashBase c_exp n_max x) 1 :=
    ExactLog.exec_exactBin (by simp +decide [h0, hash2Base]) hfit_hb
  exact e1.seq e2

private theorem ExecRand.seqDet {w : ℕ} {c₁ c₂ : Code .exact 19} {x : Data 19}
    {m₁ : ProbComp (Data 19 × ℕ)} {f : Data 19 → Data 19} {n₂ : ℕ}
    (h₁ : ExecRand w c₁ x m₁)
    (h₂ : ∀ z ∈ m₁.support, Exec w c₂ z.1 (f z.1) n₂) :
    ExecRand w (.seq c₁ c₂) x ((fun z => (f z.1, z.2 + n₂)) <$> m₁) := by
  have hseq := ExecRand.seq h₁ (m₂ := fun y => pure (f y, n₂)) fun z hz => (h₂ z hz).execRand
  simpa only [pure_bind, ← bind_pure_comp] using hseq

/-- Program resampling a single regime-switched hash block at `reg 0 = base`. -/
@[expose]
def resampleSingleCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    (KWise.resampleCode (cuckooK n_max)).rename cast18To19
  else
    (DoubleTabulation.resampleCode
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M).rename cast12To19

/-- Program shifting `reg 0` to `hash2Base`, resampling the second hash block, and restoring
`reg 0 = hashBase`. -/
@[expose]
def resampleSecondBlockCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  .seq (shiftToHash2BaseCode c_exp n_max)
  (.seq (resampleSingleCode c_exp n_max M)
        (unshiftFromHash2BaseCode c_exp n_max))

/-- Complete seed-resampling program `resampleHashPairCode`: resamples both regime-switched hash
blocks at `hashBase` and `hash2Base hashBase c_exp n_max` while preserving `reg 0 = hashBase` and
`HashPairTableRep`. -/
@[expose]
def resampleHashPairCode (c_exp n_max M : ℕ) : Code .exact 19 :=
  .seq (resampleSingleCode c_exp n_max M) (resampleSecondBlockCode c_exp n_max M)

/-- Exact instruction count of `resampleSingleCode c_exp n_max M`. -/
@[expose]
def resampleSingleSteps (c_exp n_max : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    5 * cuckooK n_max + 10
  else
    DoubleTabulation.resampleSteps
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max)

/-- Exact instruction count of `resampleHashPairCode c_exp n_max M`. -/
@[expose]
def resampleHashPairSteps (c_exp n_max : ℕ) : ℕ :=
  2 * resampleSingleSteps c_exp n_max + 4

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resampleSingleCode c_exp n_max M` at `base`. -/
@[expose]
noncomputable def resampleSingleComp (base c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) :=
  if n_max < doubleTabThreshold c_exp then
    (fun z : Data 18 × ℕ => (z.1.extend cast18To19 x, z.2)) <$>
      KWise.resampleComp base U M (cuckooK n_max) (x.comap cast18To19)
  else
    (fun z : Data 12 × ℕ => (z.1.extend cast12To19 x, z.2)) <$>
      DoubleTabulation.resampleComp base
        (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
        (DoubleTabulation.provableB n_max) M (x.comap cast12To19)

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resampleSecondBlockCode c_exp n_max M`. -/
@[expose]
noncomputable def resampleSecondBlockComp (hashBase c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) :=
  let d0 := shiftToHash2BaseData hashBase c_exp n_max x
  (fun z : Data 19 × ℕ => (unshiftFromHash2BaseData hashBase c_exp n_max z.1, 2 + (z.2 + 2))) <$>
    resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0

/-- Exact `ProbComp` semantics of `resampleHashPairCode c_exp n_max M`. -/
@[expose]
noncomputable def resampleHashPairComp (hashBase c_exp n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) := do
  let z1 ← resampleSingleComp hashBase c_exp n_max U M x
  let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
  pure (z2.1, z1.2 + z2.2)

theorem resampleSingleCode_execRand {w base c_exp n_max U M : ℕ} {x : Data 19}
    (htab : SingleTableRep base c_exp n_max U M x.mem) (hbase : x.regs 0 = base)
    (hfit_space : Fits w (base + singleHashSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleSingleCode c_exp n_max M) x
      (resampleSingleComp base c_exp n_max U M x) := by
  unfold resampleSingleCode resampleSingleComp
  split_ifs with hlt
  · have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    have hfit_end : Fits w (base + 8 + cuckooK n_max) :=
      hfit_space.of_le (by omega)
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    have hbase18 : (x.comap cast18To19).regs 0 = base := hbase
    exact (KWise.resampleCode_execRand htab_kw hbase18 hfit_end hfit_q).rename injective_cast18To19
  · have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hfit_dt : Fits w (base + DoubleTabulation.space (DoubleTabulation.provableC c_exp)
        (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max)) := by
      rwa [← hsp]
    have hpow_b_le : 2 ^ DoubleTabulation.provableB n_max ≤
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      have hc : 1 ≤ DoubleTabulation.provableC c_exp := DoubleTabulation.one_le_provableC c_exp
      have hd : 1 ≤ DoubleTabulation.provableD c_exp := by
        dsimp only [DoubleTabulation.provableD]; omega
      have hle : 1 * 2 ^ DoubleTabulation.provableB n_max ≤
          ((DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp) *
            2 ^ DoubleTabulation.provableB n_max :=
        Nat.mul_le_mul_right _ (by nlinarith)
      dsimp only [DoubleTabulation.space]
      omega
    have hfit_mask_b : Fits w (2 ^ DoubleTabulation.provableB n_max - 1) :=
      hfit_dt.of_le (by omega)
    have hfit_mask_M : Fits w (2 ^ M - 1) :=
      hfit_q.of_le ((Nat.sub_le _ 1).trans
        (Nat.pow_le_pow_right (by decide) (Probability.le_trinomialDeg U M)))
    have hfit_1 : Fits w 1 :=
      hfit_space.of_le (by have := le_singleHashSpace c_exp n_max; omega)
    have hbase12 : (x.comap cast12To19).regs 0 = base := hbase
    exact (DoubleTabulation.resampleCode_execRand hbase12 hfit_dt
      hfit_mask_b hfit_mask_M hfit_1).rename injective_cast12To19

theorem mem_support_resampleSingleComp {base c_exp n_max U M : ℕ} {x : Data 19} {z : Data 19 × ℕ}
    (htab : SingleTableRep base c_exp n_max U M x.mem) (hbase : x.regs 0 = base)
    (hz : z ∈ (resampleSingleComp base c_exp n_max U M x).support) :
    z.2 ≤ resampleSingleSteps c_exp n_max ∧
    z.1.regs 0 = base ∧
    SingleTableRep base c_exp n_max U M z.1.mem ∧
    SingleSeedRep base c_exp n_max U M (extractSingleSeed base c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < base ∨ base + singleHashSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  unfold resampleSingleComp at hz
  split_ifs at hz with hlt
  · obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    have hbase18 : (x.comap cast18To19).regs 0 = base := hbase
    obtain ⟨⟨⟨htab', hseed'⟩, hz0, hout⟩, hsteps⟩ :=
      KWise.mem_support_resampleComp htab_kw hbase18 hz₀
    have h0' : (z₀.1.extend cast18To19 x).regs 0 = base := by
      change ((z₀.1.extend cast18To19 x).comap cast18To19).regs 0 = base
      rw [Data.comap_extend injective_cast18To19, hz0]
    have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hpow : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
    have hkw : KWise.space n_max (cuckooK n_max) =
        8 + cuckooK n_max + 2 ^ (2 * KWise.chunkBits n_max) := rfl
    refine ⟨by simpa [resampleSingleSteps, hlt] using hsteps, h0', ?_, ?_,
      fun a ha => hout a (by omega)⟩
    · unfold SingleTableRep
      rw [decide_eq_true hlt]
      exact htab'
    · unfold SingleSeedRep extractSingleSeed
      revert hseed'
      rw [decide_eq_true hlt]
      exact id
  · obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hbase12 : (x.comap cast12To19).regs 0 = base := hbase
    obtain ⟨hz0, hseed', hout, hsteps⟩ :=
      DoubleTabulation.mem_support_resampleComp hbase12 hz₀
    have h0' : (z₀.1.extend cast12To19 x).regs 0 = base := by
      change ((z₀.1.extend cast12To19 x).comap cast12To19).regs 0 = base
      rw [Data.comap_extend injective_cast12To19, hz0]
    have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    refine ⟨by simp [resampleSingleSteps, hlt, hsteps], h0', ?_, ?_,
      fun a ha => hout a (by rwa [← hsp])⟩
    · unfold SingleTableRep
      rw [decide_eq_false hlt]
      trivial
    · unfold SingleSeedRep extractSingleSeed
      revert hseed'
      rw [decide_eq_false hlt]
      exact id

theorem resampleSecondBlockCode_execRand {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M x.mem)
    (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleSecondBlockCode c_exp n_max M) x
      (resampleSecondBlockComp hashBase c_exp n_max U M x) := by
  have esh := shiftToHash2BaseCode_exec h0 hfit_space
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  have hres := resampleSingleCode_execRand (x := d0) htab2 hd0_0 hfit_h2 hfit_q
  have hdet := ExecRand.seqDet hres (f := unshiftFromHash2BaseData hashBase c_exp n_max) (n₂ := 2)
    fun z hz => by
      obtain ⟨-, hz0, -, -, -⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz
      exact unshiftFromHash2BaseCode_exec hz0 hfit_space
  simpa only [resampleSecondBlockCode, resampleSecondBlockComp, d0, Functor.map_map] using
    esh.seqRand hdet

theorem mem_support_resampleSecondBlockComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    {z : Data 19 × ℕ}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M x.mem)
    (hz : z ∈ (resampleSecondBlockComp hashBase c_exp n_max U M x).support) :
    z.2 ≤ resampleSingleSteps c_exp n_max + 4 ∧
    z.1.regs 0 = hashBase ∧
    SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem ∧
    SingleSeedRep (hash2Base hashBase c_exp n_max) c_exp n_max U M
      (extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < hash2Base hashBase c_exp n_max ∨
      hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resampleSecondBlockComp] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  obtain ⟨ht, -, htab', hseed', hout⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz₀
  exact ⟨by omega, by simp +decide [unshiftFromHash2BaseData], htab', hseed', hout⟩

/-- **`resampleHashPairCode` randomized execution**: resamples both regime-switched hash blocks at
`hashBase` and `hash2Base hashBase c_exp n_max`. -/
theorem resampleHashPairCode_execRand {w hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w (resampleHashPairCode c_exp n_max M) x
      (resampleHashPairComp hashBase c_exp n_max U M x) := by
  have hfit_h1 : Fits w (hashBase + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have h1 := resampleSingleCode_execRand htab.1 h0 hfit_h1 hfit_q
  refine h1.seq fun z1 hz1 => ?_
  obtain ⟨-, hz1_0, -, -, hz1_frame⟩ := mem_support_resampleSingleComp htab.1 h0 hz1
  have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
    htab.2.congr_of_footprint (fun a ha1 _ =>
      hz1_frame a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
  exact resampleSecondBlockCode_execRand htab2_z1 hz1_0 hfit_space hfit_q

theorem mem_support_resampleHashPairComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    {z : Data 19 × ℕ}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hz : z ∈ (resampleHashPairComp hashBase c_exp n_max U M x).support) :
    z.2 ≤ resampleHashPairSteps c_exp n_max ∧
    z.1.regs 0 = hashBase ∧
    HashPairRep hashBase c_exp n_max U M (extractSeed hashBase c_exp n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < hashBase ∨ hashBase + hashPairSpace c_exp n_max ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resampleHashPairComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨ht1, -, htab1_z1, hseed1_z1, hframe1⟩ :=
    mem_support_resampleSingleComp htab.1 h0 hz1
  have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
    htab.2.congr_of_footprint (fun a ha1 _ =>
      hframe1 a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
  obtain ⟨ht2, hz2_0, htab2_z2, hseed2_z2, hframe2⟩ :=
    mem_support_resampleSecondBlockComp htab2_z1 hz2
  have hframe_block1 : ∀ a, hashBase ≤ a → a < hashBase + singleHashSpace c_exp n_max →
      z2.1.mem a = z1.1.mem a :=
    fun a _ ha2 => hframe2 a (Or.inl (by dsimp only [hash2Base]; omega))
  have htab1_z2 : SingleTableRep hashBase c_exp n_max U M z2.1.mem :=
    htab1_z1.congr_of_footprint hframe_block1
  have hextract1_eq :
      extractSingleSeed hashBase c_exp n_max U M z2.1.mem =
        extractSingleSeed hashBase c_exp n_max U M z1.1.mem :=
    extractSingleSeed_congr_of_footprint hframe_block1
  have hseed1_z2 : SingleSeedRep hashBase c_exp n_max U M
      (extractSingleSeed hashBase c_exp n_max U M z2.1.mem) z2.1.mem := by
    rw [hextract1_eq]
    exact hseed1_z1.congr_of_footprint hframe_block1
  refine ⟨by dsimp only [resampleHashPairSteps]; omega, hz2_0,
    ⟨⟨htab1_z2, htab2_z2⟩, hashPairSeedRep_extractSeed_of_single hseed1_z2 hseed2_z2⟩,
    fun a ha => ?_⟩
  have ha2 : a < hash2Base hashBase c_exp n_max ∨
      hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max ≤ a := by
    dsimp only [hash2Base, hashPairSpace] at ha ⊢
    exact ha.imp (by omega) (by omega)
  have ha1 : a < hashBase ∨ hashBase + singleHashSpace c_exp n_max ≤ a := by
    dsimp only [hashPairSpace] at ha
    exact ha.imp id (by omega)
  rw [hframe2 a ha2, hframe1 a ha1]

private theorem map_extractSingleSeed_eval_resampleSingleComp
    (base c_exp n_max U M : ℕ) (x : Data 19) :
    ((resampleSingleComp base c_exp n_max U M x).eval).map
      (fun z => extractSingleSeed base c_exp n_max U M z.1.mem) =
      PMF.uniformOfFintype (SingleSeed c_exp n_max U M) := by
  unfold resampleSingleComp SingleSeed extractSingleSeed
  split_ifs with hlt
  · rw [decide_eq_true hlt, ProbComp.eval_map, PMF.map_comp]
    exact KWise.map_extractSeeds_eval_resampleComp base U M (cuckooK n_max) (x.comap cast18To19)
  · rw [decide_eq_false hlt, ProbComp.eval_map, PMF.map_comp]
    exact DoubleTabulation.map_extractSeed_eval_resampleComp base
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) M (x.comap cast12To19)

private theorem map_pair_extractSingleSeed_eval_resampleSecondBlockComp
    {hashBase c_exp n_max U M : ℕ} {d : Data 19}
    (htab2 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M d.mem) :
    ((resampleSecondBlockComp hashBase c_exp n_max U M d).eval).map
      (fun z : Data 19 × ℕ =>
        (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
         extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) =
      (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
        (extractSingleSeed hashBase c_exp n_max U M d.mem, ·) := by
  set d0 := shiftToHash2BaseData hashBase c_exp n_max d
  have hd0_0 : d0.regs 0 = hash2Base hashBase c_exp n_max := by
    simp +decide [d0, shiftToHash2BaseData]
  dsimp only [resampleSecondBlockComp]
  rw [ProbComp.eval_map, PMF.map_comp]
  have hcongr :
      ((resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0).eval).map
        ((fun z : Data 19 × ℕ =>
            (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
             extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) ∘
          fun z : Data 19 × ℕ =>
            (unshiftFromHash2BaseData hashBase c_exp n_max z.1, 2 + (z.2 + 2))) =
      ((resampleSingleComp (hash2Base hashBase c_exp n_max) c_exp n_max U M d0).eval).map
        ((fun θ₂ => (extractSingleSeed hashBase c_exp n_max U M d.mem, θ₂)) ∘
          fun z : Data 19 × ℕ =>
            extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem) := by
    refine PMF.map_congr_on_support _ _ _ fun z hz => ?_
    rw [ProbComp.support_eval] at hz
    obtain ⟨-, -, -, -, hframe⟩ := mem_support_resampleSingleComp (x := d0) htab2 hd0_0 hz
    have h1 : extractSingleSeed hashBase c_exp n_max U M z.1.mem =
        extractSingleSeed hashBase c_exp n_max U M d.mem :=
      extractSingleSeed_congr_of_footprint (fun a _ ha2 =>
        hframe a (Or.inl (by dsimp only [hash2Base]; omega)))
    dsimp only [Function.comp_apply, unshiftFromHash2BaseData, Data.set]
    rw [h1]
  rw [hcongr, ← PMF.map_comp,
    map_extractSingleSeed_eval_resampleSingleComp
      (hash2Base hashBase c_exp n_max) c_exp n_max U M d0]

private theorem map_pair_extractSingleSeed_eval_resampleHashPairComp
    {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase) :
    ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z : Data 19 × ℕ =>
        (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
         extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) =
      PMF.uniformOfFintype (SingleSeed c_exp n_max U M × SingleSeed c_exp n_max U M) := by
  dsimp only [resampleHashPairComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  have hcongr :
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          ((do
            let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
            pure (z2.1, z1.2 + z2.2)).eval).map
            (fun z : Data 19 × ℕ =>
              (extractSingleSeed hashBase c_exp n_max U M z.1.mem,
               extractSingleSeed (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem))) =
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
            (extractSingleSeed hashBase c_exp n_max U M z1.1.mem, ·)) := by
    refine PMF.bind_congr_on_support _ _ _ fun z1 hz1 => ?_
    rw [ProbComp.support_eval] at hz1
    obtain ⟨-, -, -, -, hframe1⟩ := mem_support_resampleSingleComp htab.1 h0 hz1
    have htab2_z1 : SingleTableRep (hash2Base hashBase c_exp n_max) c_exp n_max U M z1.1.mem :=
      htab.2.congr_of_footprint (fun a ha1 _ =>
        hframe1 a (Or.inr (by dsimp only [hash2Base] at ha1; omega)))
    have hd : (do
        let z2 ← resampleSecondBlockComp hashBase c_exp n_max U M z1.1
        pure (z2.1, z1.2 + z2.2)) =
        (fun z2 : Data 19 × ℕ => (z2.1, z1.2 + z2.2)) <$>
          resampleSecondBlockComp hashBase c_exp n_max U M z1.1 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    exact map_pair_extractSingleSeed_eval_resampleSecondBlockComp htab2_z1
  rw [hcongr]
  have hbind :
      (resampleSingleComp hashBase c_exp n_max U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map
            (extractSingleSeed hashBase c_exp n_max U M z1.1.mem, ·)) =
      (((resampleSingleComp hashBase c_exp n_max U M x).eval).map
          (fun z1 => extractSingleSeed hashBase c_exp n_max U M z1.1.mem)).bind
        (fun θ₁ => (PMF.uniformOfFintype (SingleSeed c_exp n_max U M)).map (θ₁, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, map_extractSingleSeed_eval_resampleSingleComp,
    DoubleTabulation.uniformOfFintype_bind_prodMk]

private theorem map_extractSeedAux_eval_resampleHashPairComp (reg : Bool)
    {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (h : ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z : Data 19 × ℕ =>
        (extractSingleSeedAux reg hashBase c_exp n_max U M z.1.mem,
         extractSingleSeedAux reg (hash2Base hashBase c_exp n_max) c_exp n_max U M z.1.mem)) =
      PMF.uniformOfFintype (SingleSeedAux reg c_exp n_max U M ×
        SingleSeedAux reg c_exp n_max U M)) :
    ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z => extractSeedAux reg hashBase c_exp n_max U M z.1.mem) =
      PMF.uniformOfFintype (SeedAux reg c_exp n_max U M) := by
  cases reg <;> exact h

/-- **Exact uniformity of `resampleHashPairComp`**: the extracted seed
`extractSeed hashBase c_exp n_max U M z.1.mem` is distributed according to
`seedLaw c_exp n_max U M`. -/
theorem map_extractSeed_eval_resampleHashPairComp {hashBase c_exp n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase c_exp n_max U M x.mem) (h0 : x.regs 0 = hashBase) :
    ((resampleHashPairComp hashBase c_exp n_max U M x).eval).map
      (fun z => extractSeed hashBase c_exp n_max U M z.1.mem) = seedLaw c_exp n_max U M :=
  map_extractSeedAux_eval_resampleHashPairComp (decide (n_max < doubleTabThreshold c_exp))
    (map_pair_extractSingleSeed_eval_resampleHashPairComp htab h0)

/-- Regime-indexed deterministic evaluation of a single hash block (`h₁` or `h₂`). -/
@[expose]
noncomputable def evalSingleAux (reg : Bool) (c_exp n_max U M : ℕ) :
    SingleSeedAux reg c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  match reg with
  | true => fun θ u => trinomialPolyHash (trinomialStep U M) (cuckooK n_max) U M θ u
  | false => fun θ u =>
    doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max) U M θ.1 θ.2 u

/-- Deterministic evaluation of a single regime-switched hash block (`h₁` or `h₂`). -/
@[expose]
noncomputable def evalSingle (c_exp n_max U M : ℕ) :
    SingleSeed c_exp n_max U M → Fin U → Fin (2 ^ M) :=
  evalSingleAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M

/-- Extract the first block's seed from `SeedAux`. -/
@[expose]
def fstSeedAux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → SingleSeedAux reg c_exp n_max U M :=
  match reg with
  | true => Prod.fst
  | false => Prod.fst

/-- Extract the second block's seed from `SeedAux`. -/
@[expose]
def sndSeedAux (reg : Bool) (c_exp n_max U M : ℕ) :
    SeedAux reg c_exp n_max U M → SingleSeedAux reg c_exp n_max U M :=
  match reg with
  | true => Prod.snd
  | false => Prod.snd

/-- Extract the first block's seed from `θ : Seed c_exp n_max U M`. -/
@[expose]
def fstSeed {c_exp n_max U M : ℕ} (θ : Seed c_exp n_max U M) : SingleSeed c_exp n_max U M :=
  fstSeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M θ

/-- Extract the second block's seed from `θ : Seed c_exp n_max U M`. -/
@[expose]
def sndSeed {c_exp n_max U M : ℕ} (θ : Seed c_exp n_max U M) : SingleSeed c_exp n_max U M :=
  sndSeedAux (decide (n_max < doubleTabThreshold c_exp)) c_exp n_max U M θ

private theorem evalSingle_fstSeed {c_exp n_max U M : ℕ}
    (θ : Seed c_exp n_max U M) (u : Fin U) :
    evalSingle c_exp n_max U M (fstSeed θ) u = evalHash1 θ u := by
  unfold Seed evalSingle fstSeed evalHash1 at *
  revert θ
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro _ <;> rfl

private theorem evalSingle_sndSeed {c_exp n_max U M : ℕ}
    (θ : Seed c_exp n_max U M) (u : Fin U) :
    evalSingle c_exp n_max U M (sndSeed θ) u = evalHash2 θ u := by
  unfold Seed evalSingle sndSeed evalHash2 at *
  revert θ
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro _ <;> rfl

private theorem singleSeedRep_fstSeed {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem) :
    SingleSeedRep hashBase c_exp n_max U M (fstSeed θ) mem := by
  unfold Seed HashPairSeedRep SingleSeedRep fstSeed at *
  revert θ hseed
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro _ hseed <;> exact hseed.1

private theorem singleSeedRep_sndSeed {hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} {mem : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase c_exp n_max U M θ mem) :
    SingleSeedRep (hash2Base hashBase c_exp n_max) c_exp n_max U M (sndSeed θ) mem := by
  unfold Seed HashPairSeedRep SingleSeedRep sndSeed at *
  revert θ hseed
  cases decide (n_max < doubleTabThreshold c_exp) <;> intro _ hseed <;> exact hseed.2

/-- Word-RAM program evaluating a single regime-switched hash block at `reg 0 = base` and
`reg 1 = u.val` into `reg 2` (`regOut`) without modifying memory. -/
@[expose]
def evalSingleCode (c_exp n_max : ℕ) : Code .exact 19 :=
  if n_max < doubleTabThreshold c_exp then
    (KWise.evalCode (cuckooK n_max)).rename cast18To19
  else
    (DoubleTabulation.evalCode
      (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
      (DoubleTabulation.provableB n_max)).rename cast12To19

/-- Word-RAM program evaluating `h₁(u)` into `reg 2` (`regOut`) while preserving
`reg 0 = hashBase`, `reg 1 = u.val`, and all of memory (`y.mem = x.mem`). -/
@[expose]
def evalHash1Code (c_exp n_max : ℕ) : Code .exact 19 :=
  evalSingleCode c_exp n_max

/-- Word-RAM program evaluating `h₂(u)` into `reg 2` (`regOut`) while preserving
`reg 0 = hashBase`, `reg 1 = u.val`, and all of memory (`y.mem = x.mem`). -/
@[expose]
def evalHash2Code (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (shiftToHash2BaseCode c_exp n_max)
  (.seq (evalSingleCode c_exp n_max)
        (unshiftFromHash2BaseCode c_exp n_max))

/-- Step bound for `evalSingleCode c_exp n_max`. -/
@[expose]
def evalSingleSteps (c_exp n_max U M : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    KWise.evalSteps n_max U M (cuckooK n_max)
  else
    DoubleTabulation.evalSteps (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)

/-- Step bound for `evalHash1Code c_exp n_max` and `evalHash2Code c_exp n_max`. -/
@[expose]
def evalHashSteps (c_exp n_max U M : ℕ) : ℕ :=
  evalSingleSteps c_exp n_max U M + 4

/-- Uniform `O_{c_exp}(1)` instruction bound on `evalHashSteps c_exp n_max U M` across all
`n_max : ℕ`. -/
@[expose]
def evalHashBound (c_exp : ℕ) : ℕ :=
  DoubleTabulation.provableEvalBound c_exp (cuckooKBound c_exp) + 4

/-- **All-`n_max` constant instruction bound for `evalHashSteps` (`O_{c_exp}(1)`)**:
whenever `U ≤ max n_max 4 ^ c_exp` and `M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5`,
`evalHashSteps c_exp n_max U M ≤ evalHashBound c_exp`. -/
theorem evalHashSteps_le {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5) :
    evalHashSteps c_exp n_max U M ≤ evalHashBound c_exp := by
  dsimp only [evalHashSteps, evalSingleSteps, evalHashBound, DoubleTabulation.provableEvalBound]
  refine Nat.add_le_add_right ?_ 4
  split_ifs with hlt
  · refine le_trans ?_ (le_max_left _ _)
    dsimp only [KWise.evalSteps, KWise.evalStepsFromB]
    have hL : KWise.limbCountFromB (KWise.chunkBits n_max) (trinomialDeg U M) ≤
        DoubleTabulation.provableLimbBound c_exp :=
      DoubleTabulation.limbCount_le_provableLimbBound hU hM
    have hk : cuckooK n_max ≤ cuckooKBound c_exp :=
      cuckooK_le_cuckooKBound_of_lt hlt
    gcongr
  · exact le_max_right _ _

theorem evalSingleCode_execWithin {w base c_exp n_max U M : ℕ}
    {θ₀ : SingleSeed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (htab : SingleTableRep base c_exp n_max U M x.mem)
    (hseed : SingleSeedRep base c_exp n_max U M θ₀ x.mem)
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + singleHashSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalSingleCode c_exp n_max) x y (evalSingleSteps c_exp n_max U M) ∧
      y.regs 0 = base ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalSingle c_exp n_max U M θ₀ u).val ∧
      y.mem = x.mem := by
  unfold evalSingleCode evalSingleSteps
  split_ifs with hlt
  · have hsp : singleHashSpace c_exp n_max = KWise.space n_max (cuckooK n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hfit_kw : Fits w (base + KWise.space n_max (cuckooK n_max)) := by
      rwa [← hsp]
    have htab_kw : KWise.TableRep base (KWise.chunkBits n_max) U M (cuckooK n_max) x.mem := by
      unfold SingleTableRep at htab
      rwa [decide_eq_true hlt] at htab
    unfold SingleSeed SingleSeedRep evalSingle at *
    revert θ₀ hseed
    rw [decide_eq_true hlt]
    intro θ₀ hseed
    obtain ⟨y_kw, hex_kw, hy0, hy1, hy2, hymem⟩ :=
      KWise.evalCode_execWithin (w := w) (base := base) (n_max := n_max)
        (U := U) (M := M) (k := cuckooK n_max) (c := θ₀) u (x := x.comap cast18To19)
        ⟨htab_kw, hseed⟩
        (by simp +decide [cast18To19, Data.comap, h0])
        (by simp +decide [cast18To19, Data.comap, h1])
        hw hfit_kw
    refine ⟨y_kw.extend cast18To19 x, hex_kw.rename injective_cast18To19, ?_, ?_, ?_, hymem⟩
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 0 = base
      rw [Data.comap_extend injective_cast18To19, hy0]
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 1 = u.val
      rw [Data.comap_extend injective_cast18To19, hy1]
    · change ((y_kw.extend cast18To19 x).comap cast18To19).regs 2 =
        (trinomialPolyHash (trinomialStep U M) (cuckooK n_max) U M θ₀ u).val
      rw [Data.comap_extend injective_cast18To19, hy2]
  · have hsp : singleHashSpace c_exp n_max =
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      simp [singleHashSpace, DoubleTabulation.provableSpace, hlt]
    have hfit_dt : Fits w (base + DoubleTabulation.space (DoubleTabulation.provableC c_exp)
        (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max)) := by
      rwa [← hsp]
    have hpow_b_le : 2 ^ DoubleTabulation.provableB n_max ≤
        DoubleTabulation.space (DoubleTabulation.provableC c_exp)
          (DoubleTabulation.provableD c_exp) (DoubleTabulation.provableB n_max) := by
      have hc : 1 ≤ DoubleTabulation.provableC c_exp := DoubleTabulation.one_le_provableC c_exp
      have hd : 1 ≤ DoubleTabulation.provableD c_exp := by
        dsimp only [DoubleTabulation.provableD]; omega
      have hle : 1 * 2 ^ DoubleTabulation.provableB n_max ≤
          ((DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp) *
            2 ^ DoubleTabulation.provableB n_max :=
        Nat.mul_le_mul_right _ (by nlinarith)
      dsimp only [DoubleTabulation.space]
      omega
    have hfit_pow_b : Fits w (2 ^ DoubleTabulation.provableB n_max) :=
      hfit_dt.of_le (by omega)
    have hq_pos : 0 < Probability.trinomialDeg U M := by
      dsimp only [Probability.trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ Probability.trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hfit_pow_M : Fits w (2 ^ M) :=
      hfit_q.of_le (Nat.pow_le_pow_right (by decide) (Probability.le_trinomialDeg U M))
    have hfit_u : Fits w u.val :=
      hfit_q.of_le (le_trans (le_of_lt u.isLt) (Probability.le_two_pow_trinomialDeg U M))
    unfold SingleSeed SingleSeedRep evalSingle at *
    revert θ₀ hseed
    rw [decide_eq_false hlt]
    intro θ₀ hseed
    obtain ⟨y12, he12, hymem, hy0, hy1, hy2, _⟩ :=
      DoubleTabulation.evalCode_execWithin u (x := x.comap cast12To19)
        (by simp +decide [cast12To19, Data.comap, h0])
        (by simp +decide [cast12To19, Data.comap, h1])
        hseed hfit_dt hfit_pow_b hfit_pow_M hfit_u
    refine ⟨y12.extend cast12To19 x, he12.rename injective_cast12To19, ?_, ?_, ?_, hymem⟩
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 0 = base
      rw [Data.comap_extend injective_cast12To19, hy0]
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 1 = u.val
      rw [Data.comap_extend injective_cast12To19, hy1]
    · change ((y12.extend cast12To19 x).comap cast12To19).regs 2 =
        (doubleTabHash (DoubleTabulation.provableC c_exp) (DoubleTabulation.provableD c_exp)
          (DoubleTabulation.provableB n_max) U M θ₀.1 θ₀.2 u).val
      rw [Data.comap_extend injective_cast12To19, hy2]

theorem evalHash1Code_execWithin {w hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase c_exp n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalHash1Code c_exp n_max) x y (evalHashSteps c_exp n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash1 θ u).val ∧
      HashPairRep hashBase c_exp n_max U M θ y.mem ∧
      y.mem = x.mem := by
  have hfit_h1 : Fits w (hashBase + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  obtain ⟨y, ⟨t, ht, he⟩, hy0, hy1, hy2, hymem⟩ :=
    evalSingleCode_execWithin u hrep.1.1 (singleSeedRep_fstSeed hrep.2) h0 h1 hw hfit_h1
  rw [evalSingle_fstSeed] at hy2
  refine ⟨y, ⟨t, by dsimp only [evalHashSteps]; omega, he⟩, hy0, hy1, hy2, ?_, hymem⟩
  rwa [hymem]

theorem evalHash2Code_execWithin {w hashBase c_exp n_max U M : ℕ}
    {θ : Seed c_exp n_max U M} (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase c_exp n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace c_exp n_max)) :
    ∃ y : Data 19,
      ExecWithin w (evalHash2Code c_exp n_max) x y (evalHashSteps c_exp n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash2 θ u).val ∧
      HashPairRep hashBase c_exp n_max U M θ y.mem ∧
      y.mem = x.mem := by
  have esh := shiftToHash2BaseCode_exec h0 hfit_space
  set d0 := shiftToHash2BaseData hashBase c_exp n_max x
  have hfit_h2 : Fits w (hash2Base hashBase c_exp n_max + singleHashSpace c_exp n_max) :=
    hfit_space.of_le (by dsimp only [hash2Base, hashPairSpace]; omega)
  obtain ⟨d1, ⟨t, ht, he⟩, hd1_0, hd1_1, hd1_2, hd1_mem⟩ :=
    evalSingleCode_execWithin u (x := d0) hrep.1.2 (singleSeedRep_sndSeed hrep.2)
      (by simp +decide [d0, shiftToHash2BaseData])
      (by simp +decide [d0, shiftToHash2BaseData, h1])
      hw hfit_h2
  rw [evalSingle_sndSeed] at hd1_2
  have eun := unshiftFromHash2BaseCode_exec hd1_0 hfit_space
  set y := unshiftFromHash2BaseData hashBase c_exp n_max d1
  refine ⟨y, ⟨2 + (t + 2), by dsimp only [evalHashSteps]; omega, esh.seq (he.seq eun)⟩,
    by simp +decide [y, unshiftFromHash2BaseData],
    by simp +decide [y, unshiftFromHash2BaseData, hd1_1],
    by simp +decide [y, unshiftFromHash2BaseData, hd1_2],
    ?_, ?_⟩
  · change HashPairRep hashBase c_exp n_max U M θ d1.mem
    rwa [hd1_mem]
  · exact hd1_mem

end Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
