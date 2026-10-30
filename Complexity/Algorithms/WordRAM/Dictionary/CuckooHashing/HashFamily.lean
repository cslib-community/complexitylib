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
public import Complexity.Probability.PMF.UniformSubset
public import Complexity.Probability.Uniform
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Cuckoo hash family, pure replay semantics, and shared-table Word-RAM hashing

This module develops the pure displacement and replay model of Pagh and Rodler's two-table cuckoo
hashing scheme [PaghRodler2004] together with a self-contained Word-RAM hash pair
`h_r(u) = f_r(u) ^^^ Z_r[g_r(u)]` (`r ∈ {1, 2}`) built from `Cslib.Algorithms.WordRAM.Hashing.KWise`
(`k = 7`, sharing a single Four-Russians carryless-multiplication table `clmulTab` across all four
polynomial hashes `f₁, g₁, f₂, g₂`) and two random tabulation arrays `Z₁, Z₂` from
`Cslib.Algorithms.WordRAM.Hashing.Tabulation.RandomTable`.

## Primary-source mapping

* **Pagh and Rodler [PaghRodler2004]:** R. Pagh and F. F. Rodler, *"Cuckoo Hashing"*, author-hosted
  journal manuscript (8 December 2003, published in *Journal of Algorithms* 51(2):122–144, 2004),
  **Section 2.3 ("Analysis", manuscript pp. 6–10)**: **Lemma 1** (manuscript p. 7,
  distinct-subsequence structure of displacement walks when the cuckoo graph contains no component
  with more than one cycle), **Eq. (3) on manuscript p. 9** (expected displacement iterations
  `O(1)`), and **manuscript pp. 9–10** (rehash probability and amortized rebuild analysis in two
  tables of size `m ≥ (1 + ε) n`, where `ε ≥ 1` here since `m = 2 ^ M ≥ 4 n_max`).
* **Original strengthened sufficient assumptions (`IsCuckooHashPair`):** Rather than formalizing the
  paper's random-graph event directly, `GoodForSet`, `cuckooWalkRounds`, and `IsCuckooHashPair` are
  **original strengthened sufficient assumptions** tailored to insertion-order replay:
  `GoodForSet` quantifies over every duplicate-free (`Nodup`) sublist/insertion order in `S`,
  `cuckooWalkRounds` takes the supremum (`sSup`) over all `ValidPlacement`s of `S`, and
  `rehash_prob_le_half` / `step_rehash_prob_le` package the whole-set `≤ 1 / 2` and incremental
  one-step `≤ C_reh / (max n_max 1 * max MaxLoop 1)` replay failure bounds over the
  oblivious-adversary model (`Dictionary.spec U V n_max` is deterministic, fixing the sequence of
  insertion-order key lists `ks_0, …, ks_t` independently of internal coin flips). For `n_max ≤ 2`,
  `isCuckooHashPair_le_two` and `isCuckooHashFamily_le_two` instantiate `IsCuckooHashPair` and
  `IsCuckooHashFamily` unconditionally with `C_walk = 1` and `C_reh = 0`.
* **Dietzfelbinger and Woelfel [DietzfelbingerWoelfel2003] variant note:** `Seed` and
  `(evalHash1, evalHash2)` form a **modified variant** inspired by M. Dietzfelbinger and P. Woelfel,
  *"Almost Random Graphs with Simple Hash Functions"*, *Proc. 35th ACM STOC*, 2003,
  **Definition 1 (§2.1, p. 632)**. Dietzfelbinger and Woelfel's Definition 1 uses a **single shared
  auxiliary hash `g`** and addition modulo `m` (and explicitly distinguishes that shared-`g` pair
  from choosing two independent single-hash instances), whereas `(evalHash1, evalHash2)` here uses
  **independent `g₁, g₂`** and bitwise XOR (`finXor`) over `Fin (2 ^ M)`. The per-function `7`-wise
  independence theorems (`isKWiseIndependentHash_evalHash1`, `isKWiseIndependentHash_evalHash2`) do
  **not** establish Dietzfelbinger and Woelfel's graph/rehash guarantees for this modified pair, and
  correspondence / `IsCuckooHashFamily` instantiation for `n_max ≥ 3` remains unproved.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.tableBits`, `tableSize`, `maxEvictions`:
  sub-table bit-width `M = ⌈log₂ max(4 n_max, 4)⌉`, sub-table size `m = 2 ^ M`, and eviction cap
  `MaxLoop = 6 (⌈log₂ max(n_max, 2)⌉ + 2)`.
* `SlotEntry`, `PureTable`, `WellPlaced`, `lookupEntry`, `pureEvictRound`, `pureEvict`,
  `pureReplay`: pure two-table cuckoo displacement and insertion-order replay model.
* `GoodForSet`, `survivingSeeds`, `cuckooWalkRounds`, `IsCuckooHashPair`, `IsCuckooHashFamily`:
  strengthened sufficient cuckoo hash family interface for expected displacement rounds and rehash
  probability.
* `Seed`, `seedLaw`, `evalHash1`, `evalHash2`: modified tabulated polynomial seed space and hash
  pair `h_r(u) = f_r(u) ^^^ Z_r[g_r(u)]` with independent `g₁, g₂` and bitwise XOR over
  `Fin (2 ^ M)`.
* `HashPairRep`, `initTableHashPairCode`, `resampleHashPairCode`, `evalHash1Code`, `evalHash2Code`:
  Word-RAM layout and programs sharing one `KWise` `clmulTab` across `f₁, g₁, f₂, g₂`.

## Main results

* `pureReplay_append_singleton`, `pureReplay_lookupEntry_of_mem`: incremental eviction from the
  replayed table coincides with full replay of `ks ++ [u]`, and `lookupEntry` recovers the exact
  index of every inserted key in `O(1)` probes.
* `survivingSeeds_append_subset`, `mem_survivingSeeds_of_goodForSet`: monotonicity of surviving
  replay seeds across insertions (combined with `Cslib.Probability.PMF.unifOn_rehash_eq` and
  `Cslib.Probability.PMF.uniformOfFinset_le_two_mul_uniformOfFintype` from
  `Complexity/Probability/PMF/UniformSubset.lean`).
* `isKWiseIndependentHash_evalHash1`, `isKWiseIndependentHash_evalHash2`: each individual hash
  function `evalHash1` and `evalHash2` is exact `7`-wise independent onto `Fin (2 ^ M)`.
* `isCuckooHashPair_le_two`, `isCuckooHashFamily_le_two`, `isCuckooHashFamily_le_one`:
  unconditional `IsCuckooHashPair` and `IsCuckooHashFamily` instances for `n_max ≤ 2` (`C_walk = 1`,
  `C_reh = 0`).
* `initTableHashPairCode_execWithin`, `resampleHashPairCode_execRand`, `evalHash1Code_execWithin`,
  `evalHash2Code_execWithin`: Word-RAM correctness and step bounds for initializing, resampling
  (without rebuilding `clmulTab`), and evaluating the hash pair.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Analysis", pp. 6–10: Lemma 1 on p. 7, Eq. (3) on p. 9, and rehash
  analysis on pp. 9–10).
* [M. Dietzfelbinger and P. Woelfel, *Almost Random Graphs*][DietzfelbingerWoelfel2003]
  (Definition 1, §2.1, p. 632).
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

/-- Sub-table bit-width `M = ⌈log₂ max(4 * n_max, 4)⌉`, ensuring each of the two cuckoo sub-tables
has size `m = 2 ^ M ≥ max (4 * n_max) 4` (load factor `≤ 1 / 4` per table). -/
@[expose]
def tableBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max (4 * n_max) 4)

/-- Sub-table capacity `m = 2 ^ tableBits n_max`. -/
@[expose]
def tableSize (n_max : ℕ) : ℕ :=
  2 ^ tableBits n_max

/-- Maximum number of two-table cuckoo displacement rounds `6 * (⌈log₂ max(n_max, 2)⌉ + 2)` before
triggering a full-table rehash. -/
@[expose]
def maxEvictions (n_max : ℕ) : ℕ :=
  6 * (Nat.clog 2 (max n_max 2) + 2)

theorem two_le_tableBits (n_max : ℕ) : 2 ≤ tableBits n_max := by
  unfold tableBits
  have h4 : 4 ≤ max (4 * n_max) 4 := le_max_right _ _
  have h2 : Nat.clog 2 4 = 2 := by decide
  rw [← h2]
  exact Nat.clog_mono_right 2 h4

theorem tableBits_pos (n_max : ℕ) : 0 < tableBits n_max := by
  have := two_le_tableBits n_max
  omega

theorem four_mul_max_le_tableSize (n_max : ℕ) :
    max (4 * n_max) 4 ≤ tableSize n_max := by
  unfold tableSize tableBits
  exact Nat.le_pow_clog (by decide) _

theorem four_mul_le_tableSize (n_max : ℕ) : 4 * n_max ≤ tableSize n_max :=
  le_trans (le_max_left _ _) (four_mul_max_le_tableSize n_max)

theorem four_le_tableSize (n_max : ℕ) : 4 ≤ tableSize n_max :=
  le_trans (le_max_right _ _) (four_mul_max_le_tableSize n_max)

theorem tableSize_pos (n_max : ℕ) : 0 < tableSize n_max := by
  have := four_le_tableSize n_max
  omega

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

/-! ### Section 4: Concrete tabulated polynomial hash pair `f_r(u) ^^^ Z_r[g_r(u)]` -/

/-- Degree-`< 7` trinomial polynomial seed space over `TrinomialField (trinomialStep U M)`. -/
abbrev PolySeed (U M : ℕ) : Type :=
  Fin 7 → Fin (2 ^ Probability.trinomialDeg U M)

/-- Random tabulation array seed space `Fin (2 ^ M) → Fin (2 ^ M)`. -/
abbrev TabSeed (M : ℕ) : Type :=
  Fin (2 ^ M) → Fin (2 ^ M)

/-- Full cuckoo hash seed storing four 7-wise independent polynomial seeds `(cf₁, cg₁, cf₂, cg₂)`
and two random tabulation arrays `(Z₁, Z₂)` of size `2 ^ M`. This is a modified variant of
Dietzfelbinger and Woelfel [DietzfelbingerWoelfel2003, Definition 1, §2.1, p. 632] using
independent auxiliary polynomial hashes `g₁, g₂` and bitwise XOR (`finXor`) over `Fin (2 ^ M)`
rather than a single shared `g` and addition modulo `m`. -/
abbrev Seed (U M : ℕ) : Type :=
  (Fin 4 → PolySeed U M) × TabSeed M × TabSeed M

/-- Uniform seed distribution over `Seed U M`. -/
@[expose]
noncomputable def seedLaw (U M : ℕ) : PMF (Seed U M) :=
  PMF.uniformOfFintype (Seed U M)

/-- Bitwise XOR on `Fin (2 ^ M)`. -/
@[expose]
def finXor {M : ℕ} (a b : Fin (2 ^ M)) : Fin (2 ^ M) :=
  ⟨a.val ^^^ b.val, Nat.xor_lt_two_pow a.isLt b.isLt⟩

@[simp]
theorem val_finXor {M : ℕ} (a b : Fin (2 ^ M)) :
    (finXor a b).val = a.val ^^^ b.val := rfl

@[simp]
theorem finXor_cancel_right {M : ℕ} (a b : Fin (2 ^ M)) :
    finXor (finXor a b) b = a := by
  apply Fin.ext
  simp [Nat.xor_assoc]

theorem finXor_eq_iff {M : ℕ} (a b c : Fin (2 ^ M)) :
    finXor a b = c ↔ a = finXor c b := by
  constructor
  · rintro rfl; exact (finXor_cancel_right a b).symm
  · rintro rfl; exact finXor_cancel_right c b

/-- Evaluate a single 7-wise independent trinomial polynomial hash at key `u`. -/
@[expose]
noncomputable def evalPoly {U M : ℕ} (c : PolySeed U M) (u : Fin U) : Fin (2 ^ M) :=
  Probability.trinomialPolyHash (Probability.trinomialStep U M) 7 U M c u

/-- First cuckoo hash function `h₁(u) = f₁(u) ^^^ Z₁[g₁(u)]`. -/
@[expose]
noncomputable def evalHash1 {U M : ℕ} (θ : Seed U M) (u : Fin U) : Fin (2 ^ M) :=
  finXor (evalPoly (θ.1 0) u) (θ.2.1 (evalPoly (θ.1 1) u))

/-- Second cuckoo hash function `h₂(u) = f₂(u) ^^^ Z₂[g₂(u)]`. -/
@[expose]
noncomputable def evalHash2 {U M : ℕ} (θ : Seed U M) (u : Fin U) : Fin (2 ^ M) :=
  finXor (evalPoly (θ.1 2) u) (θ.2.2 (evalPoly (θ.1 3) u))

theorem isKWiseIndependentHash_evalPoly (U M : ℕ) :
    Probability.IsKWiseIndependentHash 7 (evalPoly (U := U) (M := M)) :=
  Probability.isKWiseIndependentHash_trinomialPolyHash
    (Probability.le_two_pow_trinomialDeg U M) (Probability.le_trinomialDeg U M)

/-- If every fiber over `ι₂` of a predicate on `ι₁ × ι₂` has uniform density `c` in `ι₁`, then the
predicate has density `c` in `ι₁ × ι₂`. -/
theorem dens_prod_eq_of_forall_snd {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Nonempty ι₂]
    (P : ι₁ → ι₂ → Prop) [∀ i₂, DecidablePred (P · i₂)]
    {c : ℚ≥0} (hc : ∀ i₂ : ι₂, Finset.dens {i₁ : ι₁ | P i₁ i₂} = c) :
    open scoped Classical in
    Finset.dens {p : ι₁ × ι₂ | P p.1 p.2} = c := by
  classical
  have hcard : #{p : ι₁ × ι₂ | P p.1 p.2} = ∑ i₂ : ι₂, #{i₁ : ι₁ | P i₁ i₂} := by
    rw [← Finset.card_sigma]
    refine Finset.card_nbij' (fun p => ⟨p.2, p.1⟩) (fun s => (s.2, s.1)) ?_ ?_ ?_ ?_
    · rintro ⟨i₁, i₂⟩ hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [hp]
    · rintro ⟨i₂, i₁⟩ hs
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        true_and] at hs
      simp [hs]
    · rintro ⟨i₁, i₂⟩ _; rfl
    · rintro ⟨i₂, i₁⟩ _; rfl
  rw [Finset.dens_eq_card_div_card, hcard, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul,
    div_mul_eq_div_div, Finset.sum_div]
  have hsum : (∑ i₂ : ι₂, (#{i₁ : ι₁ | P i₁ i₂} : ℚ≥0) / Fintype.card ι₁) =
      (Fintype.card ι₂ : ℚ≥0) * c := by
    calc (∑ i₂ : ι₂, (#{i₁ : ι₁ | P i₁ i₂} : ℚ≥0) / Fintype.card ι₁)
      _ = ∑ i₂ : ι₂, Finset.dens {i₁ : ι₁ | P i₁ i₂} := by
          refine Finset.sum_congr rfl fun i₂ _ => ?_
          rw [Finset.dens_eq_card_div_card]
      _ = ∑ _i₂ : ι₂, c := Finset.sum_congr rfl fun i₂ _ => hc i₂
      _ = (Fintype.card ι₂ : ℚ≥0) * c := by simp
  rw [hsum, mul_div_cancel_left₀ c (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]

/-- Masking a `k`-wise independent hash family `f : ι₁ → X → Fin (2 ^ M)` with an arbitrary
independent family `w : ι₂ → X → Fin (2 ^ M)` via `finXor` preserves `k`-wise independence. -/
theorem isKWiseIndependentHash_finXor_mask {ι₁ ι₂ X : Type*} [Fintype ι₁] [Fintype ι₂]
    [Nonempty ι₂] {k M : ℕ} {f : ι₁ → X → Fin (2 ^ M)} (w : ι₂ → X → Fin (2 ^ M))
    (hf : Probability.IsKWiseIndependentHash k f) :
    Probability.IsKWiseIndependentHash k
      (fun (p : ι₁ × ι₂) x => finXor (f p.1 x) (w p.2 x)) where
  dens_filter_restrict_eq {T} hT y := by
    refine dens_prod_eq_of_forall_snd
      (fun i₁ i₂ => T.restrict (fun x => finXor (f i₁ x) (w i₂ x)) = y) fun i₂ => ?_
    have heq : Finset.filter (fun i₁ : ι₁ => T.restrict (fun x => finXor (f i₁ x) (w i₂ x)) = y)
          Finset.univ =
        Finset.filter (fun i₁ : ι₁ => T.restrict (f i₁) = fun x => finXor (y x) (w i₂ x.1))
          Finset.univ := by
      ext i₁
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff]
      exact forall_congr' fun x => finXor_eq_iff (f i₁ x.1) (w i₂ x.1) (y x)
    rw [heq]
    exact hf.dens_filter_restrict_eq hT _

private def seedEquiv1 (U M : ℕ) :
    Seed U M ≃ PolySeed U M × ((Fin 3 → PolySeed U M) × TabSeed M × TabSeed M) where
  toFun θ := (θ.1 0, (fun i => θ.1 i.succ, θ.2))
  invFun p := (Fin.cons p.1 p.2.1, p.2.2)
  left_inv θ := by
    rcases θ with ⟨c, z⟩
    refine Prod.ext ?_ rfl
    ext i j
    refine Fin.cases rfl (fun _ => rfl) i
  right_inv p := by
    rcases p with ⟨c0, cs, z⟩
    ext <;> simp

private def seedEquiv2 (U M : ℕ) :
    Seed U M ≃ PolySeed U M × ((Fin 3 → PolySeed U M) × TabSeed M × TabSeed M) :=
  (Equiv.prodCongrLeft fun _ => Equiv.piCongrLeft' _ (Equiv.swap (0 : Fin 4) (2 : Fin 4))).trans
    (seedEquiv1 U M)

/-- **`evalHash1` is an exact `7`-wise independent hash family** onto `Fin (2 ^ M)`. -/
theorem isKWiseIndependentHash_evalHash1 (U M : ℕ) :
    Probability.IsKWiseIndependentHash 7 (evalHash1 (U := U) (M := M)) := by
  have hmask : Probability.IsKWiseIndependentHash 7
      (fun (p : PolySeed U M × ((Fin 3 → PolySeed U M) × TabSeed M × TabSeed M)) (u : Fin U) =>
        finXor (evalPoly p.1 u) (p.2.2.1 (evalPoly (p.2.1 0) u))) :=
    isKWiseIndependentHash_finXor_mask
      (fun (q : (Fin 3 → PolySeed U M) × TabSeed M × TabSeed M) (u : Fin U) =>
        q.2.1 (evalPoly (q.1 0) u))
      (isKWiseIndependentHash_evalPoly U M)
  exact hmask.comp_seedEquiv (seedEquiv1 U M)

/-- **`evalHash2` is an exact `7`-wise independent hash family** onto `Fin (2 ^ M)`. -/
theorem isKWiseIndependentHash_evalHash2 (U M : ℕ) :
    Probability.IsKWiseIndependentHash 7 (evalHash2 (U := U) (M := M)) := by
  have hmask : Probability.IsKWiseIndependentHash 7
      (fun (p : PolySeed U M × ((Fin 3 → PolySeed U M) × TabSeed M × TabSeed M)) (u : Fin U) =>
        finXor (evalPoly p.1 u) (p.2.2.2 (evalPoly (p.2.1 2) u))) :=
    isKWiseIndependentHash_finXor_mask
      (fun (q : (Fin 3 → PolySeed U M) × TabSeed M × TabSeed M) (u : Fin U) =>
        q.2.2 (evalPoly (q.1 2) u))
      (isKWiseIndependentHash_evalPoly U M)
  have hcomp := hmask.comp_seedEquiv (seedEquiv2 U M)
  convert hcomp using 1
  ext θ u
  rfl

theorem isPairwiseIndependentHash_evalHash1 (U M : ℕ) :
    Probability.IsPairwiseIndependentHash (evalHash1 (U := U) (M := M)) :=
  (isKWiseIndependentHash_evalHash1 U M).isPairwiseIndependentHash (by decide)

theorem isPairwiseIndependentHash_evalHash2 (U M : ℕ) :
    Probability.IsPairwiseIndependentHash (evalHash2 (U := U) (M := M)) :=
  (isKWiseIndependentHash_evalHash2 U M).isPairwiseIndependentHash (by decide)

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

/-- Specialization of `IsCuckooHashPair` to the concrete modified tabulated polynomial hash pair
`(evalHash1, evalHash2)` over `seedLaw U M` (independent `g₁, g₂` and bitwise XOR over
`Fin (2 ^ M)`). Per-function `7`-wise independence (`isKWiseIndependentHash_evalHash1`,
`isKWiseIndependentHash_evalHash2`) does not establish Dietzfelbinger and Woelfel's
[DietzfelbingerWoelfel2003, Definition 1, §2.1, p. 632] shared-`g` mod-`m` graph/rehash guarantees
for this modified pair; `isCuckooHashFamily_le_two` discharges `n_max ≤ 2`, while `n_max ≥ 3`
remains open. -/
abbrev IsCuckooHashFamily (U n_max M MaxLoop C_walk C_reh : ℕ) : Prop :=
  IsCuckooHashPair (seedLaw U M) evalHash1 evalHash2 n_max MaxLoop C_walk C_reh

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

/-- Unconditional `IsCuckooHashPair` instance for `n_max ≤ 2` and `0 < MaxLoop` (`C_walk = 1`,
`C_reh = 0`) over any seed distribution `μ` and hash pair `(h₁, h₂)`: inserting up to `2` keys into
two tables `T₁, T₂` always completes in `1` round with zero rehashes (even if both keys collide in
`T₁`, the displaced first key is placed into an empty slot of `T₂`). -/
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

/-- Unconditional `IsCuckooHashFamily` instance for `n_max ≤ 2` and `0 < MaxLoop` (`C_walk = 1`,
`C_reh = 0`). -/
theorem isCuckooHashFamily_le_two (U : ℕ) {n_max M MaxLoop : ℕ}
    (hn : n_max ≤ 2) (hloop : 0 < MaxLoop) :
    IsCuckooHashFamily U n_max M MaxLoop 1 0 :=
  isCuckooHashPair_le_two (seedLaw U M) evalHash1 evalHash2 hn hloop

/-- Unconditional `IsCuckooHashFamily` instance for `n_max ≤ 1` and `0 < MaxLoop` (`C_walk = 1`,
`C_reh = 0`). -/
theorem isCuckooHashFamily_le_one (U : ℕ) {n_max M MaxLoop : ℕ}
    (hn : n_max ≤ 1) (hloop : 0 < MaxLoop) :
    IsCuckooHashFamily U n_max M MaxLoop 1 0 :=
  isCuckooHashFamily_le_two U (by omega) hloop

/-! ### Section 5: Word-RAM hash pair representation and programs sharing `clmulTab` -/

open Cslib.Algorithms.WordRAM.Hashing

/-- Word-RAM memory footprint of the hash pair `(h₁, h₂)`:
- `4` header words `(M, z1Base, z2Base, 0)` at `hashBase + 0 .. 3`,
- `28` polynomial seed words (`4 × 7`) at `hashBase + 4 .. 31`,
- `KWise.space n_max 7` words (`15 + 2 ^ (2 * chunkBits n_max)`) at `hashBase + 32 ..` storing the
  shared `KWise` header, 7-word active seed slot, and Four-Russians `clmulTab`,
- `2 * 2 ^ M` words for the random tabulation arrays `Z₁` and `Z₂`. -/
@[expose]
def hashPairSpace (n_max M : ℕ) : ℕ :=
  32 + KWise.space n_max 7 + 2 * 2 ^ M

/-- Base address of the first tabulation array `Z₁`. -/
@[expose]
def z1Base (hashBase n_max : ℕ) : ℕ :=
  hashBase + 32 + KWise.space n_max 7

/-- Base address of the second tabulation array `Z₂`. -/
@[expose]
def z2Base (hashBase n_max M : ℕ) : ℕ :=
  z1Base hashBase n_max + 2 ^ M

theorem z1Base_eq (hashBase n_max : ℕ) :
    z1Base hashBase n_max = hashBase + 47 + 2 ^ (2 * KWise.chunkBits n_max) := by
  dsimp only [z1Base, KWise.space, KWise.spaceFromB]
  omega

theorem le_z1Base (hashBase n_max : ℕ) :
    hashBase + 47 ≤ z1Base hashBase n_max := by
  rw [z1Base_eq]
  exact Nat.le_add_right _ _

theorem hashPairSpace_eq (n_max M : ℕ) :
    hashPairSpace n_max M = 47 + 2 ^ (2 * KWise.chunkBits n_max) + 2 * 2 ^ M := by
  dsimp only [hashPairSpace, KWise.space, KWise.spaceFromB]
  omega

theorem le_hashPairSpace (n_max M : ℕ) :
    49 ≤ hashPairSpace n_max M := by
  have h1 : 1 ≤ 2 ^ (2 * KWise.chunkBits n_max) := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  rw [hashPairSpace_eq]
  omega

theorem z2Base_add_two_pow_eq (hashBase n_max M : ℕ) :
    z2Base hashBase n_max M + 2 ^ M = hashBase + hashPairSpace n_max M := by
  dsimp only [z2Base, z1Base, hashPairSpace]
  omega

/-- Deterministic table representation invariant for the hash pair at `hashBase`:
stores `(M, z1Base, z2Base)` at `hashBase + 0 .. 2` and `KWise.TableRep` at `hashBase + 32`. -/
@[expose]
def HashPairTableRep (hashBase n_max U M : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem hashBase = M ∧
  mem (hashBase + 1) = z1Base hashBase n_max ∧
  mem (hashBase + 2) = z2Base hashBase n_max M ∧
  KWise.TableRep (hashBase + 32) (KWise.chunkBits n_max) U M 7 mem

/-- Seed representation invariant for `θ : Seed U M` at `hashBase`:
stores the four 7-word polynomial seeds at `[hashBase + 4, hashBase + 32)`, `Z₁` at `z1Base`, and
`Z₂` at `z2Base`. -/
@[expose]
def HashPairSeedRep (hashBase n_max U M : ℕ) (θ : Seed U M) (mem : ℕ → ℕ) : Prop :=
  (∀ (r : Fin 4) (j : Fin 7),
    mem (hashBase + 4 + 7 * r.val + j.val) = (θ.1 r j).val) ∧
  (∀ i : Fin (2 ^ M), mem (z1Base hashBase n_max + i.val) = (θ.2.1 i).val) ∧
  (∀ i : Fin (2 ^ M), mem (z2Base hashBase n_max M + i.val) = (θ.2.2 i).val)

/-- Full representation invariant for the hash pair `(h₁, h₂)` at `hashBase`. -/
@[expose]
def HashPairRep (hashBase n_max U M : ℕ) (θ : Seed U M) (mem : ℕ → ℕ) : Prop :=
  HashPairTableRep hashBase n_max U M mem ∧ HashPairSeedRep hashBase n_max U M θ mem

/-- Equivalence currying a flat 28-word slice into four 7-word polynomial seeds. -/
@[expose]
def polySliceEquiv (U M : ℕ) :
    (Fin 28 → Fin (2 ^ Probability.trinomialDeg U M)) ≃ (Fin 4 → PolySeed U M) where
  toFun s r j := s ⟨7 * r.val + j.val, by omega⟩
  invFun c i := c ⟨i.val / 7, by omega⟩ ⟨i.val % 7, by omega⟩
  left_inv s := by
    funext i
    apply congrArg s
    ext
    dsimp only
    exact Nat.div_add_mod i.val 7
  right_inv c := by
    funext r j
    dsimp only
    have hr : (7 * r.val + j.val) / 7 = r.val := by omega
    have hj : (7 * r.val + j.val) % 7 = j.val := by omega
    have hr' : (⟨(7 * r.val + j.val) / 7, by omega⟩ : Fin 4) = r := Fin.ext hr
    have hj' : (⟨(7 * r.val + j.val) % 7, by omega⟩ : Fin 7) = j := Fin.ext hj
    rw [hr', hj']

/-- Equivalence splitting a flat `2 * 2 ^ M`-word slice into two `2 ^ M`-word tabulation arrays. -/
@[expose]
def tabSliceEquiv (M : ℕ) :
    (Fin (2 * 2 ^ M) → Fin (2 ^ M)) ≃ TabSeed M × TabSeed M where
  toFun s := (fun i => s ⟨i.val, by omega⟩, fun i => s ⟨2 ^ M + i.val, by omega⟩)
  invFun p j :=
    if h : j.val < 2 ^ M then p.1 ⟨j.val, h⟩
    else p.2 ⟨j.val - 2 ^ M, by omega⟩
  left_inv s := by
    funext j
    dsimp only
    split_ifs with h
    · rfl
    · congr 1
      ext
      dsimp only
      omega
  right_inv p := by
    rcases p with ⟨z1, z2⟩
    ext i : 2
    · simp only [i.isLt, ↓reduceDIte]
    · have hnot : ¬ (2 ^ M + i.val < 2 ^ M) := by omega
      simp only [hnot, ↓reduceDIte]
      congr 1
      ext
      dsimp only
      omega

/-- Extract the full cuckoo hash seed `Seed U M` from memory at `hashBase`. -/
@[expose]
def extractSeed (hashBase n_max U M : ℕ) (mem : ℕ → ℕ) : Seed U M :=
  (polySliceEquiv U M
      (Tabulation.extractSlice (hashBase + 4) (Probability.trinomialDeg U M) 28 mem),
   tabSliceEquiv M
      (Tabulation.extractSlice (z1Base hashBase n_max) M (2 * 2 ^ M) mem))

@[simp]
theorem polySliceEquiv_apply (U M : ℕ)
    (s : Fin 28 → Fin (2 ^ Probability.trinomialDeg U M)) (r : Fin 4) (j : Fin 7) :
    polySliceEquiv U M s r j =
      s ⟨7 * r.val + j.val, by have := r.isLt; have := j.isLt; omega⟩ := rfl

@[simp]
theorem tabSliceEquiv_fst (M : ℕ) (s : Fin (2 * 2 ^ M) → Fin (2 ^ M)) (i : Fin (2 ^ M)) :
    (tabSliceEquiv M s).1 i = s ⟨i.val, by have := i.isLt; omega⟩ := rfl

@[simp]
theorem tabSliceEquiv_snd (M : ℕ) (s : Fin (2 * 2 ^ M) → Fin (2 ^ M)) (i : Fin (2 ^ M)) :
    (tabSliceEquiv M s).2 i = s ⟨2 ^ M + i.val, by have := i.isLt; omega⟩ := rfl

theorem hashPairSeedRep_extractSeed {hashBase n_max U M : ℕ} {mem : ℕ → ℕ}
    (hpoly : ∀ k < 28, mem (hashBase + 4 + k) < 2 ^ Probability.trinomialDeg U M)
    (htab : ∀ i < 2 * 2 ^ M, mem (z1Base hashBase n_max + i) < 2 ^ M) :
    HashPairSeedRep hashBase n_max U M (extractSeed hashBase n_max U M mem) mem := by
  refine ⟨?_, ?_, ?_⟩
  · intro r j
    have hr := r.isLt
    have hj := j.isLt
    dsimp only [extractSeed, polySliceEquiv_apply, Tabulation.extractSlice]
    rw [show hashBase + 4 + (7 * r.val + j.val) = hashBase + 4 + 7 * r.val + j.val by omega]
    exact (Tabulation.extractWord_val_of_lt (by
      rw [show hashBase + 4 + 7 * r.val + j.val = hashBase + 4 + (7 * r.val + j.val) by omega]
      exact hpoly (7 * r.val + j.val) (by omega))).symm
  · intro i
    have hi := i.isLt
    dsimp only [extractSeed, tabSliceEquiv_fst, Tabulation.extractSlice]
    exact (Tabulation.extractWord_val_of_lt (htab i.val (by omega))).symm
  · intro i
    have hi := i.isLt
    dsimp only [extractSeed, tabSliceEquiv_snd, Tabulation.extractSlice, z2Base]
    rw [show z1Base hashBase n_max + (2 ^ M + i.val) =
      z1Base hashBase n_max + 2 ^ M + i.val by omega]
    exact (Tabulation.extractWord_val_of_lt (by
      rw [show z1Base hashBase n_max + 2 ^ M + i.val =
        z1Base hashBase n_max + (2 ^ M + i.val) by omega]
      exact htab (2 ^ M + i.val) (by omega))).symm

theorem extractSeed_eq_of_HashPairSeedRep {hashBase n_max U M : ℕ} {θ : Seed U M} {mem : ℕ → ℕ}
    (hseed : HashPairSeedRep hashBase n_max U M θ mem) :
    extractSeed hashBase n_max U M mem = θ := by
  rcases θ with ⟨c, z1, z2⟩
  rcases hseed with ⟨hc, hz1, hz2⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext r j
    ext
    dsimp only [extractSeed, polySliceEquiv_apply, Tabulation.extractSlice]
    rw [show hashBase + 4 + (7 * r.val + j.val) = hashBase + 4 + 7 * r.val + j.val by omega,
      hc r j, Tabulation.extractWord_val_of_lt (c r j).isLt]
  · funext i
    ext
    dsimp only [extractSeed, tabSliceEquiv_fst, Tabulation.extractSlice]
    rw [hz1 i, Tabulation.extractWord_val_of_lt (z1 i).isLt]
  · funext i
    ext
    dsimp only [extractSeed, tabSliceEquiv_snd, Tabulation.extractSlice]
    rw [show z1Base hashBase n_max + (2 ^ M + i.val) = z2Base hashBase n_max M + i.val by
      dsimp only [z2Base]; omega, hz2 i, Tabulation.extractWord_val_of_lt (z2 i).isLt]

theorem HashPairTableRep.congr_of_active_slot {hashBase n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : HashPairTableRep hashBase n_max U M mem)
    (hframe : ∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → mem' a = mem a) :
    HashPairTableRep hashBase n_max U M mem' := by
  rcases htab with ⟨hM, hz1, hz2, hkw⟩
  refine ⟨(hframe hashBase (Or.inl (by omega))).trans hM,
    (hframe (hashBase + 1) (Or.inl (by omega))).trans hz1,
    (hframe (hashBase + 2) (Or.inl (by omega))).trans hz2, ?_⟩
  rcases hkw with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
  refine ⟨(hframe (hashBase + 32) (Or.inl (by omega))).trans h0,
    (hframe (hashBase + 32 + 1) (Or.inl (by omega))).trans h1,
    (hframe (hashBase + 32 + 2) (Or.inl (by omega))).trans h2,
    (hframe (hashBase + 32 + 3) (Or.inl (by omega))).trans h3,
    (hframe (hashBase + 32 + 4) (Or.inl (by omega))).trans h4,
    (hframe (hashBase + 32 + 5) (Or.inl (by omega))).trans h5,
    (hframe (hashBase + 32 + 6) (Or.inl (by omega))).trans h6,
    (hframe (hashBase + 32 + 7) (Or.inl (by omega))).trans h7,
    fun idx hidx => (hframe (hashBase + 32 + 8 + 7 + idx) (Or.inr (by omega))).trans (hcl idx hidx)⟩

theorem HashPairSeedRep.congr_of_active_slot {hashBase n_max U M : ℕ} {θ : Seed U M}
    {mem mem' : ℕ → ℕ} (hseed : HashPairSeedRep hashBase n_max U M θ mem)
    (hframe : ∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → mem' a = mem a) :
    HashPairSeedRep hashBase n_max U M θ mem' := by
  rcases hseed with ⟨hc, hz1, hz2⟩
  have hz1_ge := le_z1Base hashBase n_max
  have hz2_ge : hashBase + 47 ≤ z2Base hashBase n_max M :=
    le_trans hz1_ge (Nat.le_add_right _ _)
  refine ⟨fun r j => (hframe _ (Or.inl (by omega))).trans (hc r j),
    fun i => (hframe _ (Or.inr (by omega))).trans (hz1 i),
    fun i => (hframe _ (Or.inr (by omega))).trans (hz2 i)⟩

theorem HashPairRep.congr_of_active_slot {hashBase n_max U M : ℕ} {θ : Seed U M}
    {mem mem' : ℕ → ℕ} (hrep : HashPairRep hashBase n_max U M θ mem)
    (hframe : ∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → mem' a = mem a) :
    HashPairRep hashBase n_max U M θ mem' :=
  ⟨hrep.1.congr_of_active_slot hframe, hrep.2.congr_of_active_slot hframe⟩

/-- Register injection `Fin 18 → Fin 19` embedding `KWise` programs into `Data 19`. -/
@[expose]
def cast18To19 : Fin 18 → Fin 19 :=
  Fin.castLE (by decide : 18 ≤ 19)

theorem injective_cast18To19 : Function.Injective cast18To19 :=
  Fin.castLE_injective _

/-- Prefix of `initTableHashPairCode`: stores `M` at `mem[hashBase]` and advances `reg 0` to
`hashBase + 32`. -/
@[expose]
def initHashHeaderPrefix : Code .exact 19 :=
  .seq (.op (.store 0 3))
  (.seq (.op (.const 15 32))
        (.op (.exactBin .add 0 0 15)))

/-- Suffix of `initTableHashPairCode`: restores `reg 0 = hashBase` and populates `z1Base` at
`mem[hashBase + 1]` and `z2Base` at `mem[hashBase + 2]`. -/
@[expose]
def initHashHeaderSuffix : Code .exact 19 :=
  .seq (.op (.const 15 32))
  (.seq (.op (.exactBin .sub 0 0 15))
  (.seq (.op (.const 1 1))
  (.seq (.op (.const 2 37))
  (.seq (.op (.exactBin .add 2 0 2))
  (.seq (.op (.load 2 2))
  (.seq (.op (.exactBin .add 2 2 2))
  (.seq (.op (.exactBin .shiftLeft 2 1 2))
  (.seq (.op (.const 3 47))
  (.seq (.op (.exactBin .add 3 0 3))
  (.seq (.op (.exactBin .add 3 3 2))
  (.seq (.op (.exactBin .add 4 0 1))
  (.seq (.op (.store 4 3))
  (.seq (.op (.const 5 36))
  (.seq (.op (.exactBin .add 5 0 5))
  (.seq (.op (.load 5 5))
  (.seq (.op (.exactBin .add 5 5 1))
  (.seq (.op (.exactBin .add 3 3 5))
  (.seq (.op (.exactBin .add 4 4 1))
        (.op (.store 4 3))))))))))))))))))))

/-- Deterministic table-initialization program for the hash pair at `hashBase`:
populates `(M, z1Base, z2Base)` and builds the shared `KWise` `clmulTab` at `hashBase + 32`. -/
@[expose]
def initTableHashPairCode : Code .exact 19 :=
  .seq initHashHeaderPrefix
  (.seq ((KWise.initTableCode 7).rename cast18To19)
        initHashHeaderSuffix)

/-- Exact instruction bound for `initTableHashPairCode`. -/
@[expose]
def initTableHashPairSteps (n_max U M : ℕ) : ℕ :=
  KWise.initTableSteps n_max U M + 23

theorem initTableHashPairCode_execWithin {w hashBase n_max U M : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = n_max)
    (h2 : x.regs 2 = U) (h3 : x.regs 3 = M)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M))
    (hfit_n : Fits w (max n_max 2)) (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ∃ y : Data 19,
      ExecWithin w initTableHashPairCode x y (initTableHashPairSteps n_max U M) ∧
      HashPairTableRep hashBase n_max U M y.mem ∧
      y.regs 0 = hashBase ∧
      (∀ a, (a < hashBase ∨ hashBase + hashPairSpace n_max M ≤ a) → y.mem a = x.mem a) := by
  have hpow_pos : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
  have hpowM_pos : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hsp : hashPairSpace n_max M = 47 + 2 ^ (2 * KWise.chunkBits n_max) + 2 * 2 ^ M := by
    dsimp only [hashPairSpace, KWise.space, KWise.spaceFromB]; omega
  have hfit_32 : Fits w 32 := hfit_space.of_le (by omega)
  have hfit_hb32 : Fits w (hashBase + 32) := hfit_space.of_le (by omega)
  have hfit_kw : Fits w (hashBase + 32 + KWise.space n_max 7) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  set d1 := x.write hashBase M
  have ep1 : Exec w (.op (.store 0 3) : Code .exact 19) x d1 1 := by
    simpa +decide [d1, h0, h3] using (Exec.store (B := .exact) (w := w) (a := 0) (s := 3) (x := x))
  set d2 := d1.set 15 32
  have ep2 : Exec w (.op (.const 15 32) : Code .exact 19) d1 d2 1 := Exec.const hfit_32
  set d3 := d2.set 0 (hashBase + 32)
  have ep3 : Exec w (.op (.exactBin .add 0 0 15) : Code .exact 19) d2 d3 1 :=
    ExactLog.exec_exactBin (by simp +decide [d2, d1, h0]) hfit_hb32
  have epref : Exec w initHashHeaderPrefix x d3 3 := ep1.seq (ep2.seq ep3)
  obtain ⟨y_kw, ⟨t_kw, ht_kw, he_kw⟩, htab_kw, hy_kw0, hy_kw_out⟩ :=
    KWise.initTableCode_execWithin (w := w) (base := hashBase + 32) (n_max := n_max)
      (U := U) (M := M) (k := 7) (x := d3.comap cast18To19)
      (by simp +decide [d3, d2, d1, cast18To19, Data.comap])
      (by simp +decide [d3, d2, d1, cast18To19, Data.comap, h1])
      (by simp +decide [d3, d2, d1, cast18To19, Data.comap, h2])
      (by simp +decide [d3, d2, d1, cast18To19, Data.comap, h3])
      hfit_kw hfit_n hfit_U hfit_q
  set d4 := y_kw.extend cast18To19 d3
  have he_kw' : Exec w ((KWise.initTableCode 7).rename cast18To19) d3 d4 t_kw :=
    he_kw.rename injective_cast18To19
  have hd4_0 : d4.regs 0 = hashBase + 32 := by
    change ((y_kw.extend cast18To19 d3).comap cast18To19).regs 0 = hashBase + 32
    rw [Data.comap_extend injective_cast18To19, hy_kw0]
  have hd4_mem : d4.mem = y_kw.mem := rfl
  have hd4_hb : d4.mem hashBase = M := by
    rw [hd4_mem, hy_kw_out hashBase (Or.inl (by omega))]
    simp [d3, d2, d1, Data.comap]
  set b := KWise.chunkBits n_max
  have hm_b : d4.mem (hashBase + 37) = b := by
    rw [show hashBase + 37 = hashBase + 32 + 5 by omega, hd4_mem]
    exact htab_kw.2.2.2.2.2.1
  have hm_maskM : d4.mem (hashBase + 36) = 2 ^ M - 1 := by
    rw [show hashBase + 36 = hashBase + 32 + 4 by omega, hd4_mem]
    exact htab_kw.2.2.2.2.1
  have h2b_lt : 2 * b < 2 ^ (2 * b) := Nat.lt_two_pow_self
  have hsp_eq := hashPairSpace_eq n_max M
  have hfit_1 : Fits w 1 := hfit_space.of_le (by omega)
  have hfit_37 : Fits w 37 := hfit_space.of_le (by omega)
  have hfit_hb37 : Fits w (hashBase + 37) := hfit_space.of_le (by omega)
  have hfit_2b : Fits w (2 * b) := hfit_space.of_le (by omega)
  have hfit_pow2b : Fits w (2 ^ (2 * b)) := hfit_space.of_le (by omega)
  have hfit_47 : Fits w 47 := hfit_space.of_le (by omega)
  have hfit_hb47 : Fits w (hashBase + 47) := hfit_space.of_le (by omega)
  have hfit_z1 : Fits w (z1Base hashBase n_max) := by
    rw [z1Base_eq]; exact hfit_space.of_le (by omega)
  have hfit_hb1 : Fits w (hashBase + 1) := hfit_space.of_le (by omega)
  have hfit_36 : Fits w 36 := hfit_space.of_le (by omega)
  have hfit_hb36 : Fits w (hashBase + 36) := hfit_space.of_le (by omega)
  have hfit_powM : Fits w (2 ^ M) := hfit_space.of_le (by omega)
  have hfit_z2 : Fits w (z2Base hashBase n_max M) := by
    dsimp only [z2Base]; rw [z1Base_eq]; exact hfit_space.of_le (by omega)
  have hfit_hb2 : Fits w (hashBase + 2) := hfit_space.of_le (by omega)
  have hfit_hb : Fits w hashBase := hfit_space.of_le (by omega)
  set s1 := d4.set 15 32
  have es1 : Exec w (.op (.const 15 32) : Code .exact 19) d4 s1 1 := Exec.const hfit_32
  set s2 := s1.set 0 hashBase
  have es2 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, hd4_0]) hfit_hb
  set s3 := s2.set 1 1
  have es3 : Exec w (.op (.const 1 1) : Code .exact 19) s2 s3 1 := Exec.const hfit_1
  set s4 := s3.set 2 37
  have es4 : Exec w (.op (.const 2 37) : Code .exact 19) s3 s4 1 := Exec.const hfit_37
  set s5 := s4.set 2 (hashBase + 37)
  have es5 : Exec w (.op (.exactBin .add 2 0 2) : Code .exact 19) s4 s5 1 :=
    ExactLog.exec_exactBin (by simp +decide [s4, s3, s2]) hfit_hb37
  set s6 := s5.set 2 b
  have es6 : Exec w (.op (.load 2 2) : Code .exact 19) s5 s6 1 := by
    simpa +decide [s6, s5, s4, s3, s2, s1, hm_b] using
      (Exec.load (B := .exact) (w := w) (d := 2) (a := 2) (x := s5))
  set s7 := s6.set 2 (2 * b)
  have es7 : Exec w (.op (.exactBin .add 2 2 2) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, Nat.two_mul]) hfit_2b
  set s8 := s7.set 2 (2 ^ (2 * b))
  have es8 : Exec w (.op (.exactBin .shiftLeft 2 1 2) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, Nat.shiftLeft_eq]) hfit_pow2b
  set s9 := s8.set 3 47
  have es9 : Exec w (.op (.const 3 47) : Code .exact 19) s8 s9 1 := Exec.const hfit_47
  set s10 := s9.set 3 (hashBase + 47)
  have es10 : Exec w (.op (.exactBin .add 3 0 3) : Code .exact 19) s9 s10 1 :=
    ExactLog.exec_exactBin (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2]) hfit_hb47
  set s11 := s10.set 3 (z1Base hashBase n_max)
  have es11 : Exec w (.op (.exactBin .add 3 3 2) : Code .exact 19) s10 s11 1 :=
    ExactLog.exec_exactBin (by simp +decide [s10, s9, s8, z1Base_eq, b, Nat.add_assoc]) hfit_z1
  set s12 := s11.set 4 (hashBase + 1)
  have es12 : Exec w (.op (.exactBin .add 4 0 1) : Code .exact 19) s11 s12 1 :=
    ExactLog.exec_exactBin (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]) hfit_hb1
  set s13 := s12.write (hashBase + 1) (z1Base hashBase n_max)
  have es13 : Exec w (.op (.store 4 3) : Code .exact 19) s12 s13 1 := by
    simpa +decide [s13, s12, s11] using
      (Exec.store (B := .exact) (w := w) (a := 4) (s := 3) (x := s12))
  set s14 := s13.set 5 36
  have es14 : Exec w (.op (.const 5 36) : Code .exact 19) s13 s14 1 := Exec.const hfit_36
  set s15 := s14.set 5 (hashBase + 36)
  have es15 : Exec w (.op (.exactBin .add 5 0 5) : Code .exact 19) s14 s15 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2]) hfit_hb36
  set s16 := s15.set 5 (2 ^ M - 1)
  have es16 : Exec w (.op (.load 5 5) : Code .exact 19) s15 s16 1 := by
    have hm36 : s15.mem (hashBase + 36) = 2 ^ M - 1 := by
      dsimp only [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Data.write, Data.set]
      rw [Function.update_of_ne (by omega), hm_maskM]
    simpa +decide [s16, s15, hm36] using
      (Exec.load (B := .exact) (w := w) (d := 5) (a := 5) (x := s15))
  set s17 := s16.set 5 (2 ^ M)
  have es17 : Exec w (.op (.exactBin .add 5 5 1) : Code .exact 19) s16 s17 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, hpowM_pos])
      hfit_powM
  set s18 := s17.set 3 (z2Base hashBase n_max M)
  have es18 : Exec w (.op (.exactBin .add 3 3 5) : Code .exact 19) s17 s18 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s17, s16, s15, s14, s13, s12, s11, z2Base]) hfit_z2
  set s19 := s18.set 4 (hashBase + 2)
  have es19 : Exec w (.op (.exactBin .add 4 4 1) : Code .exact 19) s18 s19 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3,
        Nat.add_assoc]) hfit_hb2
  set s20 := s19.write (hashBase + 2) (z2Base hashBase n_max M)
  have es20 : Exec w (.op (.store 4 3) : Code .exact 19) s19 s20 1 := by
    simpa +decide [s20, s19, s18] using
      (Exec.store (B := .exact) (w := w) (a := 4) (s := 3) (x := s19))
  have esuf : Exec w initHashHeaderSuffix d4 s20 20 :=
    es1.seq (es2.seq (es3.seq (es4.seq (es5.seq (es6.seq (es7.seq (es8.seq (es9.seq (es10.seq
      (es11.seq (es12.seq (es13.seq (es14.seq (es15.seq (es16.seq (es17.seq (es18.seq
        (es19.seq es20))))))))))))))))))
  have hall := epref.seq (he_kw'.seq esuf)
  have hs20_mem : ∀ a, a ≠ hashBase + 1 → a ≠ hashBase + 2 → s20.mem a = d4.mem a := by
    intro a ha1 ha2
    dsimp only [s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha2, Function.update_of_ne ha1]
  refine ⟨s20, ⟨3 + (t_kw + 20), by dsimp only [initTableHashPairSteps]; omega, hall⟩,
    ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hs20_mem hashBase (by omega) (by omega), hd4_hb]
    · dsimp only [s20, s19, s18, s17, s16, s15, s14, s13, Data.write, Data.set]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · dsimp only [s20, Data.write]
      rw [Function.update_self]
    · rcases htab_kw with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
      refine ⟨(hs20_mem _ (by omega) (by omega)).trans h0,
        (hs20_mem _ (by omega) (by omega)).trans h1,
        (hs20_mem _ (by omega) (by omega)).trans h2,
        (hs20_mem _ (by omega) (by omega)).trans h3,
        (hs20_mem _ (by omega) (by omega)).trans h4,
        (hs20_mem _ (by omega) (by omega)).trans h5,
        (hs20_mem _ (by omega) (by omega)).trans h6,
        (hs20_mem _ (by omega) (by omega)).trans h7,
        fun idx hidx => (hs20_mem _ (by omega) (by omega)).trans (hcl idx hidx)⟩
  · simp +decide [s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5,
      s4, s3, s2]
  · intro a ha
    have ha' : a < hashBase + 32 ∨ hashBase + 32 + KWise.space n_max 7 ≤ a := by
      dsimp only [hashPairSpace] at ha
      exact ha.imp (by omega) (by omega)
    rw [hs20_mem a (by omega) (by omega), hd4_mem, hy_kw_out a ha']
    dsimp only [d3, d2, d1, Data.comap, Data.write, Data.set]
    rw [Function.update_of_ne (by omega)]

/-- Injective register map embedding `Tabulation.randFillLoop` into `Data 19` while preserving
`reg 0` (`hashBase`). -/
@[expose]
def resampleMap19 : Fin 6 → Fin 19 :=
  ![2, 3, 1, 4, 5, 0]

theorem injective_resampleMap19 : Function.Injective resampleMap19 := by
  decide

/-- Setup prefix for sampling the 28 polynomial seed words at `[hashBase + 4, hashBase + 32)`. -/
@[expose]
def resamplePolySetup : Code .exact 19 :=
  .seq (.op (.const 1 35))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.load 1 1))
  (.seq (.op (.const 2 4))
  (.seq (.op (.exactBin .add 2 0 2))
  (.seq (.op (.const 3 28))
  (.seq (.op (.exactBin .add 3 2 3))
        (.op (.const 4 1))))))))

/-- Closed-form machine data after `resamplePolySetup`. -/
@[expose]
def resamplePolySetupData (hashBase U M : ℕ) (x : Data 19) : Data 19 :=
  ((((x.set 1 (2 ^ Probability.trinomialDeg U M - 1)).set 2 (hashBase + 4)).set 3
    (hashBase + 32)).set 4 1)

/-- Program sampling all 28 polynomial seed words at `[hashBase + 4, hashBase + 32)`. -/
@[expose]
def resamplePolySeedsCode : Code .exact 19 :=
  .seq resamplePolySetup (Tabulation.randFillLoop.rename resampleMap19)

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resamplePolySeedsCode`. -/
@[expose]
noncomputable def resamplePolyComp (hashBase U M : ℕ) (x : Data 19) : ProbComp (Data 19 × ℕ) :=
  let d0 := resamplePolySetupData hashBase U M x
  (fun z : Data 6 × ℕ => (z.1.extend resampleMap19 d0, 8 + z.2)) <$>
    Tabulation.randFillComp (Probability.trinomialDeg U M) (hashBase + 4) 28
      (d0.comap resampleMap19)

theorem resamplePolySetup_exec {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_end : Fits w (hashBase + 36)) :
    Exec w resamplePolySetup x (resamplePolySetupData hashBase U M x) 8 := by
  have hfit_35 : Fits w 35 := hfit_end.of_le (by omega)
  have hfit_hb35 : Fits w (hashBase + 35) := hfit_end.of_le (by omega)
  have hfit_4 : Fits w 4 := hfit_end.of_le (by omega)
  have hfit_hb4 : Fits w (hashBase + 4) := hfit_end.of_le (by omega)
  have hfit_28 : Fits w 28 := hfit_end.of_le (by omega)
  have hfit_hb32 : Fits w (hashBase + 32) := hfit_end.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hm35 : x.mem (hashBase + 35) = 2 ^ Probability.trinomialDeg U M - 1 := by
    rw [show hashBase + 35 = hashBase + 32 + 3 by omega]
    exact htab.2.2.2.2.2.2.1
  set s1 := x.set 1 35
  have e1 : Exec w (.op (.const 1 35) : Code .exact 19) x s1 1 := Exec.const hfit_35
  set s2 := s1.set 1 (hashBase + 35)
  have e2 : Exec w (.op (.exactBin .add 1 0 1) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0]) hfit_hb35
  set s3 := s2.set 1 (2 ^ Probability.trinomialDeg U M - 1)
  have e3 : Exec w (.op (.load 1 1) : Code .exact 19) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm35] using
      (Exec.load (B := .exact) (w := w) (d := 1) (a := 1) (x := s2))
  set s4 := s3.set 2 4
  have e4 : Exec w (.op (.const 2 4) : Code .exact 19) s3 s4 1 := Exec.const hfit_4
  set s5 := s4.set 2 (hashBase + 4)
  have e5 : Exec w (.op (.exactBin .add 2 0 2) : Code .exact 19) s4 s5 1 :=
    ExactLog.exec_exactBin (by simp +decide [s4, s3, s2, s1, h0]) hfit_hb4
  set s6 := s5.set 3 28
  have e6 : Exec w (.op (.const 3 28) : Code .exact 19) s5 s6 1 := Exec.const hfit_28
  set s7 := s6.set 3 (hashBase + 32)
  have e7 : Exec w (.op (.exactBin .add 3 2 3) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, s5, Nat.add_assoc]) hfit_hb32
  set s8 := s7.set 4 1
  have e8 : Exec w (.op (.const 4 1) : Code .exact 19) s7 s8 1 := Exec.const hfit_1
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  have hd : s8 = resamplePolySetupData hashBase U M x := by
    ext i : 2
    · fin_cases i <;> rfl
    · rfl
  rwa [hd] at hall

theorem resamplePolySeedsCode_execRand {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_end : Fits w (hashBase + 36))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w resamplePolySeedsCode x (resamplePolyComp hashBase U M x) := by
  have hsetup := resamplePolySetup_exec htab h0 hfit_end
  set d0 := resamplePolySetupData hashBase U M x
  have hfit_hb32 : Fits w (hashBase + 4 + 28) := hfit_end.of_le (by omega)
  have hfit_mask : Fits w (2 ^ Probability.trinomialDeg U M - 1) := hfit_q.of_le (Nat.sub_le _ 1)
  have hloop0 := Tabulation.randFillLoop_execRand (w := w)
    (bits := Probability.trinomialDeg U M) (arrBase := hashBase + 4) 28
    (x := d0.comap resampleMap19)
    (by simp +decide [d0, resamplePolySetupData, resampleMap19, Data.comap, Tabulation.regPtr])
    (by simp +decide [d0, resamplePolySetupData, resampleMap19, Data.comap, Tabulation.regEnd])
    (by simp +decide [d0, resamplePolySetupData, resampleMap19, Data.comap, Tabulation.regMask])
    (by simp +decide [d0, resamplePolySetupData, resampleMap19, Data.comap, Tabulation.regOne])
    hfit_hb32 hfit_mask
  have hloop := hloop0.rename injective_resampleMap19
  simpa only [resamplePolySeedsCode, resamplePolyComp, d0, Functor.map_map] using
    hsetup.seqRand hloop

/-- Setup prefix for sampling the `2 * 2 ^ M` tabulation words at
`[z1Base hashBase n_max, z1Base hashBase n_max + 2 * 2 ^ M)`. -/
@[expose]
def resampleTabSetup : Code .exact 19 :=
  .seq (.op (.const 1 36))
  (.seq (.op (.exactBin .add 1 0 1))
  (.seq (.op (.load 1 1))
  (.seq (.op (.const 4 1))
  (.seq (.op (.exactBin .add 3 1 4))
  (.seq (.op (.exactBin .add 3 3 3))
  (.seq (.op (.exactBin .add 2 0 4))
  (.seq (.op (.load 2 2))
        (.op (.exactBin .add 3 2 3)))))))))

/-- Closed-form machine data after `resampleTabSetup`. -/
@[expose]
def resampleTabSetupData (hashBase n_max M : ℕ) (x : Data 19) : Data 19 :=
  ((((x.set 1 (2 ^ M - 1)).set 4 1).set 3 (2 * 2 ^ M)).set 2 (z1Base hashBase n_max)).set 3
    (z1Base hashBase n_max + 2 * 2 ^ M)

/-- Program sampling all `2 * 2 ^ M` tabulation words of `(Z₁, Z₂)`. -/
@[expose]
def resampleTabSeedsCode : Code .exact 19 :=
  .seq resampleTabSetup (Tabulation.randFillLoop.rename resampleMap19)

/-- Explicit `ProbComp (Data 19 × ℕ)` induced by `resampleTabSeedsCode`. -/
@[expose]
noncomputable def resampleTabComp (hashBase n_max M : ℕ) (x : Data 19) : ProbComp (Data 19 × ℕ) :=
  let d0 := resampleTabSetupData hashBase n_max M x
  (fun z : Data 6 × ℕ => (z.1.extend resampleMap19 d0, 9 + z.2)) <$>
    Tabulation.randFillComp M (z1Base hashBase n_max) (2 * 2 ^ M) (d0.comap resampleMap19)

theorem resampleTabSetup_exec {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M)) :
    Exec w resampleTabSetup x (resampleTabSetupData hashBase n_max M x) 9 := by
  have hpowM_pos : 1 ≤ 2 ^ M := Nat.one_le_two_pow
  have hsp_eq := hashPairSpace_eq n_max M
  have hle_sp := le_hashPairSpace n_max M
  have hsp : z1Base hashBase n_max + 2 * 2 ^ M = hashBase + hashPairSpace n_max M := by
    dsimp only [z1Base, hashPairSpace]; omega
  have hfit_36 : Fits w 36 := hfit_space.of_le (by omega)
  have hfit_hb36 : Fits w (hashBase + 36) := hfit_space.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_space.of_le (by omega)
  have hfit_powM : Fits w (2 ^ M) := hfit_space.of_le (by omega)
  have hfit_2powM : Fits w (2 * 2 ^ M) := hfit_space.of_le (by omega)
  have hfit_hb1 : Fits w (hashBase + 1) := hfit_space.of_le (by omega)
  have hfit_end : Fits w (z1Base hashBase n_max + 2 * 2 ^ M) := by rwa [hsp]
  have hm36 : x.mem (hashBase + 36) = 2 ^ M - 1 := by
    rw [show hashBase + 36 = hashBase + 32 + 4 by omega]
    exact htab.2.2.2.2.2.2.2.1
  have hm1 : x.mem (hashBase + 1) = z1Base hashBase n_max := htab.2.1
  set s1 := x.set 1 36
  have e1 : Exec w (.op (.const 1 36) : Code .exact 19) x s1 1 := Exec.const hfit_36
  set s2 := s1.set 1 (hashBase + 36)
  have e2 : Exec w (.op (.exactBin .add 1 0 1) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0]) hfit_hb36
  set s3 := s2.set 1 (2 ^ M - 1)
  have e3 : Exec w (.op (.load 1 1) : Code .exact 19) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm36] using
      (Exec.load (B := .exact) (w := w) (d := 1) (a := 1) (x := s2))
  set s4 := s3.set 4 1
  have e4 : Exec w (.op (.const 4 1) : Code .exact 19) s3 s4 1 := Exec.const hfit_1
  set s5 := s4.set 3 (2 ^ M)
  have e5 : Exec w (.op (.exactBin .add 3 1 4) : Code .exact 19) s4 s5 1 :=
    ExactLog.exec_exactBin (by simp +decide [s4, s3, hpowM_pos]) hfit_powM
  set s6 := s5.set 3 (2 * 2 ^ M)
  have e6 : Exec w (.op (.exactBin .add 3 3 3) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin (by simp +decide [s5, Nat.two_mul]) hfit_2powM
  set s7 := s6.set 2 (hashBase + 1)
  have e7 : Exec w (.op (.exactBin .add 2 0 4) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, s5, s4, s3, s2, s1, h0]) hfit_hb1
  set s8 := s7.set 2 (z1Base hashBase n_max)
  have e8 : Exec w (.op (.load 2 2) : Code .exact 19) s7 s8 1 := by
    simpa +decide [s8, s7, s6, s5, s4, s3, s2, s1, hm1] using
      (Exec.load (B := .exact) (w := w) (d := 2) (a := 2) (x := s7))
  set s9 := s8.set 3 (z1Base hashBase n_max + 2 * 2 ^ M)
  have e9 : Exec w (.op (.exactBin .add 3 2 3) : Code .exact 19) s8 s9 1 :=
    ExactLog.exec_exactBin (by simp +decide [s8, s7, s6]) hfit_end
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
  have hd : s9 = resampleTabSetupData hashBase n_max M x := by
    ext i : 2
    · fin_cases i <;> rfl
    · rfl
  rwa [hd] at hall

theorem resampleTabSeedsCode_execRand {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M)) :
    ExecRand w resampleTabSeedsCode x (resampleTabComp hashBase n_max M x) := by
  have hsetup := resampleTabSetup_exec htab h0 hfit_space
  set d0 := resampleTabSetupData hashBase n_max M x
  have hsp_eq := hashPairSpace_eq n_max M
  have hsp : z1Base hashBase n_max + 2 * 2 ^ M = hashBase + hashPairSpace n_max M := by
    dsimp only [z1Base, hashPairSpace]; omega
  have hfit_end : Fits w (z1Base hashBase n_max + 2 * 2 ^ M) := by rwa [hsp]
  have hfit_mask : Fits w (2 ^ M - 1) :=
    hfit_space.of_le (by omega)
  have hloop0 := Tabulation.randFillLoop_execRand (w := w)
    (bits := M) (arrBase := z1Base hashBase n_max) (2 * 2 ^ M)
    (x := d0.comap resampleMap19)
    (by simp +decide [d0, resampleTabSetupData, resampleMap19, Data.comap, Tabulation.regPtr])
    (by simp +decide [d0, resampleTabSetupData, resampleMap19, Data.comap, Tabulation.regEnd])
    (by simp +decide [d0, resampleTabSetupData, resampleMap19, Data.comap, Tabulation.regMask])
    (by simp +decide [d0, resampleTabSetupData, resampleMap19, Data.comap, Tabulation.regOne])
    hfit_end hfit_mask
  have hloop := hloop0.rename injective_resampleMap19
  simpa only [resampleTabSeedsCode, resampleTabComp, d0, Functor.map_map] using
    hsetup.seqRand hloop

/-- Complete seed-resampling program `resampleHashPairCode`: samples all 28 polynomial seed words
and both random tabulation arrays `(Z₁, Z₂)` while preserving the shared `KWise` `clmulTab`. -/
@[expose]
def resampleHashPairCode : Code .exact 19 :=
  .seq resamplePolySeedsCode resampleTabSeedsCode

/-- Exact instruction count of `resampleHashPairCode`: `150 + (10 * 2 ^ M + 11) = 10 * 2 ^ M + 161`.
-/
@[expose]
def resampleHashPairSteps (M : ℕ) : ℕ :=
  10 * 2 ^ M + 161

/-- Exact `ProbComp` semantics of `resampleHashPairCode`. -/
@[expose]
noncomputable def resampleHashPairComp (hashBase n_max U M : ℕ) (x : Data 19) :
    ProbComp (Data 19 × ℕ) := do
  let z1 ← resamplePolyComp hashBase U M x
  let z2 ← resampleTabComp hashBase n_max M z1.1
  pure (z2.1, z1.2 + z2.2)

theorem mem_support_resamplePolyComp {hashBase U M : ℕ} {x : Data 19} {z : Data 19 × ℕ}
    (h0 : x.regs 0 = hashBase)
    (hz : z ∈ (resamplePolyComp hashBase U M x).support) :
    z.2 = 150 ∧
    z.1.regs 0 = hashBase ∧
    (∀ k < 28, z.1.mem (hashBase + 4 + k) < 2 ^ Probability.trinomialDeg U M) ∧
    (∀ a, (a < hashBase + 4 ∨ hashBase + 32 ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resamplePolyComp] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hz₀
  have h0' : (z₀.1.extend resampleMap19 (resamplePolySetupData hashBase U M x)).regs 0 =
      hashBase := by
    change ((z₀.1.extend resampleMap19
      (resamplePolySetupData hashBase U M x)).comap resampleMap19).regs Tabulation.regExtra =
      hashBase
    rw [Data.comap_extend injective_resampleMap19, hextra]
    simpa +decide [resamplePolySetupData, resampleMap19, Data.comap, Tabulation.regExtra] using h0
  exact ⟨by omega, h0', hlt, hframe⟩

theorem mem_support_resampleTabComp {hashBase n_max M : ℕ} {x : Data 19} {z : Data 19 × ℕ}
    (h0 : x.regs 0 = hashBase)
    (hz : z ∈ (resampleTabComp hashBase n_max M x).support) :
    z.2 = 10 * 2 ^ M + 11 ∧
    z.1.regs 0 = hashBase ∧
    (∀ i < 2 * 2 ^ M, z.1.mem (z1Base hashBase n_max + i) < 2 ^ M) ∧
    (∀ a, (a < z1Base hashBase n_max ∨ z1Base hashBase n_max + 2 * 2 ^ M ≤ a) →
      z.1.mem a = x.mem a) := by
  dsimp only [resampleTabComp] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
  obtain ⟨hsteps, -, -, -, -, hextra, hlt, hframe⟩ := Tabulation.mem_support_randFillComp hz₀
  have h0' : (z₀.1.extend resampleMap19 (resampleTabSetupData hashBase n_max M x)).regs 0 =
      hashBase := by
    change ((z₀.1.extend resampleMap19
      (resampleTabSetupData hashBase n_max M x)).comap resampleMap19).regs Tabulation.regExtra =
      hashBase
    rw [Data.comap_extend injective_resampleMap19, hextra]
    simpa +decide [resampleTabSetupData, resampleMap19, Data.comap, Tabulation.regExtra] using h0
  exact ⟨by omega, h0', hlt, hframe⟩

theorem HashPairTableRep.of_poly_frame {hashBase n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : HashPairTableRep hashBase n_max U M mem)
    (hframe : ∀ a, (a < hashBase + 4 ∨ hashBase + 32 ≤ a) → mem' a = mem a) :
    HashPairTableRep hashBase n_max U M mem' := by
  rcases htab with ⟨hM, hz1, hz2, hkw⟩
  refine ⟨(hframe hashBase (Or.inl (by omega))).trans hM,
    (hframe (hashBase + 1) (Or.inl (by omega))).trans hz1,
    (hframe (hashBase + 2) (Or.inl (by omega))).trans hz2, ?_⟩
  rcases hkw with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
  refine ⟨(hframe _ (Or.inr (by omega))).trans h0,
    (hframe _ (Or.inr (by omega))).trans h1,
    (hframe _ (Or.inr (by omega))).trans h2,
    (hframe _ (Or.inr (by omega))).trans h3,
    (hframe _ (Or.inr (by omega))).trans h4,
    (hframe _ (Or.inr (by omega))).trans h5,
    (hframe _ (Or.inr (by omega))).trans h6,
    (hframe _ (Or.inr (by omega))).trans h7,
    fun idx hidx => (hframe _ (Or.inr (by omega))).trans (hcl idx hidx)⟩

theorem HashPairTableRep.of_tab_frame {hashBase n_max U M : ℕ} {mem mem' : ℕ → ℕ}
    (htab : HashPairTableRep hashBase n_max U M mem)
    (hframe : ∀ a, (a < z1Base hashBase n_max ∨ z1Base hashBase n_max + 2 * 2 ^ M ≤ a) →
      mem' a = mem a) :
    HashPairTableRep hashBase n_max U M mem' := by
  have hz1_eq := z1Base_eq hashBase n_max
  have hz1_ge := le_z1Base hashBase n_max
  rcases htab with ⟨hM, hz1, hz2, hkw⟩
  refine ⟨(hframe hashBase (Or.inl (by omega))).trans hM,
    (hframe (hashBase + 1) (Or.inl (by omega))).trans hz1,
    (hframe (hashBase + 2) (Or.inl (by omega))).trans hz2, ?_⟩
  rcases hkw with ⟨h0, h1, h2, h3, h4, h5, h6, h7, hcl⟩
  refine ⟨(hframe _ (Or.inl (by omega))).trans h0,
    (hframe _ (Or.inl (by omega))).trans h1,
    (hframe _ (Or.inl (by omega))).trans h2,
    (hframe _ (Or.inl (by omega))).trans h3,
    (hframe _ (Or.inl (by omega))).trans h4,
    (hframe _ (Or.inl (by omega))).trans h5,
    (hframe _ (Or.inl (by omega))).trans h6,
    (hframe _ (Or.inl (by omega))).trans h7,
    fun idx hidx => (hframe _ (Or.inl (by omega))).trans (hcl idx hidx)⟩

/-- **`resampleHashPairCode` exact randomized execution**: runs in `resampleHashPairSteps M`
instructions and `28 + 2 * 2 ^ M` `Code.rand` calls. -/
theorem resampleHashPairCode_execRand {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    ExecRand w resampleHashPairCode x (resampleHashPairComp hashBase n_max U M x) := by
  have hle_sp := le_hashPairSpace n_max M
  have hfit_36 : Fits w (hashBase + 36) :=
    hfit_space.of_le (by omega)
  have h1 := resamplePolySeedsCode_execRand htab h0 hfit_36 hfit_q
  refine h1.seq fun z1 hz1 => ?_
  obtain ⟨-, hz1_0, -, hz1_frame⟩ := mem_support_resamplePolyComp h0 hz1
  exact resampleTabSeedsCode_execRand (htab.of_poly_frame hz1_frame) hz1_0 hfit_space

theorem mem_support_resampleHashPairComp {hashBase n_max U M : ℕ} {x : Data 19} {z : Data 19 × ℕ}
    (htab : HashPairTableRep hashBase n_max U M x.mem) (h0 : x.regs 0 = hashBase)
    (hz : z ∈ (resampleHashPairComp hashBase n_max U M x).support) :
    z.2 = resampleHashPairSteps M ∧
    z.1.regs 0 = hashBase ∧
    HashPairRep hashBase n_max U M (extractSeed hashBase n_max U M z.1.mem) z.1.mem ∧
    (∀ a, (a < hashBase + 4 ∨
      (hashBase + 32 ≤ a ∧ a < z1Base hashBase n_max) ∨
      hashBase + hashPairSpace n_max M ≤ a) → z.1.mem a = x.mem a) := by
  dsimp only [resampleHashPairComp] at hz
  obtain ⟨z1, hz1, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hz
  obtain ⟨z2, hz2, hpure⟩ := OracleComp.mem_supportWith_bind_iff.mp hrest
  cases OracleComp.eq_of_mem_supportWith_pure hpure
  obtain ⟨ht1, hz1_0, hpoly, hframe1⟩ := mem_support_resamplePolyComp h0 hz1
  obtain ⟨ht2, hz2_0, htab_lt, hframe2⟩ := mem_support_resampleTabComp hz1_0 hz2
  have hz1_ge := le_z1Base hashBase n_max
  have hpoly' : ∀ k < 28, z2.1.mem (hashBase + 4 + k) < 2 ^ Probability.trinomialDeg U M := by
    intro k hk
    rw [hframe2 (hashBase + 4 + k) (Or.inl (by omega))]
    exact hpoly k hk
  have htab' : HashPairTableRep hashBase n_max U M z2.1.mem :=
    (htab.of_poly_frame hframe1).of_tab_frame hframe2
  refine ⟨by dsimp only [resampleHashPairSteps]; omega, hz2_0,
    ⟨htab', hashPairSeedRep_extractSeed hpoly' htab_lt⟩, ?_⟩
  intro a ha
  have hsp : z1Base hashBase n_max + 2 * 2 ^ M = hashBase + hashPairSpace n_max M := by
    dsimp only [z1Base, hashPairSpace]; omega
  rcases ha with ha_lt | ⟨ha_ge, ha_lt2⟩ | ha_ge2
  · rw [hframe2 a (Or.inl (by omega)), hframe1 a (Or.inl ha_lt)]
  · rw [hframe2 a (Or.inl ha_lt2), hframe1 a (Or.inr ha_ge)]
  · rw [hframe2 a (Or.inr (by omega)), hframe1 a (Or.inr (by omega))]

theorem uniformOfFintype_bind_map_prodMk (α β : Type*) [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] :
    (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (a, ·)) =
      PMF.uniformOfFintype (α × β) := by
  ext ⟨a, b⟩
  rw [PMF.bind_map_prodMk_apply, PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply,
    PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
      (Or.inl (ENNReal.natCast_ne_top _))]

/-- **Exact uniformity of `resampleHashPairComp`**: the extracted seed
`extractSeed hashBase n_max U M z.1.mem` is distributed according to `seedLaw U M`. -/
theorem map_extractSeed_eval_resampleHashPairComp (hashBase n_max U M : ℕ) (x : Data 19) :
    ((resampleHashPairComp hashBase n_max U M x).eval).map
      (fun z => extractSeed hashBase n_max U M z.1.mem) = seedLaw U M := by
  set q := Probability.trinomialDeg U M
  set f1 : Data 19 → (Fin 4 → PolySeed U M) :=
    fun d => polySliceEquiv U M (Tabulation.extractSlice (hashBase + 4) q 28 d.mem)
  set f2 : Data 19 → TabSeed M × TabSeed M :=
    fun d => tabSliceEquiv M (Tabulation.extractSlice (z1Base hashBase n_max) M (2 * 2 ^ M) d.mem)
  have hf1_law :
      ((resamplePolyComp hashBase U M x).eval).map (fun z : Data 19 × ℕ => f1 z.1) =
        PMF.uniformOfFintype (Fin 4 → PolySeed U M) := by
    dsimp only [resamplePolyComp, f1]
    rw [ProbComp.eval_map, PMF.map_comp]
    have hslice := Tabulation.map_extractSlice_eval_randFillComp q (hashBase + 4) 28
      ((resamplePolySetupData hashBase U M x).comap resampleMap19)
    have hcomp :
        ((fun z : Data 19 × ℕ => polySliceEquiv U M
            (Tabulation.extractSlice (hashBase + 4) q 28 z.1.mem)) ∘
          fun z : Data 6 × ℕ =>
            (z.1.extend resampleMap19 (resamplePolySetupData hashBase U M x), 8 + z.2)) =
        polySliceEquiv U M ∘
          fun z : Data 6 × ℕ => Tabulation.extractSlice (hashBase + 4) q 28 z.1.mem := rfl
    rw [hcomp, ← PMF.map_comp, hslice]
    exact PMF.uniformOfFintype_map_equiv (polySliceEquiv U M)
  have hf2_law : ∀ d : Data 19,
      ((resampleTabComp hashBase n_max M d).eval).map (fun z : Data 19 × ℕ => f2 z.1) =
        PMF.uniformOfFintype (TabSeed M × TabSeed M) := by
    intro d
    dsimp only [resampleTabComp, f2]
    rw [ProbComp.eval_map, PMF.map_comp]
    have hslice := Tabulation.map_extractSlice_eval_randFillComp M (z1Base hashBase n_max)
      (2 * 2 ^ M) ((resampleTabSetupData hashBase n_max M d).comap resampleMap19)
    have hcomp :
        ((fun z : Data 19 × ℕ => tabSliceEquiv M
            (Tabulation.extractSlice (z1Base hashBase n_max) M (2 * 2 ^ M) z.1.mem)) ∘
          fun z : Data 6 × ℕ =>
            (z.1.extend resampleMap19 (resampleTabSetupData hashBase n_max M d), 9 + z.2)) =
        tabSliceEquiv M ∘
          fun z : Data 6 × ℕ =>
            Tabulation.extractSlice (z1Base hashBase n_max) M (2 * 2 ^ M) z.1.mem := rfl
    rw [hcomp, ← PMF.map_comp, hslice]
    exact PMF.uniformOfFintype_map_equiv (tabSliceEquiv M)
  have hinner : ∀ z1 : Data 19 × ℕ,
      ((do
        let z2 ← resampleTabComp hashBase n_max M z1.1
        pure (z2.1, z1.2 + z2.2)).eval).map
          (fun z : Data 19 × ℕ => extractSeed hashBase n_max U M z.1.mem) =
        (PMF.uniformOfFintype (TabSeed M × TabSeed M)).map (f1 z1.1, ·) := by
    intro z1
    have hd : (do
        let z2 ← resampleTabComp hashBase n_max M z1.1
        pure (z2.1, z1.2 + z2.2)) =
        (fun z2 : Data 19 × ℕ => (z2.1, z1.2 + z2.2)) <$>
          resampleTabComp hashBase n_max M z1.1 :=
      bind_pure_comp _ _
    rw [hd, ProbComp.eval_map, PMF.map_comp]
    have hcongr :
        ((resampleTabComp hashBase n_max M z1.1).eval).map
          ((fun z : Data 19 × ℕ => extractSeed hashBase n_max U M z.1.mem) ∘
            fun z2 : Data 19 × ℕ => (z2.1, z1.2 + z2.2)) =
        ((resampleTabComp hashBase n_max M z1.1).eval).map
          ((fun p => (f1 z1.1, p)) ∘ fun z2 : Data 19 × ℕ => f2 z2.1) := by
      apply PMF.map_congr_on_support
      intro z2 hz2
      rw [ProbComp.support_eval] at hz2
      dsimp only [resampleTabComp] at hz2
      obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz2
      obtain ⟨-, -, -, -, -, -, -, hframe⟩ := Tabulation.mem_support_randFillComp hz₀
      have hz1_ge := le_z1Base hashBase n_max
      have hslice_eq :
          Tabulation.extractSlice (hashBase + 4) q 28 z₀.1.mem =
            Tabulation.extractSlice (hashBase + 4) q 28 z1.1.mem := by
        funext i
        dsimp only [Tabulation.extractSlice]
        rw [hframe (hashBase + 4 + i.val) (Or.inl (by omega))]
        rfl
      dsimp only [Function.comp_apply, extractSeed, f1, f2]
      exact Prod.ext (congrArg (polySliceEquiv U M) hslice_eq) rfl
    rw [hcongr, ← PMF.map_comp, hf2_law z1.1]
  dsimp only [resampleHashPairComp]
  rw [ProbComp.eval_bind, PMF.map_bind]
  simp only [hinner]
  have hbind :
      (resamplePolyComp hashBase U M x).eval.bind
        (fun z1 : Data 19 × ℕ =>
          (PMF.uniformOfFintype (TabSeed M × TabSeed M)).map (f1 z1.1, ·)) =
      (((resamplePolyComp hashBase U M x).eval).map (fun z1 => f1 z1.1)).bind
        (fun c => (PMF.uniformOfFintype (TabSeed M × TabSeed M)).map (c, ·)) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, hf1_law, uniformOfFintype_bind_map_prodMk]
  rfl

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

/-- Setup block for `stageSeedCode r`: prepares `src = hashBase + 4 + 7 * r.val`,
`dst = hashBase + 40`, `dstEnd = hashBase + 47`, and `one = 1`. -/
@[expose]
def stageSeedSetup (r : Fin 4) : Code .exact 19 :=
  .seq (.op (.const 3 (4 + 7 * r.val)))
  (.seq (.op (.exactBin .add 3 0 3))
  (.seq (.op (.const 4 40))
  (.seq (.op (.exactBin .add 4 0 4))
  (.seq (.op (.const 5 47))
  (.seq (.op (.exactBin .add 5 0 5))
        (.op (.const 6 1)))))))

/-- Program copying the `r`-th 7-word polynomial seed into the active seed slot
`[hashBase + 40, hashBase + 47)`. -/
@[expose]
def stageSeedCode (r : Fin 4) : Code .exact 19 :=
  .seq (stageSeedSetup r) copyWordsLoop

/-- Program evaluating the `r`-th polynomial hash `evalPoly (θ.1 r) u` into `reg 2` (`regOut`)
while preserving `reg 0 = hashBase`, `reg 1 = u.val`, `reg 18`, and `HashPairRep`. -/
@[expose]
def evalPolyCode (r : Fin 4) : Code .exact 19 :=
  .seq (stageSeedCode r)
  (.seq (.op (.const 15 32))
  (.seq (.op (.exactBin .add 0 0 15))
  (.seq ((KWise.evalCode 7).rename cast18To19)
  (.seq (.op (.const 15 32))
        (.op (.exactBin .sub 0 0 15))))))

/-- Exact step bound for `evalPolyCode r`. -/
@[expose]
def evalPolySteps (n_max U M : ℕ) : ℕ :=
  KWise.evalSteps n_max U M 7 + 55

theorem evalPolyCode_execWithin {w hashBase n_max U M : ℕ} {θ : Seed U M}
    (r : Fin 4) (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M)) :
    ∃ y : Data 19,
      ExecWithin w (evalPolyCode r) x y (evalPolySteps n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalPoly (θ.1 r) u).val ∧
      y.regs 18 = x.regs 18 ∧
      HashPairRep hashBase n_max U M θ y.mem ∧
      (∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → y.mem a = x.mem a) := by
  have hr_lt := r.isLt
  have hle_sp := le_hashPairSpace n_max M
  have hfit_src_off : Fits w (4 + 7 * r.val) :=
    hfit_space.of_le (by omega)
  have hfit_src : Fits w (hashBase + (4 + 7 * r.val)) :=
    hfit_space.of_le (by omega)
  have hfit_40 : Fits w 40 :=
    hfit_space.of_le (by omega)
  have hfit_hb40 : Fits w (hashBase + 40) :=
    hfit_space.of_le (by omega)
  have hfit_47 : Fits w 47 :=
    hfit_space.of_le (by omega)
  have hfit_hb47 : Fits w (hashBase + 47) :=
    hfit_space.of_le (by omega)
  have hfit_1 : Fits w 1 :=
    hfit_space.of_le (by omega)
  have hfit_32 : Fits w 32 :=
    hfit_space.of_le (by omega)
  have hfit_hb32 : Fits w (hashBase + 32) :=
    hfit_space.of_le (by omega)
  have hfit_hb : Fits w hashBase :=
    hfit_space.of_le (by omega)
  have hfit_kw : Fits w (hashBase + 32 + KWise.space n_max 7) :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  set s1 := x.set 3 (4 + 7 * r.val)
  have e1 : Exec w (.op (.const 3 (4 + 7 * r.val)) : Code .exact 19) x s1 1 :=
    Exec.const hfit_src_off
  set s2 := s1.set 3 (hashBase + (4 + 7 * r.val))
  have e2 : Exec w (.op (.exactBin .add 3 0 3) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0]) hfit_src
  set s3 := s2.set 4 40
  have e3 : Exec w (.op (.const 4 40) : Code .exact 19) s2 s3 1 := Exec.const hfit_40
  set s4 := s3.set 4 (hashBase + 40)
  have e4 : Exec w (.op (.exactBin .add 4 0 4) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, h0]) hfit_hb40
  set s5 := s4.set 5 47
  have e5 : Exec w (.op (.const 5 47) : Code .exact 19) s4 s5 1 := Exec.const hfit_47
  set s6 := s5.set 5 (hashBase + 47)
  have e6 : Exec w (.op (.exactBin .add 5 0 5) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin (by simp +decide [s5, s4, s3, s2, s1, h0]) hfit_hb47
  set s7 := s6.set 6 1
  have e7 : Exec w (.op (.const 6 1) : Code .exact 19) s6 s7 1 := Exec.const hfit_1
  have esetup : Exec w (stageSeedSetup r) x s7 7 :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  obtain ⟨d1, ecopy, hd1_regs, hd1_copy, hd1_frame⟩ :=
    copyWordsLoop_exec (w := w) 7 (hashBase + (4 + 7 * r.val)) (hashBase + 40) (x := s7)
      (by simp +decide [s7, s6, s5, s4, s3, s2])
      (by simp +decide [s7, s6, s5, s4])
      (by simp +decide [s7, s6, Nat.add_assoc])
      (by simp +decide [s7])
      (by omega)
      (by rwa [show hashBase + 40 + 7 = hashBase + 47 by omega])
  have estage : Exec w (stageSeedCode r) x d1 51 := esetup.seq ecopy
  have hd1_0 : d1.regs 0 = hashBase := by
    rw [hd1_regs 0 ⟨by decide, by decide, by decide⟩]
    simp +decide [s7, s6, s5, s4, s3, s2, s1, h0]
  have hd1_1 : d1.regs 1 = u.val := by
    rw [hd1_regs 1 ⟨by decide, by decide, by decide⟩]
    simp +decide [s7, s6, s5, s4, s3, s2, s1, h1]
  have hd1_18 : d1.regs 18 = x.regs 18 := by
    rw [hd1_regs 18 ⟨by decide, by decide, by decide⟩]
    simp +decide [s7, s6, s5, s4, s3, s2, s1]
  have hd1_frame' : ∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → d1.mem a = x.mem a := by
    intro a ha
    exact hd1_frame a (by omega)
  have hd1_rep : HashPairRep hashBase n_max U M θ d1.mem :=
    hrep.congr_of_active_slot hd1_frame'
  have hd1_kw_rep : KWise.Rep (hashBase + 32) (KWise.chunkBits n_max) U M 7 (θ.1 r) d1.mem := by
    refine ⟨hd1_rep.1.2.2.2, fun j => ?_⟩
    rw [show hashBase + 32 + 8 + j.val = hashBase + 40 + j.val by omega, hd1_copy j.val j.isLt]
    dsimp only [s7, s6, s5, s4, s3, s2, s1, Data.set]
    rw [show hashBase + (4 + 7 * r.val) + j.val = hashBase + 4 + 7 * r.val + j.val by omega]
    exact hrep.2.1 r j
  set d2 := d1.set 15 32
  have esh1 : Exec w (.op (.const 15 32) : Code .exact 19) d1 d2 1 := Exec.const hfit_32
  set d3 := d2.set 0 (hashBase + 32)
  have esh2 : Exec w (.op (.exactBin .add 0 0 15) : Code .exact 19) d2 d3 1 :=
    ExactLog.exec_exactBin (by simp +decide [d2, hd1_0]) hfit_hb32
  obtain ⟨y_kw, ⟨t_kw, ht_kw, he_kw⟩, hy_kw0, hy_kw1, hy_kw2, hy_kw_mem⟩ :=
    KWise.evalCode_execWithin (w := w) (base := hashBase + 32) (n_max := n_max)
      (U := U) (M := M) (k := 7) (c := θ.1 r) u (x := d3.comap cast18To19)
      hd1_kw_rep
      (by simp +decide [d3, d2, cast18To19, Data.comap])
      (by simp +decide [d3, d2, cast18To19, Data.comap, hd1_1])
      hw hfit_kw
  set d4 := y_kw.extend cast18To19 d3
  have he_kw' : Exec w ((KWise.evalCode 7).rename cast18To19) d3 d4 t_kw :=
    he_kw.rename injective_cast18To19
  have hd4_0 : d4.regs 0 = hashBase + 32 := by
    change ((y_kw.extend cast18To19 d3).comap cast18To19).regs 0 = hashBase + 32
    rw [Data.comap_extend injective_cast18To19, hy_kw0]
  have hd4_1 : d4.regs 1 = u.val := by
    change ((y_kw.extend cast18To19 d3).comap cast18To19).regs 1 = u.val
    rw [Data.comap_extend injective_cast18To19, hy_kw1]
  have hd4_2 : d4.regs 2 = (evalPoly (θ.1 r) u).val := by
    change ((y_kw.extend cast18To19 d3).comap cast18To19).regs 2 = (evalPoly (θ.1 r) u).val
    rw [Data.comap_extend injective_cast18To19]
    exact hy_kw2
  have hd4_18 : d4.regs 18 = x.regs 18 := by
    rw [he_kw'.regs_eq (Code.preserves_rename_of_forall_ne _ _ 18 (by decide))]
    simp +decide [d3, d2, hd1_18]
  have hd4_mem : d4.mem = d1.mem := hy_kw_mem
  set d5 := d4.set 15 32
  have esh3 : Exec w (.op (.const 15 32) : Code .exact 19) d4 d5 1 := Exec.const hfit_32
  set d6 := d5.set 0 hashBase
  have esh4 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19) d5 d6 1 :=
    ExactLog.exec_exactBin (by simp +decide [d5, hd4_0]) hfit_hb
  have hall := estage.seq (esh1.seq (esh2.seq (he_kw'.seq (esh3.seq esh4))))
  refine ⟨d6, ⟨51 + (1 + (1 + (t_kw + (1 + 1)))), by dsimp only [evalPolySteps]; omega, hall⟩,
    by simp +decide [d6, d5],
    by simp +decide [d6, d5, hd4_1],
    by simp +decide [d6, d5, hd4_2],
    by simp +decide [d6, d5, hd4_18],
    by change HashPairRep hashBase n_max U M θ d4.mem; rwa [hd4_mem],
    fun a ha => by change d4.mem a = x.mem a; rw [hd4_mem]; exact hd1_frame' a ha⟩

/-- Word-RAM program evaluating `h₁(u) = f₁(u) ^^^ Z₁[g₁(u)]` into `reg 2` (`regOut`) while
preserving `reg 0 = hashBase`, `reg 1 = u.val`, and `HashPairRep`. -/
@[expose]
def evalHash1Code : Code .exact 19 :=
  .seq (evalPolyCode 0)
  (.seq (.op (.copy 18 2))
  (.seq (evalPolyCode 1)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 15 15))
  (.seq (.op (.exactBin .add 15 15 2))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .xor 2 18 15)))))))))

/-- Word-RAM program evaluating `h₂(u) = f₂(u) ^^^ Z₂[g₂(u)]` into `reg 2` (`regOut`) while
preserving `reg 0 = hashBase`, `reg 1 = u.val`, and `HashPairRep`. -/
@[expose]
def evalHash2Code : Code .exact 19 :=
  .seq (evalPolyCode 2)
  (.seq (.op (.copy 18 2))
  (.seq (evalPolyCode 3)
  (.seq (.op (.const 15 2))
  (.seq (.op (.exactBin .add 15 0 15))
  (.seq (.op (.load 15 15))
  (.seq (.op (.exactBin .add 15 15 2))
  (.seq (.op (.load 15 15))
        (.op (.exactBin .xor 2 18 15)))))))))

/-- Exact step bound for `evalHash1Code` and `evalHash2Code`. -/
@[expose]
def evalHashSteps (n_max U M : ℕ) : ℕ :=
  2 * evalPolySteps n_max U M + 7

theorem evalHash1Code_execWithin {w hashBase n_max U M : ℕ} {θ : Seed U M}
    (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M)) :
    ∃ y : Data 19,
      ExecWithin w evalHash1Code x y (evalHashSteps n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash1 θ u).val ∧
      HashPairRep hashBase n_max U M θ y.mem ∧
      (∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨d1, ⟨t1, ht1, he1⟩, hd1_0, hd1_1, hd1_2, -, hd1_rep, hd1_frame⟩ :=
    evalPolyCode_execWithin 0 u hrep h0 h1 hw hfit_space
  set d2 := d1.set 18 (evalPoly (θ.1 0) u).val
  have ec : Exec w (.op (.copy 18 2) : Code .exact 19) d1 d2 1 := by
    simpa +decide [d2, hd1_2] using (Exec.copy (B := .exact) (w := w) (d := 18) (s := 2) (x := d1))
  obtain ⟨d3, ⟨t2, ht2, he2⟩, hd3_0, hd3_1, hd3_2, hd3_18, hd3_rep, hd3_frame⟩ :=
    evalPolyCode_execWithin 1 u (x := d2) hd1_rep
      (by simp +decide [d2, hd1_0])
      (by simp +decide [d2, hd1_1])
      hw hfit_space
  have hd2_18 : d2.regs 18 = (evalPoly (θ.1 0) u).val := by simp +decide [d2]
  rw [hd2_18] at hd3_18
  have hle_sp := le_hashPairSpace n_max M
  have hfit_1 : Fits w 1 :=
    hfit_space.of_le (by omega)
  have hfit_hb1 : Fits w (hashBase + 1) :=
    hfit_space.of_le (by omega)
  have hg1_lt := (evalPoly (θ.1 1) u).isLt
  have hfit_addr : Fits w (z1Base hashBase n_max + (evalPoly (θ.1 1) u).val) :=
    hfit_space.of_le (by dsimp only [z1Base, hashPairSpace]; omega)
  have hxor_lt : (evalHash1 θ u).val < 2 ^ M := (evalHash1 θ u).isLt
  have hfit_xor : Fits w (evalHash1 θ u).val :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hm1 : d3.mem (hashBase + 1) = z1Base hashBase n_max := hd3_rep.1.2.1
  have hm_z1 : d3.mem (z1Base hashBase n_max + (evalPoly (θ.1 1) u).val) =
      (θ.2.1 (evalPoly (θ.1 1) u)).val := hd3_rep.2.2.1 (evalPoly (θ.1 1) u)
  set s1 := d3.set 15 1
  have el1 : Exec w (.op (.const 15 1) : Code .exact 19) d3 s1 1 := Exec.const hfit_1
  set s2 := s1.set 15 (hashBase + 1)
  have el2 : Exec w (.op (.exactBin .add 15 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, hd3_0]) hfit_hb1
  set s3 := s2.set 15 (z1Base hashBase n_max)
  have el3 : Exec w (.op (.load 15 15) : Code .exact 19) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm1] using
      (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s2))
  set s4 := s3.set 15 (z1Base hashBase n_max + (evalPoly (θ.1 1) u).val)
  have el4 : Exec w (.op (.exactBin .add 15 15 2) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, hd3_2]) hfit_addr
  set s5 := s4.set 15 (θ.2.1 (evalPoly (θ.1 1) u)).val
  have el5 : Exec w (.op (.load 15 15) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, hm_z1] using
      (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s4))
  set s6 := s5.set 2 (evalHash1 θ u).val
  have el6 : Exec w (.op (.exactBin .xor 2 18 15) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s5, s4, s3, s2, s1, hd3_18, evalHash1, finXor]) hfit_xor
  have hall := he1.seq (ec.seq (he2.seq (el1.seq (el2.seq (el3.seq (el4.seq (el5.seq el6)))))))
  refine ⟨s6, ⟨t1 + (1 + (t2 + 6)), by dsimp only [evalHashSteps]; omega, hall⟩,
    by simp +decide [s6, s5, s4, s3, s2, s1, hd3_0],
    by simp +decide [s6, s5, s4, s3, s2, s1, hd3_1],
    by simp +decide [s6],
    hd3_rep,
    fun a ha => (hd3_frame a ha).trans (hd1_frame a ha)⟩

theorem evalHash2Code_execWithin {w hashBase n_max U M : ℕ} {θ : Seed U M}
    (u : Fin U) {x : Data 19}
    (hrep : HashPairRep hashBase n_max U M θ x.mem)
    (h0 : x.regs 0 = hashBase) (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (hashBase + hashPairSpace n_max M)) :
    ∃ y : Data 19,
      ExecWithin w evalHash2Code x y (evalHashSteps n_max U M) ∧
      y.regs 0 = hashBase ∧
      y.regs 1 = u.val ∧
      y.regs 2 = (evalHash2 θ u).val ∧
      HashPairRep hashBase n_max U M θ y.mem ∧
      (∀ a, (a < hashBase + 40 ∨ hashBase + 47 ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨d1, ⟨t1, ht1, he1⟩, hd1_0, hd1_1, hd1_2, -, hd1_rep, hd1_frame⟩ :=
    evalPolyCode_execWithin 2 u hrep h0 h1 hw hfit_space
  set d2 := d1.set 18 (evalPoly (θ.1 2) u).val
  have ec : Exec w (.op (.copy 18 2) : Code .exact 19) d1 d2 1 := by
    simpa +decide [d2, hd1_2] using (Exec.copy (B := .exact) (w := w) (d := 18) (s := 2) (x := d1))
  obtain ⟨d3, ⟨t2, ht2, he2⟩, hd3_0, hd3_1, hd3_2, hd3_18, hd3_rep, hd3_frame⟩ :=
    evalPolyCode_execWithin 3 u (x := d2) hd1_rep
      (by simp +decide [d2, hd1_0])
      (by simp +decide [d2, hd1_1])
      hw hfit_space
  have hd2_18 : d2.regs 18 = (evalPoly (θ.1 2) u).val := by simp +decide [d2]
  rw [hd2_18] at hd3_18
  have hle_sp := le_hashPairSpace n_max M
  have hfit_2 : Fits w 2 :=
    hfit_space.of_le (by omega)
  have hfit_hb2 : Fits w (hashBase + 2) :=
    hfit_space.of_le (by omega)
  have hg2_lt := (evalPoly (θ.1 3) u).isLt
  have hfit_addr : Fits w (z2Base hashBase n_max M + (evalPoly (θ.1 3) u).val) :=
    hfit_space.of_le (by dsimp only [z2Base, z1Base, hashPairSpace]; omega)
  have hxor_lt : (evalHash2 θ u).val < 2 ^ M := (evalHash2 θ u).isLt
  have hfit_xor : Fits w (evalHash2 θ u).val :=
    hfit_space.of_le (by dsimp only [hashPairSpace]; omega)
  have hm2 : d3.mem (hashBase + 2) = z2Base hashBase n_max M := hd3_rep.1.2.2.1
  have hm_z2 : d3.mem (z2Base hashBase n_max M + (evalPoly (θ.1 3) u).val) =
      (θ.2.2 (evalPoly (θ.1 3) u)).val := hd3_rep.2.2.2 (evalPoly (θ.1 3) u)
  set s1 := d3.set 15 2
  have el1 : Exec w (.op (.const 15 2) : Code .exact 19) d3 s1 1 := Exec.const hfit_2
  set s2 := s1.set 15 (hashBase + 2)
  have el2 : Exec w (.op (.exactBin .add 15 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, hd3_0]) hfit_hb2
  set s3 := s2.set 15 (z2Base hashBase n_max M)
  have el3 : Exec w (.op (.load 15 15) : Code .exact 19) s2 s3 1 := by
    simpa +decide [s3, s2, s1, hm2] using
      (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s2))
  set s4 := s3.set 15 (z2Base hashBase n_max M + (evalPoly (θ.1 3) u).val)
  have el4 : Exec w (.op (.exactBin .add 15 15 2) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, hd3_2]) hfit_addr
  set s5 := s4.set 15 (θ.2.2 (evalPoly (θ.1 3) u)).val
  have el5 : Exec w (.op (.load 15 15) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, hm_z2] using
      (Exec.load (B := .exact) (w := w) (d := 15) (a := 15) (x := s4))
  set s6 := s5.set 2 (evalHash2 θ u).val
  have el6 : Exec w (.op (.exactBin .xor 2 18 15) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s5, s4, s3, s2, s1, hd3_18, evalHash2, finXor]) hfit_xor
  have hall := he1.seq (ec.seq (he2.seq (el1.seq (el2.seq (el3.seq (el4.seq (el5.seq el6)))))))
  refine ⟨s6, ⟨t1 + (1 + (t2 + 6)), by dsimp only [evalHashSteps]; omega, hall⟩,
    by simp +decide [s6, s5, s4, s3, s2, s1, hd3_0],
    by simp +decide [s6, s5, s4, s3, s2, s1, hd3_1],
    by simp +decide [s6],
    hd3_rep,
    fun a ha => (hd3_frame a ha).trans (hd1_frame a ha)⟩

end Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing
