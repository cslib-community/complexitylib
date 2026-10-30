/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.WordRAM.Dictionary.CuckooHashing.HashFamily
public import Complexity.Computability.WordRAM.Randomized.Subroutine
public import Complexity.Computability.WordRAM.Randomized.UniformLoopExit

/-!
# Pagh–Rodler Cuckoo Hashing on the Randomized Word RAM

This module implements Pagh and Rodler's two-table cuckoo hashing dictionary [PaghRodler2004] on
the randomized Word RAM (`Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard`), realizing
the bounded-capacity lookup-and-insert specification
`Cslib.Algorithms.Lean.Dictionary.spec U V n_max` via a composable
`Cslib.WordRAM.Randomized.SubroutineDS` certificate (`seedSlack := 2`, `potential := 0`) and an
expected-amortized sequence theorem `cuckoo_seq_expected_amortized`.

## Design overview

1. **Memory layout (`O(n_max)` words):**
   - A `20`-word header at `[base, base + 20)` storing runtime parameters `(n_max, U, M, 2 ^ M,
     MaxLoop, n)` and section base pointers `(hashBase, t1Base, t2Base, keysBase, valsBase)`
     together with scratch slots `base + 11 .. 19` preserved across hash evaluations and seed
     resamplings.
   - A self-contained hash pair region at `hashBase = base + 20` of size
     `hashPairSpace n_max (tableBits n_max)` sharing a single Four-Russians carryless-multiplication
     table `clmulTab` across the four degree-`< 7` trinomial polynomial hashes `f₁, g₁, f₂, g₂` and
     storing two random tabulation tables `Z₁, Z₂` of size `m = 2 ^ M` (`M = tableBits n_max`).
     Here `(evalHash1, evalHash2)` is a **modified variant** inspired by Dietzfelbinger and Woelfel
     [DietzfelbingerWoelfel2003, Definition 1, §2.1, p. 632]: whereas their Definition 1 uses a
     single shared auxiliary hash `g` and addition modulo `m`, `(evalHash1, evalHash2)` uses
     independent `g₁, g₂` and bitwise XOR (`finXor`) over `Fin (2 ^ M)`. Per-function `7`-wise
     independence (`isKWiseIndependentHash_evalHash1`, `isKWiseIndependentHash_evalHash2`) does not
     establish Dietzfelbinger and Woelfel's graph/rehash guarantees for this modified pair, and
     correspondence / `IsCuckooHashFamily` instantiation for `n_max ≥ 3` remains unproved.
   - Two cuckoo sub-tables `T₁` and `T₂` of size `m = 2 ^ M ≥ max(4 * n_max, 4)` each, storing
     `1`-based indices `encodeSlot (some e) = e.idx + 1` (`0` for empty slots).
   - Insertion-order key and value arrays `insKeys[0 .. n - 1]` and `insVals[0 .. n - 1]` of
     capacity `n_max` words each.

2. **Lookup, displacement, and Las Vegas rehash:**
   - `get u` probes at most the two candidate locations `T₁[h₁(u)]` and `T₂[h₂(u)]` in deterministic
     worst-case `getSteps n_max U` instructions with zero `rand` calls.
   - `insert u v` first runs the same 2-probe check (`probeKeyCode`): if `u` is already present,
     it updates `insVals[idx] ← v` in place in `insertBaseSteps n_max U` deterministic steps without
     moving any keys. If `u` is absent, it appends `(u, v)` at index `n = (dom s).card < n_max`,
     runs up to `MaxLoop = maxEvictions n_max = 6 * (⌈log₂ max(n_max, 2)⌉ + 2)` two-table
     displacement rounds (`evictLoopCode`), and on overflow enters a Las Vegas `Code.loop`
     (`rehashLoopCode`) that resamples the polynomial and tabulation seeds (without rebuilding
     `clmulTab`), clears `T₁` and `T₂`, and replays `insKeys[0 .. n]` in exact insertion order
     (`ExecCodeDist.loop_geometric`).

3. **Exact conditional-uniform seed marginal (`seedSlack = 2`, `potential = 0`):**
   - Because `Dictionary.spec` has no deletion operation (`dom s` only grows and in-place value
     updates do not displace keys) and `rehashLoopCode` replays `insKeys` in exact insertion order,
     the set `E_t = survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks_t` of seeds on which
     `pureReplay` succeeds shrinks monotonically (`E_t ⊆ E_{t - 1}`).
   - Keeping the in-memory seed when `θ ∈ E_t` and rejection-sampling uniformly from `E_t` when
     `θ ∈ E_{t - 1} \ E_t` preserves the exact conditional uniform distribution
     `PMF.uniformOfFinset E_t` (`unifOn_rehash_eq` and `loopExitPMF_map_eq_uniformOfFinset`),
     which is bounded by `2 * seedLaw U M` via `rehash_prob_le_half`
     (`uniformOfFinset_le_two_mul_uniformOfFintype`).
   - Using the **original strengthened sufficient assumptions** in `IsCuckooHashPair` —
     `GoodForSet` (all `Nodup` sublists in `S`), `cuckooWalkRounds` (`sSup` over all
     `ValidPlacement`s of `S`), `IsCuckooHashPair.expected_walk_le`, and the one-step incremental
     replay failure bound `IsCuckooHashPair.step_rehash_prob_le` (inspired by Pagh and Rodler
     [PaghRodler2004], 8 December 2003 manuscript, Section 2.3 "Amortized insertion time",
     pp. 6–10: Lemma 1 on p. 7, Eq. (3) on p. 9, and the rehash analysis on pp. 9–10) — bounds the
     expected step cost of every `insert` by `insertCharge n_max U C_walk C_reh =
     2 * (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
     C_reh * rehashAmortizedSteps n_max U)`. For `n_max ≤ 2`, `isCuckooHashFamily_le_two` supplies
     `IsCuckooHashFamily` unconditionally with `C_walk = 1` and `C_reh = 0`.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.space`: total Word-RAM footprint in words.
* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.RepWithKeys`,
  `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.Rep`: representation invariants.
* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.cuckooCode`: `SubroutineCode .exact 19 2`
  packaging `allocSpan`, `initSetup`, and `opCode`.
* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.subroutineDS`,
  `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.subroutineDSStandard`: composable randomized
  Word-RAM data-structure certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.getCode_execWithin`: worst-case deterministic
  2-probe lookup specification.
* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.rehashLoopCode_execCodeDist`: geometric Las
  Vegas termination, expected step bound, and exact conditional-uniform exit law for full-table
  rehashing.
* `Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing.cuckoo_seq_expected_amortized`: end-to-end
  expected-time bound across arbitrary valid `get`/`insert` histories.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Amortized insertion time", pp. 6–10: Lemma 1 on p. 7, Eq. (3) on p. 9, and rehash
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
open Cslib.WordRAM.Randomized
open Cslib.Probability
open Cslib.Probability.PMF
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Hashing
open scoped ENNReal

/-! ### Section 1: Memory layout, slot encoding, and representation invariants -/

/-- Base address of the hash pair region `[base + 20, t1Base base n_max)`. -/
@[expose]
def hashBase (base : ℕ) : ℕ :=
  base + 20

/-- Base address of the first cuckoo sub-table `T₁` of size `tableSize n_max`. -/
@[expose]
def t1Base (base n_max : ℕ) : ℕ :=
  hashBase base + hashPairSpace n_max (tableBits n_max)

/-- Base address of the second cuckoo sub-table `T₂` of size `tableSize n_max`. -/
@[expose]
def t2Base (base n_max : ℕ) : ℕ :=
  t1Base base n_max + tableSize n_max

/-- Base address of the insertion-order key array `insKeys[0 .. n_max - 1]`. -/
@[expose]
def keysBase (base n_max : ℕ) : ℕ :=
  t2Base base n_max + tableSize n_max

/-- Base address of the insertion-order value array `insVals[0 .. n_max - 1]`. -/
@[expose]
def valsBase (base n_max : ℕ) : ℕ :=
  keysBase base n_max + n_max

/-- Total contiguous Word-RAM memory footprint `[base, base + space n_max)` in words. -/
@[expose]
def space (n_max : ℕ) : ℕ :=
  20 + hashPairSpace n_max (tableBits n_max) + 2 * tableSize n_max + 2 * n_max

theorem valsBase_add_eq (base n_max : ℕ) :
    valsBase base n_max + n_max = base + space n_max := by
  dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]
  omega

theorem le_space (n_max : ℕ) :
    77 ≤ space n_max := by
  have h1 := le_hashPairSpace n_max (tableBits n_max)
  have h2 := four_le_tableSize n_max
  dsimp only [space]
  omega

/-- Each sub-table size `tableSize n_max = 2 ^ tableBits n_max` is at most `8 * max n_max 1`. -/
theorem tableSize_le_eight_mul_max (n_max : ℕ) :
    tableSize n_max ≤ 8 * max n_max 1 := by
  rcases eq_or_ne n_max 0 with rfl | hne
  · decide
  · have hmax : max (4 * n_max) 4 = 4 * n_max := Nat.max_eq_left (by omega)
    have hgt1 : 1 < 4 * n_max := by omega
    have hclog_pos : 0 < Nat.clog 2 (4 * n_max) :=
      Nat.clog_pos (by decide) hgt1
    have hlt_pow : 2 ^ (Nat.clog 2 (4 * n_max) - 1) < 4 * n_max := by
      by_contra! hle
      have hbad := (Nat.clog_le_iff_le_pow (by decide)).mpr hle
      omega
    have hpow_eq : 2 ^ Nat.clog 2 (4 * n_max) = 2 * 2 ^ (Nat.clog 2 (4 * n_max) - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hclog_pos, pow_succ']
    dsimp only [tableSize, tableBits]
    rw [hmax, hpow_eq, Nat.max_eq_left (by omega)]
    omega

/-- Total memory footprint `space n_max` is `O(n_max)`: at most `67 + 35 * max n_max 4` words. -/
theorem space_le (n_max : ℕ) :
    space n_max ≤ 67 + 35 * max n_max 4 := by
  have h1 := KWise.two_pow_two_mul_chunkBits_le n_max
  have h2 := tableSize_le_eight_mul_max n_max
  have h3 : hashPairSpace n_max (tableBits n_max) =
      47 + 2 ^ (2 * KWise.chunkBits n_max) + 2 * tableSize n_max := by
    rw [hashPairSpace_eq, tableSize]
  have hmax1 : max n_max 1 ≤ max n_max 4 := max_le_max_left n_max (by decide)
  have hmax2 : max 4 n_max = max n_max 4 := Nat.max_comm 4 n_max
  dsimp only [space]
  omega

/-- Encode an optional `SlotEntry U` as a single machine word: `0` for `none` and `e.idx + 1` for
`some e`. -/
@[expose]
def encodeSlot {U : ℕ} : Option (SlotEntry U) → ℕ
  | none => 0
  | some e => e.idx + 1

@[simp]
theorem encodeSlot_none {U : ℕ} : encodeSlot (none : Option (SlotEntry U)) = 0 := rfl

@[simp]
theorem encodeSlot_some {U : ℕ} (e : SlotEntry U) : encodeSlot (some e) = e.idx + 1 := rfl

theorem encodeSlot_eq_zero_iff {U : ℕ} (o : Option (SlotEntry U)) :
    encodeSlot o = 0 ↔ o = none := by
  cases o <;> simp [encodeSlot]

theorem encodeSlot_pos_iff {U : ℕ} (o : Option (SlotEntry U)) :
    0 < encodeSlot o ↔ ∃ e, o = some e := by
  cases o with
  | none => simp [encodeSlot]
  | some e => simp [encodeSlot]

/-- Memory representation of the two cuckoo sub-tables `T₁` (at `t1Addr`) and `T₂` (at `t2Addr`).
-/
@[expose]
def TableSlotsRep {U M : ℕ} (t1Addr t2Addr : ℕ) (tbl : PureTable U (2 ^ M))
    (mem : ℕ → ℕ) : Prop :=
  (∀ b : Fin (2 ^ M), mem (t1Addr + b.val) = encodeSlot (tbl.t1 b)) ∧
  (∀ b : Fin (2 ^ M), mem (t2Addr + b.val) = encodeSlot (tbl.t2 b))

theorem TableSlotsRep.congr {U M t1Addr t2Addr : ℕ} {tbl : PureTable U (2 ^ M)}
    {mem mem' : ℕ → ℕ} (h : TableSlotsRep t1Addr t2Addr tbl mem)
    (h1 : ∀ b < 2 ^ M, mem' (t1Addr + b) = mem (t1Addr + b))
    (h2 : ∀ b < 2 ^ M, mem' (t2Addr + b) = mem (t2Addr + b)) :
    TableSlotsRep t1Addr t2Addr tbl mem' :=
  ⟨fun b => (h1 b.val b.isLt).trans (h.1 b), fun b => (h2 b.val b.isLt).trans (h.2 b)⟩

/-- Static header constants stored at `base + 0 .. 4` and `base + 6 .. 10`. -/
@[expose]
def HeaderConstsRep (base n_max U : ℕ) (mem : ℕ → ℕ) : Prop :=
  mem base = n_max ∧
  mem (base + 1) = U ∧
  mem (base + 2) = tableBits n_max ∧
  mem (base + 3) = tableSize n_max ∧
  mem (base + 4) = maxEvictions n_max ∧
  mem (base + 6) = hashBase base ∧
  mem (base + 7) = t1Base base n_max ∧
  mem (base + 8) = t2Base base n_max ∧
  mem (base + 9) = keysBase base n_max ∧
  mem (base + 10) = valsBase base n_max

theorem HeaderConstsRep.congr {base n_max U : ℕ} {mem mem' : ℕ → ℕ}
    (h : HeaderConstsRep base n_max U mem)
    (heq : ∀ k ≤ 10, k ≠ 5 → mem' (base + k) = mem (base + k)) :
    HeaderConstsRep base n_max U mem' := by
  rcases h with ⟨h0, h1, h2, h3, h4, h6, h7, h8, h9, h10⟩
  have h0' := heq 0 (by decide) (by decide)
  rw [Nat.add_zero] at h0'
  exact ⟨h0'.trans h0,
    (heq 1 (by decide) (by decide)).trans h1,
    (heq 2 (by decide) (by decide)).trans h2,
    (heq 3 (by decide) (by decide)).trans h3,
    (heq 4 (by decide) (by decide)).trans h4,
    (heq 6 (by decide) (by decide)).trans h6,
    (heq 7 (by decide) (by decide)).trans h7,
    (heq 8 (by decide) (by decide)).trans h8,
    (heq 9 (by decide) (by decide)).trans h9,
    (heq 10 (by decide) (by decide)).trans h10⟩

/-- Representation of the insertion-order arrays `insKeys` and `insVals` at `keysBase` and
`valsBase` realizing abstract dictionary state `s : Dictionary.State U`. -/
@[expose]
def KeysValsRep (base n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (mem : ℕ → ℕ) : Prop :=
  ks.Nodup ∧
  ks.length ≤ n_max ∧
  mem (base + 5) = ks.length ∧
  (∀ u : Fin U, u ∈ ks ↔ u ∈ Dictionary.dom s) ∧
  (∀ (idx : ℕ) (h : idx < ks.length),
    mem (keysBase base n_max + idx) = (ks[idx]).val ∧
    s (ks[idx]) = some (mem (valsBase base n_max + idx))) ∧
  Dictionary.ValuesBounded V s

theorem KeysValsRep.congr {base n_max U V : ℕ} {ks : List (Fin U)} {s : Dictionary.State U}
    {mem mem' : ℕ → ℕ} (h : KeysValsRep base n_max U V ks s mem)
    (h5 : mem' (base + 5) = mem (base + 5))
    (hk : ∀ idx < ks.length, mem' (keysBase base n_max + idx) = mem (keysBase base n_max + idx))
    (hv : ∀ idx < ks.length, mem' (valsBase base n_max + idx) = mem (valsBase base n_max + idx)) :
    KeysValsRep base n_max U V ks s mem' := by
  rcases h with ⟨hnodup, hlen, hm5, hdom, hkv, hvb⟩
  refine ⟨hnodup, hlen, h5.trans hm5, hdom, fun idx hidx => ?_, hvb⟩
  obtain ⟨hki, hvi⟩ := hkv idx hidx
  exact ⟨(hk idx hidx).trans hki, by rw [hv idx hidx]; exact hvi⟩

theorem KeysValsRep.card_dom_eq {base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (h : KeysValsRep base n_max U V ks s mem) :
    (Dictionary.dom s).card = ks.length := by
  rcases h with ⟨hnodup, -, -, hdom, -, -⟩
  have hto : ks.toFinset = Dictionary.dom s := by
    ext u
    rw [List.mem_toFinset]
    exact hdom u
  rw [← hto, List.card_toFinset, List.dedup_eq_self.mpr hnodup]

theorem KeysValsRep.toFinset_eq_dom {base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {mem : ℕ → ℕ} (h : KeysValsRep base n_max U V ks s mem) :
    ks.toFinset = Dictionary.dom s := by
  ext u
  rw [List.mem_toFinset]
  exact h.2.2.2.1 u

theorem KeysValsRep.unique {base n_max U V : ℕ} {ks₁ ks₂ : List (Fin U)}
    {s₁ s₂ : Dictionary.State U} {mem : ℕ → ℕ}
    (h₁ : KeysValsRep base n_max U V ks₁ s₁ mem)
    (h₂ : KeysValsRep base n_max U V ks₂ s₂ mem) :
    s₁ = s₂ := by
  funext u
  have hlen : ks₁.length = ks₂.length := h₁.2.2.1.symm.trans h₂.2.2.1
  have hks_eq : ks₁ = ks₂ := by
    apply List.ext_getElem hlen
    intro idx hlt1 hlt2
    apply Fin.ext
    rw [← (h₁.2.2.2.2.1 idx hlt1).1, ← (h₂.2.2.2.2.1 idx hlt2).1]
  subst hks_eq
  by_cases hu : u ∈ ks₁
  · obtain ⟨idx, hlt, rfl⟩ := List.mem_iff_getElem.mp hu
    rw [(h₁.2.2.2.2.1 idx hlt).2, (h₂.2.2.2.2.1 idx hlt).2]
  · have hu1 : u ∉ Dictionary.dom s₁ := fun h => hu ((h₁.2.2.2.1 u).mpr h)
    have hu2 : u ∉ Dictionary.dom s₂ := fun h => hu ((h₂.2.2.2.1 u).mpr h)
    rw [Dictionary.notMem_dom_iff] at hu1 hu2
    rw [hu1, hu2]

/-- Insertion-order-indexed representation invariant `RepWithKeys w base n_max U V ks s x` for
cuckoo hashing: stores the static header, the hash pair `θ_mem = extractSeed ... x.mem`, the
insertion-order key-value arrays `ks` for `s`, and a valid table placement `tbl` obtained by
replaying `ks` under `θ_mem`. -/
@[expose]
def RepWithKeys (w base n_max U V : ℕ) (ks : List (Fin U))
    (s : Dictionary.State U) (x : Data 19) : Prop :=
  let M := tableBits n_max
  let θ_mem := extractSeed (hashBase base) n_max U M x.mem
  x.Bounded w ∧
  x.regs 0 = base ∧
  HeaderConstsRep base n_max U x.mem ∧
  HashPairRep (hashBase base) n_max U M θ_mem x.mem ∧
  KeysValsRep base n_max U V ks s x.mem ∧
  ∃ tbl : PureTable U (2 ^ M),
    pureReplay (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) ks = some tbl ∧
    TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem

/-- Representation invariant `Rep w base n_max U V s x` for cuckoo hashing. -/
@[expose]
def Rep (w base n_max U V : ℕ) (s : Dictionary.State U) (x : Data 19) : Prop :=
  ∃ ks : List (Fin U), RepWithKeys w base n_max U V ks s x

theorem RepWithKeys.toRep {w base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {x : Data 19}
    (hrep : RepWithKeys w base n_max U V ks s x) :
    Rep w base n_max U V s x :=
  ⟨ks, hrep⟩

theorem RepWithKeys.extractSeed_mem_survivingSeeds {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x : Data 19}
    (hrep : RepWithKeys w base n_max U V ks s x) :
    extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∈
      survivingSeeds (Θ := Seed U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) ks := by
  obtain ⟨-, -, -, -, -, tbl, hreplay, -⟩ := hrep
  rw [mem_survivingSeeds, hreplay]
  rfl

theorem Rep.bounded {w base n_max U V : ℕ} {s : Dictionary.State U} {x : Data 19}
    (h : Rep w base n_max U V s x) : x.Bounded w := by
  obtain ⟨_, hbdd, _⟩ := h
  exact hbdd

theorem Rep.unique {w base n_max U V : ℕ}
    {s₁ s₂ : Dictionary.State U} {x : Data 19}
    (h₁ : Rep w base n_max U V s₁ x) (h₂ : Rep w base n_max U V s₂ x) :
    s₁ = s₂ := by
  obtain ⟨ks₁, -, -, -, -, hkv₁, -, -, -⟩ := h₁
  obtain ⟨ks₂, -, -, -, -, hkv₂, -, -, -⟩ := h₂
  exact hkv₁.unique hkv₂

theorem extractSeed_congr_of_footprint {base n_max U : ℕ} {mem mem' : ℕ → ℕ}
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem' a = mem a) :
    extractSeed (hashBase base) n_max U (tableBits n_max) mem' =
      extractSeed (hashBase base) n_max U (tableBits n_max) mem := by
  have hsp_le := le_hashPairSpace n_max (tableBits n_max)
  have hpoly : Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem' =
      Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem := by
    funext i
    have hi := i.isLt
    dsimp only [Tabulation.extractSlice]
    rw [hmem (hashBase base + 4 + i.val) (by
      simp only [Block.mem_footprint, Block.Owns, hashBase, space]; omega)]
  have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem' =
      Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem := by
    funext i
    have hi := i.isLt
    have hz1 : z1Base (hashBase base) n_max + 2 * 2 ^ tableBits n_max =
        hashBase base + hashPairSpace n_max (tableBits n_max) := by
      dsimp only [z1Base, hashPairSpace]; omega
    dsimp only [Tabulation.extractSlice]
    rw [hmem (z1Base (hashBase base) n_max + i.val) (by
      simp only [Block.mem_footprint, Block.Owns, hashBase, z1Base, space] at *
      omega)]
  dsimp only [extractSeed]
  rw [hpoly, htab]

theorem RepWithKeys.supported {w base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {x x' : Data 19}
    (hreg0 : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : RepWithKeys w base n_max U V ks s x) :
    RepWithKeys w base n_max U V ks s x' := by
  obtain ⟨_, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ := hrep
  have hθ_eq : extractSeed (hashBase base) n_max U (tableBits n_max) x'.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_footprint hmem
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hhdr' : HeaderConstsRep base n_max U x'.mem :=
    hhdr.congr fun k hk _ => hmem (base + k) (by
      simp only [Block.mem_footprint, Block.Owns]; omega)
  have hhash' : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) x'.mem) x'.mem := by
    rw [hθ_eq]
    rcases hhash with ⟨⟨hM, hz1, hz2, h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
      ⟨hpoly, htab1, htab2⟩⟩
    have hin_hp : ∀ off < hashPairSpace n_max (tableBits n_max),
        x'.mem (hashBase base + off) = x.mem (hashBase base + off) := fun off hoff =>
      hmem (hashBase base + off) (by
        simp only [Block.mem_footprint, Block.Owns, hashBase, space]; omega)
    have hsp_eq := hashPairSpace_eq n_max (tableBits n_max)
    have hz1_eq := z1Base_eq (hashBase base) n_max
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · simpa using (hin_hp 0 (by omega)).trans hM
    · exact (hin_hp 1 (by omega)).trans hz1
    · exact (hin_hp 2 (by omega)).trans hz2
    · exact (hin_hp 32 (by omega)).trans h0'
    · simpa [Nat.add_assoc] using (hin_hp 33 (by omega)).trans h1'
    · simpa [Nat.add_assoc] using (hin_hp 34 (by omega)).trans h2'
    · simpa [Nat.add_assoc] using (hin_hp 35 (by omega)).trans h3'
    · simpa [Nat.add_assoc] using (hin_hp 36 (by omega)).trans h4'
    · simpa [Nat.add_assoc] using (hin_hp 37 (by omega)).trans h5'
    · simpa [Nat.add_assoc] using (hin_hp 38 (by omega)).trans h6'
    · simpa [Nat.add_assoc] using (hin_hp 39 (by omega)).trans h7'
    · intro idx hidx
      rw [show hashBase base + 32 + 8 + 7 + idx = hashBase base + (47 + idx) by omega,
        hin_hp (47 + idx) (by omega),
        show hashBase base + (47 + idx) = hashBase base + 32 + 8 + 7 + idx by omega]
      exact hcl idx hidx
    · intro r j
      have hr := r.isLt
      have hj := j.isLt
      rw [show hashBase base + 4 + 7 * r.val + j.val =
          hashBase base + (4 + 7 * r.val + j.val) by omega,
        hin_hp (4 + 7 * r.val + j.val) (by omega),
        show hashBase base + (4 + 7 * r.val + j.val) =
          hashBase base + 4 + 7 * r.val + j.val by omega]
      exact hpoly r j
    · intro i
      have hi := i.isLt
      have haddr : z1Base (hashBase base) n_max + i.val =
          hashBase base + (47 + 2 ^ (2 * KWise.chunkBits n_max) + i.val) := by
        rw [hz1_eq]; omega
      rw [haddr, hin_hp _ (by omega), ← haddr]
      exact htab1 i
    · intro i
      have hi := i.isLt
      have haddr : z2Base (hashBase base) n_max (tableBits n_max) + i.val =
          hashBase base + (47 + 2 ^ (2 * KWise.chunkBits n_max) + 2 ^ tableBits n_max + i.val) := by
        dsimp only [z2Base]; rw [hz1_eq]; omega
      rw [haddr, hin_hp _ (by omega), ← haddr]
      exact htab2 i
  have hlen_le : ks.length ≤ n_max := hkv.2.1
  have hkv' : KeysValsRep base n_max U V ks s x'.mem :=
    hkv.congr
      (hmem (base + 5) (by simp only [Block.mem_footprint, Block.Owns]; omega))
      (fun idx hidx => hmem (keysBase base n_max + idx) (by
        simp only [Block.mem_footprint, Block.Owns, keysBase, t2Base, t1Base, hashBase, space]
        omega))
      (fun idx hidx => hmem (valsBase base n_max + idx) (by
        simp only [Block.mem_footprint, Block.Owns, valsBase, keysBase, t2Base, t1Base, hashBase,
          space]
        omega))
  have hslots' : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x'.mem :=
    hslots.congr
      (fun b hb => hmem (t1Base base n_max + b) (by
        simp only [Block.mem_footprint, Block.Owns, t1Base, hashBase, space, tableSize]
        omega))
      (fun b hb => hmem (t2Base base n_max + b) (by
        simp only [Block.mem_footprint, Block.Owns, t2Base, t1Base, hashBase, space, tableSize]
        omega))
  refine ⟨hbdd, hreg0.trans h0, hhdr', hhash', hkv', tbl, ?_, hslots'⟩
  rw [hθ_eq]
  exact hreplay

theorem Rep.supported {w base n_max U V : ℕ}
    {s : Dictionary.State U} {x x' : Data 19}
    (hreg0 : x'.regs 0 = x.regs 0)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbdd : x'.Bounded w)
    (hrep : Rep w base n_max U V s x) :
    Rep w base n_max U V s x' := by
  obtain ⟨ks, hrep_ks⟩ := hrep
  exact ⟨ks, hrep_ks.supported hreg0 hmem hbdd⟩

/-! ### Section 2: `allocSpan` and `initSetup` programs and specifications -/

/-- Subprogram 1 of `computeScaleCode`: computes `b = KWise.chunkBits n_max` in `reg 5`, `1` in
`reg 6`, and `2 ^ (2 * b)` in `reg 7`. -/
@[expose]
def computeChunkScaleCode : Code .exact 19 :=
  .seq (.op (.const 7 2))
  (.seq (ExactLog.maxCode 7 3 7)
  (.seq (.op (.const 5 0))
  (.seq (.op (.const 6 1))
  (.seq (ExactLog.log2Loop.rename ![7, 5, 6])
  (.seq (.op (.const 7 3))
  (.seq (.op (.exactBin .div 5 5 7))
  (.seq (ExactLog.maxCode 5 6 5)
  (.seq (.op (.exactBin .add 7 5 5))
        (.op (.exactBin .shiftLeft 7 6 7))))))))))

/-- Subprogram 2 of `computeScaleCode`: computes `M = tableBits n_max` in `reg 8` and
`2 ^ M = tableSize n_max` in `reg 9`. -/
@[expose]
def computeTableBitsCode : Code .exact 19 :=
  .seq (.op (.const 10 4))
  (.seq (.op (.exactBin .mul 11 10 3))
  (.seq (ExactLog.maxCode 11 11 10)
  (.seq (.op (.const 8 0))
  (.seq (ExactLog.clog2Loop.rename ![11, 8, 6])
        (.op (.exactBin .shiftLeft 9 6 8))))))

/-- Subprogram 3 of `computeScaleCode`: computes `maxEvictions n_max` in `reg 10`. -/
@[expose]
def computeMaxEvictCode : Code .exact 19 :=
  .seq (.op (.const 11 2))
  (.seq (ExactLog.maxCode 12 3 11)
  (.seq (.op (.const 10 0))
  (.seq (ExactLog.clog2Loop.rename ![12, 10, 6])
  (.seq (.op (.exactBin .add 10 10 11))
  (.seq (.op (.const 11 6))
        (.op (.exactBin .mul 10 11 10)))))))

/-- Subprogram 4 of `computeScaleCode`: computes `hashPairSpace n_max (tableBits n_max)` in
`reg 11` and `space n_max` in `reg 13`. -/
@[expose]
def computeSpaceScaleCode : Code .exact 19 :=
  .seq (.op (.const 11 47))
  (.seq (.op (.exactBin .add 11 11 7))
  (.seq (.op (.exactBin .add 12 9 9))
  (.seq (.op (.exactBin .add 11 11 12))
  (.seq (.op (.const 13 20))
  (.seq (.op (.exactBin .add 13 13 11))
  (.seq (.op (.exactBin .add 13 13 12))
  (.seq (.op (.exactBin .add 14 3 3))
        (.op (.exactBin .add 13 13 14)))))))))

/-- Subprogram computing `(b, 1, 2 ^ (2 * b), M, 2 ^ M, MaxLoop, hashPairSpace, space)` into
registers `(5, 6, 7, 8, 9, 10, 11, 13)` from `n_max` in `reg 3` while preserving `reg 0, 1, 2, 3, 4`
and all memory. -/
@[expose]
def computeScaleCode : Code .exact 19 :=
  .seq computeChunkScaleCode
  (.seq computeTableBitsCode
  (.seq computeMaxEvictCode
        computeSpaceScaleCode))

/-- Exact step bound for `computeScaleCode`. -/
@[expose]
def computeScaleSteps (n_max : ℕ) : ℕ :=
  4 * Nat.log 2 (max n_max 2) + 5 * tableBits n_max + 5 * Nat.clog 2 (max n_max 2) + 46

private theorem set_regs_of_lt {r : ℕ} (x : Data r) (d : Fin r) (v : ℕ) (i : Fin r)
    (hi : i.val < d.val) : (x.set d v).regs i = x.regs i :=
  Function.update_of_ne (fun h => by subst h; omega) _ _

private theorem extend_regs_of_ne (f : Fin 3 → Fin 19) (r : Fin 19)
    (hf : ∀ j : Fin 3, f j ≠ r) (y : Data 3) (x : Data 19) :
    (y.extend f x).regs r = x.regs r := by
  refine Data.extend_regs_of_notMem y x ?_
  rintro ⟨j, hj⟩
  exact hf j hj

private theorem extend_regs_of_le_four (f : Fin 3 → Fin 19)
    (hf : ∀ j : Fin 3, 4 < (f j).val) (y : Data 3) (x : Data 19)
    (r : Fin 19) (hr : r.val ≤ 4) : (y.extend f x).regs r = x.regs r := by
  refine Data.extend_regs_of_notMem y x ?_
  rintro ⟨j, rfl⟩
  have hj := hf j
  omega

theorem computeChunkScaleCode_exec {w n_max : ℕ} {x : Data 19}
    (h3 : x.regs 3 = n_max)
    (hfit_max2 : Fits w (max n_max 2))
    (hfit_3 : Fits w 3)
    (hfit_2b : Fits w (2 * KWise.chunkBits n_max))
    (hfit_pow2b : Fits w (2 ^ (2 * KWise.chunkBits n_max))) :
    ∃ y : Data 19,
      Exec w computeChunkScaleCode x y (4 * Nat.log 2 (max n_max 2) + 15) ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 4 → y.regs r = x.regs r) ∧
      y.regs 5 = KWise.chunkBits n_max ∧
      y.regs 6 = 1 ∧
      y.regs 7 = 2 ^ (2 * KWise.chunkBits n_max) := by
  have hfit_2 : Fits w 2 := hfit_3.of_le (by decide)
  have hfit_1 : Fits w 1 := hfit_3.of_le (by decide)
  have hfit_0 : Fits w 0 := hfit_3.of_le (by decide)
  have hlog_le : Nat.log 2 (max n_max 2) ≤ max n_max 2 := Nat.log_le_self 2 _
  have hfit_log : Fits w (0 + Nat.log 2 (max n_max 2)) := hfit_max2.of_le (by omega)
  have hfit_div : Fits w (Nat.log 2 (max n_max 2) / 3) := hfit_max2.of_le (by omega)
  set s1 := x.set 7 2
  have e1 : Exec w (.op (.const 7 2) : Code .exact 19) x s1 1 := Exec.const hfit_2
  set s2 := s1.set 7 (max n_max 2)
  have e2 : Exec w (ExactLog.maxCode 7 3 7) s1 s2 3 := by
    simpa +decide [s2, s1, h3] using ExactLog.maxCode_exec (w := w) 7 3 7 s1
  set s3 := s2.set 5 0
  have e3 : Exec w (.op (.const 5 0) : Code .exact 19) s2 s3 1 := Exec.const hfit_0
  set s4 := s3.set 6 1
  have e4 : Exec w (.op (.const 6 1) : Code .exact 19) s3 s4 1 := Exec.const hfit_1
  set f1 : Fin 3 → Fin 19 := ![7, 5, 6]
  have hf1_inj : Function.Injective f1 := by decide
  have hlog_inner := ExactLog.log2Loop_exec (w := w) (max n_max 2) (acc := 0)
    (x := s4.comap f1)
    (by simp +decide [s4, s3, s2, f1, Data.comap])
    (by simp +decide [s4, s3, f1, Data.comap])
    (by simp +decide [s4, f1, Data.comap])
    hfit_max2 hfit_log
  have e5 := hlog_inner.rename hf1_inj
  set s5 := (ExactLog.log2LoopData (max n_max 2) 0 (s4.comap f1)).extend f1 s4
  have hs5_5 : s5.regs 5 = Nat.log 2 (max n_max 2) := by
    change (s5.comap f1).regs 1 = Nat.log 2 (max n_max 2)
    rw [Data.comap_extend hf1_inj]
    simp +decide [ExactLog.log2LoopData, s4, s3, s2, s1, f1, Data.comap]
  have hs5_6 : s5.regs 6 = 1 := by
    change (s5.comap f1).regs 2 = 1
    rw [Data.comap_extend hf1_inj]
    simp +decide [ExactLog.log2LoopData, s4, s3, s2, s1, f1, Data.comap]
  have hs5_low : ∀ r : Fin 19, r.val ≤ 4 → s5.regs r = x.regs r := by
    intro r hr
    rw [extend_regs_of_le_four f1 (by decide) _ _ r hr,
      set_regs_of_lt _ 6 _ r (by change r.val < 6; omega),
      set_regs_of_lt _ 5 _ r (by change r.val < 5; omega),
      set_regs_of_lt _ 7 _ r (by change r.val < 7; omega),
      set_regs_of_lt _ 7 _ r (by change r.val < 7; omega)]
  set s6 := s5.set 7 3
  have e6 : Exec w (.op (.const 7 3) : Code .exact 19) s5 s6 1 := Exec.const hfit_3
  set s7 := s6.set 5 (Nat.log 2 (max n_max 2) / 3)
  have e7 : Exec w (.op (.exactBin .div 5 5 7) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, hs5_5]) hfit_div
  set s8 := s7.set 5 (KWise.chunkBits n_max)
  have e8 : Exec w (ExactLog.maxCode 5 6 5) s7 s8 3 := by
    simpa +decide [s8, s7, s6, hs5_6, KWise.chunkBits] using
      ExactLog.maxCode_exec (w := w) 5 6 5 s7
  set s9 := s8.set 7 (2 * KWise.chunkBits n_max)
  have e9 : Exec w (.op (.exactBin .add 7 5 5) : Code .exact 19) s8 s9 1 :=
    ExactLog.exec_exactBin (by simp +decide [s8, Nat.two_mul]) hfit_2b
  set s10 := s9.set 7 (2 ^ (2 * KWise.chunkBits n_max))
  have e10 : Exec w (.op (.exactBin .shiftLeft 7 6 7) : Code .exact 19) s9 s10 1 :=
    ExactLog.exec_exactBin (by simp +decide [s9, s8, s7, s6, hs5_6, Nat.shiftLeft_eq]) hfit_pow2b
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq e10))))))))
  refine ⟨s10, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [computeChunkScaleCode, f1,
      show 1 + (3 + (1 + (1 + (4 * Nat.log 2 (max n_max 2) + 2 + (1 + (1 + (3 + (1 + 1)))))))) =
        4 * Nat.log 2 (max n_max 2) + 15 by omega] using hall
  · intro r hr
    rw [set_regs_of_lt _ 7 _ r (by change r.val < 7; omega),
      set_regs_of_lt _ 7 _ r (by change r.val < 7; omega),
      set_regs_of_lt _ 5 _ r (by change r.val < 5; omega),
      set_regs_of_lt _ 5 _ r (by change r.val < 5; omega),
      set_regs_of_lt _ 7 _ r (by change r.val < 7; omega),
      hs5_low r hr]
  · simp +decide [s10, s9, s8]
  · simp +decide [s10, s9, s8, s7, s6, hs5_6]
  · simp +decide [s10]

theorem computeTableBitsCode_exec {w n_max : ℕ} {x : Data 19}
    (h3 : x.regs 3 = n_max)
    (h6 : x.regs 6 = 1)
    (hfit_4 : Fits w 4)
    (hfit_max4n1 : Fits w (max (4 * n_max) 4 + 1))
    (hfit_M : Fits w (0 + tableBits n_max))
    (hfit_powM : Fits w (tableSize n_max)) :
    ∃ y : Data 19,
      Exec w computeTableBitsCode x y (5 * tableBits n_max + 9) ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 4 → y.regs r = x.regs r) ∧
      y.regs 5 = x.regs 5 ∧
      y.regs 6 = 1 ∧
      y.regs 7 = x.regs 7 ∧
      y.regs 8 = tableBits n_max ∧
      y.regs 9 = tableSize n_max := by
  have hfit_0 : Fits w 0 := hfit_4.of_le (by decide)
  have hfit_4n : Fits w (4 * n_max) := hfit_max4n1.of_le (by omega)
  set s1 := x.set 10 4
  have e1 : Exec w (.op (.const 10 4) : Code .exact 19) x s1 1 := Exec.const hfit_4
  set s2 := s1.set 11 (4 * n_max)
  have e2 : Exec w (.op (.exactBin .mul 11 10 3) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h3]) hfit_4n
  set s3 := s2.set 11 (max (4 * n_max) 4)
  have e3 : Exec w (ExactLog.maxCode 11 11 10) s2 s3 3 := by
    simpa +decide [s3, s2, s1] using ExactLog.maxCode_exec (w := w) 11 11 10 s2
  set s4 := s3.set 8 0
  have e4 : Exec w (.op (.const 8 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  set f2 : Fin 3 → Fin 19 := ![11, 8, 6]
  have hf2_inj : Function.Injective f2 := by decide
  have hclog_inner := ExactLog.clog2Loop_exec (w := w) (max (4 * n_max) 4) (acc := 0)
    (x := s4.comap f2)
    (by simp +decide [s4, s3, f2, Data.comap])
    (by simp +decide [s4, f2, Data.comap])
    (by simp +decide [s4, s3, s2, s1, h6, f2, Data.comap])
    hfit_max4n1 hfit_M
  have e5 := hclog_inner.rename hf2_inj
  set s5 := (ExactLog.clog2LoopData (max (4 * n_max) 4) 0 (s4.comap f2)).extend f2 s4
  have hs5_8 : s5.regs 8 = tableBits n_max := by
    change (s5.comap f2).regs 1 = tableBits n_max
    rw [Data.comap_extend hf2_inj]
    simp +decide [ExactLog.clog2LoopData, s4, f2, Data.comap, tableBits]
  have hs5_6 : s5.regs 6 = 1 := by
    change (s5.comap f2).regs 2 = 1
    rw [Data.comap_extend hf2_inj]
    simp +decide [ExactLog.clog2LoopData, s4, s3, s2, s1, h6, f2, Data.comap]
  have hs5_5 : s5.regs 5 = x.regs 5 := by
    rw [extend_regs_of_ne f2 5 (by decide)]
    simp +decide [s4, s3, s2, s1]
  have hs5_7 : s5.regs 7 = x.regs 7 := by
    rw [extend_regs_of_ne f2 7 (by decide)]
    simp +decide [s4, s3, s2, s1]
  set s6 := s5.set 9 (tableSize n_max)
  have e6 : Exec w (.op (.exactBin .shiftLeft 9 6 8) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [hs5_6, hs5_8, tableSize, Nat.shiftLeft_eq]) hfit_powM
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))
  refine ⟨s6, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [computeTableBitsCode, f2, tableBits,
      show 1 + (1 + (3 + (1 + (5 * Nat.clog 2 (max (4 * n_max) 4) + 2 + 1)))) =
        5 * Nat.clog 2 (max (4 * n_max) 4) + 9 by omega] using hall
  · intro r hr
    rw [set_regs_of_lt _ 9 _ r (by change r.val < 9; omega),
      extend_regs_of_le_four f2 (by decide) _ _ r hr,
      set_regs_of_lt _ 8 _ r (by change r.val < 8; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega),
      set_regs_of_lt _ 10 _ r (by change r.val < 10; omega)]
  · simp +decide [s6, hs5_5]
  · simp +decide [s6, hs5_6]
  · simp +decide [s6, hs5_7]
  · simp +decide [s6, hs5_8]
  · simp +decide [s6]

theorem computeMaxEvictCode_exec {w n_max : ℕ} {x : Data 19}
    (h3 : x.regs 3 = n_max)
    (h6 : x.regs 6 = 1)
    (hfit_6 : Fits w 6)
    (hfit_max2_1 : Fits w (max n_max 2 + 1))
    (hfit_ev : Fits w (maxEvictions n_max)) :
    ∃ y : Data 19,
      Exec w computeMaxEvictCode x y (5 * Nat.clog 2 (max n_max 2) + 10) ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 4 → y.regs r = x.regs r) ∧
      y.regs 5 = x.regs 5 ∧
      y.regs 6 = 1 ∧
      y.regs 7 = x.regs 7 ∧
      y.regs 8 = x.regs 8 ∧
      y.regs 9 = x.regs 9 ∧
      y.regs 10 = maxEvictions n_max := by
  have hfit_2 : Fits w 2 := hfit_6.of_le (by decide)
  have hfit_0 : Fits w 0 := hfit_6.of_le (by decide)
  have hfit_clog2 : Fits w (0 + Nat.clog 2 (max n_max 2)) :=
    hfit_ev.of_le (by dsimp only [maxEvictions]; omega)
  have hfit_clog2_add : Fits w (Nat.clog 2 (max n_max 2) + 2) :=
    hfit_ev.of_le (by dsimp only [maxEvictions]; omega)
  set s1 := x.set 11 2
  have e1 : Exec w (.op (.const 11 2) : Code .exact 19) x s1 1 := Exec.const hfit_2
  set s2 := s1.set 12 (max n_max 2)
  have e2 : Exec w (ExactLog.maxCode 12 3 11) s1 s2 3 := by
    simpa +decide [s2, s1, h3] using ExactLog.maxCode_exec (w := w) 12 3 11 s1
  set s3 := s2.set 10 0
  have e3 : Exec w (.op (.const 10 0) : Code .exact 19) s2 s3 1 := Exec.const hfit_0
  set f3 : Fin 3 → Fin 19 := ![12, 10, 6]
  have hf3_inj : Function.Injective f3 := by decide
  have hclog_inner := ExactLog.clog2Loop_exec (w := w) (max n_max 2) (acc := 0)
    (x := s3.comap f3)
    (by simp +decide [s3, s2, f3, Data.comap])
    (by simp +decide [s3, f3, Data.comap])
    (by simp +decide [s3, s2, s1, h6, f3, Data.comap])
    hfit_max2_1 hfit_clog2
  have e4 := hclog_inner.rename hf3_inj
  set s4 := (ExactLog.clog2LoopData (max n_max 2) 0 (s3.comap f3)).extend f3 s3
  have hs4_10 : s4.regs 10 = Nat.clog 2 (max n_max 2) := by
    change (s4.comap f3).regs 1 = Nat.clog 2 (max n_max 2)
    rw [Data.comap_extend hf3_inj]
    simp +decide [ExactLog.clog2LoopData, s3, f3, Data.comap]
  have hs4_6 : s4.regs 6 = 1 := by
    change (s4.comap f3).regs 2 = 1
    rw [Data.comap_extend hf3_inj]
    simp +decide [ExactLog.clog2LoopData, s3, s2, s1, h6, f3, Data.comap]
  have hs4_5 : s4.regs 5 = x.regs 5 := by
    rw [extend_regs_of_ne f3 5 (by decide)]; simp +decide [s3, s2, s1]
  have hs4_7 : s4.regs 7 = x.regs 7 := by
    rw [extend_regs_of_ne f3 7 (by decide)]; simp +decide [s3, s2, s1]
  have hs4_8 : s4.regs 8 = x.regs 8 := by
    rw [extend_regs_of_ne f3 8 (by decide)]; simp +decide [s3, s2, s1]
  have hs4_9 : s4.regs 9 = x.regs 9 := by
    rw [extend_regs_of_ne f3 9 (by decide)]; simp +decide [s3, s2, s1]
  have hs4_11 : s4.regs 11 = 2 := by
    rw [extend_regs_of_ne f3 11 (by decide)]; simp +decide [s3, s2, s1]
  set s5 := s4.set 10 (Nat.clog 2 (max n_max 2) + 2)
  have e5 : Exec w (.op (.exactBin .add 10 10 11) : Code .exact 19) s4 s5 1 :=
    ExactLog.exec_exactBin (by simp +decide [hs4_10, hs4_11]) hfit_clog2_add
  set s6 := s5.set 11 6
  have e6 : Exec w (.op (.const 11 6) : Code .exact 19) s5 s6 1 := Exec.const hfit_6
  set s7 := s6.set 10 (maxEvictions n_max)
  have e7 : Exec w (.op (.exactBin .mul 10 11 10) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, s5, maxEvictions]) hfit_ev
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))
  refine ⟨s7, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [computeMaxEvictCode, f3,
      show 1 + (3 + (1 + (5 * Nat.clog 2 (max n_max 2) + 2 + (1 + (1 + 1))))) =
        5 * Nat.clog 2 (max n_max 2) + 10 by omega] using hall
  · intro r hr
    rw [set_regs_of_lt _ 10 _ r (by change r.val < 10; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega),
      set_regs_of_lt _ 10 _ r (by change r.val < 10; omega),
      extend_regs_of_le_four f3 (by decide) _ _ r hr,
      set_regs_of_lt _ 10 _ r (by change r.val < 10; omega),
      set_regs_of_lt _ 12 _ r (by change r.val < 12; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega)]
  · simp +decide [s7, s6, s5, hs4_5]
  · simp +decide [s7, s6, s5, hs4_6]
  · simp +decide [s7, s6, s5, hs4_7]
  · simp +decide [s7, s6, s5, hs4_8]
  · simp +decide [s7, s6, s5, hs4_9]
  · simp +decide [s7]

theorem computeSpaceScaleCode_exec {w n_max : ℕ} {x : Data 19}
    (h3 : x.regs 3 = n_max)
    (h7 : x.regs 7 = 2 ^ (2 * KWise.chunkBits n_max))
    (h9 : x.regs 9 = tableSize n_max)
    (hfit_sp : Fits w (space n_max)) :
    ∃ y : Data 19,
      Exec w computeSpaceScaleCode x y 9 ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 10 → y.regs r = x.regs r) ∧
      y.regs 11 = hashPairSpace n_max (tableBits n_max) ∧
      y.regs 13 = space n_max := by
  have hle_sp := le_space n_max
  have hpow2b_pos : 0 < 2 ^ (2 * KWise.chunkBits n_max) := Nat.two_pow_pos _
  have h4_sp : 4 * tableSize n_max + 2 * n_max + 20 ≤ space n_max := by
    rw [space, hashPairSpace_eq]; dsimp only [tableSize]; omega
  have hpow2b_sp : 47 + 2 ^ (2 * KWise.chunkBits n_max) ≤ space n_max := by
    rw [space, hashPairSpace_eq]; omega
  have hfit_20 : Fits w 20 := hfit_sp.of_le (by omega)
  have hfit_47 : Fits w 47 := hfit_sp.of_le (by omega)
  have hfit_47_pow2b : Fits w (47 + 2 ^ (2 * KWise.chunkBits n_max)) := hfit_sp.of_le (by omega)
  have hfit_2powM : Fits w (2 * tableSize n_max) := hfit_sp.of_le (by omega)
  have hfit_hp : Fits w (hashPairSpace n_max (tableBits n_max)) :=
    hfit_sp.of_le (by dsimp only [space]; omega)
  have hfit_20_hp : Fits w (20 + hashPairSpace n_max (tableBits n_max)) :=
    hfit_sp.of_le (by dsimp only [space]; omega)
  have hfit_20_hp_2m : Fits w (20 + hashPairSpace n_max (tableBits n_max) + 2 * tableSize n_max) :=
    hfit_sp.of_le (by dsimp only [space]; omega)
  have hfit_2n : Fits w (2 * n_max) := hfit_sp.of_le (by omega)
  set s1 := x.set 11 47
  have e1 : Exec w (.op (.const 11 47) : Code .exact 19) x s1 1 := Exec.const hfit_47
  set s2 := s1.set 11 (47 + 2 ^ (2 * KWise.chunkBits n_max))
  have e2 : Exec w (.op (.exactBin .add 11 11 7) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h7]) hfit_47_pow2b
  set s3 := s2.set 12 (2 * tableSize n_max)
  have e3 : Exec w (.op (.exactBin .add 12 9 9) : Code .exact 19) s2 s3 1 :=
    ExactLog.exec_exactBin (by simp +decide [s2, s1, h9, Nat.two_mul]) hfit_2powM
  set s4 := s3.set 11 (hashPairSpace n_max (tableBits n_max))
  have e4 : Exec w (.op (.exactBin .add 11 11 12) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, s2, hashPairSpace_eq, tableSize]) hfit_hp
  set s5 := s4.set 13 20
  have e5 : Exec w (.op (.const 13 20) : Code .exact 19) s4 s5 1 := Exec.const hfit_20
  set s6 := s5.set 13 (20 + hashPairSpace n_max (tableBits n_max))
  have e6 : Exec w (.op (.exactBin .add 13 13 11) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin (by simp +decide [s5, s4]) hfit_20_hp
  set s7 := s6.set 13 (20 + hashPairSpace n_max (tableBits n_max) + 2 * tableSize n_max)
  have e7 : Exec w (.op (.exactBin .add 13 13 12) : Code .exact 19) s6 s7 1 :=
    ExactLog.exec_exactBin (by simp +decide [s6, s5, s4, s3]) hfit_20_hp_2m
  set s8 := s7.set 14 (2 * n_max)
  have e8 : Exec w (.op (.exactBin .add 14 3 3) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h3, Nat.two_mul]) hfit_2n
  set s9 := s8.set 13 (space n_max)
  have e9 : Exec w (.op (.exactBin .add 13 13 14) : Code .exact 19) s8 s9 1 :=
    ExactLog.exec_exactBin (by simp +decide [s8, s7, space]) hfit_sp
  have hall : Exec w computeSpaceScaleCode x s9 (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 1)))))))) :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
  refine ⟨s9, hall, rfl, ?_, ?_, ?_⟩
  · intro r hr
    rw [set_regs_of_lt _ 13 _ r (by change r.val < 13; omega),
      set_regs_of_lt _ 14 _ r (by change r.val < 14; omega),
      set_regs_of_lt _ 13 _ r (by change r.val < 13; omega),
      set_regs_of_lt _ 13 _ r (by change r.val < 13; omega),
      set_regs_of_lt _ 13 _ r (by change r.val < 13; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega),
      set_regs_of_lt _ 12 _ r (by change r.val < 12; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega),
      set_regs_of_lt _ 11 _ r (by change r.val < 11; omega)]
  · simp +decide [s9, s8, s7, s6, s5, s4]
  · simp +decide [s9]

theorem computeScaleCode_execWithin {w n_max : ℕ} {x : Data 19}
    (h3 : x.regs 3 = n_max)
    (hfit_sp : Fits w (space n_max))
    (hfit_ev : Fits w (maxEvictions n_max)) :
    ∃ y : Data 19,
      ExecWithin w computeScaleCode x y (computeScaleSteps n_max) ∧
      y.mem = x.mem ∧
      (∀ r : Fin 19, r.val ≤ 4 → y.regs r = x.regs r) ∧
      y.regs 5 = KWise.chunkBits n_max ∧
      y.regs 6 = 1 ∧
      y.regs 7 = 2 ^ (2 * KWise.chunkBits n_max) ∧
      y.regs 8 = tableBits n_max ∧
      y.regs 9 = tableSize n_max ∧
      y.regs 10 = maxEvictions n_max ∧
      y.regs 11 = hashPairSpace n_max (tableBits n_max) ∧
      y.regs 13 = space n_max := by
  have hle_sp := le_space n_max
  have hpow2b_pos : 0 < 2 ^ (2 * KWise.chunkBits n_max) := Nat.two_pow_pos _
  have h4_sp : 4 * tableSize n_max + 2 * n_max + 20 ≤ space n_max := by
    rw [space, hashPairSpace_eq]; dsimp only [tableSize]; omega
  have hpow2b_sp : 47 + 2 ^ (2 * KWise.chunkBits n_max) ≤ space n_max := by
    rw [space, hashPairSpace_eq]; omega
  have h4le := four_mul_max_le_tableSize n_max
  have hmax2_le : max n_max 2 ≤ tableSize n_max := le_trans (by omega) h4le
  have h2b_lt : 2 * KWise.chunkBits n_max < 2 ^ (2 * KWise.chunkBits n_max) := Nat.lt_two_pow_self
  have hM_lt : tableBits n_max < 2 ^ tableBits n_max := Nat.lt_two_pow_self
  have hM_le : tableBits n_max ≤ tableSize n_max := le_of_lt hM_lt
  have hfit_3 : Fits w 3 := hfit_sp.of_le (by omega)
  have hfit_4 : Fits w 4 := hfit_sp.of_le (by omega)
  have hfit_6 : Fits w 6 := hfit_sp.of_le (by omega)
  have hfit_max2 : Fits w (max n_max 2) := hfit_sp.of_le (by omega)
  have hfit_max2_1 : Fits w (max n_max 2 + 1) := hfit_sp.of_le (by omega)
  have hfit_2b : Fits w (2 * KWise.chunkBits n_max) := hfit_sp.of_le (by omega)
  have hfit_pow2b : Fits w (2 ^ (2 * KWise.chunkBits n_max)) := hfit_sp.of_le (by omega)
  have hfit_max4n1 : Fits w (max (4 * n_max) 4 + 1) := hfit_sp.of_le (by omega)
  have hfit_M : Fits w (0 + tableBits n_max) := hfit_sp.of_le (by omega)
  have hfit_powM : Fits w (tableSize n_max) := hfit_sp.of_le (by omega)
  obtain ⟨y1, he1, hm1, hlow1, hy1_5, hy1_6, hy1_7⟩ :=
    computeChunkScaleCode_exec h3 hfit_max2 hfit_3 hfit_2b hfit_pow2b
  obtain ⟨y2, he2, hm2, hlow2, hy2_5, hy2_6, hy2_7, hy2_8, hy2_9⟩ :=
    computeTableBitsCode_exec (x := y1) (by rw [hlow1 3 (by decide), h3]) hy1_6
      hfit_4 hfit_max4n1 hfit_M hfit_powM
  obtain ⟨y3, he3, hm3, hlow3, hy3_5, hy3_6, hy3_7, hy3_8, hy3_9, hy3_10⟩ :=
    computeMaxEvictCode_exec (x := y2) (by rw [hlow2 3 (by decide), hlow1 3 (by decide), h3]) hy2_6
      hfit_6 hfit_max2_1 hfit_ev
  obtain ⟨y4, he4, hm4, hlow4, hy4_11, hy4_13⟩ :=
    computeSpaceScaleCode_exec (x := y3)
      (by rw [hlow3 3 (by decide), hlow2 3 (by decide), hlow1 3 (by decide), h3])
      (by rw [hy3_7, hy2_7, hy1_7])
      (by rw [hy3_9, hy2_9])
      hfit_sp
  refine ⟨y4, ⟨_, by dsimp only [computeScaleSteps]; omega, he1.seq (he2.seq (he3.seq he4))⟩,
    hm4.trans (hm3.trans (hm2.trans hm1)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hy4_11, hy4_13⟩
  · intro r hr
    rw [hlow4 r (by omega), hlow3 r hr, hlow2 r hr, hlow1 r hr]
  · rw [hlow4 5 (by decide), hy3_5, hy2_5, hy1_5]
  · rw [hlow4 6 (by decide), hy3_6]
  · rw [hlow4 7 (by decide), hy3_7, hy2_7, hy1_7]
  · rw [hlow4 8 (by decide), hy3_8, hy2_8]
  · rw [hlow4 9 (by decide), hy3_9, hy2_9]
  · rw [hlow4 10 (by decide), hy3_10]

/-- `allocSpan` program: sets `reg 0 = base` and advances `reg 1` (`frontierReg`) to
`base + space n_max`. -/
@[expose]
def allocSpan : Code .exact 19 :=
  .seq (.op (.copy 0 1))
  (.seq computeScaleCode
        (.op (.exactBin .add 1 0 13)))

/-- Exact step bound for `allocSpan`. -/
@[expose]
def spanSteps (n_max : ℕ) : ℕ :=
  computeScaleSteps n_max + 2

theorem allocSpan_execWithin {w base n_max U : ℕ} {x : Data 19}
    (hfr : x.regs 1 = base) (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max)) :
    ∃ x₁ : Data 19,
      ExecWithin w allocSpan x x₁ (spanSteps n_max) ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 1 = base + space n_max ∧
      x₁.regs 3 = n_max ∧
      x₁.regs 4 = U := by
  have hfit_sp : Fits w (space n_max) := hfit_end.of_le (Nat.le_add_left _ _)
  set d1 := x.set 0 base
  have e1 : Exec w (.op (.copy 0 1) : Code .exact 19) x d1 1 := by
    simpa +decide [d1, hfr] using (Exec.copy (B := .exact) (w := w) (d := 0) (s := 1) (x := x))
  obtain ⟨d2, ⟨t_sc, ht_sc, he_sc⟩, hd2_mem, hd2_low, -, -, -, -, -, -, -, hd2_13⟩ :=
    computeScaleCode_execWithin (w := w) (n_max := n_max) (x := d1)
      (by simp +decide [d1, h3]) hfit_sp hfit_ev
  have hd2_0 : d2.regs 0 = base := by
    rw [hd2_low 0 (by decide)]; simp [d1]
  have hd2_3 : d2.regs 3 = n_max := by
    rw [hd2_low 3 (by decide)]; simp [d1, h3]
  have hd2_4 : d2.regs 4 = U := by
    rw [hd2_low 4 (by decide)]; simp [d1, h4]
  set d3 := d2.set 1 (base + space n_max)
  have e3 : Exec w (.op (.exactBin .add 1 0 13) : Code .exact 19) d2 d3 1 :=
    ExactLog.exec_exactBin (by simp +decide [hd2_0, hd2_13]) hfit_end
  refine ⟨d3, ⟨1 + (t_sc + 1), by dsimp only [spanSteps]; omega, e1.seq (he_sc.seq e3)⟩,
    hd2_mem, by simp +decide [d3, hd2_0], by simp +decide [d3],
    by simp +decide [d3, hd2_3], by simp +decide [d3, hd2_4]⟩

/-- Subprogram storing the static header constants `base + 0 .. 10`, saving `reg 1` (`frontierReg`)
at `base + 19`, and setting `(reg 0, reg 1, reg 2, reg 3) = (hashBase base, n_max, U, M)`. -/
@[expose]
def writeHeaderAndAdvanceCode : Code .exact 19 :=
  .seq (.op (.store 0 3))
  (.seq (.op (.exactBin .add 12 0 6))
  (.seq (.op (.store 12 4))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 8))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 9))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.store 12 10))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.const 14 0))
  (.seq (.op (.store 12 14))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.const 15 20))
  (.seq (.op (.exactBin .add 16 0 15))
  (.seq (.op (.store 12 16))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 16 11))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 9))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 9))
  (.seq (.op (.store 12 17))
  (.seq (.op (.exactBin .add 12 12 6))
  (.seq (.op (.exactBin .add 17 17 3))
  (.seq (.op (.store 12 17))
  (.seq (.op (.const 15 19))
  (.seq (.op (.exactBin .add 12 0 15))
  (.seq (.op (.store 12 1))
  (.seq (.op (.copy 0 16))
  (.seq (.op (.copy 1 3))
  (.seq (.op (.copy 2 4))
        (.op (.copy 3 8)))))))))))))))))))))))))))))))))))

theorem writeHeaderAndAdvanceCode_exec {w base n_max U : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base) (h1 : x.regs 1 = base + space n_max)
    (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (h6 : x.regs 6 = 1) (h8 : x.regs 8 = tableBits n_max)
    (h9 : x.regs 9 = tableSize n_max) (h10 : x.regs 10 = maxEvictions n_max)
    (h11 : x.regs 11 = hashPairSpace n_max (tableBits n_max))
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w writeHeaderAndAdvanceCode x y 35 ∧
      y.regs 0 = hashBase base ∧
      y.regs 1 = n_max ∧
      y.regs 2 = U ∧
      y.regs 3 = tableBits n_max ∧
      HeaderConstsRep base n_max U y.mem ∧
      y.mem (base + 5) = 0 ∧
      y.mem (base + 19) = base + space n_max ∧
      (∀ a, (a < base ∨ base + 20 ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hvals := valsBase_add_eq base n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (by omega)
  have hfit_19 : Fits w 19 := hfit_end.of_le (by omega)
  have hfit_20 : Fits w 20 := hfit_end.of_le (by omega)
  have hfit_b : ∀ k ≤ 20, Fits w (base + k) := fun k hk => hfit_end.of_le (by omega)
  have hfit_t1 : Fits w (t1Base base n_max) :=
    hfit_end.of_le (by dsimp only [t1Base, hashBase, space]; omega)
  have hfit_t2 : Fits w (t2Base base n_max) :=
    hfit_end.of_le (by dsimp only [t2Base, t1Base, hashBase, space]; omega)
  have hfit_keys : Fits w (keysBase base n_max) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have hfit_vals : Fits w (valsBase base n_max) :=
    hfit_end.of_le (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]; omega)
  set s1 := x.write base n_max
  have e1 : Exec w (.op (.store 0 3) : Code .exact 19) x s1 1 := by
    simpa +decide [s1, h0, h3] using (Exec.store (B := .exact) (w := w) (a := 0) (s := 3) (x := x))
  set s2 := s1.set 12 (base + 1)
  have e2 : Exec w (.op (.exactBin .add 12 0 6) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0, h6]) (hfit_b 1 (by decide))
  set s3 := s2.write (base + 1) U
  have e3 : Exec w (.op (.store 12 4) : Code .exact 19) s2 s3 1 := by
    simpa +decide [s3, s2, s1, h4] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 4) (x := s2))
  set s4 := s3.set 12 (base + 2)
  have e4 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s3, s2, s1, h6, Nat.add_assoc]) (hfit_b 2 (by decide))
  set s5 := s4.write (base + 2) (tableBits n_max)
  have e5 : Exec w (.op (.store 12 8) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, h8] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 8) (x := s4))
  set s6 := s5.set 12 (base + 3)
  have e6 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s5 s6 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s5, s4, s3, s2, s1, h6, Nat.add_assoc]) (hfit_b 3 (by decide))
  set s7 := s6.write (base + 3) (tableSize n_max)
  have e7 : Exec w (.op (.store 12 9) : Code .exact 19) s6 s7 1 := by
    simpa +decide [s7, s6, s5, s4, s3, s2, s1, h9] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 9) (x := s6))
  set s8 := s7.set 12 (base + 4)
  have e8 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc]) (hfit_b 4 (by decide))
  set s9 := s8.write (base + 4) (maxEvictions n_max)
  have e9 : Exec w (.op (.store 12 10) : Code .exact 19) s8 s9 1 := by
    simpa +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h10] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 10) (x := s8))
  set s10 := s9.set 12 (base + 5)
  have e10 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s9 s10 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc])
      (hfit_b 5 (by decide))
  set s11 := s10.set 14 0
  have e11 : Exec w (.op (.const 14 0) : Code .exact 19) s10 s11 1 := Exec.const hfit_0
  set s12 := s11.write (base + 5) 0
  have e12 : Exec w (.op (.store 12 14) : Code .exact 19) s11 s12 1 := by
    simpa +decide [s12, s11, s10] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 14) (x := s11))
  set s13 := s12.set 12 (base + 6)
  have e13 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s12 s13 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc])
      (hfit_b 6 (by decide))
  set s14 := s13.set 15 20
  have e14 : Exec w (.op (.const 15 20) : Code .exact 19) s13 s14 1 := Exec.const hfit_20
  set s15 := s14.set 16 (hashBase base)
  have e15 : Exec w (.op (.exactBin .add 16 0 15) : Code .exact 19) s14 s15 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0, hashBase])
      (hfit_b 20 (by decide))
  set s16 := s15.write (base + 6) (hashBase base)
  have e16 : Exec w (.op (.store 12 16) : Code .exact 19) s15 s16 1 := by
    simpa +decide [s16, s15, s14, s13] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 16) (x := s15))
  set s17 := s16.set 12 (base + 7)
  have e17 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s16 s17 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6,
        Nat.add_assoc])
      (hfit_b 7 (by decide))
  set s18 := s17.set 17 (t1Base base n_max)
  have e18 : Exec w (.op (.exactBin .add 17 16 11) : Code .exact 19) s17 s18 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        h11, t1Base])
      hfit_t1
  set s19 := s18.write (base + 7) (t1Base base n_max)
  have e19 : Exec w (.op (.store 12 17) : Code .exact 19) s18 s19 1 := by
    simpa +decide [s19, s18, s17] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 17) (x := s18))
  set s20 := s19.set 12 (base + 8)
  have e20 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s19 s20 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
        s3, s2, s1, h6, Nat.add_assoc])
      (hfit_b 8 (by decide))
  set s21 := s20.set 17 (t2Base base n_max)
  have e21 : Exec w (.op (.exactBin .add 17 17 9) : Code .exact 19) s20 s21 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5,
        s4, s3, s2, s1, h9, t2Base])
      hfit_t2
  set s22 := s21.write (base + 8) (t2Base base n_max)
  have e22 : Exec w (.op (.store 12 17) : Code .exact 19) s21 s22 1 := by
    simpa +decide [s22, s21, s20] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 17) (x := s21))
  set s23 := s22.set 12 (base + 9)
  have e23 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s22 s23 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8,
        s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc])
      (hfit_b 9 (by decide))
  set s24 := s23.set 17 (keysBase base n_max)
  have e24 : Exec w (.op (.exactBin .add 17 17 9) : Code .exact 19) s23 s24 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9,
        s8, s7, s6, s5, s4, s3, s2, s1, h9, keysBase])
      hfit_keys
  set s25 := s24.write (base + 9) (keysBase base n_max)
  have e25 : Exec w (.op (.store 12 17) : Code .exact 19) s24 s25 1 := by
    simpa +decide [s25, s24, s23] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 17) (x := s24))
  set s26 := s25.set 12 (base + 10)
  have e26 : Exec w (.op (.exactBin .add 12 12 6) : Code .exact 19) s25 s26 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11,
        s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h6, Nat.add_assoc])
      (hfit_b 10 (by decide))
  set s27 := s26.set 17 (valsBase base n_max)
  have e27 : Exec w (.op (.exactBin .add 17 17 3) : Code .exact 19) s26 s27 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12,
        s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h3, valsBase])
      hfit_vals
  set s28 := s27.write (base + 10) (valsBase base n_max)
  have e28 : Exec w (.op (.store 12 17) : Code .exact 19) s27 s28 1 := by
    simpa +decide [s28, s27, s26] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 17) (x := s27))
  set s29 := s28.set 15 19
  have e29 : Exec w (.op (.const 15 19) : Code .exact 19) s28 s29 1 := Exec.const hfit_19
  set s30 := s29.set 12 (base + 19)
  have e30 : Exec w (.op (.exactBin .add 12 0 15) : Code .exact 19) s29 s30 1 :=
    ExactLog.exec_exactBin
      (by simp +decide [s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18, s17, s16, s15,
        s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
      (hfit_b 19 (by decide))
  set s31 := s30.write (base + 19) (base + space n_max)
  have e31 : Exec w (.op (.store 12 1) : Code .exact 19) s30 s31 1 := by
    simpa +decide [s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18, s17,
      s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h1] using
      (Exec.store (B := .exact) (w := w) (a := 12) (s := 1) (x := s30))
  set s32 := s31.set 0 (hashBase base)
  have e32 : Exec w (.op (.copy 0 16) : Code .exact 19) s31 s32 1 := by
    simpa +decide [s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, s18,
      s17, s16, s15] using
      (Exec.copy (B := .exact) (w := w) (d := 0) (s := 16) (x := s31))
  set s33 := s32.set 1 n_max
  have e33 : Exec w (.op (.copy 1 3) : Code .exact 19) s32 s33 1 := by
    simpa +decide [s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19,
      s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h3] using
      (Exec.copy (B := .exact) (w := w) (d := 1) (s := 3) (x := s32))
  set s34 := s33.set 2 U
  have e34 : Exec w (.op (.copy 2 4) : Code .exact 19) s33 s34 1 := by
    simpa +decide [s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20,
      s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      h4] using (Exec.copy (B := .exact) (w := w) (d := 2) (s := 4) (x := s33))
  set s35 := s34.set 3 (tableBits n_max)
  have e35 : Exec w (.op (.copy 3 8) : Code .exact 19) s34 s35 1 := by
    simpa +decide [s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21,
      s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      h8] using (Exec.copy (B := .exact) (w := w) (d := 3) (s := 8) (x := s34))
  have hall :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq (e9.seq (e10.seq
      (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq (e16.seq (e17.seq (e18.seq (e19.seq
        (e20.seq (e21.seq (e22.seq (e23.seq (e24.seq (e25.seq (e26.seq (e27.seq (e28.seq
          (e29.seq (e30.seq (e31.seq (e32.seq (e33.seq (e34.seq e35)))))))))))))))))))))))))))))))))
  refine ⟨s35, hall,
    by simp +decide [s35, s34, s33, s32],
    by simp +decide [s35, s34, s33],
    by simp +decide [s35, s34],
    by simp +decide [s35],
    ?_, ?_, ?_, ?_⟩
  · dsimp only [HeaderConstsRep, s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23,
      s22, s21, s20, s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4,
      s3, s2, s1, Data.write, Data.set]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      repeat' first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)]
  · dsimp only [s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20,
      s19, s18, s17, s16, s15, s14, s13, s12, Data.write, Data.set]
    repeat' first | rw [Function.update_self] | rw [Function.update_of_ne (by omega)]
  · dsimp only [s35, s34, s33, s32, s31, Data.write, Data.set]
    rw [Function.update_self]
  · intro a ha
    dsimp only [s35, s34, s33, s32, s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20,
      s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Data.write, Data.set]
    repeat' rw [Function.update_of_ne (by omega)]

/-- Post-state of `restoreAfterHashInitCode`. -/
@[expose]
def restoreAfterHashInitData (base n_max : ℕ) (d : Data 19) : Data 19 :=
  ((((d.set 15 20).set 0 base).set 15 19).set 1 (base + 19)).set 1 (base + space n_max)

/-- Suffix of `initSetup`: restores `reg 0 = base` and reloads `reg 1 = base + space n_max` from
`mem[base + 19]`. -/
@[expose]
def restoreAfterHashInitCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
  (.seq (.op (.exactBin .sub 0 0 15))
  (.seq (.op (.const 15 19))
  (.seq (.op (.exactBin .add 1 0 15))
        (.op (.load 1 1)))))

theorem restoreAfterHashInitCode_exec {w base n_max : ℕ} {d : Data 19}
    (h0 : d.regs 0 = hashBase base)
    (hm19 : d.mem (base + 19) = base + space n_max)
    (hfit_end : Fits w (base + space n_max)) :
    Exec w restoreAfterHashInitCode d (restoreAfterHashInitData base n_max d) 5 := by
  have hle_sp := le_space n_max
  have hfit_19 : Fits w 19 := hfit_end.of_le (by omega)
  have hfit_20 : Fits w 20 := hfit_end.of_le (by omega)
  have hfit_base : Fits w base := hfit_end.of_le (Nat.le_add_right _ _)
  have hfit_b19 : Fits w (base + 19) := hfit_end.of_le (by omega)
  set r1 := d.set 15 20
  have er1 : Exec w (.op (.const 15 20) : Code .exact 19) d r1 1 := Exec.const hfit_20
  set r2 := r1.set 0 base
  have er2 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19) r1 r2 1 :=
    ExactLog.exec_exactBin (by simp +decide [r1, h0, hashBase]) hfit_base
  set r3 := r2.set 15 19
  have er3 : Exec w (.op (.const 15 19) : Code .exact 19) r2 r3 1 := Exec.const hfit_19
  set r4 := r3.set 1 (base + 19)
  have er4 : Exec w (.op (.exactBin .add 1 0 15) : Code .exact 19) r3 r4 1 :=
    ExactLog.exec_exactBin (by simp +decide [r3, r2]) hfit_b19
  set r5 := r4.set 1 (base + space n_max)
  have er5 : Exec w (.op (.load 1 1) : Code .exact 19) r4 r5 1 := by
    simpa +decide [r5, r4, r3, r2, r1, hm19] using
      (Exec.load (B := .exact) (w := w) (d := 1) (a := 1) (x := r4))
  exact er1.seq (er2.seq (er3.seq (er4.seq er5)))

@[simp]
theorem restoreAfterHashInitData_mem (base n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base n_max d).mem = d.mem := rfl

@[simp]
theorem restoreAfterHashInitData_regs_zero (base n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base n_max d).regs 0 = base := by
  simp +decide [restoreAfterHashInitData]

@[simp]
theorem restoreAfterHashInitData_regs_one (base n_max : ℕ) (d : Data 19) :
    (restoreAfterHashInitData base n_max d).regs 1 = base + space n_max := by
  simp +decide [restoreAfterHashInitData]

/-- Deterministic prefix of `initSetup` before `resampleHashPairCode`. -/
@[expose]
def initSetupDetPrefix : Code .exact 19 :=
  .seq computeScaleCode
  (.seq writeHeaderAndAdvanceCode
        initTableHashPairCode)

/-- Complete `initSetup` program for cuckoo hashing: populates the header, builds the shared
`KWise` `clmulTab`, samples the initial cuckoo hash pair `(h₁, h₂)`, and restores `base` and
`frontierReg`. -/
@[expose]
def initSetup : Code .exact 19 :=
  .seq initSetupDetPrefix
  (.seq resampleHashPairCode
        restoreAfterHashInitCode)

/-- Exact step bound for `initSetup`. -/
@[expose]
def setupSteps (n_max U : ℕ) : ℕ :=
  computeScaleSteps n_max + 35 + initTableHashPairSteps n_max U (tableBits n_max) +
    resampleHashPairSteps (tableBits n_max) + 5

/-- Distributional execution specification for `resampleHashPairCode`. -/
theorem resampleHashPairCode_execCodeDist {w hashBase n_max U M : ℕ} {x : Data 19}
    (htab : HashPairTableRep hashBase n_max U M x.mem)
    (h0 : x.regs 0 = hashBase)
    (hfit_end : Fits w (hashBase + hashPairSpace n_max M))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U M)) :
    let μ_res := (Prod.fst <$> resampleHashPairComp hashBase n_max U M x).eval
    ExecCodeDist w resampleHashPairCode x μ_res (resampleHashPairSteps M) ∧
    μ_res.map (fun y => extractSeed hashBase n_max U M y.mem) = seedLaw U M ∧
    ∀ y ∈ μ_res.support,
      y.regs 0 = hashBase ∧
      HashPairRep hashBase n_max U M (extractSeed hashBase n_max U M y.mem) y.mem ∧
      (∀ a, (a < hashBase + 4 ∨
        (hashBase + 32 ≤ a ∧ a < z1Base hashBase n_max) ∨
        hashBase + hashPairSpace n_max M ≤ a) → y.mem a = x.mem a) := by
  intro μ_res
  have hres := resampleHashPairCode_execRand (w := w) htab h0 hfit_end hfit_q
  refine ⟨?_, ?_, ?_⟩
  · refine (ExecCodeDist.of_execRand hres).mono ?_
    refine (ProbComp.expect_mono_on_support fun z hz => ?_).trans (ProbComp.expect_const _ _).le
    obtain ⟨ht, -, -, -⟩ := mem_support_resampleHashPairComp htab h0 hz
    simp only [ht, le_refl]
  · dsimp only [μ_res]
    rw [ProbComp.eval_map, PMF.map_comp]
    exact map_extractSeed_eval_resampleHashPairComp hashBase n_max U M x
  · intro y hy
    dsimp only [μ_res] at hy
    rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [ProbComp.support_eval] at hz
    obtain ⟨-, hz_0, hz_hash, hz_frame⟩ := mem_support_resampleHashPairComp htab h0 hz
    exact ⟨hz_0, hz_hash, hz_frame⟩

theorem initSetup_spec {w base n_max U V : ℕ} {x₁ : Data 19}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 1 = base + space n_max)
    (h3 : x₁.regs 3 = n_max) (h4 : x₁.regs 4 = U)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ μ_init : PMF (Data 19),
      ExecCodeDist w initSetup x₁ μ_init (setupSteps n_max U) ∧
      μ_init.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) ∧
      ∀ y ∈ μ_init.support,
        y.regs 1 = base + space n_max ∧
        RepWithKeys w base n_max U V [] (Dictionary.empty U) y ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem y.mem := by
  have hfit_end : Fits w (base + space n_max) := by
    rw [← hfr]; exact hx₁.1 1
  have hfit_sp : Fits w (space n_max) := hfit_end.of_le (Nat.le_add_left _ _)
  have hle_sp := le_space n_max
  have h4le := four_mul_max_le_tableSize n_max
  have hmax2_le : max n_max 2 ≤ tableSize n_max := le_trans (by omega) h4le
  have hfit_n : Fits w (max n_max 2) :=
    hfit_sp.of_le (by dsimp only [space]; omega)
  have hfit_hp : Fits w (hashBase base + hashPairSpace n_max (tableBits n_max)) :=
    hfit_end.of_le (by dsimp only [hashBase, space]; omega)
  obtain ⟨d1, ⟨t_sc, ht_sc, he_sc⟩, hd1_mem, hd1_low, -, hd1_6, -, hd1_8, hd1_9, hd1_10,
      hd1_11, -⟩ :=
    computeScaleCode_execWithin (w := w) (n_max := n_max) (x := x₁) h3 hfit_sp hfit_ev
  obtain ⟨d2, he_wh, hd2_0, hd2_1, hd2_2, hd2_3, hd2_hdr, hd2_m5, hd2_m19, hd2_frame⟩ :=
    writeHeaderAndAdvanceCode_exec (w := w) (base := base) (n_max := n_max) (U := U) (x := d1)
      (by rw [hd1_low 0 (by decide), hb])
      (by rw [hd1_low 1 (by decide), hfr])
      (by rw [hd1_low 3 (by decide), h3])
      (by rw [hd1_low 4 (by decide), h4])
      hd1_6 hd1_8 hd1_9 hd1_10 hd1_11 hfit_end
  obtain ⟨d3, ⟨t_it, ht_it, he_it⟩, hd3_tab, hd3_0, hd3_frame⟩ :=
    initTableHashPairCode_execWithin (w := w) (hashBase := hashBase base) (n_max := n_max)
      (U := U) (M := tableBits n_max) (x := d2) hd2_0 hd2_1 hd2_2 hd2_3 hfit_hp hfit_n hfit_U
      hfit_q
  have he_pref : Exec w initSetupDetPrefix x₁ d3 (t_sc + (35 + t_it)) :=
    he_sc.seq (he_wh.seq he_it)
  obtain ⟨hres_dist, hres_law, hres_supp⟩ :=
    resampleHashPairCode_execCodeDist (w := w) hd3_tab hd3_0 hfit_hp hfit_q
  let μ_res : PMF (Data 19) :=
    (Prod.fst <$> resampleHashPairComp (hashBase base) n_max U (tableBits n_max) d3).eval
  have hrestore : ∀ z ∈ μ_res.support,
      ExecCodeDist w restoreAfterHashInitCode z
        (PMF.pure (restoreAfterHashInitData base n_max z)) 5 := by
    intro z hz
    obtain ⟨hz_0, -, hz_frame⟩ := hres_supp z hz
    have hm19 : z.mem (base + 19) = base + space n_max := by
      rw [hz_frame (base + 19) (Or.inl (by dsimp only [hashBase]; omega)),
        hd3_frame (base + 19) (Or.inl (by dsimp only [hashBase]; omega)), hd2_m19]
    exact ExecCodeDist.of_exec (restoreAfterHashInitCode_exec hz_0 hm19 hfit_end)
  have htail_dist : ExecCodeDist w (.seq resampleHashPairCode restoreAfterHashInitCode) d3
      (μ_res.map (restoreAfterHashInitData base n_max))
      (resampleHashPairSteps (tableBits n_max) + 5) := by
    have hseq := hres_dist.seq_const hrestore (fun _ _ => le_rfl)
    exact hseq.congr_dist rfl le_rfl
  let μ_init : PMF (Data 19) := μ_res.map (restoreAfterHashInitData base n_max)
  have hfull_dist : ExecCodeDist w initSetup x₁ μ_init (setupSteps n_max U) := by
    have hseq := (ExecCodeDist.of_exec he_pref).seq_const
      (μ₂ := fun _ => μ_init)
      (T₂ := fun _ => (resampleHashPairSteps (tableBits n_max) : ℝ≥0∞) + 5)
      (B₂ := (resampleHashPairSteps (tableBits n_max) : ℝ≥0∞) + 5)
      (fun y hy => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact htail_dist)
      (fun _ _ => le_rfl)
    refine hseq.congr_dist (PMF.pure_bind d3 _) ?_
    exact_mod_cast (by dsimp only [setupSteps]; omega : t_sc + (35 + t_it) +
      (resampleHashPairSteps (tableBits n_max) + 5) ≤ setupSteps n_max U)
  have hseed_law :
      μ_init.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) := by
    dsimp only [μ_init]
    rw [PMF.map_comp]
    have hmem_eq :
        ((fun y : Data 19 => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) ∘
          restoreAfterHashInitData base n_max) =
        fun z : Data 19 => extractSeed (hashBase base) n_max U (tableBits n_max) z.mem := by
      funext z
      simp only [Function.comp_apply, restoreAfterHashInitData_mem]
    rw [hmem_eq]
    exact hres_law
  refine ⟨μ_init, hfull_dist, hseed_law, ?_⟩
  intro y hy
  have hy_bdd : y.Bounded w := hfull_dist.bounded hx₁ y hy
  dsimp only [μ_init] at hy
  rw [PMF.mem_support_map_iff] at hy
  obtain ⟨z₀, hz₀, rfl⟩ := hy
  obtain ⟨hz₀_0, hz₀_hash, hz₀_frame⟩ := hres_supp z₀ hz₀
  have hpost_mem : (restoreAfterHashInitData base n_max z₀).mem = z₀.mem := rfl
  have hpost_0 : (restoreAfterHashInitData base n_max z₀).regs 0 = base :=
    restoreAfterHashInitData_regs_zero base n_max z₀
  have hpost_1 : (restoreAfterHashInitData base n_max z₀).regs 1 = base + space n_max :=
    restoreAfterHashInitData_regs_one base n_max z₀
  have hhdr_z : HeaderConstsRep base n_max U z₀.mem := by
    refine hd2_hdr.congr fun k hk _ => ?_
    rw [hz₀_frame (base + k) (Or.inl (by dsimp only [hashBase]; omega)),
      hd3_frame (base + k) (Or.inl (by dsimp only [hashBase]; omega))]
  have hm5_z : z₀.mem (base + 5) = 0 := by
    rw [hz₀_frame (base + 5) (Or.inl (by dsimp only [hashBase]; omega)),
      hd3_frame (base + 5) (Or.inl (by dsimp only [hashBase]; omega)), hd2_m5]
  have hkv_z : KeysValsRep base n_max U V [] (Dictionary.empty U) z₀.mem := by
    refine ⟨List.nodup_nil, Nat.zero_le _, hm5_z, ?_, fun _ h => by simp at h,
      Dictionary.valuesBounded_empty U V⟩
    intro u
    simp [Dictionary.dom_empty]
  have hslots_z :
      TableSlotsRep (t1Base base n_max) (t2Base base n_max)
        (PureTable.empty U (2 ^ tableBits n_max)) z₀.mem := by
    refine ⟨fun b => ?_, fun b => ?_⟩
    · have hb_lt := b.isLt
      rw [hz₀_frame (t1Base base n_max + b.val) (Or.inr (Or.inr (by dsimp only [t1Base]; omega))),
        hd3_frame (t1Base base n_max + b.val) (Or.inr (by dsimp only [t1Base]; omega)),
        hd2_frame (t1Base base n_max + b.val) (Or.inr (by
          dsimp only [t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega)),
        hd1_mem,
        hz (t1Base base n_max + b.val) (by
          simp only [Block.mem_footprint, Block.Owns, t1Base, hashBase, space, tableSize]
          omega)]
      rfl
    · have hb_lt := b.isLt
      rw [hz₀_frame (t2Base base n_max + b.val) (Or.inr (Or.inr (by
          dsimp only [t2Base, t1Base]; omega))),
        hd3_frame (t2Base base n_max + b.val) (Or.inr (by dsimp only [t2Base, t1Base]; omega)),
        hd2_frame (t2Base base n_max + b.val) (Or.inr (by
          dsimp only [t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega)),
        hd1_mem,
        hz (t2Base base n_max + b.val) (by
          simp only [Block.mem_footprint, Block.Owns, t2Base, t1Base, hashBase, space, tableSize]
          omega)]
      rfl
  refine ⟨hpost_1, ?_, ?_⟩
  · refine ⟨hy_bdd, hpost_0, hhdr_z, hz₀_hash, hkv_z,
      PureTable.empty U (2 ^ tableBits n_max), rfl, hslots_z⟩
  · intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
    rw [hpost_mem,
      hz₀_frame a (ha.imp (by dsimp only [hashBase]; omega)
        (fun h => Or.inr (by dsimp only [hashBase, space] at *; omega))),
      hd3_frame a (ha.imp (by dsimp only [hashBase]; omega)
        (by dsimp only [hashBase, space] at *; omega)),
      hd2_frame a (ha.imp (by omega) (by have := le_space n_max; omega)),
      hd1_mem]

/-! ### Section 3: Base-shifted hash wrappers, `probeKeyCode`, and `getCode` -/

/-- Encode `Option ℕ` as a single machine word (`0` for `none` and `v + 1` for `some v`). -/
@[expose]
def encodeOptionNat : Option ℕ → ℕ
  | none => 0
  | some v => v + 1

/-- Decode a single machine word into `Option ℕ` (`0` as `none` and `v + 1` as `some v`). -/
@[expose]
def decodeOptionNat : ℕ → Option ℕ
  | 0 => none
  | v + 1 => some v

@[simp]
theorem decodeOptionNat_encodeOptionNat (o : Option ℕ) :
    decodeOptionNat (encodeOptionNat o) = o := by
  cases o <;> rfl

theorem extractSeed_congr_of_not_scratch {base n_max U : ℕ} {mem mem' : ℕ → ℕ}
    (h : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → mem' a = mem a) :
    extractSeed (hashBase base) n_max U (tableBits n_max) mem' =
      extractSeed (hashBase base) n_max U (tableBits n_max) mem := by
  have hpoly : Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem' =
      Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem := by
    funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
    exact congrArg (Tabulation.extractWord _) (h (hashBase base + 4 + i.val) (Or.inl (by omega)))
  have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem' =
      Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem := by
    funext i
    have hz1 : hashBase base + 47 ≤ z1Base (hashBase base) n_max := by
      rw [z1Base_eq]; exact Nat.le_add_right _ _
    dsimp only [Tabulation.extractSlice]
    exact congrArg (Tabulation.extractWord _)
      (h (z1Base (hashBase base) n_max + i.val) (Or.inr (by omega)))
  dsimp only [extractSeed]
  rw [hpoly, htab]

theorem extractSeed_congr_of_ge_hashBase {base n_max U : ℕ} {mem mem' : ℕ → ℕ}
    (h : ∀ a, hashBase base ≤ a → mem' a = mem a) :
    extractSeed (hashBase base) n_max U (tableBits n_max) mem' =
      extractSeed (hashBase base) n_max U (tableBits n_max) mem := by
  have hpoly : Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem' =
      Tabulation.extractSlice (hashBase base + 4)
        (Probability.trinomialDeg U (tableBits n_max)) 28 mem := by
    funext i; dsimp only [Tabulation.extractSlice]
    exact congrArg (Tabulation.extractWord _) (h (hashBase base + 4 + i.val) (by omega))
  have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem' =
      Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
        (2 * 2 ^ tableBits n_max) mem := by
    funext i
    have hz1 : hashBase base + 47 ≤ z1Base (hashBase base) n_max := by
      rw [z1Base_eq]; exact Nat.le_add_right _ _
    dsimp only [Tabulation.extractSlice]
    exact congrArg (Tabulation.extractWord _) (h (z1Base (hashBase base) n_max + i.val) (by omega))
  dsimp only [extractSeed]
  rw [hpoly, htab]

theorem HashPairRep.congr_of_ge_hashBase {base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {mem mem' : ℕ → ℕ}
    (hrep : HashPairRep (hashBase base) n_max U (tableBits n_max) θ mem)
    (h : ∀ a, hashBase base ≤ a → mem' a = mem a) :
    HashPairRep (hashBase base) n_max U (tableBits n_max) θ mem' := by
  rcases hrep with ⟨⟨hM, hz1, hz2, h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
    ⟨hpoly, htab1, htab2⟩⟩
  have hz1_le : hashBase base ≤ z1Base (hashBase base) n_max := by
    rw [z1Base_eq, Nat.add_assoc]; exact Nat.le_add_right _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [h (hashBase base) (by omega)]; exact hM
  · rw [h (hashBase base + 1) (by omega)]; exact hz1
  · rw [h (hashBase base + 2) (by omega)]; exact hz2
  · rw [h (hashBase base + 32) (by omega)]; exact h0'
  · rw [h (hashBase base + 33) (by omega)]; exact h1'
  · rw [h (hashBase base + 34) (by omega)]; exact h2'
  · rw [h (hashBase base + 35) (by omega)]; exact h3'
  · rw [h (hashBase base + 36) (by omega)]; exact h4'
  · rw [h (hashBase base + 37) (by omega)]; exact h5'
  · rw [h (hashBase base + 38) (by omega)]; exact h6'
  · rw [h (hashBase base + 39) (by omega)]; exact h7'
  · intro idx hidx
    rw [h (hashBase base + 47 + idx) (by omega)]; exact hcl idx hidx
  · intro r j
    rw [h (hashBase base + 4 + 7 * r.val + j.val) (by omega)]; exact hpoly r j
  · intro i
    rw [h (z1Base (hashBase base) n_max + i.val) (by omega)]; exact htab1 i
  · intro i
    rw [h (z2Base (hashBase base) n_max (tableBits n_max) + i.val)
      (by dsimp only [z2Base]; omega)]
    exact htab2 i

/-- Shifts `reg 0` from `base` to `hashBase base = base + 20` using `reg 15` as scratch. -/
@[expose]
def shiftToHashBaseCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
       (.op (.exactBin .add 0 0 15))

/-- Restores `reg 0` from `hashBase base = base + 20` back to `base` using `reg 15` as scratch. -/
@[expose]
def unshiftFromHashBaseCode : Code .exact 19 :=
  .seq (.op (.const 15 20))
       (.op (.exactBin .sub 0 0 15))

theorem shiftToHashBaseCode_exec {w base : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hfit_20 : Fits w 20)
    (hfit_hb : Fits w (hashBase base)) :
    Exec w shiftToHashBaseCode x ((x.set 15 20).set 0 (hashBase base)) 2 := by
  set s1 := x.set 15 20
  have e1 : Exec w (.op (.const 15 20) : Code .exact 19) x s1 1 := Exec.const hfit_20
  set s2 := s1.set 0 (hashBase base)
  have e2 : Exec w (.op (.exactBin .add 0 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0, hashBase]) hfit_hb
  exact e1.seq e2

theorem unshiftFromHashBaseCode_exec {w base : ℕ} {x : Data 19}
    (h0 : x.regs 0 = hashBase base)
    (hfit_20 : Fits w 20)
    (hfit_base : Fits w base) :
    Exec w unshiftFromHashBaseCode x ((x.set 15 20).set 0 base) 2 := by
  set s1 := x.set 15 20
  have e1 : Exec w (.op (.const 15 20) : Code .exact 19) x s1 1 := Exec.const hfit_20
  set s2 := s1.set 0 base
  have e2 : Exec w (.op (.exactBin .sub 0 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h0, hashBase]) hfit_base
  exact e1.seq e2

/-- Evaluates `h₁(u)` with `reg 0 = base`, `reg 1 = u.val`, placing `(evalHash1 θ u).val` in `reg 2`
and restoring `reg 0 = base`. -/
@[expose]
def evalHash1AtBaseCode : Code .exact 19 :=
  .seq shiftToHashBaseCode
  (.seq evalHash1Code
        unshiftFromHashBaseCode)

/-- Evaluates `h₂(u)` with `reg 0 = base`, `reg 1 = u.val`, placing `(evalHash2 θ u).val` in `reg 2`
and restoring `reg 0 = base`. -/
@[expose]
def evalHash2AtBaseCode : Code .exact 19 :=
  .seq shiftToHashBaseCode
  (.seq evalHash2Code
        unshiftFromHashBaseCode)

/-- Resamples `(h₁, h₂)` with `reg 0 = base` and restores `reg 0 = base`. -/
@[expose]
def resampleAtBaseCode : Code .exact 19 :=
  .seq shiftToHashBaseCode
  (.seq resampleHashPairCode
        unshiftFromHashBaseCode)

/-- Step bound for `evalHash1AtBaseCode` and `evalHash2AtBaseCode`. -/
@[expose]
def evalHashAtBaseSteps (n_max U : ℕ) : ℕ :=
  evalHashSteps n_max U (tableBits n_max) + 4

/-- Step bound for `resampleAtBaseCode`. -/
@[expose]
def resampleAtBaseSteps (n_max : ℕ) : ℕ :=
  resampleHashPairSteps (tableBits n_max) + 4

theorem evalHash1AtBaseCode_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {u : Fin U} {x : Data 19}
    (hrep : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w evalHash1AtBaseCode x y (evalHashAtBaseSteps n_max U) ∧
      y.regs 0 = base ∧
      y.regs 2 = (evalHash1 θ u).val ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_20 : Fits w 20 := hfit_end.of_le (by omega)
  have hfit_base : Fits w base := hfit_end.of_le (Nat.le_add_right _ _)
  have hfit_hb : Fits w (hashBase base) := hfit_end.of_le (by dsimp only [hashBase]; omega)
  have hfit_hp : Fits w (hashBase base + hashPairSpace n_max (tableBits n_max)) :=
    hfit_end.of_le (by dsimp only [hashBase, space]; omega)
  have e_sh := shiftToHashBaseCode_exec h0 hfit_20 hfit_hb
  set s1 := (x.set 15 20).set 0 (hashBase base)
  obtain ⟨s2, ⟨t_ev, ht_ev, he_ev⟩, hs2_0, -, hs2_2, hs2_rep, hs2_frame⟩ :=
    evalHash1Code_execWithin (w := w) (hashBase := hashBase base) (n_max := n_max)
      (U := U) (M := tableBits n_max) (θ := θ) (u := u) (x := s1)
      hrep (by simp +decide [s1]) (by simp +decide [s1, h1]) hw hfit_hp
  have e_un := unshiftFromHashBaseCode_exec (x := s2) hs2_0 hfit_20 hfit_base
  set y := (s2.set 15 20).set 0 base
  refine ⟨y, ⟨2 + (t_ev + 2), by dsimp only [evalHashAtBaseSteps]; omega,
    e_sh.seq (he_ev.seq e_un)⟩,
    by simp +decide [y], by simp +decide [y, hs2_2], hs2_rep,
    extractSeed_congr_of_not_scratch hs2_frame, hs2_frame⟩

theorem evalHash2AtBaseCode_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {u : Fin U} {x : Data 19}
    (hrep : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (h1 : x.regs 1 = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w evalHash2AtBaseCode x y (evalHashAtBaseSteps n_max U) ∧
      y.regs 0 = base ∧
      y.regs 2 = (evalHash2 θ u).val ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_20 : Fits w 20 := hfit_end.of_le (by omega)
  have hfit_base : Fits w base := hfit_end.of_le (Nat.le_add_right _ _)
  have hfit_hb : Fits w (hashBase base) := hfit_end.of_le (by dsimp only [hashBase]; omega)
  have hfit_hp : Fits w (hashBase base + hashPairSpace n_max (tableBits n_max)) :=
    hfit_end.of_le (by dsimp only [hashBase, space]; omega)
  have e_sh := shiftToHashBaseCode_exec h0 hfit_20 hfit_hb
  set s1 := (x.set 15 20).set 0 (hashBase base)
  obtain ⟨s2, ⟨t_ev, ht_ev, he_ev⟩, hs2_0, -, hs2_2, hs2_rep, hs2_frame⟩ :=
    evalHash2Code_execWithin (w := w) (hashBase := hashBase base) (n_max := n_max)
      (U := U) (M := tableBits n_max) (θ := θ) (u := u) (x := s1)
      hrep (by simp +decide [s1]) (by simp +decide [s1, h1]) hw hfit_hp
  have e_un := unshiftFromHashBaseCode_exec (x := s2) hs2_0 hfit_20 hfit_base
  set y := (s2.set 15 20).set 0 base
  refine ⟨y, ⟨2 + (t_ev + 2), by dsimp only [evalHashAtBaseSteps]; omega,
    e_sh.seq (he_ev.seq e_un)⟩,
    by simp +decide [y], by simp +decide [y, hs2_2], hs2_rep,
    extractSeed_congr_of_not_scratch hs2_frame, hs2_frame⟩

/-- Distributional execution specification for `resampleAtBaseCode`. -/
theorem resampleAtBaseCode_execCodeDist {w base n_max U : ℕ} {x : Data 19}
    (htab : HashPairTableRep (hashBase base) n_max U (tableBits n_max) x.mem)
    (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ μ_res : PMF (Data 19),
      ExecCodeDist w resampleAtBaseCode x μ_res (resampleAtBaseSteps n_max) ∧
      μ_res.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) ∧
      ∀ y ∈ μ_res.support,
        y.regs 0 = base ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max)
          (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) y.mem ∧
        (∀ a, (a < hashBase base + 4 ∨
          (hashBase base + 32 ≤ a ∧ a < z1Base (hashBase base) n_max) ∨
          hashBase base + hashPairSpace n_max (tableBits n_max) ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_20 : Fits w 20 := hfit_end.of_le (by omega)
  have hfit_base : Fits w base := hfit_end.of_le (Nat.le_add_right _ _)
  have hfit_hb : Fits w (hashBase base) := hfit_end.of_le (by dsimp only [hashBase]; omega)
  have hfit_hp : Fits w (hashBase base + hashPairSpace n_max (tableBits n_max)) :=
    hfit_end.of_le (by dsimp only [hashBase, space]; omega)
  have e_sh := shiftToHashBaseCode_exec h0 hfit_20 hfit_hb
  set s1 := (x.set 15 20).set 0 (hashBase base)
  obtain ⟨hres_dist, hres_law, hres_supp⟩ :=
    resampleHashPairCode_execCodeDist (w := w) (x := s1) htab (by simp +decide [s1]) hfit_hp hfit_q
  let μ_inner : PMF (Data 19) :=
    (Prod.fst <$> resampleHashPairComp (hashBase base) n_max U (tableBits n_max) s1).eval
  let unshiftFn : Data 19 → Data 19 := fun d => (d.set 15 20).set 0 base
  have hun : ∀ z ∈ μ_inner.support,
      ExecCodeDist w unshiftFromHashBaseCode z (PMF.pure (unshiftFn z)) 2 := by
    intro z hz
    obtain ⟨hz_0, -, -⟩ := hres_supp z hz
    exact ExecCodeDist.of_exec (unshiftFromHashBaseCode_exec hz_0 hfit_20 hfit_base)
  let μ_res : PMF (Data 19) := μ_inner.map unshiftFn
  have htail : ExecCodeDist w (.seq resampleHashPairCode unshiftFromHashBaseCode) s1
      μ_res (resampleHashPairSteps (tableBits n_max) + 2) :=
    (hres_dist.seq_const hun (fun _ _ => le_rfl)).congr_dist rfl le_rfl
  have hfull : ExecCodeDist w resampleAtBaseCode x μ_res (resampleAtBaseSteps n_max) := by
    have hseq := (ExecCodeDist.of_exec e_sh).seq_const
      (μ₂ := fun _ => μ_res)
      (T₂ := fun _ => (resampleHashPairSteps (tableBits n_max) : ℝ≥0∞) + 2)
      (B₂ := (resampleHashPairSteps (tableBits n_max) : ℝ≥0∞) + 2)
      (fun y hy => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy; exact htail)
      (fun _ _ => le_rfl)
    refine hseq.congr_dist (PMF.pure_bind s1 _) ?_
    exact_mod_cast (by dsimp only [resampleAtBaseSteps]; omega :
      2 + (resampleHashPairSteps (tableBits n_max) + 2) ≤ resampleAtBaseSteps n_max)
  refine ⟨μ_res, hfull, ?_, ?_⟩
  · dsimp only [μ_res]
    rw [PMF.map_comp]
    exact hres_law
  · intro y hy
    dsimp only [μ_res] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨-, hz_hash, hz_frame⟩ := hres_supp z hz
    exact ⟨by simp +decide [unshiftFn], hz_hash, hz_frame⟩

/-- Helper subprogram that loads `mem[base + off]` into `reg dst` using `reg 15` as scratch. -/
@[expose]
def loadHeaderCode (dst : Fin 19) (off : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 off))
  (.seq (.op (.exactBin .add dst 0 15))
        (.op (.load dst dst)))

theorem loadHeaderCode_exec {w base off : ℕ} (dst : Fin 19) {x : Data 19}
    (h0 : x.regs 0 = base)
    (hne0 : dst ≠ 0) (hne15 : dst ≠ 15)
    (hfit_off : Fits w off)
    (hfit_addr : Fits w (base + off)) :
    Exec w (loadHeaderCode dst off) x ((x.set 15 off).set dst (x.mem (base + off))) 3 := by
  set s1 := x.set 15 off
  have e1 : Exec w (.op (.const 15 off) : Code .exact 19) x s1 1 := Exec.const hfit_off
  set s2 := s1.set dst (base + off)
  have e2 : Exec w (.op (.exactBin .add dst 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp [s1, h0]) hfit_addr
  set s3 := s2.set dst (x.mem (base + off))
  have e3 : Exec w (.op (.load dst dst) : Code .exact 19) s2 s3 1 := by
    simpa [s3, s2, s1] using (Exec.load (B := .exact) (w := w) (d := dst) (a := dst) (x := s2))
  have heq : s3 = (x.set 15 off).set dst (x.mem (base + off)) := by
    cases x; dsimp only [s3, s2, s1, Data.set]; congr 1
    funext r
    by_cases hr : r = dst
    · subst hr; simp
    · simp [hr]
  rw [← heq]
  exact e1.seq (e2.seq e3)

/-- Helper subprogram that stores `reg src` into `mem[base + off]` using `reg 15, 16` as scratch. -/
@[expose]
def storeHeaderCode (off : ℕ) (src : Fin 19) : Code .exact 19 :=
  .seq (.op (.const 15 off))
  (.seq (.op (.exactBin .add 16 0 15))
        (.op (.store 16 src)))

theorem storeHeaderCode_exec {w base off : ℕ} (src : Fin 19) {x : Data 19}
    (h0 : x.regs 0 = base)
    (hne15 : src ≠ 15) (hne16 : src ≠ 16)
    (hfit_off : Fits w off)
    (hfit_addr : Fits w (base + off)) :
    Exec w (storeHeaderCode off src) x
      (((x.set 15 off).set 16 (base + off)).write (base + off) (x.regs src)) 3 := by
  set s1 := x.set 15 off
  have e1 : Exec w (.op (.const 15 off) : Code .exact 19) x s1 1 := Exec.const hfit_off
  set s2 := s1.set 16 (base + off)
  have e2 : Exec w (.op (.exactBin .add 16 0 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp [s1, h0]) hfit_addr
  set s3 := s2.write (base + off) (x.regs src)
  have e3 : Exec w (.op (.store 16 src) : Code .exact 19) s2 s3 1 := by
    simpa [s3, s2, s1, hne15, hne16] using
      (Exec.store (B := .exact) (w := w) (a := 16) (s := src) (x := s2))
  exact e1.seq (e2.seq e3)

/-- Helper subprogram that stores constant `val` into `mem[base + off]` using `reg 15, 16, 18` as
scratch. -/
@[expose]
def storeHeaderConstCode (off val : ℕ) : Code .exact 19 :=
  .seq (.op (.const 18 val))
       (storeHeaderCode off 18)

theorem storeHeaderConstCode_exec {w base off val : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hfit_val : Fits w val)
    (hfit_off : Fits w off)
    (hfit_addr : Fits w (base + off)) :
    Exec w (storeHeaderConstCode off val) x
      ((((x.set 18 val).set 15 off).set 16 (base + off)).write (base + off) val) 4 := by
  set s1 := x.set 18 val
  have e1 : Exec w (.op (.const 18 val) : Code .exact 19) x s1 1 := Exec.const hfit_val
  have e2 := storeHeaderCode_exec (src := 18) (x := s1) (by simp +decide [s1, h0])
    (by decide) (by decide) hfit_off hfit_addr
  exact e1.seq e2

/-- Inner branch of `probeTableSlotCode` when `0 < slotVal` (`reg 17 = e.idx + 1`):
computes `idx = reg 17 - 1`, loads `mem[keysBase + idx]` into `reg 16` and `u.val = mem[base + 11]`
into `reg 18`, and if equal sets `mem[base + 13] ← 1` and `mem[base + 14] ← idx`. -/
@[expose]
def probeCheckOccupiedCode : Code .exact 19 :=
  .seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 16 16))
  (.seq (loadHeaderCode 18 11)
  (.branch (.eq 16 18)
    (.seq (storeHeaderConstCode 13 1)
          (storeHeaderCode 14 17))
    (.op (.const 15 0))))))))

/-- Probes a single table (`T₁` when `hashCode = evalHash1AtBaseCode, tablePtrOff = 7`;
`T₂` when `hashCode = evalHash2AtBaseCode, tablePtrOff = 8`) for the key `u` stored in
`mem[base + 11]`. If the probed slot holds `some e` with `e.key = u`, sets `mem[base + 13] = 1`
and `mem[base + 14] = e.idx`; otherwise leaves `mem[base + 13]` and `mem[base + 14]` unchanged. -/
@[expose]
def probeTableSlotCode (hashCode : Code .exact 19) (tablePtrOff : ℕ) : Code .exact 19 :=
  .seq (loadHeaderCode 1 11)
  (.seq hashCode
  (.seq (loadHeaderCode 16 tablePtrOff)
  (.seq (.op (.exactBin .add 16 16 2))
  (.seq (.op (.load 17 16))
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 17)
    probeCheckOccupiedCode
    (.op (.const 15 0))))))))

/-- Step bound for `probeTableSlotCode`. -/
@[expose]
def probeTableSlotSteps (n_max U : ℕ) : ℕ :=
  evalHashAtBaseSteps n_max U + 31

theorem probeCheckOccupiedCode_execWithin {w base n_max U : ℕ}
    {ks : List (Fin U)} {e : SlotEntry U} {u : Fin U} {x : Data 19}
    (h0 : x.regs 0 = base)
    (h17 : x.regs 17 = e.idx + 1)
    (hm9 : x.mem (base + 9) = keysBase base n_max)
    (hm11 : x.mem (base + 11) = u.val)
    (hidx_lt : e.idx < ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hkey_idx : ks[e.idx]? = some e.key)
    (hmem_key : x.mem (keysBase base n_max + e.idx) = ks[e.idx].val)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w probeCheckOccupiedCode x y 19 ∧
      y.regs 0 = base ∧
      y.mem (base + 13) = (if e.key = u then 1 else x.mem (base + 13)) ∧
      y.mem (base + 14) = (if e.key = u then e.idx else x.mem (base + 14)) ∧
      (∀ a, a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (by omega)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_9 : Fits w 9 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_13 : Fits w 13 := hfit_end.of_le (by omega)
  have hfit_14 : Fits w 14 := hfit_end.of_le (by omega)
  have hfit_b9 : Fits w (base + 9) := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b13 : Fits w (base + 13) := hfit_end.of_le (by omega)
  have hfit_b14 : Fits w (base + 14) := hfit_end.of_le (by omega)
  have hfit_idx : Fits w e.idx :=
    hfit_end.of_le (by dsimp only [space]; omega)
  have hfit_kaddr : Fits w (keysBase base n_max + e.idx) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have hks_eq : ks[e.idx] = e.key := by
    rw [List.getElem?_eq_getElem hidx_lt] at hkey_idx
    exact Option.some.inj hkey_idx
  set s1 := x.set 15 1
  have e1 : Exec w (.op (.const 15 1) : Code .exact 19) x s1 1 := Exec.const hfit_1
  set s2 := s1.set 17 e.idx
  have e2 : Exec w (.op (.exactBin .sub 17 17 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h17]) hfit_idx
  have e3 := loadHeaderCode_exec (dst := 16) (off := 9) (x := s2)
    (by simp +decide [s2, s1, h0]) (by decide) (by decide) hfit_9 hfit_b9
  set s3 := (s2.set 15 9).set 16 (s2.mem (base + 9))
  set s4 := s3.set 16 (keysBase base n_max + e.idx)
  have e4 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, s2, s1, hm9]) hfit_kaddr
  set s5 := s4.set 16 e.key.val
  have e5 : Exec w (.op (.load 16 16) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, hmem_key, hks_eq] using
      (Exec.load (B := .exact) (w := w) (d := 16) (a := 16) (x := s4))
  have e6 := loadHeaderCode_exec (dst := 18) (off := 11) (x := s5)
    (by simp +decide [s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_11 hfit_b11
  set s6 := (s5.set 15 11).set 18 (s5.mem (base + 11))
  have hs6_16 : s6.regs 16 = e.key.val := by simp +decide [s6, s5]
  have hs6_18 : s6.regs 18 = u.val := by simp +decide [s6, s5, s4, s3, s2, s1, hm11]
  have hs6_17 : s6.regs 17 = e.idx := by simp +decide [s6, s5, s4, s3, s2]
  have hs6_0 : s6.regs 0 = base := by simp +decide [s6, s5, s4, s3, s2, s1, h0]
  by_cases hku : e.key = u
  · have hcond : (Cond.eq 16 18 : Cond 19).Holds s6 := by
      simp [Cond.Holds, hs6_16, hs6_18, hku]
    have e7a := storeHeaderConstCode_exec (off := 13) (val := 1) (x := s6)
      hs6_0 hfit_1 hfit_13 hfit_b13
    set s7 := (((s6.set 18 1).set 15 13).set 16 (base + 13)).write (base + 13) 1
    have e7b := storeHeaderCode_exec (off := 14) (src := 17) (x := s7)
      (by simp +decide [s7, hs6_0]) (by decide) (by decide) hfit_14 hfit_b14
    set s8 := (((s7.set 15 14).set 16 (base + 14)).write (base + 14) (s7.regs 17))
    have e_br := (e7a.seq e7b).branch_pos (neg := .op (.const 15 0)) hcond
    have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e_br)))))
    refine ⟨s8, ⟨1 + (1 + (3 + (1 + (1 + (3 + (4 + 3 + 1)))))), by decide, hall⟩,
      by simp +decide [s8, s7, hs6_0], ?_, ?_, ?_⟩
    · simp only [hku, ↓reduceIte]
      dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · simp only [hku, ↓reduceIte]
      dsimp only [s8, s7, Data.write, Data.set]
      rw [Function.update_self]
      exact hs6_17
    · intro a ha13 ha14
      dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
      rw [Function.update_of_ne ha14, Function.update_of_ne ha13]
  · have hcond : ¬(Cond.eq 16 18 : Cond 19).Holds s6 := by
      simp only [Cond.Holds, hs6_16, hs6_18]
      exact fun h => hku (Fin.ext h)
    set s7 := s6.set 15 0
    have e7 : Exec w (.op (.const 15 0) : Code .exact 19) s6 s7 1 := Exec.const hfit_0
    have e_br := e7.branch_neg
      (pos := .seq (storeHeaderConstCode 13 1) (storeHeaderCode 14 17)) hcond
    have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e_br)))))
    refine ⟨s7, ⟨1 + (1 + (3 + (1 + (1 + (3 + (1 + 2)))))), by decide, hall⟩,
      by simp +decide [s7, hs6_0], ?_, ?_, ?_⟩
    · simp only [hku, ↓reduceIte]; rfl
    · simp only [hku, ↓reduceIte]; rfl
    · intro a _ _
      rfl

theorem probeTableSlotCode_execWithin {w base n_max U tablePtrOff tableBase : ℕ}
    {hashCode : Code .exact 19}
    {θ : Seed U (tableBits n_max)} {h : Fin U → Fin (2 ^ tableBits n_max)}
    {slotFn : Fin (2 ^ tableBits n_max) → Option (SlotEntry U)}
    {ks : List (Fin U)} {u : Fin U} {x : Data 19}
    (hhash_exec : ∀ (d : Data 19),
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ d.mem →
      d.regs 0 = base → d.regs 1 = u.val →
      ∃ d' : Data 19,
        ExecWithin w hashCode d d' (evalHashAtBaseSteps n_max U) ∧
        d'.regs 0 = base ∧
        d'.regs 2 = (h u).val ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max) θ d'.mem ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) d'.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) d.mem ∧
        (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → d'.mem a = d.mem a))
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (hoff_le : tablePtrOff ≤ 10)
    (hm_ptr : x.mem (base + tablePtrOff) = tableBase)
    (htb_lo : hashBase base + hashPairSpace n_max (tableBits n_max) ≤ tableBase)
    (htb_hi : tableBase + 2 ^ tableBits n_max ≤ base + space n_max)
    (hm9 : x.mem (base + 9) = keysBase base n_max)
    (hm11 : x.mem (base + 11) = u.val)
    (hslot_mem : ∀ b : Fin (2 ^ tableBits n_max),
      x.mem (tableBase + b.val) = encodeSlot (slotFn b))
    (hslot_valid : ∀ e, slotFn (h u) = some e →
      e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base n_max + idx) = ks[idx].val)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w (probeTableSlotCode hashCode tablePtrOff) x y
        (probeTableSlotSteps n_max U) ∧
      y.regs 0 = base ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      y.mem (base + 13) =
        (match slotFn (h u) with
         | some e => if e.key = u then 1 else x.mem (base + 13)
         | none => x.mem (base + 13)) ∧
      y.mem (base + 14) =
        (match slotFn (h u) with
         | some e => if e.key = u then e.idx else x.mem (base + 14)
         | none => x.mem (base + 14)) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_off : Fits w tablePtrOff := hfit_end.of_le (by omega)
  have hfit_boff : Fits w (base + tablePtrOff) := hfit_end.of_le (by omega)
  have hhu_lt := (h u).isLt
  have hfit_saddr : Fits w (tableBase + (h u).val) := hfit_end.of_le (by omega)
  have e1 := loadHeaderCode_exec (dst := 1) (off := 11) (x := x)
    h0 (by decide) (by decide) hfit_11 hfit_b11
  set s1 := (x.set 15 11).set 1 (x.mem (base + 11))
  obtain ⟨s2, ⟨t_h, ht_h, he_h⟩, hs2_0, hs2_2, hs2_hash, hs2_seed, hs2_frame⟩ :=
    hhash_exec s1 hrep_hash (by simp +decide [s1, h0]) (by simp +decide [s1, hm11])
  have hm_ptr_s2 : s2.mem (base + tablePtrOff) = tableBase :=
    (hs2_frame (base + tablePtrOff) (Or.inl (by dsimp only [hashBase]; omega))).trans hm_ptr
  have e3 := loadHeaderCode_exec (dst := 16) (off := tablePtrOff) (x := s2)
    hs2_0 (by decide) (by decide) hfit_off hfit_boff
  set s3 := (s2.set 15 tablePtrOff).set 16 (s2.mem (base + tablePtrOff))
  set s4 := s3.set 16 (tableBase + (h u).val)
  have e4 : Exec w (.op (.exactBin .add 16 16 2) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, hs2_2, hm_ptr_s2]) hfit_saddr
  have hslot_s2 : s2.mem (tableBase + (h u).val) = encodeSlot (slotFn (h u)) :=
    (hs2_frame (tableBase + (h u).val) (Or.inr (by
      have := le_hashPairSpace n_max (tableBits n_max); omega))).trans (hslot_mem (h u))
  set s5 := s4.set 17 (encodeSlot (slotFn (h u)))
  have e5 : Exec w (.op (.load 17 16) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, hslot_s2] using
      (Exec.load (B := .exact) (w := w) (d := 17) (a := 16) (x := s4))
  set s6 := s5.set 15 0
  have e6 : Exec w (.op (.const 15 0) : Code .exact 19) s5 s6 1 := Exec.const hfit_0
  have hs6_0 : s6.regs 0 = base := by simp +decide [s6, s5, s4, s3, hs2_0]
  have hs6_15 : s6.regs 15 = 0 := by simp +decide [s6]
  have hs6_17 : s6.regs 17 = encodeSlot (slotFn (h u)) := by simp +decide [s6, s5]
  cases hslot_eq : slotFn (h u) with
  | none =>
    have hcond : ¬(Cond.lt 15 17 : Cond 19).Holds s6 := by
      simp [Cond.Holds, hs6_15, hs6_17, hslot_eq, encodeSlot]
    set s7 := s6.set 15 0
    have e7 : Exec w (.op (.const 15 0) : Code .exact 19) s6 s7 1 := Exec.const hfit_0
    have e_br := e7.branch_neg (pos := probeCheckOccupiedCode) hcond
    have hall := e1.seq (he_h.seq (e3.seq (e4.seq (e5.seq (e6.seq e_br)))))
    refine ⟨s7, ⟨3 + (t_h + (3 + (1 + (1 + (1 + (1 + 2)))))),
      by dsimp only [probeTableSlotSteps]; omega, hall⟩,
      by simp +decide [s7, hs6_0], hs2_hash, hs2_seed, ?_, ?_, ?_⟩
    · exact hs2_frame (base + 13) (Or.inl (by dsimp only [hashBase]; omega))
    · exact hs2_frame (base + 14) (Or.inl (by dsimp only [hashBase]; omega))
    · intro a ha _ _
      exact hs2_frame a ha
  | some e =>
    have hcond : (Cond.lt 15 17 : Cond 19).Holds s6 := by
      simp [Cond.Holds, hs6_15, hs6_17, hslot_eq, encodeSlot]
    obtain ⟨hidx_lt, hkey_idx⟩ := hslot_valid e hslot_eq
    have hm9_s6 : s6.mem (base + 9) = keysBase base n_max :=
      (hs2_frame (base + 9) (Or.inl (by dsimp only [hashBase]; omega))).trans hm9
    have hm11_s6 : s6.mem (base + 11) = u.val :=
      (hs2_frame (base + 11) (Or.inl (by dsimp only [hashBase]; omega))).trans hm11
    have hm_key_s6 : s6.mem (keysBase base n_max + e.idx) = ks[e.idx].val :=
      (hs2_frame (keysBase base n_max + e.idx) (Or.inr (by
        dsimp only [keysBase, t2Base, t1Base, hashBase]
        have := le_hashPairSpace n_max (tableBits n_max); omega))).trans (hmem_keys e.idx hidx_lt)
    obtain ⟨s7, ⟨t_chk, ht_chk, he_chk⟩, hs7_0, hs7_13, hs7_14, hs7_frame⟩ :=
      probeCheckOccupiedCode_execWithin hs6_0
        (by rw [hs6_17, hslot_eq]; rfl) hm9_s6 hm11_s6 hidx_lt hlen_le hkey_idx hm_key_s6 hfit_end
    have e_br := he_chk.branch_pos (neg := .op (.const 15 0)) hcond
    have hall := e1.seq (he_h.seq (e3.seq (e4.seq (e5.seq (e6.seq e_br)))))
    have hs7_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s7.mem :=
      hs2_hash.congr_of_ge_hashBase fun a ha =>
        hs7_frame a (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega)
    have hs7_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s7.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
      (extractSeed_congr_of_ge_hashBase fun a ha =>
        hs7_frame a (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega)).trans hs2_seed
    refine ⟨s7, ⟨3 + (t_h + (3 + (1 + (1 + (1 + (t_chk + 1)))))),
      by dsimp only [probeTableSlotSteps]; omega, hall⟩,
      hs7_0, hs7_hash, hs7_seed, ?_, ?_, ?_⟩
    · rw [hs7_13]
      have hm13_s6 : s6.mem (base + 13) = x.mem (base + 13) :=
        hs2_frame (base + 13) (Or.inl (by dsimp only [hashBase]; omega))
      rw [hm13_s6]
    · rw [hs7_14]
      have hm14_s6 : s6.mem (base + 14) = x.mem (base + 14) :=
        hs2_frame (base + 14) (Or.inl (by dsimp only [hashBase]; omega))
      rw [hm14_s6]
    · intro a ha ha13 ha14
      exact (hs7_frame a ha13 ha14).trans (hs2_frame a ha)

/-- Every entry in `tbl` comes from `ks` at its recorded index `e.idx`. -/
@[expose]
def TableIdxValid {U m : ℕ} (ks : List (Fin U)) (tbl : PureTable U m) : Prop :=
  ∀ e : SlotEntry U, EntryIn tbl e → e.idx < ks.length ∧ ks[e.idx]? = some e.key

theorem pureReplay_tableIdxValid {U m : ℕ} {h₁ h₂ : Fin U → Fin m} {maxLoop : ℕ}
    {ks : List (Fin U)} {tbl : PureTable U m} (hnodup : ks.Nodup)
    (hrep : pureReplay h₁ h₂ maxLoop ks = some tbl) :
    TableIdxValid ks tbl := by
  obtain ⟨_, hent⟩ := pureReplay_spec hnodup hrep
  intro e he
  rw [hent, List.mem_zipIdx_iff_getElem?] at he
  exact ⟨(List.getElem?_eq_some_iff.mp he).1, he⟩

/-- Two-probe cuckoo lookup (`probeKeyCode`): probes `T₁[h₁(u)]`, and if `u` is not found in `T₁`,
probes `T₂[h₂(u)]`. Stores `foundFlag ∈ {0, 1}` in `mem[base + 13]` and `foundIdx` in
`mem[base + 14]`. -/
@[expose]
def probeKeyCode : Code .exact 19 :=
  .seq (storeHeaderConstCode 13 0)
  (.seq (probeTableSlotCode evalHash1AtBaseCode 7)
  (.seq (loadHeaderCode 16 13)
  (.seq (.op (.const 15 0))
  (.branch (.eq 16 15)
    (probeTableSlotCode evalHash2AtBaseCode 8)
    (.op (.const 15 0))))))

/-- Step bound for `probeKeyCode`. -/
@[expose]
def probeKeySteps (n_max U : ℕ) : ℕ :=
  2 * probeTableSlotSteps n_max U + 12

theorem probeKeyCode_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)} {tbl : PureTable U (2 ^ tableBits n_max)}
    {u : Fin U} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w probeKeyCode x y (probeKeySteps n_max U) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base n_max U y.mem ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (match lookupEntry (evalHash1 θ) (evalHash2 θ) tbl u with
       | some e => y.mem (base + 13) = 1 ∧ y.mem (base + 14) = e.idx
       | none => y.mem (base + 13) = 0) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 13 → a ≠ base + 14 → y.mem a = x.mem a) := by
  have ⟨_, _, _, _, _, _, hm7, hm8, hm9, _⟩ := hhdr
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (by omega)
  have hfit_13 : Fits w 13 := hfit_end.of_le (by omega)
  have hfit_b13 : Fits w (base + 13) := hfit_end.of_le (by omega)
  have e_init := storeHeaderConstCode_exec (off := 13) (val := 0) (x := x)
    h0 hfit_0 hfit_13 hfit_b13
  set s1 := (((x.set 18 0).set 15 13).set 16 (base + 13)).write (base + 13) 0
  have hs1_frame : ∀ a, a ≠ base + 13 → s1.mem a = x.mem a :=
    fun a ha => Function.update_of_ne ha _ _
  have hs1_13 : s1.mem (base + 13) = 0 := Function.update_self _ _ _
  have hs1_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s1.mem :=
    hrep_hash.congr_of_ge_hashBase fun a ha =>
      hs1_frame a (by dsimp only [hashBase] at ha; omega)
  have hs1_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_ge_hashBase fun a ha =>
      hs1_frame a (by dsimp only [hashBase] at ha; omega)
  obtain ⟨s2, ⟨t_p1, ht_p1, he_p1⟩, hs2_0, hs2_hash, hs2_seed, hs2_13, hs2_14, hs2_frame⟩ :=
    probeTableSlotCode_execWithin (tablePtrOff := 7) (tableBase := t1Base base n_max)
      (hashCode := evalHash1AtBaseCode) (θ := θ) (h := evalHash1 θ) (slotFn := tbl.t1)
      (ks := ks) (u := u) (x := s1)
      (fun d hd h0d h1d => evalHash1AtBaseCode_execWithin hd h0d h1d hw hfit_end)
      hs1_hash (by simp +decide [s1, h0]) (by decide)
      (by rw [hs1_frame _ (by omega), hm7])
      (by dsimp only [t1Base]; omega)
      (by dsimp only [t1Base, hashBase, space, tableSize]; omega)
      (by rw [hs1_frame _ (by omega), hm9])
      (by rw [hs1_frame _ (by omega), hm11])
      (fun b => by
        rw [hs1_frame _ (by
          dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega)]
        exact hslots.1 b)
      (fun e he => htiv e (Or.inl ⟨evalHash1 θ u, he⟩))
      hlen_le
      (fun idx hlt => by
        rw [hs1_frame _ (by
          dsimp only [keysBase, t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega)]
        exact hmem_keys idx hlt)
      hfit_end
  have e_ld := loadHeaderCode_exec (dst := 16) (off := 13) (x := s2)
    hs2_0 (by decide) (by decide) hfit_13 hfit_b13
  set s3 := (s2.set 15 13).set 16 (s2.mem (base + 13))
  set s4 := s3.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  have hs4_0 : s4.regs 0 = base := by simp +decide [s4, s3, hs2_0]
  have hs4_15 : s4.regs 15 = 0 := by simp +decide [s4]
  have hs4_16 : s4.regs 16 = s2.mem (base + 13) := by simp +decide [s4, s3]
  by_cases hfound1 : ∃ e₁, tbl.t1 (evalHash1 θ u) = some e₁ ∧ e₁.key = u
  · obtain ⟨e₁, ht1, hk1⟩ := hfound1
    have hs2_13_eq : s2.mem (base + 13) = 1 := by simp only [hs2_13, ht1, hk1, ↓reduceIte]
    have hs2_14_eq : s2.mem (base + 14) = e₁.idx := by simp only [hs2_14, ht1, hk1, ↓reduceIte]
    have hcond : ¬(Cond.eq 16 15 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_16, hs4_15, hs2_13_eq]
    set s5 := s4.set 15 0
    have e_nop : Exec w (.op (.const 15 0) : Code .exact 19) s4 s5 1 := Exec.const hfit_0
    have e_br := e_nop.branch_neg (pos := probeTableSlotCode evalHash2AtBaseCode 8) hcond
    have hall := e_init.seq (he_p1.seq (e_ld.seq (e_c0.seq e_br)))
    have hframe5 : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 13 → a ≠ base + 14 → s5.mem a = x.mem a := by
      intro a ha ha13 ha14
      exact (hs2_frame a ha ha13 ha14).trans (hs1_frame a ha13)
    have hhdr5 : HeaderConstsRep base n_max U s5.mem :=
      hhdr.congr fun k hk _ => hframe5 (base + k)
        (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega)
    refine ⟨s5, ⟨4 + (t_p1 + (3 + (1 + (1 + 2)))),
      by dsimp only [probeKeySteps]; omega, hall⟩,
      by simp +decide [s5, hs4_0], hhdr5, hs2_hash, hs2_seed.trans hs1_seed, ?_, hframe5⟩
    dsimp only [lookupEntry]
    simp only [ht1, hk1, ↓reduceIte]
    exact ⟨hs2_13_eq, hs2_14_eq⟩
  · have hs2_13_eq : s2.mem (base + 13) = 0 := by
      rw [hs2_13, hs1_13]
      cases ht1 : tbl.t1 (evalHash1 θ u) with
      | none => rfl
      | some e₁ =>
        have hne : e₁.key ≠ u := fun h => hfound1 ⟨e₁, ht1, h⟩
        simp only [hne, ↓reduceIte]
    have hcond : (Cond.eq 16 15 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_16, hs4_15, hs2_13_eq]
    have hs2_frame_x : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 13 → a ≠ base + 14 → s2.mem a = x.mem a :=
      fun a ha ha13 ha14 => (hs2_frame a ha ha13 ha14).trans (hs1_frame a ha13)
    obtain ⟨s5, ⟨t_p2, ht_p2, he_p2⟩, hs5_0, hs5_hash, hs5_seed, hs5_13, hs5_14, hs5_frame⟩ :=
      probeTableSlotCode_execWithin (tablePtrOff := 8) (tableBase := t2Base base n_max)
        (hashCode := evalHash2AtBaseCode) (θ := θ) (h := evalHash2 θ) (slotFn := tbl.t2)
        (ks := ks) (u := u) (x := s4)
        (fun d hd h0d h1d => evalHash2AtBaseCode_execWithin hd h0d h1d hw hfit_end)
        hs2_hash hs4_0 (by decide)
        (by rw [show s4.mem = s2.mem from rfl,
          hs2_frame_x _ (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega), hm8])
        (by dsimp only [t2Base, t1Base]; omega)
        (by dsimp only [t2Base, t1Base, hashBase, space, tableSize]; omega)
        (by rw [show s4.mem = s2.mem from rfl,
          hs2_frame_x _ (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega), hm9])
        (by rw [show s4.mem = s2.mem from rfl,
          hs2_frame_x _ (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega), hm11])
        (fun b => by
          rw [show s4.mem = s2.mem from rfl,
            hs2_frame_x _ (Or.inr (by
              dsimp only [t2Base, t1Base, hashBase]
              have := le_hashPairSpace n_max (tableBits n_max); omega))
              (by dsimp only [t2Base, t1Base, hashBase]
                  have := le_hashPairSpace n_max (tableBits n_max); omega)
              (by dsimp only [t2Base, t1Base, hashBase]
                  have := le_hashPairSpace n_max (tableBits n_max); omega)]
          exact hslots.2 b)
        (fun e he => htiv e (Or.inr ⟨evalHash2 θ u, he⟩))
        hlen_le
        (fun idx hlt => by
          rw [show s4.mem = s2.mem from rfl,
            hs2_frame_x _ (Or.inr (by
              dsimp only [keysBase, t2Base, t1Base, hashBase]
              have := le_hashPairSpace n_max (tableBits n_max); omega))
              (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                  have := le_hashPairSpace n_max (tableBits n_max); omega)
              (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                  have := le_hashPairSpace n_max (tableBits n_max); omega)]
          exact hmem_keys idx hlt)
        hfit_end
    have e_br := he_p2.branch_pos (neg := .op (.const 15 0)) hcond
    have hall := e_init.seq (he_p1.seq (e_ld.seq (e_c0.seq e_br)))
    have hframe5 : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 13 → a ≠ base + 14 → s5.mem a = x.mem a :=
      fun a ha ha13 ha14 => (hs5_frame a ha ha13 ha14).trans (hs2_frame_x a ha ha13 ha14)
    have hhdr5 : HeaderConstsRep base n_max U s5.mem :=
      hhdr.congr fun k hk _ => hframe5 (base + k)
        (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega)
    refine ⟨s5, ⟨4 + (t_p1 + (3 + (1 + (t_p2 + 1)))),
      by dsimp only [probeKeySteps]; omega, hall⟩,
      hs5_0, hhdr5, hs5_hash, hs5_seed.trans (hs2_seed.trans hs1_seed), ?_, hframe5⟩
    have hlookup_eq : lookupEntry (evalHash1 θ) (evalHash2 θ) tbl u =
        (match tbl.t2 (evalHash2 θ u) with
         | some e₂ => if e₂.key = u then some e₂ else none
         | none => none) := by
      dsimp only [lookupEntry]
      cases ht1 : tbl.t1 (evalHash1 θ u) with
      | none => rfl
      | some e₁ =>
        have hne : e₁.key ≠ u := fun h => hfound1 ⟨e₁, ht1, h⟩
        simp only [hne, ↓reduceIte]
        cases tbl.t2 (evalHash2 θ u) <;> rfl
    rw [hlookup_eq]
    cases ht2 : tbl.t2 (evalHash2 θ u) with
    | none =>
      rw [hs5_13, ht2]
      exact hs2_13_eq
    | some e₂ =>
      by_cases hk2 : e₂.key = u
      · simp only [hk2, ↓reduceIte, hs5_13, hs5_14, ht2, true_and]
      · simp only [hk2, ↓reduceIte, hs5_13, ht2]
        exact hs2_13_eq

/-- Positive branch of `getCode` when `foundFlag = 1`: loads `idx = mem[base + 14]`,
`valsBase = mem[base + 10]`, `v = mem[valsBase + idx]`, and sets `reg 2 = v + 1`. -/
@[expose]
def getFoundBranchCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 14)
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 16 16))
  (.seq (.op (.const 15 1))
        (.op (.exactBin .add 2 16 15))))))

/-- Lookup operation (`getCode`): stores `u.val` from `reg 3` into `mem[base + 11]`, runs
`probeKeyCode`, and writes `encodeOptionNat (s u)` into `reg 2`. -/
@[expose]
def getCode : Code .exact 19 :=
  .seq (storeHeaderCode 11 3)
  (.seq probeKeyCode
  (.seq (loadHeaderCode 16 13)
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 16)
    getFoundBranchCode
    (.op (.const 2 0))))))

/-- Step bound for `getCode`. -/
@[expose]
def getSteps (n_max U : ℕ) : ℕ :=
  probeKeySteps n_max U + 19

theorem getCode_execWithin {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    {u : Fin U} {x : Data 19}
    (hrep : RepWithKeys w base n_max U V ks s x)
    (h3 : x.regs 3 = u.val)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_V : Fits w V) :
    ∃ y : Data 19,
      ExecWithin w getCode x y (getSteps n_max U) ∧
      y.regs 2 = encodeOptionNat (s u) ∧
      RepWithKeys w base n_max U V ks s y ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  obtain ⟨hx_bdd, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ := hrep
  rcases hkv with ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_10 : Fits w 10 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_13 : Fits w 13 := hfit_end.of_le (by omega)
  have hfit_14 : Fits w 14 := hfit_end.of_le (by omega)
  have hfit_b10 : Fits w (base + 10) := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b13 : Fits w (base + 13) := hfit_end.of_le (by omega)
  have hfit_b14 : Fits w (base + 14) := hfit_end.of_le (by omega)
  have e_st11 := storeHeaderCode_exec (off := 11) (src := 3) (x := x)
    h0 (by decide) (by decide) hfit_11 hfit_b11
  set s1 := (((x.set 15 11).set 16 (base + 11)).write (base + 11) (x.regs 3))
  have hs1_frame : ∀ a, a ≠ base + 11 → s1.mem a = x.mem a :=
    fun a hne => Function.update_of_ne hne _ _
  have hs1_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_ge_hashBase fun a ha =>
      hs1_frame a (by dsimp only [hashBase] at ha; omega)
  have hs1_hash : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) x.mem) s1.mem :=
    hhash.congr_of_ge_hashBase fun a ha =>
      hs1_frame a (by dsimp only [hashBase] at ha; omega)
  have hs1_hdr : HeaderConstsRep base n_max U s1.mem :=
    hhdr.congr fun k hk _ => hs1_frame (base + k) (by omega)
  have hs1_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s1.mem :=
    hslots.congr
      (fun b _ => hs1_frame _ (by
        dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega))
      (fun b _ => hs1_frame _ (by
        dsimp only [t2Base, t1Base, hashBase]
        have := le_hashPairSpace n_max (tableBits n_max); omega))
  have htiv := pureReplay_tableIdxValid hnodup hreplay
  obtain ⟨s2, ⟨t_probe, ht_probe, he_probe⟩, hs2_0, hs2_hdr, hs2_hash, hs2_seed, hs2_lookup,
      hs2_frame⟩ :=
    probeKeyCode_execWithin (x := s1)
      hs1_hdr hs1_hash hs1_slots htiv hlen_le
      (fun idx hlt => by
        rw [hs1_frame _ (by
          dsimp only [keysBase, t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega)]
        exact (hkv_idx idx hlt).1)
      (by simp +decide [s1, h0])
      (by dsimp only [s1, Data.write, Data.set]; rw [Function.update_self]; exact h3)
      hw hfit_end
  have hs2_frame_x : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
      a ≠ base + 11 → a ≠ base + 13 → a ≠ base + 14 → s2.mem a = x.mem a :=
    fun a ha ha11 ha13 ha14 => (hs2_frame a ha ha13 ha14).trans (hs1_frame a ha11)
  have hs2_mod : Modifies (Block.mk base (space n_max)).footprint x.mem s2.mem := by
    intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
    have ha_out : a < hashBase base + 40 ∨ hashBase base + 47 ≤ a :=
      ha.imp (by dsimp only [hashBase]; omega) (by dsimp only [hashBase]; omega)
    exact hs2_frame_x a ha_out (by omega) (by omega) (by omega)
  have hs2_seed_x : extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    hs2_seed.trans hs1_seed
  have hs2_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s2.mem :=
    hslots.congr
      (fun b _ => hs2_frame_x _
        (Or.inr (by
          dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega))
        (by dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega))
      (fun b _ => hs2_frame_x _
        (Or.inr (by
          dsimp only [t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega))
        (by dsimp only [t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega))
  have hs2_kv : KeysValsRep base n_max U V ks s s2.mem :=
    KeysValsRep.congr ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩
      (hs2_frame_x _ (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega))
      (fun idx _ => hs2_frame_x _
        (Or.inr (by
          dsimp only [keysBase, t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega))
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega))
      (fun idx _ => hs2_frame_x _
        (Or.inr (by
          dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega))
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]
            have := le_hashPairSpace n_max (tableBits n_max); omega))
  have e_ld13 := loadHeaderCode_exec (dst := 16) (off := 13) (x := s2)
    hs2_0 (by decide) (by decide) hfit_13 hfit_b13
  set s3 := (s2.set 15 13).set 16 (s2.mem (base + 13))
  set s4 := s3.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  have hs4_0 : s4.regs 0 = base := by simp +decide [s4, s3, hs2_0]
  have hs4_15 : s4.regs 15 = 0 := by simp +decide [s4]
  have hs4_16 : s4.regs 16 = s2.mem (base + 13) := by simp +decide [s4, s3]
  by_cases hmem : u ∈ ks
  · obtain ⟨idx, hlt, hks_idx⟩ := List.mem_iff_getElem.mp hmem
    have hlkp := pureReplay_lookupEntry_of_mem hnodup hreplay hlt
    rw [hks_idx] at hlkp
    rw [hlkp] at hs2_lookup
    obtain ⟨hs2_13, hs2_14⟩ := hs2_lookup
    have hcond : (Cond.lt 15 16 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_15, hs4_16, hs2_13]
    have e_ld14 := loadHeaderCode_exec (dst := 17) (off := 14) (x := s4)
      hs4_0 (by decide) (by decide) hfit_14 hfit_b14
    set s5 := (s4.set 15 14).set 17 (s4.mem (base + 14))
    have hs5_0 : s5.regs 0 = base := by simp +decide [s5, hs4_0]
    have hs5_17 : s5.regs 17 = idx := by
      change s2.mem (base + 14) = idx; exact hs2_14
    have e_ld10 := loadHeaderCode_exec (dst := 16) (off := 10) (x := s5)
      hs5_0 (by decide) (by decide) hfit_10 hfit_b10
    set s6 := (s5.set 15 10).set 16 (s5.mem (base + 10))
    have hs6_16 : s6.regs 16 = valsBase base n_max := by
      change s2.mem (base + 10) = valsBase base n_max
      obtain ⟨_, _, _, _, _, _, _, _, _, hm10_s2⟩ := hs2_hdr
      exact hm10_s2
    have hs6_17 : s6.regs 17 = idx := hs5_17
    have hfit_vaddr : Fits w (valsBase base n_max + idx) :=
      hfit_end.of_le (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]; omega)
    set s7 := s6.set 16 (valsBase base n_max + idx)
    have e_add1 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s6 s7 1 :=
      ExactLog.exec_exactBin (by simp +decide [s6, hs6_16, hs6_17]) hfit_vaddr
    set s8 := s7.set 16 (s2.mem (valsBase base n_max + idx))
    have e_ldv : Exec w (.op (.load 16 16) : Code .exact 19) s7 s8 1 := by
      simpa +decide [s8, s7, s6, s5, s4, s3] using
        (Exec.load (B := .exact) (w := w) (d := 16) (a := 16) (x := s7))
    set s9 := s8.set 15 1
    have e_c1 : Exec w (.op (.const 15 1) : Code .exact 19) s8 s9 1 := Exec.const hfit_1
    have hs9_16 : s9.regs 16 = s2.mem (valsBase base n_max + idx) := by simp +decide [s9, s8]
    have hs9_15 : s9.regs 15 = 1 := by simp +decide [s9]
    have hsu : s u = some (s2.mem (valsBase base n_max + idx)) := by
      rw [← hks_idx]
      exact (hs2_kv.2.2.2.2.1 idx hlt).2
    have hv_lt : s2.mem (valsBase base n_max + idx) < V := hvb u _ hsu
    have hfit_res : Fits w (s2.mem (valsBase base n_max + idx) + 1) :=
      hfit_V.of_le (by omega)
    set s10 := s9.set 2 (s2.mem (valsBase base n_max + idx) + 1)
    have e_add2 : Exec w (.op (.exactBin .add 2 16 15) : Code .exact 19) s9 s10 1 :=
      ExactLog.exec_exactBin (by simp +decide [s9, hs9_16, hs9_15]) hfit_res
    have e_found : Exec w getFoundBranchCode s4 s10 (3 + (3 + (1 + (1 + (1 + 1))))) :=
      e_ld14.seq (e_ld10.seq (e_add1.seq (e_ldv.seq (e_c1.seq e_add2))))
    have e_br := e_found.branch_pos (neg := .op (.const 2 0)) hcond
    have hall : Exec w getCode x s10
        (3 + (t_probe + (3 + (1 + ((3 + (3 + (1 + (1 + (1 + 1))))) + 1))))) :=
      e_st11.seq (he_probe.seq (e_ld13.seq (e_c0.seq e_br)))
    have hwithin : ExecWithin w getCode x s10 (getSteps n_max U) :=
      ⟨_, by dsimp only [getSteps]; omega, hall⟩
    refine ⟨s10, hwithin, ?_, ?_, hs2_seed_x, hs2_mod⟩
    · simp only [s10, Data.set, Function.update_self, hsu, encodeOptionNat]
    · refine ⟨hwithin.bounded hx_bdd, by simp +decide [s10, s9, s8, s7, s6, hs5_0],
        hs2_hdr, ?_, hs2_kv, tbl, ?_, hs2_slots⟩
      · change HashPairRep (hashBase base) n_max U (tableBits n_max)
          (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem) s2.mem
        rw [hs2_seed_x]; exact hs2_hash
      · change pureReplay (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem))
          (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem))
          (maxEvictions n_max) ks = some tbl
        rw [hs2_seed_x]; exact hreplay
  · have hlkp := pureReplay_lookupEntry_of_notMem hnodup hreplay hmem
    rw [hlkp] at hs2_lookup
    have hcond : ¬(Cond.lt 15 16 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_15, hs4_16, hs2_lookup]
    set s5 := s4.set 2 0
    have e_c2 : Exec w (.op (.const 2 0) : Code .exact 19) s4 s5 1 := Exec.const hfit_0
    have e_br := e_c2.branch_neg (pos := getFoundBranchCode) hcond
    have hall : Exec w getCode x s5 (3 + (t_probe + (3 + (1 + (1 + 2))))) :=
      e_st11.seq (he_probe.seq (e_ld13.seq (e_c0.seq e_br)))
    have hwithin : ExecWithin w getCode x s5 (getSteps n_max U) :=
      ⟨_, by dsimp only [getSteps]; omega, hall⟩
    have hsu : s u = none := by
      rw [← Dictionary.notMem_dom_iff]
      exact fun h => hmem ((hdom_iff u).mpr h)
    refine ⟨s5, hwithin, ?_, ?_, hs2_seed_x, hs2_mod⟩
    · simp only [s5, Data.set, Function.update_self, hsu, encodeOptionNat]
    · refine ⟨hwithin.bounded hx_bdd, by simp +decide [s5, hs4_0],
        hs2_hdr, ?_, hs2_kv, tbl, ?_, hs2_slots⟩
      · change HashPairRep (hashBase base) n_max U (tableBits n_max)
          (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem) s2.mem
        rw [hs2_seed_x]; exact hs2_hash
      · change pureReplay (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem))
          (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem))
          (maxEvictions n_max) ks = some tbl
        rw [hs2_seed_x]; exact hreplay

/-! ### Section 4: Bounded cuckoo eviction loop (`putTableSlotCode`, `evictLoopCode`) -/

theorem TableIdxValid.putT1 {U m : ℕ} {h₁ : Fin U → Fin m} {ks : List (Fin U)}
    {tbl : PureTable U m} {e : SlotEntry U}
    (htiv : TableIdxValid ks tbl) (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key) :
    TableIdxValid ks (putT1 h₁ tbl e).1 := by
  rintro d (⟨b, hb⟩ | ⟨b, hb⟩)
  · dsimp only [CuckooHashing.putT1] at hb
    by_cases hbe : b = h₁ e.key
    · subst hbe
      rw [Function.update_self] at hb
      injection hb with hb
      subst hb
      exact he
    · rw [Function.update_of_ne hbe] at hb
      exact htiv d (Or.inl ⟨b, hb⟩)
  · exact htiv d (Or.inr ⟨b, hb⟩)

theorem TableIdxValid.putT2 {U m : ℕ} {h₂ : Fin U → Fin m} {ks : List (Fin U)}
    {tbl : PureTable U m} {e : SlotEntry U}
    (htiv : TableIdxValid ks tbl) (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key) :
    TableIdxValid ks (putT2 h₂ tbl e).1 := by
  rintro d (⟨b, hb⟩ | ⟨b, hb⟩)
  · exact htiv d (Or.inl ⟨b, hb⟩)
  · dsimp only [CuckooHashing.putT2] at hb
    by_cases hbe : b = h₂ e.key
    · subst hbe
      rw [Function.update_self] at hb
      injection hb with hb
      subst hb
      exact he
    · rw [Function.update_of_ne hbe] at hb
      exact htiv d (Or.inr ⟨b, hb⟩)

/-- Positive branch of `putTableSlotCode` when the target slot was occupied
(`reg 17 = e_old.idx + 1`): computes `e_old.idx = reg 17 - 1`, stores `e_old.idx` into
`mem[base + 12]`, loads `e_old.key.val = mem[keysBase + e_old.idx]`, stores it into
`mem[base + 11]`, and sets `mem[base + 16] ← 1`. -/
@[expose]
def putDisplacedBranchCode : Code .exact 19 :=
  .seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 17 16))
  (.seq (storeHeaderCode 11 17)
        (storeHeaderConstCode 16 1)))))))

theorem putDisplacedBranchCode_exec {w base n_max U : ℕ}
    {ks : List (Fin U)} {e_old : SlotEntry U} {x : Data 19}
    (h0 : x.regs 0 = base)
    (h17 : x.regs 17 = e_old.idx + 1)
    (hm9 : x.mem (base + 9) = keysBase base n_max)
    (hidx_lt : e_old.idx < ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hkey_idx : ks[e_old.idx]? = some e_old.key)
    (hmem_key : x.mem (keysBase base n_max + e_old.idx) = ks[e_old.idx].val)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w putDisplacedBranchCode x y 17 ∧
      y.regs 0 = base ∧
      y.mem (base + 11) = e_old.key.val ∧
      y.mem (base + 12) = e_old.idx ∧
      y.mem (base + 16) = 1 ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 16 → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_9 : Fits w 9 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_12 : Fits w 12 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b9 : Fits w (base + 9) := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b12 : Fits w (base + 12) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_idx : Fits w e_old.idx := hfit_end.of_le (by dsimp only [space]; omega)
  have hfit_kaddr : Fits w (keysBase base n_max + e_old.idx) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have hks_eq : ks[e_old.idx] = e_old.key := by
    rw [List.getElem?_eq_getElem hidx_lt] at hkey_idx
    exact Option.some.inj hkey_idx
  set s1 := x.set 15 1
  have e1 : Exec w (.op (.const 15 1) : Code .exact 19) x s1 1 := Exec.const hfit_1
  set s2 := s1.set 17 e_old.idx
  have e2 : Exec w (.op (.exactBin .sub 17 17 15) : Code .exact 19) s1 s2 1 :=
    ExactLog.exec_exactBin (by simp +decide [s1, h17]) hfit_idx
  have e3 := storeHeaderCode_exec (off := 12) (src := 17) (x := s2)
    (by simp +decide [s2, s1, h0]) (by decide) (by decide) hfit_12 hfit_b12
  set s3 := (((s2.set 15 12).set 16 (base + 12)).write (base + 12) (s2.regs 17))
  have hs3_9 : s3.mem (base + 9) = keysBase base n_max := by
    dsimp only [s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega)]
    exact hm9
  have hs3_kaddr : s3.mem (keysBase base n_max + e_old.idx) = e_old.key.val := by
    dsimp only [s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by
      dsimp only [keysBase, t2Base, t1Base, hashBase]
      have := le_hashPairSpace n_max (tableBits n_max); omega)]
    rw [hmem_key, hks_eq]
  have e4 := loadHeaderCode_exec (dst := 16) (off := 9) (x := s3)
    (by simp +decide [s3, s2, s1, h0]) (by decide) (by decide) hfit_9 hfit_b9
  set s4 := (s3.set 15 9).set 16 (s3.mem (base + 9))
  set s5 := s4.set 16 (keysBase base n_max + e_old.idx)
  have e5 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s4 s5 1 :=
    ExactLog.exec_exactBin
      (by rw [show s4.regs 16 = keysBase base n_max from hs3_9]; simp +decide [s4, s3, s2])
      hfit_kaddr
  set s6 := s5.set 17 e_old.key.val
  have e6 : Exec w (.op (.load 17 16) : Code .exact 19) s5 s6 1 := by
    simpa +decide [s6, s5, s4, hs3_kaddr] using
      (Exec.load (B := .exact) (w := w) (d := 17) (a := 16) (x := s5))
  have e7 := storeHeaderCode_exec (off := 11) (src := 17) (x := s6)
    (by simp +decide [s6, s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_11 hfit_b11
  set s7 := (((s6.set 15 11).set 16 (base + 11)).write (base + 11) (s6.regs 17))
  have e8 := storeHeaderConstCode_exec (off := 16) (val := 1) (x := s7)
    (by simp +decide [s7, s6, s5, s4, s3, s2, s1, h0]) hfit_1 hfit_16 hfit_b16
  set s8 := (((s7.set 18 1).set 15 16).set 16 (base + 16)).write (base + 16) 1
  have hall : Exec w putDisplacedBranchCode x s8 (1 + (1 + (3 + (3 + (1 + (1 + (3 + 4))))))) :=
    e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq e8))))))
  refine ⟨s8, hall, by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h0], ?_, ?_, ?_, ?_⟩
  · dsimp only [s8, s7, s6, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_self]
    rfl
  · dsimp only [s8, s7, s6, s5, s4, s3, s2, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    rfl
  · dsimp only [s8, Data.write, Data.set]
    rw [Function.update_self]
  · intro a ha11 ha12 ha16
    dsimp only [s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha16, Function.update_of_ne ha11, Function.update_of_ne ha12]

/-- Prefix of `putTableSlotCode`: evaluates `b = h(curKey)`, loads `oldSlot = mem[tableBase + b]`
into `reg 17`, and stores `curIdx + 1` into `mem[tableBase + b]`. -/
@[expose]
def putSlotSwapCode (hashCode : Code .exact 19) (tablePtrOff : ℕ) : Code .exact 19 :=
  .seq (loadHeaderCode 1 11)
  (.seq hashCode
  (.seq (loadHeaderCode 16 tablePtrOff)
  (.seq (.op (.exactBin .add 16 16 2))
  (.seq (.op (.load 17 16))
  (.seq (loadHeaderCode 18 12)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 18 18 15))
        (.op (.store 16 18)))))))))

/-- Places `(curKey = mem[base + 11], curIdx = mem[base + 12])` into slot `h(curKey)` of the table
whose base address is stored at `mem[base + tablePtrOff]`. If the slot was empty (`0`), sets
`mem[base + 16] ← 0`; if the slot held `e_old`, loads `e_old.key` into `mem[base + 11]`, `e_old.idx`
into `mem[base + 12]`, and sets `mem[base + 16] ← 1`. -/
@[expose]
def putTableSlotCode (hashCode : Code .exact 19) (tablePtrOff : ℕ) : Code .exact 19 :=
  .seq (putSlotSwapCode hashCode tablePtrOff)
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 17)
    putDisplacedBranchCode
    (storeHeaderConstCode 16 0)))

/-- Step bound for `putTableSlotCode`. -/
@[expose]
def putTableSlotSteps (n_max U : ℕ) : ℕ :=
  evalHashAtBaseSteps n_max U + 35

theorem putSlotSwapCode_execWithin {w base n_max U tablePtrOff tableBase : ℕ}
    {hashCode : Code .exact 19} {θ : Seed U (tableBits n_max)}
    {h : Fin U → Fin (2 ^ tableBits n_max)}
    {slotFn : Fin (2 ^ tableBits n_max) → Option (SlotEntry U)}
    {e : SlotEntry U} {x : Data 19}
    (hhash_exec : ∀ (d : Data 19),
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ d.mem →
      d.regs 0 = base → d.regs 1 = e.key.val →
      ∃ d', ExecWithin w hashCode d d' (evalHashAtBaseSteps n_max U) ∧
        d'.regs 0 = base ∧ d'.regs 2 = (h e.key).val ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max) θ d'.mem ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) d'.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) d.mem ∧
        (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → d'.mem a = d.mem a))
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (hptr_lt : tablePtrOff < 20)
    (hm_ptr : x.mem (base + tablePtrOff) = tableBase)
    (htb_ge : t1Base base n_max ≤ tableBase)
    (htb_le : tableBase + 2 ^ tableBits n_max ≤ keysBase base n_max)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (he_idx : e.idx < n_max)
    (hslots : ∀ b : Fin (2 ^ tableBits n_max),
      x.mem (tableBase + b.val) = encodeSlot (slotFn b))
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w (putSlotSwapCode hashCode tablePtrOff) x y
        (evalHashAtBaseSteps n_max U + 15) ∧
      y.regs 0 = base ∧
      y.regs 17 = encodeSlot (slotFn (h e.key)) ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (∀ b : Fin (2 ^ tableBits n_max),
        y.mem (tableBase + b.val) = encodeSlot (Function.update slotFn (h e.key) (some e) b)) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ tableBase + (h e.key).val → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_12 : Fits w 12 := hfit_end.of_le (by omega)
  have hfit_ptr : Fits w tablePtrOff := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b12 : Fits w (base + 12) := hfit_end.of_le (by omega)
  have hfit_bptr : Fits w (base + tablePtrOff) := hfit_end.of_le (by omega)
  have hfit_enc : Fits w (e.idx + 1) := hfit_end.of_le (by dsimp only [space]; omega)
  have hb_lt := (h e.key).isLt
  have hfit_slot : Fits w (tableBase + (h e.key).val) :=
    hfit_end.of_le (by
      dsimp only [keysBase, t2Base, t1Base, hashBase, space, tableSize] at *; omega)
  have e1 := loadHeaderCode_exec (dst := 1) (off := 11) (x := x)
    h0 (by decide) (by decide) hfit_11 hfit_b11
  set s1 := (x.set 15 11).set 1 (x.mem (base + 11))
  obtain ⟨s2, ⟨t_h, ht_h, he_h⟩, hs2_0, hs2_2, hs2_hash, hs2_seed, hs2_frame⟩ :=
    hhash_exec s1 hrep_hash (by simp +decide [s1, h0]) (by simp +decide [s1, hm11])
  have hs2_ptr : s2.mem (base + tablePtrOff) = tableBase := by
    rw [hs2_frame (base + tablePtrOff) (Or.inl (by dsimp only [hashBase]; omega))]
    exact hm_ptr
  have hs2_12 : s2.mem (base + 12) = e.idx := by
    rw [hs2_frame (base + 12) (Or.inl (by dsimp only [hashBase]; omega))]
    exact hm12
  have hs2_slot : s2.mem (tableBase + (h e.key).val) = encodeSlot (slotFn (h e.key)) := by
    rw [hs2_frame (tableBase + (h e.key).val) (Or.inr (by
      dsimp only [t1Base, hashBase] at *; omega))]
    exact hslots (h e.key)
  have e3 := loadHeaderCode_exec (dst := 16) (off := tablePtrOff) (x := s2)
    hs2_0 (by decide) (by decide) hfit_ptr hfit_bptr
  set s3 := (s2.set 15 tablePtrOff).set 16 (s2.mem (base + tablePtrOff))
  set s4 := s3.set 16 (tableBase + (h e.key).val)
  have e4 : Exec w (.op (.exactBin .add 16 16 2) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, hs2_ptr, hs2_2]) hfit_slot
  set s5 := s4.set 17 (encodeSlot (slotFn (h e.key)))
  have e5 : Exec w (.op (.load 17 16) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, hs2_slot] using
      (Exec.load (B := .exact) (w := w) (d := 17) (a := 16) (x := s4))
  have e6 := loadHeaderCode_exec (dst := 18) (off := 12) (x := s5)
    (by simp +decide [s5, s4, s3, hs2_0]) (by decide) (by decide) hfit_12 hfit_b12
  set s6 := (s5.set 15 12).set 18 (s5.mem (base + 12))
  set s7 := s6.set 15 1
  have e7 : Exec w (.op (.const 15 1) : Code .exact 19) s6 s7 1 := Exec.const hfit_1
  set s8 := s7.set 18 (e.idx + 1)
  have e8 : Exec w (.op (.exactBin .add 18 18 15) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin (by simp +decide [s7, s6, s5, s4, s3, hs2_12]) hfit_enc
  set s9 := s8.write (tableBase + (h e.key).val) (e.idx + 1)
  have e9 : Exec w (.op (.store 16 18) : Code .exact 19) s8 s9 1 := by
    simpa +decide [s9, s8, s7, s6, s5, s4] using
      (Exec.store (B := .exact) (w := w) (a := 16) (s := 18) (x := s8))
  have hall := e1.seq (he_h.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq e9)))))))
  have hs9_frame : ∀ a, a ≠ tableBase + (h e.key).val → s9.mem a = s2.mem a :=
    fun a hne => Function.update_of_ne hne _ _
  have hs9_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s9.mem := by
    rcases hs2_hash with ⟨⟨hM, hz1, hz2, h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
      ⟨hpoly, htab1, htab2⟩⟩
    have hin_hp : ∀ off < hashPairSpace n_max (tableBits n_max),
        s9.mem (hashBase base + off) = s2.mem (hashBase base + off) := fun off hoff =>
      hs9_frame (hashBase base + off) (by dsimp only [t1Base] at htb_ge; omega)
    have hsp_eq := hashPairSpace_eq n_max (tableBits n_max)
    have hz1_eq := z1Base_eq (hashBase base) n_max
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · simpa using (hin_hp 0 (by omega)).trans hM
    · exact (hin_hp 1 (by omega)).trans hz1
    · exact (hin_hp 2 (by omega)).trans hz2
    · exact (hin_hp 32 (by omega)).trans h0'
    · simpa [Nat.add_assoc] using (hin_hp 33 (by omega)).trans h1'
    · simpa [Nat.add_assoc] using (hin_hp 34 (by omega)).trans h2'
    · simpa [Nat.add_assoc] using (hin_hp 35 (by omega)).trans h3'
    · simpa [Nat.add_assoc] using (hin_hp 36 (by omega)).trans h4'
    · simpa [Nat.add_assoc] using (hin_hp 37 (by omega)).trans h5'
    · simpa [Nat.add_assoc] using (hin_hp 38 (by omega)).trans h6'
    · simpa [Nat.add_assoc] using (hin_hp 39 (by omega)).trans h7'
    · intro idx hidx
      rw [show hashBase base + 32 + 8 + 7 + idx = hashBase base + (47 + idx) by omega,
        hin_hp (47 + idx) (by omega),
        show hashBase base + (47 + idx) = hashBase base + 32 + 8 + 7 + idx by omega]
      exact hcl idx hidx
    · intro r j
      have hr := r.isLt; have hj := j.isLt
      rw [show hashBase base + 4 + 7 * r.val + j.val =
          hashBase base + (4 + 7 * r.val + j.val) by omega,
        hin_hp (4 + 7 * r.val + j.val) (by omega),
        show hashBase base + (4 + 7 * r.val + j.val) =
          hashBase base + 4 + 7 * r.val + j.val by omega]
      exact hpoly r j
    · intro i
      have hi := i.isLt
      have haddr : z1Base (hashBase base) n_max + i.val =
          hashBase base + (47 + 2 ^ (2 * KWise.chunkBits n_max) + i.val) := by
        rw [hz1_eq]; omega
      rw [haddr, hin_hp _ (by omega), ← haddr]; exact htab1 i
    · intro i
      have hi := i.isLt
      have haddr : z2Base (hashBase base) n_max (tableBits n_max) + i.val =
          hashBase base + (47 + 2 ^ (2 * KWise.chunkBits n_max) + 2 ^ tableBits n_max + i.val) := by
        dsimp only [z2Base]; rw [hz1_eq]; omega
      rw [haddr, hin_hp _ (by omega), ← haddr]; exact htab2 i
  have hs9_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s9.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem := by
    have hpoly : Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 s9.mem =
        Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 s2.mem := by
      funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _)
        (hs9_frame (hashBase base + 4 + i.val) (by dsimp only [t1Base] at htb_ge; omega))
    have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) s9.mem =
        Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) s2.mem := by
      funext i; have hi := i.isLt
      have hz1 : z1Base (hashBase base) n_max + 2 * 2 ^ tableBits n_max =
          hashBase base + hashPairSpace n_max (tableBits n_max) := by
        dsimp only [z1Base, hashPairSpace]; omega
      dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _)
        (hs9_frame (z1Base (hashBase base) n_max + i.val) (by
          dsimp only [t1Base] at htb_ge; omega))
    dsimp only [extractSeed]
    rw [hpoly, htab]
  refine ⟨s9, ⟨3 + (t_h + (3 + (1 + (1 + (3 + (1 + (1 + 1))))))), by omega, hall⟩,
    by simp +decide [s9, s8, s7, s6, s5, s4, s3, hs2_0],
    by simp +decide [s9, s8, s7, s6, s5],
    hs9_hash, hs9_seed.trans hs2_seed, ?_, ?_⟩
  · intro b
    by_cases hb : b = h e.key
    · subst hb
      rw [Function.update_self]
      dsimp only [s9, Data.write, encodeSlot]
      rw [Function.update_self]
    · rw [Function.update_of_ne hb]
      have hne_addr : tableBase + b.val ≠ tableBase + (h e.key).val :=
        fun h => hb (Fin.ext (by omega))
      rw [hs9_frame _ hne_addr,
        hs2_frame _ (Or.inr (by dsimp only [t1Base, hashBase] at *; omega))]
      exact hslots b
  · intro a ha hne
    exact (hs9_frame a hne).trans (hs2_frame a ha)

theorem putTableSlotCode_execWithin {w base n_max U tablePtrOff tableBase : ℕ}
    {hashCode : Code .exact 19} {θ : Seed U (tableBits n_max)}
    {h : Fin U → Fin (2 ^ tableBits n_max)}
    {slotFn : Fin (2 ^ tableBits n_max) → Option (SlotEntry U)}
    {ks : List (Fin U)} {e : SlotEntry U} {x : Data 19}
    (hhash_exec : ∀ (d : Data 19),
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ d.mem →
      d.regs 0 = base → d.regs 1 = e.key.val →
      ∃ d', ExecWithin w hashCode d d' (evalHashAtBaseSteps n_max U) ∧
        d'.regs 0 = base ∧ d'.regs 2 = (h e.key).val ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max) θ d'.mem ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) d'.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) d.mem ∧
        (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) → d'.mem a = d.mem a))
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (h0 : x.regs 0 = base)
    (hptr_lt : tablePtrOff < 20)
    (hm_ptr : x.mem (base + tablePtrOff) = tableBase)
    (htb_ge : t1Base base n_max ≤ tableBase)
    (htb_le : tableBase + 2 ^ tableBits n_max ≤ keysBase base n_max)
    (hm9 : x.mem (base + 9) = keysBase base n_max)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (he_idx : e.idx < n_max)
    (hslots : ∀ b : Fin (2 ^ tableBits n_max),
      x.mem (tableBase + b.val) = encodeSlot (slotFn b))
    (hvalid_slot : ∀ e_old, slotFn (h e.key) = some e_old →
      e_old.idx < ks.length ∧ ks[e_old.idx]? = some e_old.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base n_max + idx) = ks[idx].val)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w (putTableSlotCode hashCode tablePtrOff) x y (putTableSlotSteps n_max U) ∧
      y.regs 0 = base ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (∀ b : Fin (2 ^ tableBits n_max),
        y.mem (tableBase + b.val) = encodeSlot (Function.update slotFn (h e.key) (some e) b)) ∧
      (match slotFn (h e.key) with
       | none => y.mem (base + 16) = 0
       | some e_old =>
         y.mem (base + 16) = 1 ∧ y.mem (base + 11) = e_old.key.val ∧
           y.mem (base + 12) = e_old.idx) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 16 →
        a ≠ tableBase + (h e.key).val → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  obtain ⟨s1, ⟨t_sw, ht_sw, he_sw⟩, hs1_0, hs1_17, hs1_hash, hs1_seed, hs1_slots, hs1_frame⟩ :=
    putSlotSwapCode_execWithin hhash_exec hrep_hash h0 hptr_lt hm_ptr htb_ge htb_le
      hm11 hm12 he_idx hslots hfit_end
  set s2 := s1.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s1 s2 1 := Exec.const hfit_0
  have hs2_0 : s2.regs 0 = base := by simp +decide [s2, hs1_0]
  have hs2_15 : s2.regs 15 = 0 := by simp +decide [s2]
  have hs2_17 : s2.regs 17 = encodeSlot (slotFn (h e.key)) := by simp +decide [s2, hs1_17]
  cases hold : slotFn (h e.key) with
  | none =>
    have hcond : ¬(Cond.lt 15 17 : Cond 19).Holds s2 := by
      simp [Cond.Holds, hs2_15, hs2_17, hold, encodeSlot]
    have e_st0 := storeHeaderConstCode_exec (off := 16) (val := 0) (x := s2)
      hs2_0 hfit_0 hfit_16 hfit_b16
    set s3 := (((s2.set 18 0).set 15 16).set 16 (base + 16)).write (base + 16) 0
    have e_br := e_st0.branch_neg (pos := putDisplacedBranchCode) hcond
    have hall := he_sw.seq (e_c0.seq e_br)
    have hs3_frame : ∀ a, a ≠ base + 16 → s3.mem a = s1.mem a :=
      fun a ha => Function.update_of_ne ha _ _
    have hs3_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s3.mem :=
      hs1_hash.congr_of_ge_hashBase fun a ha =>
        hs3_frame a (by dsimp only [hashBase] at ha; omega)
    have hs3_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s3.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem :=
      extractSeed_congr_of_ge_hashBase fun a ha =>
        hs3_frame a (by dsimp only [hashBase] at ha; omega)
    refine ⟨s3, ⟨t_sw + (1 + (4 + 2)), by dsimp only [putTableSlotSteps]; omega, hall⟩,
      by simp +decide [s3, hs2_0], hs3_hash, hs3_seed.trans hs1_seed, ?_, ?_, ?_⟩
    · intro b
      rw [hs3_frame (tableBase + b.val) (by dsimp only [t1Base, hashBase] at *; omega)]
      exact hs1_slots b
    · dsimp only [s3, Data.write, Data.set]
      rw [Function.update_self]
    · intro a ha _ _ ha16 hne_slot
      exact (hs3_frame a ha16).trans (hs1_frame a ha hne_slot)
  | some e_old =>
    obtain ⟨hidx_lt, hkey_idx⟩ := hvalid_slot e_old hold
    have hcond : (Cond.lt 15 17 : Cond 19).Holds s2 := by
      simp [Cond.Holds, hs2_15, hs2_17, hold, encodeSlot]
    have hs2_9 : s2.mem (base + 9) = keysBase base n_max := by
      change s1.mem (base + 9) = keysBase base n_max
      rw [hs1_frame (base + 9) (Or.inl (by dsimp only [hashBase]; omega))
        (by dsimp only [t1Base, hashBase] at *; omega)]
      exact hm9
    have hs2_key : s2.mem (keysBase base n_max + e_old.idx) = ks[e_old.idx].val := by
      change s1.mem (keysBase base n_max + e_old.idx) = ks[e_old.idx].val
      rw [hs1_frame (keysBase base n_max + e_old.idx)
        (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase] at *; omega))
        (by have := (h e.key).isLt; omega)]
      exact hmem_keys e_old.idx hidx_lt
    obtain ⟨s3, he_disp, hs3_0, hs3_11, hs3_12, hs3_16, hs3_frame⟩ :=
      putDisplacedBranchCode_exec (x := s2) hs2_0
        (by rw [hs2_17, hold, encodeSlot]) hs2_9 hidx_lt hlen_le hkey_idx hs2_key hfit_end
    have e_br := he_disp.branch_pos (neg := storeHeaderConstCode 16 0) hcond
    have hall := he_sw.seq (e_c0.seq e_br)
    have hs3_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s3.mem :=
      hs1_hash.congr_of_ge_hashBase fun a ha =>
        hs3_frame a (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
    have hs3_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s3.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem :=
      extractSeed_congr_of_ge_hashBase fun a ha =>
        hs3_frame a (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
    refine ⟨s3, ⟨t_sw + (1 + (17 + 1)), by dsimp only [putTableSlotSteps]; omega, hall⟩,
      hs3_0, hs3_hash, hs3_seed.trans hs1_seed, ?_, ⟨hs3_16, hs3_11, hs3_12⟩, ?_⟩
    · intro b
      rw [hs3_frame (tableBase + b.val)
        (by dsimp only [t1Base, hashBase] at *; omega)
        (by dsimp only [t1Base, hashBase] at *; omega)
        (by dsimp only [t1Base, hashBase] at *; omega)]
      exact hs1_slots b
    · intro a ha ha11 ha12 ha16 hne_slot
      exact (hs3_frame a ha11 ha12 ha16).trans (hs1_frame a ha hne_slot)

/-- Decrements `remFuel = mem[base + 15]` by `1`. -/
@[expose]
def decHeader15Code : Code .exact 19 :=
  .seq (loadHeaderCode 17 15)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .sub 17 17 15))
        (storeHeaderCode 15 17)))

theorem decHeader15Code_exec {w base fuel : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm15 : x.mem (base + 15) = fuel + 1)
    (hfit_15 : Fits w 15)
    (hfit_b15 : Fits w (base + 15))
    (hfit_fuel : Fits w fuel) :
    ∃ y : Data 19,
      Exec w decHeader15Code x y 8 ∧
      y.regs 0 = base ∧
      y.mem (base + 15) = fuel ∧
      (∀ a, a ≠ base + 15 → y.mem a = x.mem a) := by
  have hfit_1 : Fits w 1 := hfit_15.of_le (by decide)
  have e1 := loadHeaderCode_exec (dst := 17) (off := 15) (x := x)
    h0 (by decide) (by decide) hfit_15 hfit_b15
  set s1 := (x.set 15 15).set 17 (x.mem (base + 15))
  set s2 := s1.set 15 1
  have e2 : Exec w (.op (.const 15 1) : Code .exact 19) s1 s2 1 := Exec.const hfit_1
  set s3 := s2.set 17 fuel
  have e3 : Exec w (.op (.exactBin .sub 17 17 15) : Code .exact 19) s2 s3 1 :=
    ExactLog.exec_exactBin (by simp +decide [s2, s1, hm15]) hfit_fuel
  have e4 := storeHeaderCode_exec (off := 15) (src := 17) (x := s3)
    (by simp +decide [s3, s2, s1, h0]) (by decide) (by decide) hfit_15 hfit_b15
  set s4 := (((s3.set 15 15).set 16 (base + 15)).write (base + 15) (s3.regs 17))
  have hall : Exec w decHeader15Code x s4 (3 + (1 + (1 + 3))) :=
    e1.seq (e2.seq (e3.seq e4))
  refine ⟨s4, hall, by simp +decide [s4, s3, s2, s1, h0], ?_, ?_⟩
  · dsimp only [s4, s3, Data.write, Data.set]
    rw [Function.update_self]
    rfl
  · intro a ha
    dsimp only [s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha]

/-- Body of one two-table displacement round (`evictRoundBodyCode`):
places the active displaced entry in `T₁`; if `T₁` displaced an entry (`mem[base + 16] > 0`),
places that entry in `T₂`; then decrements `remFuel = mem[base + 15]` by `1`. -/
@[expose]
def evictRoundBodyCode : Code .exact 19 :=
  .seq (putTableSlotCode evalHash1AtBaseCode 7)
  (.seq (loadHeaderCode 16 16)
  (.seq (.op (.const 15 0))
  (.seq (.branch (.lt 15 16)
          (putTableSlotCode evalHash2AtBaseCode 8)
          (.op (.const 15 0)))
        decHeader15Code)))

/-- Step bound for `evictRoundBodyCode`. -/
@[expose]
def evictRoundSteps (n_max U : ℕ) : ℕ :=
  2 * putTableSlotSteps n_max U + 15

theorem evictRoundBodyCode_execWithin {w base n_max U fuel : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (hm15 : x.mem (base + 15) = fuel + 1)
    (hfit_fuel : Fits w fuel)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    let res := pureEvictRound (evalHash1 θ) (evalHash2 θ) tbl e
    ∃ y : Data 19,
      ExecWithin w evictRoundBodyCode x y (evictRoundSteps n_max U) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base n_max U y.mem ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      TableSlotsRep (t1Base base n_max) (t2Base base n_max) res.1 y.mem ∧
      TableIdxValid ks res.1 ∧
      y.mem (base + 15) = fuel ∧
      (match res.2 with
       | none => y.mem (base + 16) = 0
       | some e' =>
         y.mem (base + 16) = 1 ∧ y.mem (base + 11) = e'.key.val ∧ y.mem (base + 12) = e'.idx ∧
           e'.idx < ks.length ∧ ks[e'.idx]? = some e'.key) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a) := by
  intro res
  have ⟨_, _, _, _, _, _, hm7, hm8, hm9, _⟩ := hhdr
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hpowM_pos : 0 < 2 ^ tableBits n_max := Nat.two_pow_pos _
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_15 : Fits w 15 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b15 : Fits w (base + 15) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  obtain ⟨s1, ⟨t_p1, ht_p1, he_p1⟩, hs1_0, hs1_hash, hs1_seed, hs1_t1, hs1_out, hs1_frame⟩ :=
    putTableSlotCode_execWithin (tablePtrOff := 7) (tableBase := t1Base base n_max)
      (hashCode := evalHash1AtBaseCode) (θ := θ) (h := evalHash1 θ) (slotFn := tbl.t1)
      (ks := ks) (e := e) (x := x)
      (fun d hd h0d h1d => evalHash1AtBaseCode_execWithin hd h0d h1d hw hfit_end)
      hrep_hash h0 (by decide) hm7 (le_rfl)
      (by dsimp only [keysBase, t2Base, t1Base, tableSize]; omega)
      hm9 hm11 hm12 (by omega) hslots.1
      (fun e₁ he₁ => htiv e₁ (Or.inl ⟨evalHash1 θ e.key, he₁⟩))
      hlen_le hmem_keys hfit_end
  have htiv1 : TableIdxValid ks (putT1 (evalHash1 θ) tbl e).1 := htiv.putT1 he
  have hs1_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max)
      (putT1 (evalHash1 θ) tbl e).1 s1.mem := by
    refine ⟨hs1_t1, fun b => ?_⟩
    have hb_lt := b.isLt
    have h1_lt := (evalHash1 θ e.key).isLt
    rw [hs1_frame (t2Base base n_max + b.val)
      (Or.inr (by dsimp only [t2Base, t1Base, hashBase]; omega))
      (by dsimp only [t2Base, t1Base, hashBase]; omega)
      (by dsimp only [t2Base, t1Base, hashBase]; omega)
      (by dsimp only [t2Base, t1Base, hashBase]; omega)
      (by dsimp only [t2Base, t1Base, tableSize]; omega)]
    exact hslots.2 b
  have e_ld16 := loadHeaderCode_exec (dst := 16) (off := 16) (x := s1)
    hs1_0 (by decide) (by decide) hfit_16 hfit_b16
  set s2 := (s1.set 15 16).set 16 (s1.mem (base + 16))
  set s3 := s2.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s2 s3 1 := Exec.const hfit_0
  have hs3_0 : s3.regs 0 = base := by simp +decide [s3, s2, hs1_0]
  have hs3_15 : s3.regs 15 = 0 := by simp +decide [s3]
  have hs3_16 : s3.regs 16 = s1.mem (base + 16) := by simp +decide [s3, s2]
  cases hold1 : tbl.t1 (evalHash1 θ e.key) with
  | none =>
    rw [hold1] at hs1_out
    have hcond : ¬(Cond.lt 15 16 : Cond 19).Holds s3 := by
      simp [Cond.Holds, hs3_15, hs3_16, hs1_out]
    set s4 := s3.set 15 0
    have e_nop : Exec w (.op (.const 15 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
    have e_br := e_nop.branch_neg (pos := putTableSlotCode evalHash2AtBaseCode 8) hcond
    have hs4_15_mem : s4.mem (base + 15) = fuel + 1 := by
      change s1.mem (base + 15) = fuel + 1
      rw [hs1_frame (base + 15) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega)
        (by dsimp only [t1Base, hashBase]; omega)]
      exact hm15
    obtain ⟨s5, he_dec, hs5_0, hs5_15, hs5_frame⟩ :=
      decHeader15Code_exec (x := s4) (by simp +decide [s4, hs3_0]) hs4_15_mem
        hfit_15 hfit_b15 hfit_fuel
    have hall := he_p1.seq (e_ld16.seq (e_c0.seq (e_br.seq he_dec)))
    have hframe5 : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → s5.mem a = x.mem a := by
      intro a ha ha11 ha12 ha15 ha16 hnot_tbl
      have h1_lt := (evalHash1 θ e.key).isLt
      have hne_slot1 : a ≠ t1Base base n_max + (evalHash1 θ e.key).val := by
        dsimp only [keysBase, t2Base, t1Base, tableSize] at hnot_tbl ⊢; omega
      exact (hs5_frame a ha15).trans (hs1_frame a ha ha11 ha12 ha16 hne_slot1)
    have hhdr5 : HeaderConstsRep base n_max U s5.mem :=
      hhdr.congr fun k hk _ => hframe5 (base + k)
        (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega))
    have hs5_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s5.mem :=
      hs1_hash.congr_of_ge_hashBase fun a ha =>
        hs5_frame a (by dsimp only [hashBase] at ha; omega)
    have hs5_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s5.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem :=
      extractSeed_congr_of_ge_hashBase fun a ha =>
        hs5_frame a (by dsimp only [hashBase] at ha; omega)
    have hs5_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max)
        (putT1 (evalHash1 θ) tbl e).1 s5.mem :=
      hs1_slots.congr
        (fun b _ => hs5_frame _ (by dsimp only [t1Base, hashBase]; omega))
        (fun b _ => hs5_frame _ (by dsimp only [t2Base, t1Base, hashBase]; omega))
    have hres_eq : res = ((putT1 (evalHash1 θ) tbl e).1, none) := by
      dsimp only [res, pureEvictRound, putT1]
      rw [hold1]
    rw [hres_eq]
    refine ⟨s5, ⟨t_p1 + (3 + (1 + ((1 + 2) + 8))), by dsimp only [evictRoundSteps]; omega, hall⟩,
      hs5_0, hhdr5, hs5_hash, hs5_seed.trans hs1_seed, hs5_slots, htiv1, hs5_15, ?_, hframe5⟩
    exact (hs5_frame (base + 16) (by omega)).trans hs1_out
  | some e₁ =>
    rw [hold1] at hs1_out
    obtain ⟨hs1_16, hs1_11, hs1_12⟩ := hs1_out
    have he₁_valid : e₁.idx < ks.length ∧ ks[e₁.idx]? = some e₁.key :=
      htiv e₁ (Or.inl ⟨evalHash1 θ e.key, hold1⟩)
    have hcond : (Cond.lt 15 16 : Cond 19).Holds s3 := by
      simp [Cond.Holds, hs3_15, hs3_16, hs1_16]
    have h1_lt := (evalHash1 θ e.key).isLt
    have hs3_8 : s3.mem (base + 8) = t2Base base n_max := by
      change s1.mem (base + 8) = t2Base base n_max
      rw [hs1_frame (base + 8) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by dsimp only [t1Base, hashBase]; omega)]
      exact hm8
    have hs3_9 : s3.mem (base + 9) = keysBase base n_max := by
      change s1.mem (base + 9) = keysBase base n_max
      rw [hs1_frame (base + 9) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by dsimp only [t1Base, hashBase]; omega)]
      exact hm9
    obtain ⟨s4, ⟨t_p2, ht_p2, he_p2⟩, hs4_0, hs4_hash, hs4_seed, hs4_t2, hs4_out, hs4_frame⟩ :=
      putTableSlotCode_execWithin (tablePtrOff := 8) (tableBase := t2Base base n_max)
        (hashCode := evalHash2AtBaseCode) (θ := θ) (h := evalHash2 θ)
        (slotFn := (putT1 (evalHash1 θ) tbl e).1.t2)
        (ks := ks) (e := e₁) (x := s3)
        (fun d hd h0d h1d => evalHash2AtBaseCode_execWithin hd h0d h1d hw hfit_end)
        hs1_hash hs3_0 (by decide) hs3_8
        (by dsimp only [t2Base, t1Base]; omega)
        (by dsimp only [keysBase, t2Base, tableSize]; omega)
        hs3_9 hs1_11 hs1_12 (by omega) hs1_slots.2
        (fun e₂ he₂ => htiv1 e₂ (Or.inr ⟨evalHash2 θ e₁.key, he₂⟩))
        hlen_le
        (fun idx hlt => by
          change s1.mem (keysBase base n_max + idx) = ks[idx].val
          rw [hs1_frame (keysBase base n_max + idx)
            (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
            (by dsimp only [keysBase, t2Base, t1Base, tableSize]; omega)]
          exact hmem_keys idx hlt)
        hfit_end
    have e_br := he_p2.branch_pos (neg := .op (.const 15 0)) hcond
    have h2_lt := (evalHash2 θ e₁.key).isLt
    have hs4_15_mem : s4.mem (base + 15) = fuel + 1 := by
      rw [hs4_frame (base + 15) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)]
      change s1.mem (base + 15) = fuel + 1
      rw [hs1_frame (base + 15) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega)
        (by dsimp only [t1Base, hashBase]; omega)]
      exact hm15
    obtain ⟨s5, he_dec, hs5_0, hs5_15, hs5_frame⟩ :=
      decHeader15Code_exec (x := s4) hs4_0 hs4_15_mem hfit_15 hfit_b15 hfit_fuel
    have hall := he_p1.seq (e_ld16.seq (e_c0.seq (e_br.seq he_dec)))
    have hframe5 : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → s5.mem a = x.mem a := by
      intro a ha ha11 ha12 ha15 ha16 hnot_tbl
      have hne_slot1 : a ≠ t1Base base n_max + (evalHash1 θ e.key).val := by
        dsimp only [keysBase, t2Base, t1Base, tableSize] at hnot_tbl ⊢; omega
      have hne_slot2 : a ≠ t2Base base n_max + (evalHash2 θ e₁.key).val := by
        dsimp only [keysBase, t2Base, t1Base, tableSize] at hnot_tbl ⊢; omega
      exact (hs5_frame a ha15).trans
        ((hs4_frame a ha ha11 ha12 ha16 hne_slot2).trans
          (hs1_frame a ha ha11 ha12 ha16 hne_slot1))
    have hhdr5 : HeaderConstsRep base n_max U s5.mem :=
      hhdr.congr fun k hk _ => hframe5 (base + k)
        (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega))
    have hs5_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s5.mem :=
      hs4_hash.congr_of_ge_hashBase fun a ha =>
        hs5_frame a (by dsimp only [hashBase] at ha; omega)
    have hs5_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s5.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem :=
      extractSeed_congr_of_ge_hashBase fun a ha =>
        hs5_frame a (by dsimp only [hashBase] at ha; omega)
    have hres_eq : res = putT2 (evalHash2 θ) (putT1 (evalHash1 θ) tbl e).1 e₁ := by
      dsimp only [res, pureEvictRound, putT1]
      rw [hold1]
    rw [hres_eq]
    have htiv2 : TableIdxValid ks (putT2 (evalHash2 θ) (putT1 (evalHash1 θ) tbl e).1 e₁).1 :=
      htiv1.putT2 he₁_valid
    have hs5_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max)
        (putT2 (evalHash2 θ) (putT1 (evalHash1 θ) tbl e).1 e₁).1 s5.mem := by
      refine ⟨fun b => ?_, fun b => ?_⟩
      · have hb_lt := b.isLt
        rw [hs5_frame (t1Base base n_max + b.val) (by dsimp only [t1Base, hashBase]; omega),
          hs4_frame (t1Base base n_max + b.val)
            (Or.inr (by dsimp only [t1Base, hashBase]; omega))
            (by dsimp only [t1Base, hashBase]; omega)
            (by dsimp only [t1Base, hashBase]; omega)
            (by dsimp only [t1Base, hashBase]; omega)
            (by dsimp only [t2Base, t1Base, tableSize]; omega)]
        exact hs1_slots.1 b
      · rw [hs5_frame (t2Base base n_max + b.val) (by dsimp only [t2Base, t1Base, hashBase]; omega)]
        exact hs4_t2 b
    refine ⟨s5, ⟨t_p1 + (3 + (1 + ((t_p2 + 1) + 8))), by dsimp only [evictRoundSteps]; omega, hall⟩,
      hs5_0, hhdr5, hs5_hash, hs5_seed.trans (hs4_seed.trans hs1_seed), hs5_slots, htiv2, hs5_15,
      ?_, hframe5⟩
    dsimp only [putT2]
    cases hold2 : (putT1 (evalHash1 θ) tbl e).1.t2 (evalHash2 θ e₁.key) with
    | none =>
      rw [hold2] at hs4_out
      exact (hs5_frame (base + 16) (by omega)).trans hs4_out
    | some e₂ =>
      rw [hold2] at hs4_out
      obtain ⟨hs4_16, hs4_11, hs4_12⟩ := hs4_out
      have he₂_valid : e₂.idx < ks.length ∧ ks[e₂.idx]? = some e₂.key :=
        htiv1 e₂ (Or.inr ⟨evalHash2 θ e₁.key, hold2⟩)
      exact ⟨(hs5_frame (base + 16) (by omega)).trans hs4_16,
        (hs5_frame (base + 11) (by omega)).trans hs4_11,
        (hs5_frame (base + 12) (by omega)).trans hs4_12,
        he₂_valid.1, he₂_valid.2⟩

/-- Synchronizes the loop continuation condition of `evictLoopCode`:
computes `reg 17 = mem[base + 16] * mem[base + 15]` (`activeFlag * remFuel`) and `reg 18 = 0`, so
that `(Cond.lt 18 17).Holds` iff `activeFlag = 1 ∧ 0 < remFuel`. -/
@[expose]
def syncEvictCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 16)
  (.seq (loadHeaderCode 17 15)
  (.seq (.op (.exactBin .mul 17 16 17))
        (.op (.const 18 0))))

theorem syncEvictCondCode_exec {w base n_max act fuel : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm15 : x.mem (base + 15) = fuel)
    (hm16 : x.mem (base + 16) = act)
    (hact : act ≤ 1)
    (hfit_fuel : Fits w fuel)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w syncEvictCondCode x y 8 ∧
      y.regs 0 = base ∧
      y.regs 17 = act * fuel ∧
      y.regs 18 = 0 ∧
      y.mem = x.mem := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_15 : Fits w 15 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b15 : Fits w (base + 15) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_prod : Fits w (act * fuel) :=
    hfit_fuel.of_le (by
      calc act * fuel ≤ 1 * fuel := Nat.mul_le_mul_right fuel hact
      _ = fuel := Nat.one_mul fuel)
  have e1 := loadHeaderCode_exec (dst := 16) (off := 16) (x := x)
    h0 (by decide) (by decide) hfit_16 hfit_b16
  set s1 := (x.set 15 16).set 16 (x.mem (base + 16))
  have e2 := loadHeaderCode_exec (dst := 17) (off := 15) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_15 hfit_b15
  set s2 := (s1.set 15 15).set 17 (s1.mem (base + 15))
  set s3 := s2.set 17 (act * fuel)
  have e3 : Exec w (.op (.exactBin .mul 17 16 17) : Code .exact 19) s2 s3 1 :=
    ExactLog.exec_exactBin (by simp +decide [s2, s1, hm15, hm16]) hfit_prod
  set s4 := s3.set 18 0
  have e4 : Exec w (.op (.const 18 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  have hall : Exec w syncEvictCondCode x s4 (3 + (3 + (1 + 1))) :=
    e1.seq (e2.seq (e3.seq e4))
  exact ⟨s4, hall, by simp +decide [s4, s3, s2, s1, h0],
    by simp +decide [s4, s3], by simp +decide [s4], rfl⟩

/-- Inner loop of `evictLoopCode`: repeats `evictRoundBodyCode` followed by `syncEvictCondCode`
while `0 < reg 17` (`activeFlag = 1 ∧ 0 < remFuel`). -/
@[expose]
def evictLoopInner : Code .exact 19 :=
  .loop (.lt 18 17) (.seq evictRoundBodyCode syncEvictCondCode)

/-- Bounded cuckoo eviction loop (`evictLoopCode`): executes up to `remFuel = mem[base + 15]`
displacement rounds starting from `(curKey = mem[base + 11], curIdx = mem[base + 12])` with
`activeFlag = mem[base + 16] = 1`. -/
@[expose]
def evictLoopCode : Code .exact 19 :=
  .seq syncEvictCondCode evictLoopInner

/-- Step bound per displacement round in `evictLoopInner` (including `syncEvictCondCode` and loop
branch overhead). -/
@[expose]
def evictIterSteps (n_max U : ℕ) : ℕ :=
  evictRoundSteps n_max U + 10

theorem evictLoopInner_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)}
    (hlen_le : ks.length ≤ n_max)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∀ (fuel : ℕ) {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19},
      HeaderConstsRep base n_max U x.mem →
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem →
      TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem →
      TableIdxValid ks tbl →
      (e.idx < ks.length ∧ ks[e.idx]? = some e.key) →
      (∀ idx (hlt : idx < ks.length), x.mem (keysBase base n_max + idx) = ks[idx].val) →
      x.regs 0 = base →
      x.regs 17 = fuel →
      x.regs 18 = 0 →
      x.mem (base + 11) = e.key.val →
      x.mem (base + 12) = e.idx →
      x.mem (base + 15) = fuel →
      x.mem (base + 16) = 1 →
      Fits w fuel →
      ∃ y : Data 19,
        ExecWithin w evictLoopInner x y
          (evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl e * evictIterSteps n_max U + 2) ∧
        y.regs 0 = base ∧
        HeaderConstsRep base n_max U y.mem ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
        (match pureEvict (evalHash1 θ) (evalHash2 θ) fuel tbl e with
         | some tbl' =>
           y.mem (base + 16) = 0 ∧
           TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl' y.mem ∧
           TableIdxValid ks tbl'
         | none =>
           y.mem (base + 16) = 1) ∧
        (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
          a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
          (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a)
  | 0, tbl, e, x, hhdr, hhash, _, _, _, _, h0, h17, h18, _, _, _, hm16, _ => by
    have hcond : ¬(Cond.lt 18 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h17, h18]
    refine ⟨x, ⟨2, by simp [evictRounds], Exec.loop_exit hcond⟩,
      h0, hhdr, hhash, rfl, hm16, fun _ _ _ _ _ _ _ => rfl⟩
  | fuel + 1, tbl, e, x, hhdr, hhash, hslots, htiv, he, hmem_keys,
      h0, h17, h18, hm11, hm12, hm15, _, hfit_fuel1 => by
    have hcond : (Cond.lt 18 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h17, h18]
    have hfit_fuel : Fits w fuel := hfit_fuel1.of_le (Nat.le_succ fuel)
    obtain ⟨s1, ⟨t_bd, ht_bd, he_bd⟩, hs1_0, hs1_hdr, hs1_hash, hs1_seed, hs1_slots, hs1_tiv,
        hs1_15, hs1_res, hs1_frame⟩ :=
      evictRoundBodyCode_execWithin (fuel := fuel) hhdr hhash hslots htiv he hlen_le hmem_keys
        h0 hm11 hm12 hm15 hfit_fuel hw hfit_end
    unfold pureEvict evictRounds
    cases hround : pureEvictRound (evalHash1 θ) (evalHash2 θ) tbl e with
    | mk tbl' oe =>
      rw [hround] at hs1_slots hs1_tiv hs1_res
      cases oe with
      | none =>
        obtain ⟨s2, he_sync, hs2_0, hs2_17, hs2_18, hs2_mem⟩ :=
          syncEvictCondCode_exec (act := 0) (fuel := fuel) hs1_0 hs1_15 hs1_res
            (by decide) hfit_fuel hfit_end
        have hcond2 : ¬(Cond.lt 18 17 : Cond 19).Holds s2 := by
          simp [Cond.Holds, hs2_17, hs2_18]
        have he_stop : Exec w evictLoopInner s2 s2 2 := Exec.loop_exit hcond2
        have hall := Exec.loop_iter hcond (he_bd.seq he_sync) he_stop
        refine ⟨s2, ⟨(t_bd + 8) + 2 + 2, by dsimp only [evictIterSteps]; omega, hall⟩,
          hs2_0,
          by rw [hs2_mem]; exact hs1_hdr,
          by rw [hs2_mem]; exact hs1_hash,
          by rw [hs2_mem]; exact hs1_seed,
          by rw [hs2_mem]; exact ⟨hs1_res, hs1_slots, hs1_tiv⟩,
          fun a ha ha11 ha12 ha15 ha16 hnot_tbl => by
            rw [hs2_mem]; exact hs1_frame a ha ha11 ha12 ha15 ha16 hnot_tbl⟩
      | some e' =>
        obtain ⟨hs1_16, hs1_11, hs1_12, he'_idx, he'_key⟩ := hs1_res
        obtain ⟨s2, he_sync, hs2_0, hs2_17, hs2_18, hs2_mem⟩ :=
          syncEvictCondCode_exec (act := 1) (fuel := fuel) hs1_0 hs1_15 hs1_16
            (le_rfl) hfit_fuel hfit_end
        rw [Nat.one_mul] at hs2_17
        have hs2_keys : ∀ idx (hlt : idx < ks.length),
            s2.mem (keysBase base n_max + idx) = ks[idx].val := by
          intro idx hlt
          rw [hs2_mem, hs1_frame (keysBase base n_max + idx)
            (Or.inr (by
              dsimp only [keysBase, t2Base, t1Base, hashBase]
              have := le_hashPairSpace n_max (tableBits n_max); omega))
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                have := le_hashPairSpace n_max (tableBits n_max); omega)
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                have := le_hashPairSpace n_max (tableBits n_max); omega)
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                have := le_hashPairSpace n_max (tableBits n_max); omega)
            (by dsimp only [keysBase, t2Base, t1Base, hashBase]
                have := le_hashPairSpace n_max (tableBits n_max); omega)
            (Or.inr (Nat.le_add_right _ _))]
          exact hmem_keys idx hlt
        obtain ⟨y, ⟨t_rec, ht_rec, he_rec⟩, hy_0, hy_hdr, hy_hash, hy_seed, hy_res, hy_frame⟩ :=
          evictLoopInner_execWithin hlen_le hw hfit_end fuel
            (by rw [hs2_mem]; exact hs1_hdr)
            (by rw [hs2_mem]; exact hs1_hash)
            (by rw [hs2_mem]; exact hs1_slots)
            hs1_tiv ⟨he'_idx, he'_key⟩ hs2_keys hs2_0 hs2_17 hs2_18
            (by rw [hs2_mem]; exact hs1_11)
            (by rw [hs2_mem]; exact hs1_12)
            (by rw [hs2_mem]; exact hs1_15)
            (by rw [hs2_mem]; exact hs1_16)
            hfit_fuel
        have hall := Exec.loop_iter hcond (he_bd.seq he_sync) he_rec
        refine ⟨y, ⟨(t_bd + 8) + t_rec + 2, by
            dsimp only [evictIterSteps] at *
            calc (t_bd + 8) + t_rec + 2
              _ ≤ (evictRoundSteps n_max U + 10) +
                  (evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl' e' *
                    (evictRoundSteps n_max U + 10) + 2) := by omega
              _ = (1 + evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl' e') *
                    (evictRoundSteps n_max U + 10) + 2 := by ring,
            hall⟩,
          hy_0, hy_hdr, hy_hash,
          hy_seed.trans (by rw [hs2_mem]; exact hs1_seed),
          hy_res,
          fun a ha ha11 ha12 ha15 ha16 hnot_tbl =>
            (hy_frame a ha ha11 ha12 ha15 ha16 hnot_tbl).trans
              (by rw [hs2_mem]; exact hs1_frame a ha ha11 ha12 ha15 ha16 hnot_tbl)⟩

theorem evictLoopCode_execWithin {w base n_max U fuel : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {e : SlotEntry U} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem)
    (htiv : TableIdxValid ks tbl)
    (he : e.idx < ks.length ∧ ks[e.idx]? = some e.key)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ idx (hlt : idx < ks.length),
      x.mem (keysBase base n_max + idx) = ks[idx].val)
    (h0 : x.regs 0 = base)
    (hm11 : x.mem (base + 11) = e.key.val)
    (hm12 : x.mem (base + 12) = e.idx)
    (hm15 : x.mem (base + 15) = fuel)
    (hm16 : x.mem (base + 16) = 1)
    (hfit_fuel : Fits w fuel)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w evictLoopCode x y
        (evictRounds (evalHash1 θ) (evalHash2 θ) fuel tbl e * evictIterSteps n_max U + 10) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base n_max U y.mem ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (match pureEvict (evalHash1 θ) (evalHash2 θ) fuel tbl e with
       | some tbl' =>
         y.mem (base + 16) = 0 ∧
         TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl' y.mem ∧
         TableIdxValid ks tbl'
       | none =>
         y.mem (base + 16) = 1) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a) := by
  obtain ⟨s1, he_sync, hs1_0, hs1_17, hs1_18, hs1_mem⟩ :=
    syncEvictCondCode_exec (act := 1) (fuel := fuel) h0 hm15 hm16 (le_rfl) hfit_fuel hfit_end
  rw [Nat.one_mul] at hs1_17
  obtain ⟨y, ⟨t_in, ht_in, he_in⟩, hy_0, hy_hdr, hy_hash, hy_seed, hy_res, hy_frame⟩ :=
    evictLoopInner_execWithin hlen_le hw hfit_end fuel
      (by rw [hs1_mem]; exact hhdr)
      (by rw [hs1_mem]; exact hrep_hash)
      (by rw [hs1_mem]; exact hslots)
      htiv he
      (fun idx hlt => by rw [hs1_mem]; exact hmem_keys idx hlt)
      hs1_0 hs1_17 hs1_18
      (by rw [hs1_mem]; exact hm11)
      (by rw [hs1_mem]; exact hm12)
      (by rw [hs1_mem]; exact hm15)
      (by rw [hs1_mem]; exact hm16)
      hfit_fuel
  refine ⟨y, ⟨8 + t_in, by omega, he_sync.seq he_in⟩,
    hy_0, hy_hdr, hy_hash,
    hy_seed.trans (by rw [hs1_mem]),
    hy_res,
    fun a ha ha11 ha12 ha15 ha16 hnot_tbl =>
      (hy_frame a ha ha11 ha12 ha15 ha16 hnot_tbl).trans (by rw [hs1_mem])⟩

/-! ### Section 5: Rehashing (`clearTablesCode`, `replayLoopCode`, `rehashLoopCode`)
and `insertCode` -/

/-- Loop zeroing `mem[ptr .. endPtr - 1]` using `reg 16 = ptr`, `reg 17 = endPtr`, `reg 18 = 0`,
and `reg 15 = 1`. -/
@[expose]
def zeroRangeLoop : Code .exact 19 :=
  .loop (.lt 16 17)
    (.seq (.op (.store 16 18))
          (.op (.exactBin .add 16 16 15)))

theorem zeroRangeLoop_exec {w : ℕ} :
    ∀ (rem ptr : ℕ) {x : Data 19}
      (_h16 : x.regs 16 = ptr)
      (_h17 : x.regs 17 = ptr + rem)
      (_h18 : x.regs 18 = 0)
      (_h15 : x.regs 15 = 1)
      (_hfit : Fits w (ptr + rem)),
      ∃ y : Data 19,
        Exec w zeroRangeLoop x y (4 * rem + 2) ∧
        y.regs 0 = x.regs 0 ∧
        (∀ a, ptr ≤ a → a < ptr + rem → y.mem a = 0) ∧
        (∀ a, (a < ptr ∨ ptr + rem ≤ a) → y.mem a = x.mem a)
  | 0, ptr, x, h16, h17, _, _, _ => by
    have hcond : ¬(Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17]
    exact ⟨x, Exec.loop_exit hcond, rfl, fun a hlo hhi => by omega, fun _ _ => rfl⟩
  | rem + 1, ptr, x, h16, h17, h18, h15, hfit => by
    have hcond : (Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17]
    have hfit_next : Fits w (ptr + 1) := hfit.of_le (by omega)
    set s1 := x.write ptr 0
    have e1 : Exec w (.op (.store 16 18) : Code .exact 19) x s1 1 := by
      simpa +decide [s1, h16, h18] using
        (Exec.store (B := .exact) (w := w) (a := 16) (s := 18) (x := x))
    set s2 := s1.set 16 (ptr + 1)
    have e2 : Exec w (.op (.exactBin .add 16 16 15) : Code .exact 19) s1 s2 1 :=
      ExactLog.exec_exactBin (by simp +decide [s1, h16, h15]) hfit_next
    have he_body :
        Exec w (.seq (.op (.store 16 18)) (.op (.exactBin .add 16 16 15))) x s2 (1 + 1) :=
      e1.seq e2
    have hptr_eq : (ptr + 1) + rem = ptr + (rem + 1) := by omega
    obtain ⟨y, he_rec, hy_0, hy_zero, hy_frame⟩ :=
      zeroRangeLoop_exec rem (ptr + 1) (x := s2)
        (by simp +decide [s2])
        (by simp +decide [s2, s1, h17, hptr_eq])
        (by simp +decide [s2, s1, h18])
        (by simp +decide [s2, s1, h15])
        (by rw [hptr_eq]; exact hfit)
    have hall : Exec w zeroRangeLoop x y ((1 + 1) + (4 * rem + 2) + 2) :=
      Exec.loop_iter hcond he_body he_rec
    have hsteps : (1 + 1) + (4 * rem + 2) + 2 = 4 * (rem + 1) + 2 := by ring
    rw [hsteps] at hall
    refine ⟨y, hall, hy_0.trans (by simp +decide [s2, s1]), ?_, ?_⟩
    · intro a hlo hhi
      by_cases ha : a = ptr
      · subst a
        rw [hy_frame ptr (Or.inl (by omega))]
        dsimp only [s2, s1, Data.write, Data.set]
        exact Function.update_self _ _ _
      · exact hy_zero a (by omega) (by omega)
    · intro a ha
      rw [hy_frame a (ha.imp (by omega) (by omega))]
      dsimp only [s2, s1, Data.write, Data.set]
      exact Function.update_of_ne (by omega) _ _

/-- Clears both cuckoo sub-tables `T₁` and `T₂` (`mem[t1Base .. keysBase - 1] ← 0`). -/
@[expose]
def clearTablesCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 7)
  (.seq (loadHeaderCode 17 9)
  (.seq (.op (.const 18 0))
  (.seq (.op (.const 15 1))
        zeroRangeLoop)))

/-- Step count for `clearTablesCode`. -/
@[expose]
def clearTablesSteps (n_max : ℕ) : ℕ :=
  8 * tableSize n_max + 10

theorem clearTablesCode_exec {w base n_max U : ℕ} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w clearTablesCode x y (clearTablesSteps n_max) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base n_max U y.mem ∧
      TableSlotsRep (t1Base base n_max) (t2Base base n_max)
        (PureTable.empty U (2 ^ tableBits n_max)) y.mem ∧
      (∀ a, (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a) := by
  have ⟨_, _, _, _, _, _, hm7, _, hm9, _⟩ := hhdr
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_7 : Fits w 7 := hfit_end.of_le (by omega)
  have hfit_9 : Fits w 9 := hfit_end.of_le (by omega)
  have hfit_b7 : Fits w (base + 7) := hfit_end.of_le (by omega)
  have hfit_b9 : Fits w (base + 9) := hfit_end.of_le (by omega)
  have hfit_kb : Fits w (keysBase base n_max) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have e1 := loadHeaderCode_exec (dst := 16) (off := 7) (x := x)
    h0 (by decide) (by decide) hfit_7 hfit_b7
  set s1 := (x.set 15 7).set 16 (x.mem (base + 7))
  have e2 := loadHeaderCode_exec (dst := 17) (off := 9) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_9 hfit_b9
  set s2 := (s1.set 15 9).set 17 (s1.mem (base + 9))
  set s3 := s2.set 18 0
  have e3 : Exec w (.op (.const 18 0) : Code .exact 19) s2 s3 1 := Exec.const hfit_0
  set s4 := s3.set 15 1
  have e4 : Exec w (.op (.const 15 1) : Code .exact 19) s3 s4 1 := Exec.const hfit_1
  have hkb_eq : t1Base base n_max + 2 * tableSize n_max = keysBase base n_max := by
    dsimp only [keysBase, t2Base]; omega
  obtain ⟨y, he_loop, hy_0, hy_zero, hy_frame⟩ :=
    zeroRangeLoop_exec (2 * tableSize n_max) (t1Base base n_max) (x := s4)
      (by simp +decide [s4, s3, s2, s1, hm7])
      (by simp +decide [s4, s3, s2, s1, hm9, hkb_eq])
      (by simp +decide [s4, s3])
      (by simp +decide [s4])
      (by rw [hkb_eq]; exact hfit_kb)
  have hall : Exec w clearTablesCode x y (3 + (3 + (1 + (1 + (4 * (2 * tableSize n_max) + 2))))) :=
    e1.seq (e2.seq (e3.seq (e4.seq he_loop)))
  have hsteps : 3 + (3 + (1 + (1 + (4 * (2 * tableSize n_max) + 2)))) = clearTablesSteps n_max := by
    dsimp only [clearTablesSteps]; ring
  rw [hsteps] at hall
  have hy_frame_x : ∀ a, (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a := by
    intro a ha
    rw [hkb_eq] at hy_frame
    exact hy_frame a ha
  refine ⟨y, hall, hy_0.trans (by simp +decide [s4, s3, s2, s1, h0]),
    hhdr.congr (fun k hk _ => hy_frame_x (base + k)
      (Or.inl (by
        dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega))),
    ⟨fun b => ?_, fun b => ?_⟩, hy_frame_x⟩
  · have hb := b.isLt
    rw [hkb_eq] at hy_zero
    exact hy_zero (t1Base base n_max + b.val) (by omega)
      (by dsimp only [keysBase, t2Base, tableSize]; omega)
  · have hb := b.isLt
    rw [hkb_eq] at hy_zero
    exact hy_zero (t2Base base n_max + b.val)
      (by dsimp only [t2Base]; omega)
      (by dsimp only [keysBase, t2Base, tableSize]; omega)

/-- Index-based replay of `rem` remaining keys of `ks` starting at index `i` from `tbl`. -/
@[expose]
def pureReplayFrom {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ) (ks : List (Fin U)) :
    ℕ → ℕ → PureTable U m → Option (PureTable U m)
  | 0, _, tbl => some tbl
  | rem + 1, i, tbl =>
    if h : i < ks.length then
      match pureEvict h₁ h₂ maxLoop tbl ⟨ks[i], i⟩ with
      | some tbl' => pureReplayFrom h₁ h₂ maxLoop ks rem (i + 1) tbl'
      | none => none
    else some tbl

theorem pureReplayFrom_eq_foldlM {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (ks : List (Fin U)) :
    ∀ (sfx pfx : List (Fin U)) (tbl : PureTable U m),
      ks = pfx ++ sfx →
      pureReplayFrom h₁ h₂ maxLoop ks sfx.length pfx.length tbl =
        (sfx.zipIdx pfx.length).foldlM
          (fun t p => pureEvict h₁ h₂ maxLoop t ⟨p.1, p.2⟩) tbl
  | [], pfx, tbl, _ => rfl
  | u :: sfx, pfx, tbl, hks => by
    have hlt : pfx.length < ks.length := by
      rw [hks, List.length_append, List.length_cons]; omega
    have hget : ks[pfx.length] = u := by
      subst hks
      simp
    simp only [List.length_cons, pureReplayFrom, hlt, ↓reduceDIte, hget,
      List.zipIdx_cons, List.foldlM_cons]
    cases hev : pureEvict h₁ h₂ maxLoop tbl ⟨u, pfx.length⟩ with
    | none => rfl
    | some tbl' =>
      have hks' : ks = (pfx ++ [u]) ++ sfx := by
        rw [List.append_assoc, List.singleton_append]; exact hks
      have hlen' : (pfx ++ [u]).length = pfx.length + 1 := by simp
      rw [← hlen']
      exact pureReplayFrom_eq_foldlM h₁ h₂ maxLoop ks sfx (pfx ++ [u]) tbl' hks'

theorem pureReplayFrom_eq_pureReplay {U m : ℕ} (h₁ h₂ : Fin U → Fin m) (maxLoop : ℕ)
    (ks : List (Fin U)) :
    pureReplayFrom h₁ h₂ maxLoop ks ks.length 0 (PureTable.empty U m) =
      pureReplay h₁ h₂ maxLoop ks :=
  pureReplayFrom_eq_foldlM h₁ h₂ maxLoop ks ks [] (PureTable.empty U m) rfl

/-- Synchronizes the replay loop condition `(Cond.lt 16 17)`: loads `i = mem[base + 17]` into
`reg 16`, `allocCount = mem[base + 5]` into `reg 17`, and `act = mem[base + 16]` into `reg 18`;
if `act ≠ 0` (meaning a previous eviction failed), copies `reg 17` into `reg 16` so that
`reg 16 < reg 17` is false. -/
@[expose]
def syncReplayCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 16 17)
  (.seq (loadHeaderCode 17 5)
  (.seq (loadHeaderCode 18 16)
  (.seq (.op (.const 15 0))
  (.branch (.eq 18 15)
    (.seq (.op (.const 15 0)) (.op (.const 15 0)))
    (.op (.copy 16 17))))))

theorem syncReplayCondCode_exec {w base n_max idx allocCount act : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm5 : x.mem (base + 5) = allocCount)
    (hm16 : x.mem (base + 16) = act)
    (hm17 : x.mem (base + 17) = idx)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w syncReplayCondCode x y 13 ∧
      y.regs 0 = base ∧
      y.regs 16 = (if act = 0 then idx else allocCount) ∧
      y.regs 17 = allocCount ∧
      y.mem = x.mem := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_5 : Fits w 5 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_17 : Fits w 17 := hfit_end.of_le (by omega)
  have hfit_b5 : Fits w (base + 5) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_b17 : Fits w (base + 17) := hfit_end.of_le (by omega)
  have e1 := loadHeaderCode_exec (dst := 16) (off := 17) (x := x)
    h0 (by decide) (by decide) hfit_17 hfit_b17
  set s1 := (x.set 15 17).set 16 (x.mem (base + 17))
  have e2 := loadHeaderCode_exec (dst := 17) (off := 5) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_5 hfit_b5
  set s2 := (s1.set 15 5).set 17 (s1.mem (base + 5))
  have e3 := loadHeaderCode_exec (dst := 18) (off := 16) (x := s2)
    (by simp +decide [s2, s1, h0]) (by decide) (by decide) hfit_16 hfit_b16
  set s3 := (s2.set 15 16).set 18 (s2.mem (base + 16))
  set s4 := s3.set 15 0
  have e4 : Exec w (.op (.const 15 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  have hs4_0 : s4.regs 0 = base := by simp +decide [s4, s3, s2, s1, h0]
  have hs4_16 : s4.regs 16 = idx := by simp +decide [s4, s3, s2, s1, hm17]
  have hs4_17 : s4.regs 17 = allocCount := by simp +decide [s4, s3, s2, s1, hm5]
  have hs4_18 : s4.regs 18 = act := by simp +decide [s4, s3, s2, s1, hm16]
  have hs4_15 : s4.regs 15 = 0 := by simp +decide [s4]
  by_cases hact : act = 0
  · have hcond : (Cond.eq 18 15 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_18, hs4_15, hact]
    set s5 := s4.set 15 0
    have e5a : Exec w (.op (.const 15 0) : Code .exact 19) s4 s5 1 := Exec.const hfit_0
    set s6 := s5.set 15 0
    have e5b : Exec w (.op (.const 15 0) : Code .exact 19) s5 s6 1 := Exec.const hfit_0
    have e5 := e5a.seq e5b
    have e_br := e5.branch_pos (neg := .op (.copy 16 17)) hcond
    refine ⟨s6, e1.seq (e2.seq (e3.seq (e4.seq e_br))),
      by simp +decide [s6, s5, hs4_0], by simp +decide [s6, s5, hs4_16, hact],
      by simp +decide [s6, s5, hs4_17], rfl⟩
  · have hcond : ¬(Cond.eq 18 15 : Cond 19).Holds s4 := by
      simp [Cond.Holds, hs4_18, hs4_15, hact]
    set s5 := s4.set 16 (s4.regs 17)
    have e5 : Exec w (.op (.copy 16 17) : Code .exact 19) s4 s5 1 := Exec.copy
    have e_br := e5.branch_neg
      (pos := .seq (.op (.const 15 0)) (.op (.const 15 0))) hcond
    refine ⟨s5, e1.seq (e2.seq (e3.seq (e4.seq e_br))),
      by simp +decide [s5, hs4_0], by simp +decide [s5, hs4_17, hact],
      by simp +decide [s5, hs4_17], rfl⟩

/-- Setup prefix of one replay iteration at index `i = mem[base + 17]`:
loads `i`, stores `mem[base + 12] ← i`, loads `u_i = mem[keysBase + i]`, stores
`mem[base + 11] ← u_i`, stores `mem[base + 17] ← i + 1`, loads `maxEvictions = mem[base + 4]`,
stores `mem[base + 15] ← maxEvictions`, and sets `mem[base + 16] ← 1`. -/
@[expose]
def replayIterSetupCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 17)
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (.op (.load 18 16))
  (.seq (storeHeaderCode 11 18)
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 17 17 15))
  (.seq (storeHeaderCode 17 17)
  (.seq (loadHeaderCode 18 4)
  (.seq (storeHeaderCode 15 18)
        (storeHeaderConstCode 16 1)))))))))))

theorem replayIterSetupCode_exec {w base n_max U idx : ℕ}
    {ks : List (Fin U)} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hm17 : x.mem (base + 17) = idx)
    (hlt : idx < ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base n_max + j) = ks[j].val)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w replayIterSetupCode x y 29 ∧
      y.regs 0 = base ∧
      y.mem (base + 11) = ks[idx].val ∧
      y.mem (base + 12) = idx ∧
      y.mem (base + 15) = maxEvictions n_max ∧
      y.mem (base + 16) = 1 ∧
      y.mem (base + 17) = idx + 1 ∧
      (∀ a, a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 →
        a ≠ base + 16 → a ≠ base + 17 → y.mem a = x.mem a) := by
  have ⟨_, _, _, _, hm4, _, _, _, hm9, _⟩ := hhdr
  have hle_sp := le_space n_max
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_4 : Fits w 4 := hfit_end.of_le (by omega)
  have hfit_9 : Fits w 9 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_12 : Fits w 12 := hfit_end.of_le (by omega)
  have hfit_15 : Fits w 15 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_17 : Fits w 17 := hfit_end.of_le (by omega)
  have hfit_b4 : Fits w (base + 4) := hfit_end.of_le (by omega)
  have hfit_b9 : Fits w (base + 9) := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b12 : Fits w (base + 12) := hfit_end.of_le (by omega)
  have hfit_b15 : Fits w (base + 15) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_b17 : Fits w (base + 17) := hfit_end.of_le (by omega)
  have hfit_idx1 : Fits w (idx + 1) :=
    hfit_end.of_le (by dsimp only [space]; omega)
  have hfit_kaddr : Fits w (keysBase base n_max + idx) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have e1 := loadHeaderCode_exec (dst := 17) (off := 17) (x := x)
    h0 (by decide) (by decide) hfit_17 hfit_b17
  set s1 := (x.set 15 17).set 17 (x.mem (base + 17))
  have e2 := storeHeaderCode_exec (off := 12) (src := 17) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_12 hfit_b12
  set s2 := (((s1.set 15 12).set 16 (base + 12)).write (base + 12) (s1.regs 17))
  have e3 := loadHeaderCode_exec (dst := 16) (off := 9) (x := s2)
    (by simp +decide [s2, s1, h0]) (by decide) (by decide) hfit_9 hfit_b9
  set s3 := (s2.set 15 9).set 16 (s2.mem (base + 9))
  have hs3_16 : s3.regs 16 = keysBase base n_max := by
    change s2.mem (base + 9) = keysBase base n_max
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega)]
    exact hm9
  have hs3_17 : s3.regs 17 = idx := by simp +decide [s3, s2, s1, hm17]
  set s4 := s3.set 16 (keysBase base n_max + idx)
  have e4 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, hs3_16, hs3_17]) hfit_kaddr
  have hs4_kmem : s4.mem (keysBase base n_max + idx) = ks[idx].val := by
    change s2.mem (keysBase base n_max + idx) = ks[idx].val
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by
      dsimp only [keysBase, t2Base, t1Base, hashBase]
      have := le_hashPairSpace n_max (tableBits n_max); omega)]
    exact hmem_keys idx hlt
  set s5 := s4.set 18 ks[idx].val
  have e5 : Exec w (.op (.load 18 16) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, hs4_kmem] using
      (Exec.load (B := .exact) (w := w) (d := 18) (a := 16) (x := s4))
  have e6 := storeHeaderCode_exec (off := 11) (src := 18) (x := s5)
    (by simp +decide [s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_11 hfit_b11
  set s6 := (((s5.set 15 11).set 16 (base + 11)).write (base + 11) (s5.regs 18))
  set s7 := s6.set 15 1
  have e7 : Exec w (.op (.const 15 1) : Code .exact 19) s6 s7 1 := Exec.const hfit_1
  set s8 := s7.set 17 (idx + 1)
  have e8 : Exec w (.op (.exactBin .add 17 17 15) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin (by simp +decide [s7, s6, s5, s4, hs3_17]) hfit_idx1
  have e9 := storeHeaderCode_exec (off := 17) (src := 17) (x := s8)
    (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_17 hfit_b17
  set s9 := (((s8.set 15 17).set 16 (base + 17)).write (base + 17) (s8.regs 17))
  have e10 := loadHeaderCode_exec (dst := 18) (off := 4) (x := s9)
    (by simp +decide [s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    (by decide) (by decide) hfit_4 hfit_b4
  set s10 := (s9.set 15 4).set 18 (s9.mem (base + 4))
  have hs10_18 : s10.regs 18 = maxEvictions n_max := by
    change s9.mem (base + 4) = maxEvictions n_max
    dsimp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
    exact hm4
  have e11 := storeHeaderCode_exec (off := 15) (src := 18) (x := s10)
    (by simp +decide [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    (by decide) (by decide) hfit_15 hfit_b15
  set s11 := (((s10.set 15 15).set 16 (base + 15)).write (base + 15) (s10.regs 18))
  have e12 := storeHeaderConstCode_exec (off := 16) (val := 1) (x := s11)
    (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0]) hfit_1 hfit_16 hfit_b16
  set s12 := ((((s11.set 18 1).set 15 16).set 16 (base + 16)).write (base + 16) 1)
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
    (e7.seq (e8.seq (e9.seq (e10.seq (e11.seq e12))))))))))
  refine ⟨s12, hall,
    by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0],
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
    rfl
  · dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_self]
    exact hm17
  · dsimp only [s12, s11, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_self]
    exact hs10_18
  · dsimp only [s12, Data.write, Data.set]
    exact Function.update_self _ _ _
  · dsimp only [s12, s11, s10, s9, s8, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    rfl
  · intro a ha11 ha12 ha15 ha16 ha17
    dsimp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha16, Function.update_of_ne ha15,
      Function.update_of_ne ha17, Function.update_of_ne ha11, Function.update_of_ne ha12]

/-- Main loop of `replayLoopCode`. -/
@[expose]
def replayLoopInner : Code .exact 19 :=
  .loop (.lt 16 17)
    (.seq replayIterSetupCode
    (.seq evictLoopCode
          syncReplayCondCode))

/-- Step bound for a single iteration of `replayLoopInner`. -/
@[expose]
def replayIterSteps (n_max U : ℕ) : ℕ :=
  maxEvictions n_max * evictIterSteps n_max U + 54

/-- Replays all `allocCount = mem[base + 5]` keys from `insKeys[0 .. allocCount - 1]` into `T₁, T₂`.
Sets `mem[base + 16] = 0` if all keys settle within `maxEvictions n_max` rounds per key, or
`mem[base + 16] = 1` if any key exceeds the eviction cap. -/
@[expose]
def replayLoopCode : Code .exact 19 :=
  .seq (storeHeaderConstCode 17 0)
  (.seq (storeHeaderConstCode 16 0)
  (.seq syncReplayCondCode
        replayLoopInner))

/-- Step bound for `replayLoopCode` over at most `n_max` keys. -/
@[expose]
def replayLoopSteps (n_max U : ℕ) : ℕ :=
  n_max * replayIterSteps n_max U + 23

theorem replayLoopInner_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)}
    (hlen_le : ks.length ≤ n_max)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∀ (rem idx : ℕ) {tbl : PureTable U (2 ^ tableBits n_max)} {x : Data 19}
      (_hhdr : HeaderConstsRep base n_max U x.mem)
      (_hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
      (_hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem)
      (_htiv : TableIdxValid ks tbl)
      (_hidx_rem : idx + rem = ks.length)
      (_hm5 : x.mem (base + 5) = ks.length)
      (_hm16 : x.mem (base + 16) = 0)
      (_hm17 : x.mem (base + 17) = idx)
      (_hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base n_max + j) = ks[j].val)
      (_h0 : x.regs 0 = base)
      (_h16 : x.regs 16 = idx)
      (_h17 : x.regs 17 = ks.length),
      ∃ y : Data 19,
        ExecWithin w replayLoopInner x y (rem * replayIterSteps n_max U + 2) ∧
        y.regs 0 = base ∧
        HeaderConstsRep base n_max U y.mem ∧
        HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
        (match pureReplayFrom (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks rem idx tbl with
         | some tbl' =>
           y.mem (base + 16) = 0 ∧
           TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl' y.mem ∧
           TableIdxValid ks tbl'
         | none =>
           y.mem (base + 16) = 1) ∧
        (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
          a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
          (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a)
  | 0, idx, tbl, x, hhdr, hrep_hash, hslots, htiv, hidx_rem, _, hm16, _, _, h0, h16, h17 => by
    have hidx_eq : idx = ks.length := by omega
    have hcond : ¬(Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17, hidx_eq]
    refine ⟨x, ⟨2, by omega, Exec.loop_exit hcond⟩, h0, hhdr, hrep_hash, rfl,
      ⟨hm16, hslots, htiv⟩, fun _ _ _ _ _ _ _ _ => rfl⟩
  | rem + 1, idx, tbl, x, hhdr, hrep_hash, hslots, htiv, hidx_rem, hm5, hm16, hm17,
      hmem_keys, h0, h16, h17 => by
    have hlt : idx < ks.length := by omega
    have hcond : (Cond.lt 16 17 : Cond 19).Holds x := by
      simp [Cond.Holds, h16, h17, hlt]
    obtain ⟨s1, he_setup, hs1_0, hs1_11, hs1_12, hs1_15, hs1_16, hs1_17, hs1_frame⟩ :=
      replayIterSetupCode_exec hhdr h0 hm17 hlt hlen_le hmem_keys hfit_end
    have hs1_hdr : HeaderConstsRep base n_max U s1.mem :=
      hhdr.congr fun k hk _ =>
        hs1_frame (base + k) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hs1_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s1.mem :=
      hrep_hash.congr_of_ge_hashBase fun a ha =>
        hs1_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega)
    have hs1_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
      extractSeed_congr_of_ge_hashBase fun a ha =>
        hs1_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
          (by dsimp only [hashBase] at ha; omega)
    have hle_hp := le_hashPairSpace n_max (tableBits n_max)
    have hs1_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s1.mem :=
      hslots.congr
        (fun b _ => hs1_frame _
          (by dsimp only [t1Base, hashBase]; omega)
          (by dsimp only [t1Base, hashBase]; omega)
          (by dsimp only [t1Base, hashBase]; omega)
          (by dsimp only [t1Base, hashBase]; omega)
          (by dsimp only [t1Base, hashBase]; omega))
        (fun b _ => hs1_frame _
          (by dsimp only [t2Base, t1Base, hashBase]; omega)
          (by dsimp only [t2Base, t1Base, hashBase]; omega)
          (by dsimp only [t2Base, t1Base, hashBase]; omega)
          (by dsimp only [t2Base, t1Base, hashBase]; omega)
          (by dsimp only [t2Base, t1Base, hashBase]; omega))
    have hs1_keys : ∀ j (hj : j < ks.length), s1.mem (keysBase base n_max + j) = ks[j].val := by
      intro j hj
      rw [hs1_frame _
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)]
      exact hmem_keys j hj
    obtain ⟨s2, ⟨t_ev, ht_ev, he_ev⟩, hs2_0, hs2_hdr, hs2_hash, hs2_seed, hs2_res, hs2_frame⟩ :=
      evictLoopCode_execWithin (e := ⟨ks[idx], idx⟩)
        hs1_hdr hs1_hash hs1_slots htiv ⟨hlt, List.getElem?_eq_getElem hlt⟩
        hlen_le hs1_keys hs1_0 hs1_11 hs1_12 hs1_15 hs1_16 hfit_ev hw hfit_end
    have hrounds_le :
        evictRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl ⟨ks[idx], idx⟩ ≤
          maxEvictions n_max :=
      evictRounds_le (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl ⟨ks[idx], idx⟩
    have ht_ev_le : t_ev ≤ maxEvictions n_max * evictIterSteps n_max U + 10 :=
      le_trans ht_ev (Nat.add_le_add_right (Nat.mul_le_mul_right _ hrounds_le) 10)
    have hs2_frame_x : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → s2.mem a = x.mem a :=
      fun a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl =>
        (hs2_frame a ha ha11 ha12 ha15 ha16 hnot_tbl).trans
          (hs1_frame a ha11 ha12 ha15 ha16 ha17)
    have hs2_5 : s2.mem (base + 5) = ks.length := by
      rw [hs2_frame_x (base + 5) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega))]
      exact hm5
    have hs2_17 : s2.mem (base + 17) = idx + 1 := by
      rw [hs2_frame (base + 17) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega))]
      exact hs1_17
    obtain ⟨s3, he_sync, hs3_0, hs3_16, hs3_17, hs3_mem⟩ :=
      syncReplayCondCode_exec (n_max := n_max) hs2_0 hs2_5 rfl hs2_17 hfit_end
    have he_body : Exec w (.seq replayIterSetupCode (.seq evictLoopCode syncReplayCondCode))
        x s3 (29 + (t_ev + 13)) :=
      he_setup.seq (he_ev.seq he_sync)
    have hbody_le : 29 + (t_ev + 13) + 2 ≤ replayIterSteps n_max U := by
      dsimp only [replayIterSteps]; omega
    simp only [pureReplayFrom, hlt, ↓reduceDIte]
    cases hev_eq :
        pureEvict (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) tbl ⟨ks[idx], idx⟩ with
    | none =>
      rw [hev_eq] at hs2_res
      have hcond3 : ¬(Cond.lt 16 17 : Cond 19).Holds s3 := by
        simp [Cond.Holds, hs3_16, hs3_17, hs2_res]
      have he_stop : Exec w replayLoopInner s3 s3 2 := Exec.loop_exit hcond3
      have hall : Exec w replayLoopInner x s3 ((29 + (t_ev + 13)) + 2 + 2) :=
        Exec.loop_iter hcond he_body he_stop
      refine ⟨s3, ⟨(29 + (t_ev + 13)) + 2 + 2, by
        calc (29 + (t_ev + 13)) + 2 + 2
            ≤ replayIterSteps n_max U + 2 := by omega
          _ ≤ (rem + 1) * replayIterSteps n_max U + 2 := by
            rw [Nat.add_mul, Nat.one_mul]; omega, hall⟩,
        hs3_0,
        by rw [hs3_mem]; exact hs2_hdr,
        by rw [hs3_mem]; exact hs2_hash,
        by rw [hs3_mem]; exact hs2_seed.trans hs1_seed,
        by rw [hs3_mem]; exact hs2_res,
        fun a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl => by
          rw [hs3_mem]; exact hs2_frame_x a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl⟩
    | some tbl' =>
      rw [hev_eq] at hs2_res
      obtain ⟨hs2_16_0, hs2_slots, hs2_tiv⟩ := hs2_res
      rw [hs2_16_0] at hs3_16
      simp only [↓reduceIte] at hs3_16
      have hs3_keys : ∀ j (hj : j < ks.length), s3.mem (keysBase base n_max + j) = ks[j].val := by
        intro j hj
        rw [hs3_mem, hs2_frame_x _
          (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (Or.inr (le_trans (Nat.le_add_right _ _) (Nat.le_refl _)))]
        exact hmem_keys j hj
      obtain ⟨y, ⟨t_rec, ht_rec, he_rec⟩, hy_0, hy_hdr, hy_hash, hy_seed, hy_res, hy_frame⟩ :=
        replayLoopInner_execWithin hlen_le hfit_ev hw hfit_end rem (idx + 1)
          (by rw [hs3_mem]; exact hs2_hdr)
          (by rw [hs3_mem]; exact hs2_hash)
          (by rw [hs3_mem]; exact hs2_slots)
          hs2_tiv
          (by omega)
          (by rw [hs3_mem]; exact hs2_5)
          (by rw [hs3_mem]; exact hs2_16_0)
          (by rw [hs3_mem]; exact hs2_17)
          hs3_keys hs3_0 hs3_16 hs3_17
      have hall : Exec w replayLoopInner x y ((29 + (t_ev + 13)) + t_rec + 2) :=
        Exec.loop_iter hcond he_body he_rec
      refine ⟨y, ⟨(29 + (t_ev + 13)) + t_rec + 2, by
        calc (29 + (t_ev + 13)) + t_rec + 2
            ≤ replayIterSteps n_max U + (rem * replayIterSteps n_max U + 2) := by omega
          _ = (rem + 1) * replayIterSteps n_max U + 2 := by ring, hall⟩,
        hy_0, hy_hdr, hy_hash,
        hy_seed.trans (by rw [hs3_mem]; exact hs2_seed.trans hs1_seed),
        hy_res,
        fun a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl =>
          (hy_frame a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl).trans
            (by rw [hs3_mem]; exact hs2_frame_x a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl)⟩

theorem replayLoopCode_execWithin {w base n_max U : ℕ}
    {θ : Seed U (tableBits n_max)} {ks : List (Fin U)} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (hrep_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ x.mem)
    (hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max)
      (PureTable.empty U (2 ^ tableBits n_max)) x.mem)
    (hm5 : x.mem (base + 5) = ks.length)
    (hlen_le : ks.length ≤ n_max)
    (hmem_keys : ∀ j (hj : j < ks.length), x.mem (keysBase base n_max + j) = ks[j].val)
    (h0 : x.regs 0 = base)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      ExecWithin w replayLoopCode x y (replayLoopSteps n_max U) ∧
      y.regs 0 = base ∧
      HeaderConstsRep base n_max U y.mem ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max) θ y.mem ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem ∧
      (match pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks with
       | some tbl' =>
         y.mem (base + 16) = 0 ∧
         TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl' y.mem ∧
         TableIdxValid ks tbl'
       | none =>
         y.mem (base + 16) = 1) ∧
      (∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
        a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
        (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_17 : Fits w 17 := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_b17 : Fits w (base + 17) := hfit_end.of_le (by omega)
  have e1 := storeHeaderConstCode_exec (off := 17) (val := 0) (x := x)
    h0 hfit_0 hfit_17 hfit_b17
  set s1 := ((((x.set 18 0).set 15 17).set 16 (base + 17)).write (base + 17) 0)
  have e2 := storeHeaderConstCode_exec (off := 16) (val := 0) (x := s1)
    (by simp +decide [s1, h0]) hfit_0 hfit_16 hfit_b16
  set s2 := ((((s1.set 18 0).set 15 16).set 16 (base + 16)).write (base + 16) 0)
  have hs2_frame : ∀ a, a ≠ base + 16 → a ≠ base + 17 → s2.mem a = x.mem a := by
    intro a ha16 ha17
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha16, Function.update_of_ne ha17]
  have hs2_16 : s2.mem (base + 16) = 0 := Function.update_self _ _ _
  have hs2_17 : s2.mem (base + 17) = 0 := by
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hs2_5 : s2.mem (base + 5) = ks.length := by
    rw [hs2_frame (base + 5) (by omega) (by omega)]; exact hm5
  obtain ⟨s3, he_sync, hs3_0, hs3_16, hs3_17, hs3_mem⟩ :=
    syncReplayCondCode_exec (n_max := n_max)
      (by simp +decide [s2, s1, h0]) hs2_5 hs2_16 hs2_17 hfit_end
  simp only [↓reduceIte] at hs3_16
  have htiv_empty : TableIdxValid ks (PureTable.empty U (2 ^ tableBits n_max)) :=
    fun _ h => False.elim (not_entryIn_empty _ h)
  have hs3_hdr : HeaderConstsRep base n_max U s3.mem := by
    rw [hs3_mem]
    exact hhdr.congr fun k hk _ => hs2_frame (base + k) (by omega) (by omega)
  have hs3_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ s3.mem := by
    rw [hs3_mem]
    exact hrep_hash.congr_of_ge_hashBase fun a ha =>
      hs2_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
  have hs3_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s3.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem := by
    rw [hs3_mem]
    exact extractSeed_congr_of_ge_hashBase fun a ha =>
      hs2_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
  have hs3_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max)
      (PureTable.empty U (2 ^ tableBits n_max)) s3.mem := by
    rw [hs3_mem]
    exact hslots.congr
      (fun b _ => hs2_frame _
        (by
          dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by
          dsimp only [t1Base, hashBase]; have := le_hashPairSpace n_max (tableBits n_max); omega))
      (fun b _ => hs2_frame _
        (by
          dsimp only [t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega)
        (by
          dsimp only [t2Base, t1Base, hashBase]
          have := le_hashPairSpace n_max (tableBits n_max); omega))
  have hs3_keys : ∀ j (hj : j < ks.length), s3.mem (keysBase base n_max + j) = ks[j].val := by
    intro j hj
    rw [hs3_mem, hs2_frame _
      (by
        dsimp only [keysBase, t2Base, t1Base, hashBase]
        have := le_hashPairSpace n_max (tableBits n_max); omega)
      (by
        dsimp only [keysBase, t2Base, t1Base, hashBase]
        have := le_hashPairSpace n_max (tableBits n_max); omega)]
    exact hmem_keys j hj
  obtain ⟨y, ⟨t_in, ht_in, he_in⟩, hy_0, hy_hdr, hy_hash, hy_seed, hy_res, hy_frame⟩ :=
    replayLoopInner_execWithin hlen_le hfit_ev hw hfit_end ks.length 0
      hs3_hdr hs3_hash hs3_slots htiv_empty (Nat.zero_add _)
      (by rw [hs3_mem]; exact hs2_5)
      (by rw [hs3_mem]; exact hs2_16)
      (by rw [hs3_mem]; exact hs2_17)
      hs3_keys hs3_0 hs3_16 hs3_17
  rw [pureReplayFrom_eq_pureReplay] at hy_res
  have ht_in_le : t_in ≤ n_max * replayIterSteps n_max U + 2 :=
    le_trans ht_in (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen_le) 2)
  refine ⟨y, ⟨4 + (4 + (13 + t_in)), by dsimp only [replayLoopSteps]; omega,
    e1.seq (e2.seq (he_sync.seq he_in))⟩,
    hy_0, hy_hdr, hy_hash, hy_seed.trans hs3_seed, hy_res,
    fun a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl =>
      (hy_frame a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl).trans
        (by rw [hs3_mem]; exact hs2_frame a ha16 ha17)⟩

/-- Synchronizes the rehash loop condition `(Cond.lt 18 17)`: loads `act = mem[base + 16]` into
`reg 17` and sets `reg 18 = 0`, so `(Cond.lt 18 17).Holds` iff `0 < mem[base + 16]`. -/
@[expose]
def syncRehashCondCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 16)
        (.op (.const 18 0))

theorem syncRehashCondCode_exec {w base n_max act : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm16 : x.mem (base + 16) = act)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w syncRehashCondCode x y 4 ∧
      y.regs 0 = base ∧
      y.regs 17 = act ∧
      y.regs 18 = 0 ∧
      y.mem = x.mem := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have e1 := loadHeaderCode_exec (dst := 17) (off := 16) (x := x)
    h0 (by decide) (by decide) hfit_16 hfit_b16
  set s1 := (x.set 15 16).set 17 (x.mem (base + 16))
  set s2 := s1.set 18 0
  have e2 : Exec w (.op (.const 18 0) : Code .exact 19) s1 s2 1 := Exec.const hfit_0
  exact ⟨s2, e1.seq e2, by simp +decide [s2, s1, h0],
    by simp +decide [s2, s1, hm16], by simp +decide [s2], rfl⟩

/-- One rehash attempt: resamples `(h₁, h₂)` without rebuilding `clmulTab`, clears `T₁` and `T₂`,
replays all `allocCount` keys from `insKeys`, and synchronizes `(Cond.lt 18 17)`. -/
@[expose]
def rehashAttemptCode : Code .exact 19 :=
  .seq resampleAtBaseCode
  (.seq clearTablesCode
  (.seq replayLoopCode
        syncRehashCondCode))

/-- Step bound for a single `rehashAttemptCode` execution. -/
@[expose]
def rehashAttemptSteps (n_max U : ℕ) : ℕ :=
  resampleAtBaseSteps n_max + clearTablesSteps n_max + replayLoopSteps n_max U + 4

/-- Loop invariant for `rehashLoopInner`: machine configuration is word-bounded, `reg 0 = base`,
the header and `clmulTab` are intact, `insKeys` / `insVals` realize `(ks, s)`, and all memory
modifications since `x₀` lie inside `[base, base + space n_max)`. -/
@[expose]
def RehashLoopInv (w base n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (x₀ z : Data 19) : Prop :=
  z.Bounded w ∧
  z.regs 0 = base ∧
  HeaderConstsRep base n_max U z.mem ∧
  HashPairTableRep (hashBase base) n_max U (tableBits n_max) z.mem ∧
  KeysValsRep base n_max U V ks s z.mem ∧
  Modifies (Block.mk base (space n_max)).footprint x₀.mem z.mem

/-- Exit postcondition for `rehashLoopInner`: `RehashLoopInv` holds together with `HashPairRep`
for `θ_mem = extractSeed ... z.mem` and a valid replayed table `tbl` in `T₁, T₂`. -/
@[expose]
def RehashLoopPost (w base n_max U V : ℕ) (ks : List (Fin U)) (s : Dictionary.State U)
    (x₀ z : Data 19) : Prop :=
  RehashLoopInv w base n_max U V ks s x₀ z ∧
  HashPairRep (hashBase base) n_max U (tableBits n_max)
    (extractSeed (hashBase base) n_max U (tableBits n_max) z.mem) z.mem ∧
  ∃ tbl : PureTable U (2 ^ tableBits n_max),
    pureReplay (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) z.mem))
      (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) z.mem))
      (maxEvictions n_max) ks = some tbl ∧
    TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl z.mem

theorem rehashDetTail_execWithin {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ z1 : Data 19}
    (hinv : RehashLoopInv w base n_max U V ks s x₀ z1)
    (hhash : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem) z1.mem)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max)) :
    let θ₁ := extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem
    ∃ y : Data 19,
      ExecWithin w (.seq clearTablesCode (.seq replayLoopCode syncRehashCondCode)) z1 y
        (clearTablesSteps n_max + replayLoopSteps n_max U + 4) ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) y.mem = θ₁ ∧
      LoopStateInv (.lt 18 17)
        (RehashLoopInv w base n_max U V ks s x₀)
        (RehashLoopPost w base n_max U V ks s x₀) y ∧
      (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
        θ₁ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) ∧
      (GoodForSet (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) (Dictionary.dom s) →
        ¬(Cond.lt 18 17 : Cond 19).Holds y) := by
  intro θ₁
  rcases hinv with ⟨hz1_bdd, hz1_0, hz1_hdr, _, hz1_kv, hz1_mod⟩
  rcases hz1_kv with ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩
  obtain ⟨s1, he_clr, hs1_0, hs1_hdr, hs1_slots, hs1_frame⟩ :=
    clearTablesCode_exec hz1_hdr hz1_0 hfit_end
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hz1_ge : hashBase base + 47 ≤ z1Base (hashBase base) n_max := by
    rw [z1Base_eq]; exact Nat.le_add_right _ _
  have hz1_end : z1Base (hashBase base) n_max + 2 * 2 ^ tableBits n_max = t1Base base n_max := by
    dsimp only [t1Base]; rw [z1Base_eq, hashPairSpace_eq]; omega
  have hcl_end : hashBase base + 47 + 2 ^ (2 * KWise.chunkBits n_max) ≤ t1Base base n_max := by
    rw [← z1Base_eq, ← hz1_end]; exact Nat.le_add_right _ _
  have hs1_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ₁ s1.mem := by
    rcases hhash with ⟨⟨hM, hz1', hz2', h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
      ⟨hpoly, htab1, htab2⟩⟩
    have hin : ∀ a < t1Base base n_max, s1.mem a = z1.mem a :=
      fun a ha => hs1_frame a (Or.inl ha)
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans hM
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans hz1'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans hz2'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h0'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h1'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h2'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h3'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h4'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h5'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h6'
    · exact (hin _ (by dsimp only [t1Base]; omega)).trans h7'
    · intro idx hidx
      exact (hin _ (by omega)).trans (hcl idx hidx)
    · intro r j
      have hr := r.isLt; have hj := j.isLt
      exact (hin _ (by dsimp only [t1Base]; omega)).trans (hpoly r j)
    · intro i
      have hi := i.isLt
      exact (hin _ (by omega)).trans (htab1 i)
    · intro i
      have hi := i.isLt
      exact (hin _ (by dsimp only [z2Base]; omega)).trans (htab2 i)
  have hs1_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem = θ₁ := by
    have hpoly : Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 s1.mem =
        Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 z1.mem := by
      funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _) (hs1_frame _ (Or.inl (by
        dsimp only [t1Base]; omega)))
    have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) s1.mem =
        Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) z1.mem := by
      funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _) (hs1_frame _ (Or.inl (by omega)))
    dsimp only [θ₁, extractSeed]
    rw [hpoly, htab]
  have hs1_5 : s1.mem (base + 5) = ks.length := by
    rw [hs1_frame (base + 5) (Or.inl (by dsimp only [t1Base, hashBase]; omega))]
    exact hm5
  have hs1_keys : ∀ j (hj : j < ks.length), s1.mem (keysBase base n_max + j) = ks[j].val := by
    intro j hj
    rw [hs1_frame _ (Or.inr (Nat.le_add_right _ _))]
    exact (hkv_idx j hj).1
  obtain ⟨s2, ⟨t_rep, ht_rep, he_rep⟩, hs2_0, hs2_hdr, hs2_hash, hs2_seed, hs2_res, hs2_frame⟩ :=
    replayLoopCode_execWithin hs1_hdr hs1_hash hs1_slots hs1_5 hlen_le hs1_keys hs1_0
      hfit_ev hw hfit_end
  obtain ⟨y, he_sync, hy_0, hy_17, hy_18, hy_mem⟩ :=
    syncRehashCondCode_exec (n_max := n_max) hs2_0 rfl hfit_end
  have hwithin : ExecWithin w (.seq clearTablesCode (.seq replayLoopCode syncRehashCondCode)) z1 y
      (clearTablesSteps n_max + replayLoopSteps n_max U + 4) :=
    ⟨clearTablesSteps n_max + (t_rep + 4), by omega, he_clr.seq (he_rep.seq he_sync)⟩
  have hy_seed : extractSeed (hashBase base) n_max U (tableBits n_max) y.mem = θ₁ := by
    rw [hy_mem]; exact hs2_seed.trans hs1_seed
  have hy_frame_z1 : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
      a ≠ base + 11 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 → a ≠ base + 17 →
      (a < t1Base base n_max ∨ keysBase base n_max ≤ a) → y.mem a = z1.mem a := by
    intro a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl
    rw [hy_mem]
    exact (hs2_frame a ha ha11 ha12 ha15 ha16 ha17 hnot_tbl).trans (hs1_frame a hnot_tbl)
  have hy_mod : Modifies (Block.mk base (space n_max)).footprint x₀.mem y.mem := by
    intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
    have ha_out : a < hashBase base + 40 ∨ hashBase base + 47 ≤ a :=
      ha.imp (by dsimp only [hashBase]; omega) (by dsimp only [hashBase]; omega)
    have ha_tbl : a < t1Base base n_max ∨ keysBase base n_max ≤ a :=
      ha.imp (by dsimp only [t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase, space, tableSize] at *; omega)
    rw [hy_frame_z1 a ha_out (by omega) (by omega) (by omega) (by omega) (by omega) ha_tbl]
    exact hz1_mod a (by simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le]; exact ha)
  have hy_kv : KeysValsRep base n_max U V ks s y.mem :=
    KeysValsRep.congr ⟨hnodup, hlen_le, hm5, hdom_iff, hkv_idx, hvb⟩
      (hy_frame_z1 (base + 5) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega)))
      (fun idx _ => hy_frame_z1 (keysBase base n_max + idx)
        (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (Or.inr (Nat.le_add_right _ _)))
      (fun idx _ => hy_frame_z1 (valsBase base n_max + idx)
        (Or.inr (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (Or.inr (by dsimp only [valsBase]; omega)))
  have hy_hash : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) y.mem := by
    rw [hy_seed, hy_mem]; exact hs2_hash
  have hy_inv : RehashLoopInv w base n_max U V ks s x₀ y :=
    ⟨hwithin.bounded hz1_bdd, hy_0, by rw [hy_mem]; exact hs2_hdr, hy_hash.1, hy_kv, hy_mod⟩
  have hiff : ¬(Cond.lt 18 17 : Cond 19).Holds y ↔
      θ₁ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks := by
    rw [mem_survivingSeeds]
    cases hrep_eq : pureReplay (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) ks with
    | none =>
      rw [hrep_eq] at hs2_res
      simp [Cond.Holds, hy_17, hy_18, hs2_res]
    | some tbl' =>
      rw [hrep_eq] at hs2_res
      obtain ⟨hs2_16_0, _, _⟩ := hs2_res
      simp [Cond.Holds, hy_17, hy_18, hs2_16_0]
  refine ⟨y, hwithin, hy_seed, ?_, hiff, ?_⟩
  · cases hrep_eq : pureReplay (evalHash1 θ₁) (evalHash2 θ₁) (maxEvictions n_max) ks with
    | none =>
      rw [hrep_eq] at hs2_res
      refine Or.inl ⟨?_, hy_inv⟩
      simp [Cond.Holds, hy_17, hy_18, hs2_res]
    | some tbl' =>
      rw [hrep_eq] at hs2_res
      obtain ⟨hs2_16_0, hs2_slots, _⟩ := hs2_res
      refine Or.inr ⟨?_, hy_inv, hy_hash, tbl', ?_, ?_⟩
      · simp [Cond.Holds, hy_17, hy_18, hs2_16_0]
      · rwa [hy_seed]
      · rw [hy_mem]; exact hs2_slots
  · intro hgood
    exact hiff.mpr
      (mem_survivingSeeds_of_goodForSet hnodup (fun u hu => (hdom_iff u).mp hu) hgood)

theorem pmf_toOuterMeasure_mono_on_support {α : Type*} (p : PMF α) {S T : Set α}
    (h : ∀ y ∈ p.support, y ∈ S → y ∈ T) :
    p.toOuterMeasure S ≤ p.toOuterMeasure T := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  refine tsum_le_tsum fun y => ?_
  by_cases hyS : y ∈ S
  · by_cases hyp : y ∈ p.support
    · rw [Set.indicator_of_mem hyS, Set.indicator_of_mem (h y hyp hyS)]
    · have hp0 : p y = 0 := (PMF.apply_eq_zero_iff p y).mpr hyp
      rw [Set.indicator_of_mem hyS, hp0]
      exact zero_le
  · rw [Set.indicator_of_notMem hyS]
    exact zero_le

theorem half_le_toOuterMeasure_of_compl_le_half {α : Type*} (p : PMF α) (S : Set α)
    (hc : p.toOuterMeasure {x | x ∉ S} ≤ 1 / 2) :
    (1 : ℝ≥0∞) / 2 ≤ p.toOuterMeasure S := by
  have hsum : p.toOuterMeasure S + p.toOuterMeasure {x | x ∉ S} = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
      ← Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
    conv_rhs => rw [← p.tsum_coe]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ S <;> simp [hx]
  have hle : (1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 2 ≤ p.toOuterMeasure S + (1 : ℝ≥0∞) / 2 := by
    calc (1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 2
      _ = 1 := ENNReal.add_halves 1
      _ = p.toOuterMeasure S + p.toOuterMeasure {x | x ∉ S} := hsum.symm
      _ ≤ p.toOuterMeasure S + (1 : ℝ≥0∞) / 2 := add_le_add le_rfl hc
  exact (ENNReal.add_le_add_iff_right (by norm_num : (1 : ℝ≥0∞) / 2 ≠ ⊤)).mp hle

/-- Under the `≤ 1 / 2` rehash failure probability bound `hreh`, every duplicate-free key list `ks`
of length at most `n_max` has a nonempty set of surviving seeds of cardinality at least half the
seed space. -/
theorem survivingSeeds_card_and_nonempty {n_max U : ℕ}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    {ks : List (Fin U)} (hnodup : ks.Nodup) (hlen : ks.length ≤ n_max) :
    Fintype.card (Seed U (tableBits n_max)) ≤
      2 * (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2
        (maxEvictions n_max) ks).card ∧
      (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2
        (maxEvictions n_max) ks).Nonempty := by
  classical
  have hcard_S : ks.toFinset.card ≤ n_max := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen
  have hprob :
      (PMF.uniformOfFintype (Seed U (tableBits n_max))).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks} ≤ 1 / 2 := by
    refine le_trans (pmf_toOuterMeasure_mono_on_support _ ?_) (hreh ks.toFinset hcard_S)
    intro θ _ hnot hgood
    exact hnot (mem_survivingSeeds_of_goodForSet hnodup
      (fun u hu => List.mem_toFinset.mpr hu) hgood)
  exact card_le_two_mul_card_of_uniformOfFintype_compl_le_half hprob

theorem rehashAttemptCode_execCodeDist {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ z : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hinv : RehashLoopInv w base n_max U V ks s x₀ z)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ μ_att : PMF (Data 19),
      ExecCodeDist w rehashAttemptCode z μ_att (rehashAttemptSteps n_max U) ∧
      μ_att.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) ∧
      (∀ y ∈ μ_att.support,
        LoopStateInv (.lt 18 17)
          (RehashLoopInv w base n_max U V ks s x₀)
          (RehashLoopPost w base n_max U V ks s x₀) y ∧
        (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
          extractSeed (hashBase base) n_max U (tableBits n_max) y.mem ∈
            survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks)) ∧
      (1 : ℝ≥0∞) / 2 ≤ μ_att.toOuterMeasure {y | ¬(Cond.lt 18 17 : Cond 19).Holds y} := by
  classical
  rcases hinv with ⟨hz_bdd, hz_0, hz_hdr, hz_tab, hz_kv, hz_mod⟩
  obtain ⟨μ_res, hres_dist, hres_law, hres_supp⟩ :=
    resampleAtBaseCode_execCodeDist (w := w) (base := base) (n_max := n_max) (U := U) (x := z)
      hz_tab hz_0 hfit_end hfit_q
  have hz1_inv : ∀ z1 ∈ μ_res.support,
      RehashLoopInv w base n_max U V ks s x₀ z1 ∧
      HashPairRep (hashBase base) n_max U (tableBits n_max)
        (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem) z1.mem := by
    intro z1 hz1
    obtain ⟨hz1_0, hz1_hash, hz1_frame⟩ := hres_supp z1 hz1
    have hz1_bdd : z1.Bounded w := hres_dist.bounded hz_bdd z1 hz1
    have hz1_hdr : HeaderConstsRep base n_max U z1.mem :=
      hz_hdr.congr fun k hk _ =>
        hz1_frame (base + k) (Or.inl (by dsimp only [hashBase]; omega))
    have hz1_kv : KeysValsRep base n_max U V ks s z1.mem :=
      hz_kv.congr
        (hz1_frame (base + 5) (Or.inl (by dsimp only [hashBase]; omega)))
        (fun idx _ => hz1_frame _ (Or.inr (Or.inr (by
          dsimp only [keysBase, t2Base, t1Base]; omega))))
        (fun idx _ => hz1_frame _ (Or.inr (Or.inr (by
          dsimp only [valsBase, keysBase, t2Base, t1Base]; omega))))
    have hz1_mod : Modifies (Block.mk base (space n_max)).footprint x₀.mem z1.mem := by
      intro a ha
      simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
      rw [hz1_frame a (ha.imp (by dsimp only [hashBase]; omega)
        (fun h => Or.inr (by dsimp only [hashBase, space] at *; omega)))]
      exact hz_mod a (by simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le]; exact ha)
    exact ⟨⟨hz1_bdd, hz1_0, hz1_hdr, hz1_hash.1, hz1_kv, hz1_mod⟩, hz1_hash⟩
  have htail_ex : ∀ z1 ∈ μ_res.support,
      ∃ y : Data 19,
        ExecWithin w (.seq clearTablesCode (.seq replayLoopCode syncRehashCondCode)) z1 y
          (clearTablesSteps n_max + replayLoopSteps n_max U + 4) ∧
        extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
          extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem ∧
        LoopStateInv (.lt 18 17)
          (RehashLoopInv w base n_max U V ks s x₀)
          (RehashLoopPost w base n_max U V ks s x₀) y ∧
        (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
          extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem ∈
            survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) ∧
        (GoodForSet (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem))
          (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem))
          (maxEvictions n_max) (Dictionary.dom s) →
          ¬(Cond.lt 18 17 : Cond 19).Holds y) :=
    fun z1 hz1 =>
      rehashDetTail_execWithin (hz1_inv z1 hz1).1 (hz1_inv z1 hz1).2 hfit_ev hw hfit_end
  let tailFn : Data 19 → Data 19 := fun z1 =>
    if h : z1 ∈ μ_res.support then Classical.choose (htail_ex z1 h) else z1
  have htail_spec : ∀ z1 (hz1 : z1 ∈ μ_res.support),
      ExecWithin w (.seq clearTablesCode (.seq replayLoopCode syncRehashCondCode)) z1 (tailFn z1)
        (clearTablesSteps n_max + replayLoopSteps n_max U + 4) ∧
      extractSeed (hashBase base) n_max U (tableBits n_max) (tailFn z1).mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem ∧
      LoopStateInv (.lt 18 17)
        (RehashLoopInv w base n_max U V ks s x₀)
        (RehashLoopPost w base n_max U V ks s x₀) (tailFn z1) ∧
      (¬(Cond.lt 18 17 : Cond 19).Holds (tailFn z1) ↔
        extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem ∈
          survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) ∧
      (GoodForSet (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem))
        (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem))
        (maxEvictions n_max) (Dictionary.dom s) →
        ¬(Cond.lt 18 17 : Cond 19).Holds (tailFn z1)) := by
    intro z1 hz1
    dsimp only [tailFn]
    simp only [hz1, ↓reduceDIte]
    exact Classical.choose_spec (htail_ex z1 hz1)
  let μ_att : PMF (Data 19) := μ_res.map tailFn
  have hfull : ExecCodeDist w rehashAttemptCode z μ_att (rehashAttemptSteps n_max U) := by
    have hseq := hres_dist.seq_const
      (c₂ := .seq clearTablesCode (.seq replayLoopCode syncRehashCondCode))
      (μ₂ := fun z1 => PMF.pure (tailFn z1))
      (T₂ := fun _ => (clearTablesSteps n_max + replayLoopSteps n_max U + 4 : ℕ))
      (B₂ := (clearTablesSteps n_max + replayLoopSteps n_max U + 4 : ℕ))
      (fun z1 hz1 => ExecCodeDist.of_execWithin (htail_spec z1 hz1).1)
      (fun _ _ => le_rfl)
    refine hseq.congr_dist rfl ?_
    exact_mod_cast (by dsimp only [rehashAttemptSteps]; omega :
      resampleAtBaseSteps n_max + (clearTablesSteps n_max + replayLoopSteps n_max U + 4) ≤
        rehashAttemptSteps n_max U)
  have hlaw_att :
      μ_att.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) := by
    dsimp only [μ_att]
    rw [PMF.map_comp]
    have hcongr :
        μ_res.map ((fun y : Data 19 =>
            extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) ∘ tailFn) =
          μ_res.map (fun z1 : Data 19 =>
            extractSeed (hashBase base) n_max U (tableBits n_max) z1.mem) :=
      PMF.map_congr_on_support _ _ _ fun z1 hz1 => (htail_spec z1 hz1).2.1
    rw [hcongr]
    exact hres_law
  refine ⟨μ_att, hfull, hlaw_att, ?_, ?_⟩
  · intro y hy
    dsimp only [μ_att] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z1, hz1, rfl⟩ := hy
    refine ⟨(htail_spec z1 hz1).2.2.1, ?_⟩
    rw [(htail_spec z1 hz1).2.1]
    exact (htail_spec z1 hz1).2.2.2.1
  · let G : Set (Seed U (tableBits n_max)) :=
      {θ' | GoodForSet (evalHash1 θ') (evalHash2 θ') (maxEvictions n_max) (Dictionary.dom s)}
    have hcard_le : (Dictionary.dom s).card ≤ n_max := by
      rw [hz_kv.card_dom_eq]; exact hz_kv.2.1
    have hgood_prob : (1 : ℝ≥0∞) / 2 ≤ (seedLaw U (tableBits n_max)).toOuterMeasure G :=
      half_le_toOuterMeasure_of_compl_le_half (seedLaw U (tableBits n_max)) G
        (hreh (Dictionary.dom s) hcard_le)
    rw [← hlaw_att, PMF.toOuterMeasure_map_apply] at hgood_prob
    refine le_trans hgood_prob (pmf_toOuterMeasure_mono_on_support μ_att ?_)
    intro y hy hyG
    dsimp only [μ_att] at hy
    rw [PMF.mem_support_map_iff] at hy
    obtain ⟨z1, hz1, rfl⟩ := hy
    have hyG' : GoodForSet
        (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) (tailFn z1).mem))
        (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) (tailFn z1).mem))
        (maxEvictions n_max) (Dictionary.dom s) := hyG
    rw [(htail_spec z1 hz1).2.1] at hyG'
    exact (htail_spec z1 hz1).2.2.2.2 hyG'

/-- Las Vegas rehash loop: synchronizes `(Cond.lt 18 17)` from `mem[base + 16]` and repeats
`rehashAttemptCode` while `0 < mem[base + 16]`. -/
@[expose]
def rehashLoopCode : Code .exact 19 :=
  .seq syncRehashCondCode
        (.loop (.lt 18 17) rehashAttemptCode)

/-- Expected step bound for `rehashLoopCode`:
`4 + 2 * (rehashAttemptSteps n_max U + 2) + 2 = 2 * rehashAttemptSteps n_max U + 10`. -/
@[expose]
def rehashLoopSteps (n_max U : ℕ) : ℕ :=
  2 * rehashAttemptSteps n_max U + 10

theorem rehashLoopCode_execCodeDist {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hinv : RehashLoopInv w base n_max U V ks s x₀ x)
    (hm16 : x.mem (base + 16) = 1)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ (μ_reh : PMF (Data 19))
      (hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty),
      ExecCodeDist w rehashLoopCode x μ_reh (rehashLoopSteps n_max U) ∧
      μ_reh.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE ∧
      ∀ y ∈ μ_reh.support, RehashLoopPost w base n_max U V ks s x₀ y := by
  classical
  have hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty :=
    (survivingSeeds_card_and_nonempty hreh hinv.2.2.2.2.1.1 hinv.2.2.2.2.1.2.1).2
  obtain ⟨s1, he_sync, hs1_0, hs1_17, hs1_18, hs1_mem⟩ :=
    syncRehashCondCode_exec (n_max := n_max) hinv.2.1 hm16 hfit_end
  have hs1_inv : RehashLoopInv w base n_max U V ks s x₀ s1 :=
    ⟨he_sync.bounded hinv.1, hs1_0, by rw [hs1_mem]; exact hinv.2.2.1,
      by rw [hs1_mem]; exact hinv.2.2.2.1,
      by rw [hs1_mem]; exact hinv.2.2.2.2.1,
      by rw [hs1_mem]; exact hinv.2.2.2.2.2⟩
  let I := RehashLoopInv w base n_max U V ks s x₀
  let Q := RehashLoopPost w base n_max U V ks s x₀
  let E : Finset (Seed U (tableBits n_max)) :=
    survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks
  have hbody_ex : ∀ z, I z →
      ∃ μ_att : PMF (Data 19),
        ExecCodeDist w rehashAttemptCode z μ_att (rehashAttemptSteps n_max U) ∧
        μ_att.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
          seedLaw U (tableBits n_max) ∧
        (∀ y ∈ μ_att.support,
          LoopStateInv (.lt 18 17) I Q y ∧
          (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
            extractSeed (hashBase base) n_max U (tableBits n_max) y.mem ∈ E)) ∧
        (1 : ℝ≥0∞) / 2 ≤ μ_att.toOuterMeasure {y | ¬(Cond.lt 18 17 : Cond 19).Holds y} :=
    fun z hz => rehashAttemptCode_execCodeDist hreh hz hfit_ev hw hfit_end hfit_q
  let μ_body : Data 19 → PMF (Data 19) := fun z =>
    if hz : I z then Classical.choose (hbody_ex z hz) else PMF.pure z
  have hbody_spec : ∀ z (hz : I z),
      ExecCodeDist w rehashAttemptCode z (μ_body z) (rehashAttemptSteps n_max U) ∧
      (μ_body z).map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        seedLaw U (tableBits n_max) ∧
      (∀ y ∈ (μ_body z).support,
        LoopStateInv (.lt 18 17) I Q y ∧
        (¬(Cond.lt 18 17 : Cond 19).Holds y ↔
          extractSeed (hashBase base) n_max U (tableBits n_max) y.mem ∈ E)) ∧
      (1 : ℝ≥0∞) / 2 ≤ (μ_body z).toOuterMeasure {y | ¬(Cond.lt 18 17 : Cond 19).Holds y} := by
    intro z hz
    dsimp only [μ_body]
    simp only [hz, ↓reduceDIte]
    exact Classical.choose_spec (hbody_ex z hz)
  have hp_pos : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  have hp_top : ((1 : ℝ≥0∞) / 2) ≠ ⊤ := by norm_num
  have hs1_cond : (Cond.lt 18 17 : Cond 19).Holds s1 := by
    simp [Cond.Holds, hs1_17, hs1_18]
  have hs1_loop_inv : LoopStateInv (.lt 18 17) I Q s1 :=
    Or.inl ⟨hs1_cond, hs1_inv⟩
  have hloop := ExecCodeDist.loop_geometric I Q hp_pos hp_top
    (μ_body := μ_body)
    (T_body := fun _ => (rehashAttemptSteps n_max U : ℝ≥0∞))
    (B_body := (rehashAttemptSteps n_max U : ℝ≥0∞))
    (x := s1)
    (fun z hz _ => (hbody_spec z hz).1)
    (fun _ _ _ => le_rfl)
    (fun z hz _ y hy => ((hbody_spec z hz).2.2.1 y hy).1)
    (fun z hz _ => (hbody_spec z hz).2.2.2)
    hs1_loop_inv
  have hdiv : ((rehashAttemptSteps n_max U : ℝ≥0∞) + 2) / ((1 : ℝ≥0∞) / 2) ≤
      2 * ((rehashAttemptSteps n_max U : ℝ≥0∞) + 2) := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      two_mul, add_mul, ← mul_add, ENNReal.add_halves 1, mul_one]
  have hseq := (ExecCodeDist.of_exec he_sync).seq_pure hloop
  refine ⟨loopExitPMF (.lt 18 17) μ_body s1, hE, hseq.mono ?_, ?_, ?_⟩
  · calc (4 : ℝ≥0∞) + (((rehashAttemptSteps n_max U : ℝ≥0∞) + 2) / (1 / 2) + 2)
      _ ≤ 4 + (2 * ((rehashAttemptSteps n_max U : ℝ≥0∞) + 2) + 2) :=
          add_le_add le_rfl (add_le_add hdiv le_rfl)
      _ = (rehashLoopSteps n_max U : ℝ≥0∞) := by
          dsimp only [rehashLoopSteps]
          push_cast
          ring
  · exact loopExitPMF_map_eq_uniformOfFinset hE hp_pos hp_top
      (fun z hz _ => (hbody_spec z hz).2.2.1)
      (fun z hz _ => (hbody_spec z hz).2.2.2)
      (fun z hz _ => (hbody_spec z hz).2.1)
      hs1_inv hs1_cond
  · intro y hy
    exact (mem_support_loopExitPMF hp_pos hp_top
      (fun z hz _ y hy => ((hbody_spec z hz).2.2.1 y hy).1)
      (fun z hz _ => (hbody_spec z hz).2.2.2)
      hs1_loop_inv hy).1.2

private theorem valuesBounded_update {U V : ℕ} {s : Dictionary.State U}
    (hvb : Dictionary.ValuesBounded V s) (u : Fin U) {v : ℕ} (hv : v < V) :
    Dictionary.ValuesBounded V (Function.update s u (some v)) := by
  intro x w hxw
  by_cases hxu : x = u
  · subst hxu
    rw [Function.update_self] at hxw
    injection hxw with hvw
    subst hvw; exact hv
  · rw [Function.update_of_ne hxu] at hxw
    exact hvb x w hxw

theorem KeysValsRep.insert_of_mem {base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {u : Fin U} {v idx : ℕ} {mem mem' : ℕ → ℕ}
    (hkv : KeysValsRep base n_max U V ks s mem)
    (hv : v < V)
    (hidx_lt : idx < ks.length)
    (hks_idx : ks[idx] = u)
    (h5 : mem' (base + 5) = mem (base + 5))
    (hk : ∀ j < ks.length, mem' (keysBase base n_max + j) = mem (keysBase base n_max + j))
    (hv_eq : mem' (valsBase base n_max + idx) = v)
    (hv_other : ∀ j < ks.length, j ≠ idx →
      mem' (valsBase base n_max + j) = mem (valsBase base n_max + j)) :
    KeysValsRep base n_max U V ks (Function.update s u (some v)) mem' := by
  rcases hkv with ⟨hnodup, hlen, hm5, hdom, hkv_idx, hvb⟩
  have hu_mem : u ∈ ks := by
    rw [← hks_idx]
    exact List.getElem_mem hidx_lt
  have hdom_ins : Dictionary.dom (Function.update s u (some v)) = Dictionary.dom s := by
    rw [Dictionary.dom_insert]
    exact Finset.insert_eq_of_mem ((hdom u).mp hu_mem)
  refine ⟨hnodup, hlen, h5.trans hm5, fun u' => ?_, fun j hj => ?_, valuesBounded_update hvb u hv⟩
  · rw [hdom_ins]; exact hdom u'
  · refine ⟨(hk j hj).trans (hkv_idx j hj).1, ?_⟩
    by_cases hj_eq : j = idx
    · subst hj_eq
      rw [hks_idx, Function.update_self, hv_eq]
    · have hne_key : ks[j] ≠ u := by
        rw [← hks_idx]
        exact (List.Nodup.getElem_inj_iff hnodup).not.mpr hj_eq
      rw [Function.update_of_ne hne_key, hv_other j hj hj_eq]
      exact (hkv_idx j hj).2

theorem KeysValsRep.insert_of_notMem {base n_max U V : ℕ} {ks : List (Fin U)}
    {s : Dictionary.State U} {u : Fin U} {v : ℕ} {mem mem' : ℕ → ℕ}
    (hkv : KeysValsRep base n_max U V ks s mem)
    (hv : v < V)
    (hu_notMem : u ∉ ks)
    (hlen_lt : ks.length < n_max)
    (h5 : mem' (base + 5) = ks.length + 1)
    (hk_old : ∀ j < ks.length, mem' (keysBase base n_max + j) = mem (keysBase base n_max + j))
    (hk_new : mem' (keysBase base n_max + ks.length) = u.val)
    (hv_old : ∀ j < ks.length, mem' (valsBase base n_max + j) = mem (valsBase base n_max + j))
    (hv_new : mem' (valsBase base n_max + ks.length) = v) :
    KeysValsRep base n_max U V (ks ++ [u]) (Function.update s u (some v)) mem' := by
  rcases hkv with ⟨hnodup, _, _, hdom, hkv_idx, hvb⟩
  have hnodup' : (ks ++ [u]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton u, fun x hx y hy hxy => ?_⟩
    rw [List.mem_singleton] at hy
    subst hy; subst hxy
    exact hu_notMem hx
  have hlen' : (ks ++ [u]).length ≤ n_max := by simp; omega
  have hm5' : mem' (base + 5) = (ks ++ [u]).length := by simp [h5]
  refine ⟨hnodup', hlen', hm5', fun u' => ?_, fun j hj => ?_, valuesBounded_update hvb u hv⟩
  · rw [List.mem_append, List.mem_singleton, Dictionary.dom_insert, Finset.mem_insert,
      hdom u', or_comm]
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hj_lt : j < ks.length
    · rw [List.getElem_append_left hj_lt]
      have hne_key : ks[j] ≠ u := fun h => hu_notMem (h ▸ List.getElem_mem hj_lt)
      refine ⟨(hk_old j hj_lt).trans (hkv_idx j hj_lt).1, ?_⟩
      rw [Function.update_of_ne hne_key, hv_old j hj_lt]
      exact (hkv_idx j hj_lt).2
    · have hj_eq : j = ks.length := by omega
      subst hj_eq
      simp only [List.getElem_concat_length]
      exact ⟨hk_new, by rw [Function.update_self, hv_new]⟩

/-- Positive branch of `insertCode` when `u ∈ dom s` (`foundFlag = mem[base + 13] = 1`):
overwrites `mem[valsBase + foundIdx] ← mem[base + 18]` in place and sets `reg 2 = 0`. -/
@[expose]
def insertOverwriteBranchCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 14)
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 18)
  (.seq (.op (.store 16 18))
        (.op (.const 2 0))))))

theorem insertOverwriteBranchCode_exec {w base n_max idx v : ℕ} {x : Data 19}
    (h0 : x.regs 0 = base)
    (hm10 : x.mem (base + 10) = valsBase base n_max)
    (hm14 : x.mem (base + 14) = idx)
    (hm18 : x.mem (base + 18) = v)
    (hidx_lt : idx < n_max)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w insertOverwriteBranchCode x y 12 ∧
      y.regs 0 = base ∧
      y.regs 2 = 0 ∧
      y.mem (valsBase base n_max + idx) = v ∧
      (∀ a, a ≠ valsBase base n_max + idx → y.mem a = x.mem a) := by
  have hle_sp := le_space n_max
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_10 : Fits w 10 := hfit_end.of_le (by omega)
  have hfit_14 : Fits w 14 := hfit_end.of_le (by omega)
  have hfit_18 : Fits w 18 := hfit_end.of_le (by omega)
  have hfit_b10 : Fits w (base + 10) := hfit_end.of_le (by omega)
  have hfit_b14 : Fits w (base + 14) := hfit_end.of_le (by omega)
  have hfit_b18 : Fits w (base + 18) := hfit_end.of_le (by omega)
  have hfit_vaddr : Fits w (valsBase base n_max + idx) :=
    hfit_end.of_le (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]; omega)
  have e1 := loadHeaderCode_exec (dst := 17) (off := 14) (x := x)
    h0 (by decide) (by decide) hfit_14 hfit_b14
  set s1 := (x.set 15 14).set 17 (x.mem (base + 14))
  have e2 := loadHeaderCode_exec (dst := 16) (off := 10) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_10 hfit_b10
  set s2 := (s1.set 15 10).set 16 (s1.mem (base + 10))
  set s3 := s2.set 16 (valsBase base n_max + idx)
  have e3 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s2 s3 1 :=
    ExactLog.exec_exactBin (by simp +decide [s2, s1, hm10, hm14]) hfit_vaddr
  have e4 := loadHeaderCode_exec (dst := 18) (off := 18) (x := s3)
    (by simp +decide [s3, s2, s1, h0]) (by decide) (by decide) hfit_18 hfit_b18
  set s4 := (s3.set 15 18).set 18 (s3.mem (base + 18))
  set s5 := s4.write (valsBase base n_max + idx) v
  have e5 : Exec w (.op (.store 16 18) : Code .exact 19) s4 s5 1 := by
    simpa +decide [s5, s4, s3, s2, s1, hm18] using
      (Exec.store (B := .exact) (w := w) (a := 16) (s := 18) (x := s4))
  set s6 := s5.set 2 0
  have e6 : Exec w (.op (.const 2 0) : Code .exact 19) s5 s6 1 := Exec.const hfit_0
  exact ⟨s6, e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6)))),
    by simp +decide [s6, s5, s4, s3, s2, s1, h0],
    by simp +decide [s6],
    Function.update_self _ _ _,
    fun a hne => Function.update_of_ne hne _ _⟩

/-- Setup prefix of `insertNewKeyBranchCode` when `u ∉ dom s`
(`foundFlag = 0`, `idx = ks.length < n_max`):
stores `mem[base + 12] ← idx`, writes `mem[keysBase + idx] ← u.val` and `mem[valsBase + idx] ← v`,
increments `mem[base + 5] ← idx + 1`, sets `mem[base + 15] ← maxEvictions n_max`, and sets
`mem[base + 16] ← 1`. -/
@[expose]
def insertNewKeySetupCode : Code .exact 19 :=
  .seq (loadHeaderCode 17 5)
  (.seq (storeHeaderCode 12 17)
  (.seq (loadHeaderCode 16 9)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 11)
  (.seq (.op (.store 16 18))
  (.seq (loadHeaderCode 16 10)
  (.seq (.op (.exactBin .add 16 16 17))
  (.seq (loadHeaderCode 18 18)
  (.seq (.op (.store 16 18))
  (.seq (.op (.const 15 1))
  (.seq (.op (.exactBin .add 17 17 15))
  (.seq (storeHeaderCode 5 17)
  (.seq (loadHeaderCode 18 4)
  (.seq (storeHeaderCode 15 18)
        (storeHeaderConstCode 16 1)))))))))))))))

theorem insertNewKeySetupCode_exec {w base n_max U idx u_val v : ℕ} {x : Data 19}
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (h0 : x.regs 0 = base)
    (hm5 : x.mem (base + 5) = idx)
    (hm11 : x.mem (base + 11) = u_val)
    (hm18 : x.mem (base + 18) = v)
    (hidx_lt : idx < n_max)
    (hfit_end : Fits w (base + space n_max)) :
    ∃ y : Data 19,
      Exec w insertNewKeySetupCode x y 37 ∧
      y.regs 0 = base ∧
      y.mem (base + 5) = idx + 1 ∧
      y.mem (base + 11) = u_val ∧
      y.mem (base + 12) = idx ∧
      y.mem (base + 15) = maxEvictions n_max ∧
      y.mem (base + 16) = 1 ∧
      y.mem (keysBase base n_max + idx) = u_val ∧
      y.mem (valsBase base n_max + idx) = v ∧
      (∀ a, a ≠ base + 5 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
        a ≠ keysBase base n_max + idx → a ≠ valsBase base n_max + idx →
        y.mem a = x.mem a) := by
  have ⟨_, _, _, _, hm4, _, _, _, hm9, hm10⟩ := hhdr
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hfit_1 : Fits w 1 := hfit_end.of_le (by omega)
  have hfit_4 : Fits w 4 := hfit_end.of_le (by omega)
  have hfit_5 : Fits w 5 := hfit_end.of_le (by omega)
  have hfit_9 : Fits w 9 := hfit_end.of_le (by omega)
  have hfit_10 : Fits w 10 := hfit_end.of_le (by omega)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_12 : Fits w 12 := hfit_end.of_le (by omega)
  have hfit_15 : Fits w 15 := hfit_end.of_le (by omega)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_18 : Fits w 18 := hfit_end.of_le (by omega)
  have hfit_b4 : Fits w (base + 4) := hfit_end.of_le (by omega)
  have hfit_b5 : Fits w (base + 5) := hfit_end.of_le (by omega)
  have hfit_b9 : Fits w (base + 9) := hfit_end.of_le (by omega)
  have hfit_b10 : Fits w (base + 10) := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b12 : Fits w (base + 12) := hfit_end.of_le (by omega)
  have hfit_b15 : Fits w (base + 15) := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  have hfit_b18 : Fits w (base + 18) := hfit_end.of_le (by omega)
  have hfit_idx1 : Fits w (idx + 1) := hfit_end.of_le (by dsimp only [space]; omega)
  have hfit_kaddr : Fits w (keysBase base n_max + idx) :=
    hfit_end.of_le (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
  have hfit_vaddr : Fits w (valsBase base n_max + idx) :=
    hfit_end.of_le (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]; omega)
  have e1 := loadHeaderCode_exec (dst := 17) (off := 5) (x := x)
    h0 (by decide) (by decide) hfit_5 hfit_b5
  set s1 := (x.set 15 5).set 17 (x.mem (base + 5))
  have e2 := storeHeaderCode_exec (off := 12) (src := 17) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_12 hfit_b12
  set s2 := (((s1.set 15 12).set 16 (base + 12)).write (base + 12) (s1.regs 17))
  have e3 := loadHeaderCode_exec (dst := 16) (off := 9) (x := s2)
    (by simp +decide [s2, s1, h0]) (by decide) (by decide) hfit_9 hfit_b9
  set s3 := (s2.set 15 9).set 16 (s2.mem (base + 9))
  have hs3_16 : s3.regs 16 = keysBase base n_max := by
    change s2.mem (base + 9) = keysBase base n_max
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega)]; exact hm9
  have hs3_17 : s3.regs 17 = idx := by simp +decide [s3, s2, s1, hm5]
  set s4 := s3.set 16 (keysBase base n_max + idx)
  have e4 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s3 s4 1 :=
    ExactLog.exec_exactBin (by simp +decide [s3, hs3_16, hs3_17]) hfit_kaddr
  have e5 := loadHeaderCode_exec (dst := 18) (off := 11) (x := s4)
    (by simp +decide [s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_11 hfit_b11
  set s5 := (s4.set 15 11).set 18 (s4.mem (base + 11))
  have hs3_m11 : s3.mem (base + 11) = u_val := by
    change s2.mem (base + 11) = u_val
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega)]; exact hm11
  set s6 := s5.write (keysBase base n_max + idx) u_val
  have e6 : Exec w (.op (.store 16 18) : Code .exact 19) s5 s6 1 := by
    simpa +decide [s6, s5, s4, hs3_m11] using
      (Exec.store (B := .exact) (w := w) (a := 16) (s := 18) (x := s5))
  have e7 := loadHeaderCode_exec (dst := 16) (off := 10) (x := s6)
    (by simp +decide [s6, s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_10 hfit_b10
  set s7 := (s6.set 15 10).set 16 (s6.mem (base + 10))
  have hs6_m10 : s6.mem (base + 10) = valsBase base n_max := by
    dsimp only [s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by omega)]
    exact hm10
  have hs7_16 : s7.regs 16 = valsBase base n_max := by simp +decide [s7, hs6_m10]
  have hs7_17 : s7.regs 17 = idx := by simp +decide [s7, s6, s5, s4, hs3_17]
  set s8 := s7.set 16 (valsBase base n_max + idx)
  have e8 : Exec w (.op (.exactBin .add 16 16 17) : Code .exact 19) s7 s8 1 :=
    ExactLog.exec_exactBin (by simp +decide [hs7_16, hs7_17]) hfit_vaddr
  have e9 := loadHeaderCode_exec (dst := 18) (off := 18) (x := s8)
    (by simp +decide [s8, s7, s6, s5, s4, s3, s2, s1, h0]) (by decide) (by decide) hfit_18 hfit_b18
  set s9 := (s8.set 15 18).set 18 (s8.mem (base + 18))
  have hs7_m18 : s7.mem (base + 18) = v := by
    change s6.mem (base + 18) = v
    dsimp only [s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by omega)]
    exact hm18
  set s10 := s9.write (valsBase base n_max + idx) v
  have e10 : Exec w (.op (.store 16 18) : Code .exact 19) s9 s10 1 := by
    simpa +decide [s10, s9, s8, hs7_m18] using
      (Exec.store (B := .exact) (w := w) (a := 16) (s := 18) (x := s9))
  set s11 := s10.set 15 1
  have e11 : Exec w (.op (.const 15 1) : Code .exact 19) s10 s11 1 := Exec.const hfit_1
  set s12 := s11.set 17 (idx + 1)
  have e12 : Exec w (.op (.exactBin .add 17 17 15) : Code .exact 19) s11 s12 1 :=
    ExactLog.exec_exactBin (by simp +decide [s11, s10, s9, s8, s7, s6, s5, s4, hs3_17]) hfit_idx1
  have e13 := storeHeaderCode_exec (off := 5) (src := 17) (x := s12)
    (by simp +decide [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    (by decide) (by decide) hfit_5 hfit_b5
  set s13 := (((s12.set 15 5).set 16 (base + 5)).write (base + 5) (s12.regs 17))
  have e14 := loadHeaderCode_exec (dst := 18) (off := 4) (x := s13)
    (by simp +decide [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    (by decide) (by decide) hfit_4 hfit_b4
  set s14 := (s13.set 15 4).set 18 (s13.mem (base + 4))
  have hs14_18 : s14.regs 18 = maxEvictions n_max := by
    change s13.mem (base + 4) = maxEvictions n_max
    dsimp only [s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega),
      Function.update_of_ne (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by omega)]
    exact hm4
  have e15 := storeHeaderCode_exec (off := 15) (src := 18) (x := s14)
    (by simp +decide [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    (by decide) (by decide) hfit_15 hfit_b15
  set s15 := (((s14.set 15 15).set 16 (base + 15)).write (base + 15) (s14.regs 18))
  have e16 := storeHeaderConstCode_exec (off := 16) (val := 1) (x := s15)
    (by simp +decide [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0])
    hfit_1 hfit_16 hfit_b16
  set s16 := ((((s15.set 18 1).set 15 16).set 16 (base + 16)).write (base + 16) 1)
  have hall := e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (e8.seq
    (e9.seq (e10.seq (e11.seq (e12.seq (e13.seq (e14.seq (e15.seq e16))))))))))))))
  have hframe : ∀ a, a ≠ base + 5 → a ≠ base + 12 → a ≠ base + 15 → a ≠ base + 16 →
      a ≠ keysBase base n_max + idx → a ≠ valsBase base n_max + idx → s16.mem a = x.mem a := by
    intro a ha5 ha12 ha15 ha16 hak hav
    dsimp only [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Data.write, Data.set]
    rw [Function.update_of_ne ha16, Function.update_of_ne ha15, Function.update_of_ne ha5,
      Function.update_of_ne hav, Function.update_of_ne hak, Function.update_of_ne ha12]
  refine ⟨s16, hall,
    by simp +decide [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h0],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, hframe⟩
  · dsimp only [s16, s15, s14, s13, s12, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    rfl
  · rw [hframe (base + 11) (by omega) (by omega) (by omega) (by omega)
      (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
      (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)]
    exact hm11
  · dsimp only [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),
      Function.update_of_ne (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_self]
    exact hm5
  · dsimp only [s16, s15, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_self]
    exact hs14_18
  · dsimp only [s16, Data.write, Data.set]
    exact Function.update_self _ _ _
  · dsimp only [s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, Data.write, Data.set]
    rw [Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [valsBase]; omega),
      Function.update_self]
  · dsimp only [s16, s15, s14, s13, s12, s11, s10, Data.write, Data.set]
    rw [Function.update_of_ne (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_of_ne (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega),
      Function.update_self]

/-- Negative branch of `insertCode` when `u ∉ dom s` (`foundFlag = mem[base + 13] = 0`):
appends `(u, v)` at `idx = allocCount`, runs `evictLoopCode`, and if `0 < mem[base + 16]`
(meaning the eviction cap was reached) runs `rehashLoopCode`; sets `reg 2 = 0`. -/
@[expose]
def insertNewKeyBranchCode : Code .exact 19 :=
  .seq insertNewKeySetupCode
  (.seq evictLoopCode
  (.seq (loadHeaderCode 16 16)
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 16)
    (.seq rehashLoopCode (.op (.const 2 0)))
    (.op (.const 2 0))))))

/-- Full `insert` operation (`insertCode`): stores `u.val = reg 3` in `mem[base + 11]` and
`v = reg 4` in `mem[base + 18]`, runs `probeKeyCode`, and branches on `foundFlag = mem[base + 13]`
between in-place value overwrite (`insertOverwriteBranchCode`) and new-key insertion with bounded
eviction and Las Vegas rehash (`insertNewKeyBranchCode`). -/
@[expose]
def insertCode : Code .exact 19 :=
  .seq (storeHeaderCode 11 3)
  (.seq (storeHeaderCode 18 4)
  (.seq probeKeyCode
  (.seq (loadHeaderCode 16 13)
  (.seq (.op (.const 15 0))
  (.branch (.lt 15 16)
    insertOverwriteBranchCode
    insertNewKeyBranchCode)))))

/-- Base step overhead of `insertCode` outside the eviction and rehash loops. -/
@[expose]
def insertBaseSteps (n_max U : ℕ) : ℕ :=
  probeKeySteps n_max U + 66

/-- Worst-case expected step bound of `insertCode` when a rehash may be triggered. -/
@[expose]
def insertWorstSteps (n_max U : ℕ) : ℕ :=
  insertBaseSteps n_max U + maxEvictions n_max * evictIterSteps n_max U +
    rehashLoopSteps n_max U + 2

/-- State-and-seed-dependent step bound for `insertCode` on insertion-order key list `ks`,
seed `θ`, dictionary state `s`, and key `u`. -/
@[expose]
noncomputable def insertSeedSteps (n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed U (tableBits n_max)) (s : Dictionary.State U) (u : Fin U) : ℝ≥0∞ := by
  classical
  exact
    if u ∈ Dictionary.dom s then
      (insertBaseSteps n_max U : ℝ≥0∞)
    else if θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) ∨
        θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks then
      (insertBaseSteps n_max U +
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps n_max U : ℕ)
    else
      (insertWorstSteps n_max U : ℝ≥0∞)

theorem insertSeedSteps_le_insertWorstSteps (n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed U (tableBits n_max)) (s : Dictionary.State U) (u : Fin U) :
    insertSeedSteps n_max U ks θ s u ≤ (insertWorstSteps n_max U : ℝ≥0∞) := by
  classical
  dsimp only [insertSeedSteps]
  split_ifs
  · exact_mod_cast (by dsimp only [insertWorstSteps]; omega :
      insertBaseSteps n_max U ≤ insertWorstSteps n_max U)
  · have hwalk := cuckooWalkRounds_le_maxLoop (evalHash1 θ) (evalHash2 θ)
      (maxEvictions n_max) (Dictionary.dom s) u
    have hmul :
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps n_max U ≤
          maxEvictions n_max * evictIterSteps n_max U :=
      Nat.mul_le_mul_right _ hwalk
    exact_mod_cast (by dsimp only [insertWorstSteps]; omega :
      insertBaseSteps n_max U +
        cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (Dictionary.dom s) u *
          evictIterSteps n_max U ≤ insertWorstSteps n_max U)
  · exact le_rfl

/-- Insertion-order key list after executing dictionary operation `o` from key list `ks`. -/
@[expose]
def stepKeys {U : ℕ} (ks : List (Fin U)) : Dictionary.Op U → List (Fin U)
  | .get _ => ks
  | .insert u _ => if u ∈ ks then ks else ks ++ [u]

theorem survivingSeeds_stepKeys_subset {U : ℕ} (n_max : ℕ) (ks : List (Fin U))
    (o : Dictionary.Op U) :
    survivingSeeds (Θ := Seed U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) ⊆
      survivingSeeds (Θ := Seed U (tableBits n_max))
        evalHash1 evalHash2 (maxEvictions n_max) ks := by
  cases o with
  | get _ => exact Finset.Subset.refl _
  | insert u _ =>
    dsimp only [stepKeys]
    split_ifs
    · exact Finset.Subset.refl _
    · exact survivingSeeds_append_subset _ _ _ _ _

theorem rehashLoopCode_set2_execCodeDist {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {x₀ x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hinv : RehashLoopInv w base n_max U V ks s x₀ x)
    (hm16 : x.mem (base + 16) = 1)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    ∃ (μ_out : PMF (Data 19))
      (hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty),
      ExecCodeDist w (.seq rehashLoopCode (.op (.const 2 0))) x μ_out
        (rehashLoopSteps n_max U + 1) ∧
      μ_out.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE ∧
      ∀ y ∈ μ_out.support,
        y.regs 2 = 0 ∧ RehashLoopPost w base n_max U V ks s x₀ y := by
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  obtain ⟨μ_reh, hE, hreh_dist, hreh_law, hreh_supp⟩ :=
    rehashLoopCode_execCodeDist hreh hinv hm16 hfit_ev hw hfit_end hfit_q
  let μ_out := μ_reh.map (fun z => z.set 2 0)
  have hseq := hreh_dist.seq_const
    (c₂ := .op (.const 2 0))
    (μ₂ := fun z => PMF.pure (z.set 2 0))
    (T₂ := fun _ => ((1 : ℕ) : ℝ≥0∞))
    (B₂ := ((1 : ℕ) : ℝ≥0∞))
    (fun z _ => ExecCodeDist.of_exec (Exec.const (B := .exact) (d := 2) hfit_0))
    (fun _ _ => le_rfl)
  have hout_law :
      μ_out.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE := by
    dsimp only [μ_out]
    rw [PMF.map_comp]
    exact hreh_law
  refine ⟨μ_out, hE, hseq.congr_dist rfl (by push_cast; rfl), hout_law, ?_⟩
  intro y hy
  dsimp only [μ_out] at hy
  rw [PMF.mem_support_map_iff] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨⟨hz_bdd, hz_0, hz_hdr, hz_tab, hz_kv, hz_mod⟩, hz_hash, tbl, hrep, hslots⟩ :=
    hreh_supp z hz
  have hy_bdd : (z.set 2 0).Bounded w :=
    (Exec.const (B := .exact) (d := 2) hfit_0).bounded hz_bdd
  refine ⟨by simp +decide [Data.set], ⟨hy_bdd, by simp +decide [Data.set, hz_0],
    hz_hdr, hz_tab, hz_kv, hz_mod⟩, hz_hash, tbl, hrep, hslots⟩

open Classical in
theorem insertNewKeyBranchCode_execCodeDist {w base n_max U V v : ℕ}
    {ks : List (Fin U)}
    {tbl : PureTable U (2 ^ tableBits n_max)} {s : Dictionary.State U}
    {u : Fin U} {x₀ x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hx_bdd : x.Bounded w)
    (h0 : x.regs 0 = base)
    (hhdr : HeaderConstsRep base n_max U x.mem)
    (hhash : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) x.mem) x.mem)
    (hkv : KeysValsRep base n_max U V ks s x.mem)
    (hreplay : pureReplay
      (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) x.mem))
      (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) x.mem))
      (maxEvictions n_max) ks = some tbl)
    (hslots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl x.mem)
    (hm11 : x.mem (base + 11) = u.val)
    (hm18 : x.mem (base + 18) = v)
    (hu_notMem : u ∉ ks)
    (hlen_lt : ks.length < n_max)
    (hv : v < V)
    (hmod : Modifies (Block.mk base (space n_max)).footprint x₀.mem x.mem)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) n_max U (tableBits n_max) x.mem
    ∃ (μ_br : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u])).Nonempty),
      ExecCodeDist w insertNewKeyBranchCode x μ_br
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) then
          (cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
            (Dictionary.dom s) u * evictIterSteps n_max U + 54 : ℕ)
         else
          (maxEvictions n_max * evictIterSteps n_max U + 54 +
            rehashLoopSteps n_max U + 2 : ℕ)) ∧
      μ_br.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u])) hE') ∧
      ∀ y ∈ μ_br.support,
        y.regs 2 = 0 ∧
        RepWithKeys w base n_max U V (ks ++ [u]) (Function.update s u (some v)) y ∧
        Modifies (Block.mk base (space n_max)).footprint x₀.mem y.mem := by
  classical
  intro θ_mem
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_16 : Fits w 16 := hfit_end.of_le (by omega)
  have hfit_b16 : Fits w (base + 16) := hfit_end.of_le (by omega)
  obtain ⟨s1, he_setup, hs1_0, hs1_5, hs1_11, hs1_12, hs1_15, hs1_16, hs1_knew, hs1_vnew,
      hs1_frame⟩ :=
    insertNewKeySetupCode_exec hhdr h0 hkv.2.2.1 hm11 hm18 hlen_lt hfit_end
  have hs1_hdr : HeaderConstsRep base n_max U s1.mem :=
    hhdr.congr fun k hk _ => hs1_frame (base + k)
      (by omega) (by omega) (by omega) (by omega)
      (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
      (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
  have hin_hp : ∀ a, hashBase base ≤ a → a < t1Base base n_max → s1.mem a = x.mem a :=
    fun a hlo hhi => hs1_frame a (by dsimp only [hashBase] at hlo; omega)
      (by dsimp only [hashBase] at hlo; omega) (by dsimp only [hashBase] at hlo; omega)
      (by dsimp only [hashBase] at hlo; omega)
      (by dsimp only [keysBase, t2Base] at *; omega)
      (by dsimp only [valsBase, keysBase, t2Base] at *; omega)
  have hz1_ge : hashBase base + 47 ≤ z1Base (hashBase base) n_max := by
    rw [z1Base_eq]; exact Nat.le_add_right _ _
  have hz1_end : z1Base (hashBase base) n_max + 2 * 2 ^ tableBits n_max = t1Base base n_max := by
    dsimp only [t1Base]; rw [z1Base_eq, hashPairSpace_eq]; omega
  have hcl_end : hashBase base + 47 + 2 ^ (2 * KWise.chunkBits n_max) ≤ t1Base base n_max := by
    rw [← z1Base_eq, ← hz1_end]; exact Nat.le_add_right _ _
  have hs1_hash : HashPairRep (hashBase base) n_max U (tableBits n_max) θ_mem s1.mem := by
    rcases hhash with ⟨⟨hM, hz1, hz2, h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
      ⟨hpoly, htab1, htab2⟩⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans hM
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans hz1
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans hz2
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h0'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h1'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h2'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h3'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h4'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h5'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h6'
    · exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans h7'
    · intro idx hidx
      exact (hin_hp _ (by omega) (by omega)).trans (hcl idx hidx)
    · intro r j
      have hr := r.isLt; have hj := j.isLt
      exact (hin_hp _ (by omega) (by dsimp only [t1Base]; omega)).trans (hpoly r j)
    · intro i
      have hi := i.isLt
      exact (hin_hp _ (by omega) (by omega)).trans (htab1 i)
    · intro i
      have hi := i.isLt
      exact (hin_hp _ (by dsimp only [z2Base]; omega)
        (by dsimp only [z2Base]; omega)).trans (htab2 i)
  have hs1_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s1.mem = θ_mem := by
    have hpoly : Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 s1.mem =
        Tabulation.extractSlice (hashBase base + 4)
          (Probability.trinomialDeg U (tableBits n_max)) 28 x.mem := by
      funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _)
        (hin_hp _ (by omega) (by dsimp only [t1Base]; omega))
    have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) s1.mem =
        Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
          (2 * 2 ^ tableBits n_max) x.mem := by
      funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
      exact congrArg (Tabulation.extractWord _)
        (hin_hp _ (by omega) (by omega))
    dsimp only [θ_mem, extractSeed]; rw [hpoly, htab]
  have hs1_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s1.mem :=
    hslots.congr
      (fun b hb => hs1_frame _
        (by dsimp only [t1Base, hashBase]; omega) (by dsimp only [t1Base, hashBase]; omega)
        (by dsimp only [t1Base, hashBase]; omega) (by dsimp only [t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, tableSize] at *; omega)
        (by dsimp only [valsBase, keysBase, t2Base, tableSize] at *; omega))
      (fun b hb => hs1_frame _
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, tableSize] at *; omega)
        (by dsimp only [valsBase, keysBase, tableSize] at *; omega))
  have hs1_kv : KeysValsRep base n_max U V (ks ++ [u]) (Function.update s u (some v)) s1.mem :=
    hkv.insert_of_notMem hv hu_notMem hlen_lt hs1_5
      (fun j hj => hs1_frame _
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by omega) (by dsimp only [valsBase]; omega))
      hs1_knew
      (fun j hj => hs1_frame _
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase]; omega) (by omega))
      hs1_vnew
  have hs1_tiv : TableIdxValid (ks ++ [u]) tbl := by
    intro e he
    obtain ⟨hlt, hget⟩ := pureReplay_tableIdxValid hkv.1 hreplay e he
    exact ⟨by simp; omega, by rw [List.getElem?_append_left hlt]; exact hget⟩
  obtain ⟨s2, ⟨t_ev, ht_ev, he_ev⟩, hs2_0, hs2_hdr, hs2_hash, hs2_seed, hs2_res, hs2_frame⟩ :=
    evictLoopCode_execWithin (ks := ks ++ [u]) (e := ⟨u, ks.length⟩)
      hs1_hdr hs1_hash hs1_slots hs1_tiv
      ⟨by simp, by simp⟩ hs1_kv.2.1
      (fun idx hidx => (hs1_kv.2.2.2.2.1 idx hidx).1)
      hs1_0 hs1_11 hs1_12 hs1_15 hs1_16 hfit_ev hw hfit_end
  have e_ld16 := loadHeaderCode_exec (dst := 16) (off := 16) (x := s2)
    hs2_0 (by decide) (by decide) hfit_16 hfit_b16
  set s3 := (s2.set 15 16).set 16 (s2.mem (base + 16))
  set s4 := s3.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s3 s4 1 := Exec.const hfit_0
  have hs4_0 : s4.regs 0 = base := by simp +decide [s4, s3, hs2_0]
  have hs4_mem : s4.mem = s2.mem := rfl
  have hs4_kv : KeysValsRep base n_max U V (ks ++ [u]) (Function.update s u (some v)) s4.mem := by
    rw [hs4_mem]
    exact hs1_kv.congr
      (hs2_frame (base + 5) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by omega)
        (Or.inl (by dsimp only [t1Base, hashBase]; omega)))
      (fun idx _ => hs2_frame (keysBase base n_max + idx)
        (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (Or.inr (Nat.le_add_right _ _)))
      (fun idx _ => hs2_frame (valsBase base n_max + idx)
        (Or.inr (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (Or.inr (by dsimp only [valsBase]; omega)))
  have hs4_mod : Modifies (Block.mk base (space n_max)).footprint x₀.mem s4.mem := by
    intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
    have ha_out : a < hashBase base + 40 ∨ hashBase base + 47 ≤ a :=
      ha.imp (by dsimp only [hashBase]; omega) (by dsimp only [hashBase]; omega)
    have ha_tbl : a < t1Base base n_max ∨ keysBase base n_max ≤ a :=
      ha.imp (by dsimp only [t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase, space]; omega)
    rw [hs4_mem, hs2_frame a ha_out (by omega) (by omega) (by omega) (by omega) ha_tbl,
      hs1_frame a (by omega) (by omega) (by omega) (by omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase, space] at *; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space] at *; omega)]
    exact hmod a (by simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le]; exact ha)
  have hs4_bdd : s4.Bounded w :=
    (he_setup.seq (he_ev.seq (e_ld16.seq e_c0))).bounded hx_bdd
  have hs4_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem = θ_mem := by
    rw [hs4_mem]; exact hs2_seed.trans hs1_seed
  have hrounds_le_max :
      evictRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl ⟨u, ks.length⟩ ≤
        maxEvictions n_max :=
    evictRounds_le (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl ⟨u, ks.length⟩
  cases hev_eq : pureEvict (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl
      ⟨u, ks.length⟩ with
  | some tbl' =>
    rw [hev_eq] at hs2_res
    obtain ⟨hs2_16_0, hs2_slots, _⟩ := hs2_res
    have hmem_surv :
        θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) := by
      rw [mem_survivingSeeds, pureReplay_append_singleton, hreplay]
      simp [hev_eq]
    have hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u])).Nonempty :=
      ⟨θ_mem, hmem_surv⟩
    have hcond : ¬(Cond.lt 15 16 : Cond 19).Holds s4 := by
      simp [Cond.Holds, s4, s3, hs2_16_0]
    set s5 := s4.set 2 0
    have e_c2 : Exec w (.op (.const 2 0) : Code .exact 19) s4 s5 1 := Exec.const hfit_0
    have e_br := e_c2.branch_neg (pos := .seq rehashLoopCode (.op (.const 2 0))) hcond
    have hall : Exec w insertNewKeyBranchCode x s5 (37 + (t_ev + (3 + (1 + (1 + 2))))) :=
      he_setup.seq (he_ev.seq (e_ld16.seq (e_c0.seq e_br)))
    have hrep_s5 : RepWithKeys w base n_max U V (ks ++ [u]) (Function.update s u (some v)) s5 := by
      refine ⟨hall.bounded hx_bdd, by simp +decide [s5, hs4_0], hs2_hdr, ?_,
        hs4_kv, tbl', ?_, hs2_slots⟩
      · change HashPairRep _ _ _ _
          (extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem) s4.mem
        rw [hs4_seed, hs4_mem]; exact hs2_hash
      · change pureReplay
          (evalHash1 (extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem))
          (evalHash2 (extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem))
          (maxEvictions n_max) (ks ++ [u]) = some tbl'
        rw [hs4_seed, pureReplay_append_singleton, hreplay]
        simp [hev_eq]
    refine ⟨PMF.pure s5, hE', (ExecCodeDist.of_exec hall).mono ?_, ?_, ?_⟩
    · simp only [hmem_surv, ↓reduceIte]
      have hvp : ValidPlacement (evalHash1 θ_mem) (evalHash2 θ_mem) (Dictionary.dom s) tbl :=
        pureReplay_validPlacement hkv.1 (fun x hx => (hkv.2.2.2.1 x).mp hx) hreplay
      have hwalk_le :=
        evictRounds_le_cuckooWalkRounds (maxLoop := maxEvictions n_max) hvp u ks.length
      have hwalk_mul :
          evictRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max) tbl
              { key := u, idx := ks.length } * evictIterSteps n_max U ≤
            cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
              (Dictionary.dom s) u * evictIterSteps n_max U :=
        Nat.mul_le_mul_right _ hwalk_le
      exact_mod_cast (by omega : 37 + (t_ev + (3 + (1 + (1 + 2)))) ≤
        cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
          (Dictionary.dom s) u * evictIterSteps n_max U + 54)
    · simp only [hmem_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply]
      change PMF.pure (extractSeed (hashBase base) n_max U (tableBits n_max) s4.mem) =
        PMF.pure θ_mem
      rw [hs4_seed]
    · intro y hy
      rw [PMF.support_pure, Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨by simp +decide [s5], hrep_s5, hs4_mod⟩
  | none =>
    rw [hev_eq] at hs2_res
    have hnot_surv :
        θ_mem ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) := by
      rw [mem_survivingSeeds, pureReplay_append_singleton, hreplay]
      simp [hev_eq]
    simp only [hnot_surv, ↓reduceIte]
    have hcond : (Cond.lt 15 16 : Cond 19).Holds s4 := by
      simp [Cond.Holds, s4, s3, hs2_res]
    have hs4_inv :
        RehashLoopInv w base n_max U V (ks ++ [u]) (Function.update s u (some v)) x₀ s4 :=
      ⟨hs4_bdd, hs4_0, hs2_hdr, hs2_hash.1, hs4_kv, hs4_mod⟩
    obtain ⟨μ_out, hE', hout_dist, hout_law, hout_supp⟩ :=
      rehashLoopCode_set2_execCodeDist hreh hs4_inv hs2_res hfit_ev hw hfit_end hfit_q
    have hbr := hout_dist.branch_pos (neg := .op (.const 2 0)) hcond
    have h1 := (ExecCodeDist.of_exec e_c0).seq_pure hbr
    have h2 := (ExecCodeDist.of_exec e_ld16).seq_pure h1
    have h3 := (ExecCodeDist.of_exec he_ev).seq_pure h2
    have hseq := (ExecCodeDist.of_exec he_setup).seq_pure h3
    have ht_ev_max : t_ev ≤ maxEvictions n_max * evictIterSteps n_max U + 10 :=
      le_trans ht_ev (Nat.add_le_add_right (Nat.mul_le_mul_right _ hrounds_le_max) 10)
    refine ⟨μ_out, hE', hseq.mono ?_, hout_law, ?_⟩
    · exact_mod_cast (by omega :
        37 + (t_ev + (3 + (1 + ((rehashLoopSteps n_max U + 1) + 1)))) ≤
          maxEvictions n_max * evictIterSteps n_max U + 54 + rehashLoopSteps n_max U + 2)
    · intro y hy
      obtain ⟨hy_2, ⟨hy_bdd, hy_0, hy_hdr, _, hy_kv, hy_mod⟩, hy_hash, tbl', hy_rep, hy_slots⟩ :=
        hout_supp y hy
      exact ⟨hy_2, ⟨hy_bdd, hy_0, hy_hdr, hy_hash, hy_kv, tbl', hy_rep, hy_slots⟩, hy_mod⟩

theorem insertCode_execCodeDist {w base n_max U V v : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    {u : Fin U} {x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hrep : RepWithKeys w base n_max U V ks s x)
    (h3 : x.regs 3 = u.val)
    (h4 : x.regs 4 = v)
    (hpre : ((Dictionary.dom s).card < n_max ∨ (s u).isSome) ∧ v < V)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) n_max U (tableBits n_max) x.mem
    ∃ (μ_ins : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
        (stepKeys ks (.insert u v))).Nonempty),
      ExecCodeDist w insertCode x μ_ins (insertSeedSteps n_max U ks θ_mem s u) ∧
      μ_ins.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
            (stepKeys ks (.insert u v)) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
              (stepKeys ks (.insert u v))) hE') ∧
      ∀ y ∈ μ_ins.support,
        y.regs 2 = 0 ∧
        RepWithKeys w base n_max U V (stepKeys ks (.insert u v))
          (Function.update s u (some v)) y ∧
        Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  classical
  intro θ_mem
  have hθ_surv : θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks :=
    hrep.extractSeed_mem_survivingSeeds
  obtain ⟨hx_bdd, h0, hhdr, hhash, hkv, tbl, hreplay, hslots⟩ := hrep
  have hle_sp := le_space n_max
  have hle_hp := le_hashPairSpace n_max (tableBits n_max)
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hfit_11 : Fits w 11 := hfit_end.of_le (by omega)
  have hfit_13 : Fits w 13 := hfit_end.of_le (by omega)
  have hfit_18 : Fits w 18 := hfit_end.of_le (by omega)
  have hfit_b11 : Fits w (base + 11) := hfit_end.of_le (by omega)
  have hfit_b13 : Fits w (base + 13) := hfit_end.of_le (by omega)
  have hfit_b18 : Fits w (base + 18) := hfit_end.of_le (by omega)
  have e_st11 := storeHeaderCode_exec (off := 11) (src := 3) (x := x)
    h0 (by decide) (by decide) hfit_11 hfit_b11
  set s1 := (((x.set 15 11).set 16 (base + 11)).write (base + 11) (x.regs 3))
  have e_st18 := storeHeaderCode_exec (off := 18) (src := 4) (x := s1)
    (by simp +decide [s1, h0]) (by decide) (by decide) hfit_18 hfit_b18
  set s2 := (((s1.set 15 18).set 16 (base + 18)).write (base + 18) (s1.regs 4))
  have hs2_frame : ∀ a, a ≠ base + 11 → a ≠ base + 18 → s2.mem a = x.mem a := by
    intro a ha11 ha18
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne ha18, Function.update_of_ne ha11]
  have hs2_11 : s2.mem (base + 11) = u.val := by
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_of_ne (by omega), Function.update_self, h3]
  have hs2_18 : s2.mem (base + 18) = v := by
    dsimp only [s2, s1, Data.write, Data.set]
    rw [Function.update_self]; simp +decide [h4]
  have hs2_seed : extractSeed (hashBase base) n_max U (tableBits n_max) s2.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    extractSeed_congr_of_ge_hashBase fun a ha =>
      hs2_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
  have hs2_hash : HashPairRep (hashBase base) n_max U (tableBits n_max)
      (extractSeed (hashBase base) n_max U (tableBits n_max) x.mem) s2.mem :=
    hhash.congr_of_ge_hashBase fun a ha =>
      hs2_frame a (by dsimp only [hashBase] at ha; omega) (by dsimp only [hashBase] at ha; omega)
  have hs2_hdr : HeaderConstsRep base n_max U s2.mem :=
    hhdr.congr fun k hk _ => hs2_frame (base + k) (by omega) (by omega)
  have hs2_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s2.mem :=
    hslots.congr
      (fun b _ => hs2_frame _
        (by dsimp only [t1Base, hashBase]; omega) (by dsimp only [t1Base, hashBase]; omega))
      (fun b _ => hs2_frame _
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega))
  have htiv := pureReplay_tableIdxValid hkv.1 hreplay
  obtain ⟨s3, ⟨t_probe, ht_probe, he_probe⟩, hs3_0, hs3_hdr, hs3_hash, hs3_seed, hs3_lookup,
      hs3_frame⟩ :=
    probeKeyCode_execWithin (x := s2)
      hs2_hdr hs2_hash hs2_slots htiv hkv.2.1
      (fun idx hlt => by
        rw [hs2_frame _
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
          (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)]
        exact (hkv.2.2.2.2.1 idx hlt).1)
      (by simp +decide [s2, s1, h0]) hs2_11 hw hfit_end
  have hs3_frame_x : ∀ a, (a < hashBase base + 40 ∨ hashBase base + 47 ≤ a) →
      a ≠ base + 11 → a ≠ base + 13 → a ≠ base + 14 → a ≠ base + 18 → s3.mem a = x.mem a :=
    fun a ha ha11 ha13 ha14 ha18 =>
      (hs3_frame a ha ha13 ha14).trans (hs2_frame a ha11 ha18)
  have hs3_seed_x : extractSeed (hashBase base) n_max U (tableBits n_max) s3.mem =
      extractSeed (hashBase base) n_max U (tableBits n_max) x.mem :=
    hs3_seed.trans hs2_seed
  have hs3_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl s3.mem :=
    hslots.congr
      (fun b _ => hs3_frame_x _
        (Or.inr (by dsimp only [t1Base, hashBase]; omega))
        (by dsimp only [t1Base, hashBase]; omega) (by dsimp only [t1Base, hashBase]; omega)
        (by dsimp only [t1Base, hashBase]; omega) (by dsimp only [t1Base, hashBase]; omega))
      (fun b _ => hs3_frame_x _
        (Or.inr (by dsimp only [t2Base, t1Base, hashBase]; omega))
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega)
        (by dsimp only [t2Base, t1Base, hashBase]; omega))
  have hs3_kv : KeysValsRep base n_max U V ks s s3.mem :=
    hkv.congr
      (hs3_frame_x (base + 5) (Or.inl (by dsimp only [hashBase]; omega))
        (by omega) (by omega) (by omega) (by omega))
      (fun idx _ => hs3_frame_x (keysBase base n_max + idx)
        (Or.inr (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [keysBase, t2Base, t1Base, hashBase]; omega))
      (fun idx _ => hs3_frame_x (valsBase base n_max + idx)
        (Or.inr (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega))
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega)
        (by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega))
  have hs3_11 : s3.mem (base + 11) = u.val := by
    rw [hs3_frame (base + 11) (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega)]
    exact hs2_11
  have hs3_18 : s3.mem (base + 18) = v := by
    rw [hs3_frame (base + 18) (Or.inl (by dsimp only [hashBase]; omega)) (by omega) (by omega)]
    exact hs2_18
  have e_ld13 := loadHeaderCode_exec (dst := 16) (off := 13) (x := s3)
    hs3_0 (by decide) (by decide) hfit_13 hfit_b13
  set s4 := (s3.set 15 13).set 16 (s3.mem (base + 13))
  set s5 := s4.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) s4 s5 1 := Exec.const hfit_0
  have hs5_0 : s5.regs 0 = base := by simp +decide [s5, s4, hs3_0]
  have hs5_mem : s5.mem = s3.mem := rfl
  have hs5_mod : Modifies (Block.mk base (space n_max)).footprint x.mem s5.mem := by
    intro a ha
    simp only [Block.mem_footprint, Block.Owns, not_and_or, not_le] at ha
    have ha_out : a < hashBase base + 40 ∨ hashBase base + 47 ≤ a :=
      ha.imp (by dsimp only [hashBase]; omega) (by dsimp only [hashBase]; omega)
    exact hs3_frame_x a ha_out (by omega) (by omega) (by omega) (by omega)
  have he_pref : Exec w
      (.seq (storeHeaderCode 11 3)
      (.seq (storeHeaderCode 18 4)
      (.seq probeKeyCode
      (.seq (loadHeaderCode 16 13)
            (.op (.const 15 0)))))) x s5 (3 + (3 + (t_probe + (3 + 1)))) :=
    e_st11.seq (e_st18.seq (he_probe.seq (e_ld13.seq e_c0)))
  by_cases hu : u ∈ Dictionary.dom s
  · have hu_ks : u ∈ ks := (hkv.2.2.2.1 u).mpr hu
    obtain ⟨idx, hidx_lt, hks_idx⟩ := List.mem_iff_getElem.mp hu_ks
    have hlook := pureReplay_lookupEntry_of_mem hkv.1 hreplay hidx_lt
    rw [hks_idx] at hlook
    rw [hlook] at hs3_lookup
    obtain ⟨hs3_13, hs3_14⟩ := hs3_lookup
    dsimp only at hs3_14
    have hcond : (Cond.lt 15 16 : Cond 19).Holds s5 := by
      simp [Cond.Holds, s5, s4, hs3_13]
    obtain ⟨y, he_ov, hy_0, hy_2, hy_val, hy_frame⟩ :=
      insertOverwriteBranchCode_exec (n_max := n_max) hs5_0 hs3_hdr.2.2.2.2.2.2.2.2.2
        hs3_14 hs3_18 (lt_of_lt_of_le hidx_lt hkv.2.1) hfit_end
    have e_br := he_ov.branch_pos (neg := insertNewKeyBranchCode) hcond
    have hall : Exec w insertCode x y (3 + (3 + (t_probe + (3 + (1 + (12 + 1)))))) :=
      e_st11.seq (e_st18.seq (he_probe.seq (e_ld13.seq (e_c0.seq e_br))))
    have hin_lt_t1 : ∀ a < t1Base base n_max, y.mem a = s3.mem a :=
      fun a ha => hy_frame a (by dsimp only [valsBase, keysBase, t2Base] at *; omega)
    have hy_seed : extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) x.mem := by
      have hsp_eq := hashPairSpace_eq n_max (tableBits n_max)
      have hz1_eq := z1Base_eq (hashBase base) n_max
      have hpoly : Tabulation.extractSlice (hashBase base + 4)
            (Probability.trinomialDeg U (tableBits n_max)) 28 y.mem =
          Tabulation.extractSlice (hashBase base + 4)
            (Probability.trinomialDeg U (tableBits n_max)) 28 s3.mem := by
        funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
        exact congrArg (Tabulation.extractWord _)
          (hin_lt_t1 _ (by dsimp only [t1Base]; omega))
      have htab : Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
            (2 * 2 ^ tableBits n_max) y.mem =
          Tabulation.extractSlice (z1Base (hashBase base) n_max) (tableBits n_max)
            (2 * 2 ^ tableBits n_max) s3.mem := by
        funext i; have hi := i.isLt; dsimp only [Tabulation.extractSlice]
        exact congrArg (Tabulation.extractWord _)
          (hin_lt_t1 _ (by dsimp only [t1Base]; rw [hz1_eq] at *; omega))
      refine (?_ : extractSeed (hashBase base) n_max U (tableBits n_max) y.mem =
        extractSeed (hashBase base) n_max U (tableBits n_max) s3.mem).trans hs3_seed_x
      dsimp only [extractSeed]; rw [hpoly, htab]
    have hy_hash : HashPairRep (hashBase base) n_max U (tableBits n_max)
        (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) y.mem := by
      rw [hy_seed]
      rcases hs3_hash with ⟨⟨hM, hz1, hz2, h0', h1', h2', h3', h4', h5', h6', h7', hcl⟩,
        ⟨hpoly, htab1, htab2⟩⟩
      have hsp_eq := hashPairSpace_eq n_max (tableBits n_max)
      have hz1_eq := z1Base_eq (hashBase base) n_max
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans hM
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans hz1
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans hz2
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h0'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h1'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h2'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h3'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h4'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h5'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h6'
      · exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans h7'
      · intro j hj; exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans (hcl j hj)
      · intro r j
        have hr := r.isLt; have hj := j.isLt
        exact (hin_lt_t1 _ (by dsimp only [t1Base]; omega)).trans (hpoly r j)
      · intro i
        have hi := i.isLt
        exact (hin_lt_t1 _ (by dsimp only [t1Base]; rw [hz1_eq] at *; omega)).trans (htab1 i)
      · intro i
        have hi := i.isLt
        exact (hin_lt_t1 _ (by dsimp only [t1Base, z2Base]; rw [hz1_eq] at *; omega)).trans
          (htab2 i)
    have hy_hdr : HeaderConstsRep base n_max U y.mem :=
      hs3_hdr.congr fun k hk _ => hin_lt_t1 (base + k) (by dsimp only [t1Base, hashBase]; omega)
    have hy_slots : TableSlotsRep (t1Base base n_max) (t2Base base n_max) tbl y.mem :=
      hs3_slots.congr
        (fun b hb => hy_frame _ (by dsimp only [valsBase, keysBase, t2Base, tableSize] at *; omega))
        (fun b hb => hy_frame _ (by dsimp only [valsBase, keysBase, tableSize] at *; omega))
    have hlen_le : ks.length ≤ n_max := hkv.2.1
    have hy_kv : KeysValsRep base n_max U V ks (Function.update s u (some v)) y.mem :=
      hs3_kv.insert_of_mem hpre.2 hidx_lt hks_idx
        (hin_lt_t1 (base + 5) (by dsimp only [t1Base, hashBase]; omega))
        (fun j hj => hy_frame _ (by dsimp only [valsBase]; omega))
        hy_val
        (fun j _ hne => hy_frame _ (by omega))
    have hy_mod : Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
      intro a ha
      have ha_ne : a ≠ valsBase base n_max + idx := by
        intro h; subst h
        have hlt_n : idx < n_max := lt_of_lt_of_le hidx_lt hkv.2.1
        simp only [Block.mem_footprint, Block.Owns] at ha
        exact ha ⟨by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase]; omega,
          by dsimp only [valsBase, keysBase, t2Base, t1Base, hashBase, space]; omega⟩
      rw [hy_frame a ha_ne]
      exact hs5_mod a ha
    have hstep_eq : stepKeys ks (.insert u v) = ks := by
      simp [stepKeys, hu_ks]
    have hE' :
        (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2 (maxEvictions n_max)
          (stepKeys ks (.insert u v))).Nonempty := by
      rw [hstep_eq]
      exact ⟨θ_mem, hθ_surv⟩
    have hy_rep :
        RepWithKeys w base n_max U V (stepKeys ks (.insert u v))
          (Function.update s u (some v)) y := by
      rw [hstep_eq]
      exact ⟨hall.bounded hx_bdd, hy_0, hy_hdr, hy_hash, hy_kv, tbl,
        by rw [hy_seed]; exact hreplay, hy_slots⟩
    refine ⟨PMF.pure y, hE', (ExecCodeDist.of_exec hall).mono ?_, ?_, ?_⟩
    · dsimp only [insertSeedSteps]
      simp only [hu, ↓reduceIte]
      exact_mod_cast (by dsimp only [insertBaseSteps]; omega :
        3 + (3 + (t_probe + (3 + (1 + (12 + 1))))) ≤ insertBaseSteps n_max U)
    · simp only [hstep_eq, hθ_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply]
      rw [hy_seed]
    · intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨hy_2, hy_rep, hy_mod⟩
  · have hu_ks : u ∉ ks := fun h => hu ((hkv.2.2.2.1 u).mp h)
    have hstep_eq : stepKeys ks (.insert u v) = ks ++ [u] := by
      simp [stepKeys, hu_ks]
    have hnone_u : s u = none := Dictionary.notMem_dom_iff.mp hu
    have hcard_lt : (Dictionary.dom s).card < n_max := by
      rcases hpre.1 with hlt | hsome
      · exact hlt
      · rw [hnone_u] at hsome; exact Bool.noConfusion hsome
    have hlen_lt : ks.length < n_max := by
      rwa [← hkv.card_dom_eq]
    have hlook := pureReplay_lookupEntry_of_notMem hkv.1 hreplay hu_ks
    rw [hlook] at hs3_lookup
    have hcond : ¬(Cond.lt 15 16 : Cond 19).Holds s5 := by
      simp [Cond.Holds, s5, s4, hs3_lookup]
    obtain ⟨μ_br, hE'_br, hbr_dist, hbr_law, hbr_supp⟩ :=
      insertNewKeyBranchCode_execCodeDist (x₀ := x) (x := s5)
        hreh (he_pref.bounded hx_bdd) hs5_0 hs3_hdr
        (by rw [hs5_mem, hs3_seed_x]; exact hs3_hash)
        hs3_kv
        (by rw [hs5_mem, hs3_seed_x]; exact hreplay)
        hs3_slots hs3_11 hs3_18 hu_ks hlen_lt hpre.2 hs5_mod
        hfit_ev hw hfit_end hfit_q
    rw [hs5_mem, hs3_seed_x] at hbr_dist hbr_law
    have hE' :
        (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2 (maxEvictions n_max)
          (stepKeys ks (.insert u v))).Nonempty := by
      rw [hstep_eq]
      exact hE'_br
    have hbr := hbr_dist.branch_neg (pos := insertOverwriteBranchCode) hcond
    have h1 := (ExecCodeDist.of_exec e_c0).seq_pure hbr
    have h2 := (ExecCodeDist.of_exec e_ld13).seq_pure h1
    have h3 := (ExecCodeDist.of_exec he_probe).seq_pure h2
    have h4 := (ExecCodeDist.of_exec e_st18).seq_pure h3
    have hseq := (ExecCodeDist.of_exec e_st11).seq_pure h4
    refine ⟨μ_br, hE', hseq.mono ?_, ?_, ?_⟩
    · dsimp only [insertSeedSteps]
      simp only [hu, hθ_surv, not_true_eq_false, or_false, ↓reduceIte]
      split_ifs with hsurv'
      · exact_mod_cast (by dsimp only [insertBaseSteps]; omega :
          3 + (3 + (t_probe + (3 + (1 +
            ((cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
              (Dictionary.dom s) u * evictIterSteps n_max U + 54) + 2))))) ≤
          insertBaseSteps n_max U +
            cuckooWalkRounds (evalHash1 θ_mem) (evalHash2 θ_mem) (maxEvictions n_max)
              (Dictionary.dom s) u * evictIterSteps n_max U)
      · exact_mod_cast (by dsimp only [insertWorstSteps, insertBaseSteps]; omega :
          3 + (3 + (t_probe + (3 + (1 +
            ((maxEvictions n_max * evictIterSteps n_max U + 54 +
              rehashLoopSteps n_max U + 2) + 2))))) ≤
          insertWorstSteps n_max U)
    · simp only [hstep_eq]
      exact hbr_law
    · rw [hstep_eq]
      exact hbr_supp

/-! ### Section 6: `opCode`, `cuckooCode`, `subroutineDS`, and `cuckoo_seq_expected_amortized` -/

/-- Standalone register encoding for `Dictionary.Op U`:
* `get u` sets `reg 2 = 0` (selector) and `reg 3 = u.val`.
* `insert u v` sets `reg 2 = 1` (selector), `reg 3 = u.val`, and `reg 4 = v`. -/
@[expose]
def encode {U : ℕ} (o : Dictionary.Op U) (i : Fin 19) : ℕ :=
  match o with
  | .get u =>
    if i = 2 then 0
    else if i = 3 then u.val
    else 0
  | .insert u v =>
    if i = 2 then 1
    else if i = 3 then u.val
    else if i = 4 then v
    else 0

/-- Partial argument-matching predicate for inline callers on `Fin 19 → ℕ`. -/
@[expose]
def argMatch {U : ℕ} (o : Dictionary.Op U) (regs : Fin 19 → ℕ) : Prop :=
  match o with
  | .get u => regs 2 = 0 ∧ regs 3 = u.val
  | .insert u v => regs 2 = 1 ∧ regs 3 = u.val ∧ regs 4 = v

/-- Output decoder reading `Option ((Dictionary.spec U V n_max).Result o)` from final registers. -/
@[expose]
def decode {U V n_max : ℕ} (o : Dictionary.Op U) (regs : Fin 19 → ℕ) :
    Option ((Dictionary.spec U V n_max).Result o) :=
  match o with
  | .get _ => some (decodeOptionNat (regs 2))
  | .insert _ _ => some ()

/-- Combined operation body (`opCode`): dispatches on `reg 2 = 0` (`getCode`) vs `reg 2 ≠ 0`
(`insertCode`). -/
@[expose]
def opCode : Code .exact 19 :=
  .seq (.op (.const 15 0))
  (.branch (.eq 2 15)
    getCode
    insertCode)

/-- Amortized rehash contribution per insertion:
`(maxEvictions n_max * evictIterSteps n_max U + rehashLoopSteps n_max U + 2) /
  (max n_max 1 * max (maxEvictions n_max) 1) + 1`,
which is `O(evictIterSteps n_max U)`. -/
@[expose]
def rehashAmortizedSteps (n_max U : ℕ) : ℕ :=
  (maxEvictions n_max * evictIterSteps n_max U + rehashLoopSteps n_max U + 2) /
    (max n_max 1 * max (maxEvictions n_max) 1) + 1

/-- Amortized instruction charge for `insert` under a `(C_walk, C_reh)` cuckoo hash family. -/
@[expose]
def insertCharge (n_max U C_walk C_reh : ℕ) : ℕ :=
  2 * (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
    C_reh * rehashAmortizedSteps n_max U)

/-- Per-operation amortized instruction charge for `Dictionary.Op U`. -/
@[expose]
def charge (n_max U C_walk C_reh : ℕ) (_s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .get _ => getSteps n_max U + 2
  | .insert _ _ => insertCharge n_max U C_walk C_reh

/-- State-independent expected step bound for a single `opCode` invocation under an arbitrary
input distribution (used in the standalone `SubroutineDS` certificate, while
`cuckoo_seq_expected_amortized` establishes the tighter `charge` bound along valid trajectories
from `initFresh`). -/
@[expose]
def stepWorstCharge (n_max U : ℕ) (_s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .get _ => getSteps n_max U + 2
  | .insert _ _ => insertWorstSteps n_max U + 3

/-- Seed-and-state-dependent step bound for `opCode`. -/
@[expose]
noncomputable def opSeedSteps (n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed U (tableBits n_max)) (s : Dictionary.State U) : Dictionary.Op U → ℝ≥0∞
  | .get _ => (getSteps n_max U + 2 : ℕ)
  | .insert u _ => insertSeedSteps n_max U ks θ s u + 3

theorem opSeedSteps_le_stepWorstCharge (n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed U (tableBits n_max)) (s : Dictionary.State U) (o : Dictionary.Op U) :
    opSeedSteps n_max U ks θ s o ≤ (stepWorstCharge n_max U s o : ℝ≥0∞) := by
  cases o with
  | get _ => exact le_rfl
  | insert u _ =>
    dsimp only [opSeedSteps, stepWorstCharge]
    push_cast
    exact add_le_add (insertSeedSteps_le_insertWorstSteps n_max U ks θ s u) le_rfl

open Classical in
theorem opCode_execCodeDist {w base n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    (o : Dictionary.Op U) {x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hrep : RepWithKeys w base n_max U V ks s x)
    (hvalid : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatch o x.regs)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_V : Fits w V)
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) n_max U (tableBits n_max) x.mem
    ∃ (μ_op : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
        (stepKeys ks o)).Nonempty),
      ExecCodeDist w opCode x μ_op (opSeedSteps n_max U ks θ_mem s o) ∧
      μ_op.map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE') ∧
      ∀ y ∈ μ_op.support,
        decode (V := V) (n_max := n_max) o y.regs =
          some ((Dictionary.spec U V n_max).step s o).2 ∧
        RepWithKeys w base n_max U V (stepKeys ks o) ((Dictionary.spec U V n_max).step s o).1 y ∧
        Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  classical
  intro θ_mem
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  set s1 := x.set 15 0
  have e_c0 : Exec w (.op (.const 15 0) : Code .exact 19) x s1 1 := Exec.const hfit_0
  have hs1_rep : RepWithKeys w base n_max U V ks s s1 :=
    RepWithKeys.supported (x := x) (x' := s1) (by simp +decide [s1]) (fun _ _ => rfl)
      (e_c0.bounded hrep.1) hrep
  cases o with
  | get u =>
    obtain ⟨h2, h3⟩ := harg
    have hcond : (Cond.eq 2 15 : Cond 19).Holds s1 := by
      simp +decide [Cond.Holds, s1, h2]
    obtain ⟨y, ⟨t_g, ht_g, he_g⟩, hy_2, hy_rep, hy_seed, hy_mod⟩ :=
      getCode_execWithin (u := u) hs1_rep (by simp +decide [s1, h3]) hw hfit_end hfit_V
    have e_br := he_g.branch_pos (neg := insertCode) hcond
    have hall := e_c0.seq e_br
    have hθ_surv : θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks :=
      hrep.extractSeed_mem_survivingSeeds
    have hE' :
        (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
          (stepKeys ks (.get u))).Nonempty :=
      ⟨θ_mem, hθ_surv⟩
    refine ⟨PMF.pure y, hE', (ExecCodeDist.of_exec hall).mono ?_, ?_, ?_⟩
    · dsimp only [opSeedSteps]
      exact_mod_cast (by omega : 1 + (t_g + 1) ≤ getSteps n_max U + 2)
    · dsimp only [stepKeys]
      simp only [hθ_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply]
      rw [hy_seed]
      rfl
    · intro z hz
      rw [PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨?_, hy_rep, hy_mod⟩
      dsimp only [decode, Dictionary.spec]
      rw [hy_2, decodeOptionNat_encodeOptionNat]
  | insert u v =>
    obtain ⟨h2, h3, h4⟩ := harg
    have hcond : ¬(Cond.eq 2 15 : Cond 19).Holds s1 := by
      simp +decide [Cond.Holds, s1, h2]
    obtain ⟨μ_ins, hE', hins_dist, hins_law, hins_supp⟩ :=
      insertCode_execCodeDist hreh hs1_rep (by simp +decide [s1, h3])
        (by simp +decide [s1, h4]) hvalid hfit_ev hw hfit_end hfit_q
    have hbr := hins_dist.branch_neg (pos := getCode) hcond
    have hseq := (ExecCodeDist.of_exec e_c0).seq_pure hbr
    refine ⟨μ_ins, hE', hseq.mono ?_, hins_law, ?_⟩
    · dsimp only [opSeedSteps]
      change ((1 : ℕ) : ℝ≥0∞) + (insertSeedSteps n_max U ks θ_mem s u + 2) ≤
        insertSeedSteps n_max U ks θ_mem s u + 3
      rw [Nat.cast_one]
      exact le_of_eq (by ring)
    · intro y hy
      obtain ⟨_, hy_rep, hy_mod⟩ := hins_supp y hy
      exact ⟨rfl, hy_rep, hy_mod⟩

theorem tsum_seedLaw_insertSeedSteps_le {n_max U V C_walk C_reh v : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {u : Fin U}
    (hfam : IsCuckooHashFamily U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hnodup : ks.Nodup)
    (hdom : ∀ x, x ∈ ks ↔ x ∈ Dictionary.dom s)
    (hvalid : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    (∑' θ : Seed U (tableBits n_max),
      seedLaw U (tableBits n_max) θ * (insertSeedSteps n_max U ks θ s u + 3)) ≤
      (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
        C_reh * rehashAmortizedSteps n_max U : ℕ) := by
  classical
  set M := tableBits n_max
  set p := seedLaw U M
  by_cases hu : u ∈ Dictionary.dom s
  · have heq : (∑' θ : Seed U M, p θ * (insertSeedSteps n_max U ks θ s u + 3)) =
        (insertBaseSteps n_max U + 3 : ℝ≥0∞) := by
      have hcongr : ∀ θ : Seed U M,
          p θ * (insertSeedSteps n_max U ks θ s u + 3) =
            p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) := by
        intro θ; dsimp only [insertSeedSteps]; simp only [hu, ↓reduceIte]
      simp_rw [hcongr, ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
    rw [heq]
    exact_mod_cast (by omega : insertBaseSteps n_max U + 3 ≤
      insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
        C_reh * rehashAmortizedSteps n_max U)
  · have hu_ks : u ∉ ks := fun h => hu ((hdom u).mp h)
    have hnone_u : s u = none := Dictionary.notMem_dom_iff.mp hu
    have hcard_lt : (Dictionary.dom s).card < n_max := by
      rcases hvalid.1 with hlt | hsome
      · exact hlt
      · rw [hnone_u] at hsome; exact Bool.noConfusion hsome
    have htoFinset : ks.toFinset = Dictionary.dom s := by
      ext x; simp [hdom x]
    have hlen_lt : ks.length < n_max := by
      rw [← List.dedup_eq_self.mpr hnodup, ← List.card_toFinset, htoFinset]
      exact hcard_lt
    let F : Set (Seed U M) :=
      {θ | (pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks).isSome ∧
        (pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (ks ++ [u])).isNone}
    set R := maxEvictions n_max * evictIterSteps n_max U + rehashLoopSteps n_max U + 2
    have hpw : ∀ θ : Seed U M,
        p θ * (insertSeedSteps n_max U ks θ s u + 3) ≤
          p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) +
          (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max)
            (Dictionary.dom s) u : ℝ≥0∞)) * (evictIterSteps n_max U : ℝ≥0∞) +
          F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞) := by
      intro θ
      dsimp only [insertSeedSteps]
      simp only [hu, ↓reduceIte]
      by_cases hcond :
          θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) ∨
          θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks
      · have hnotF : θ ∉ F := by
          rcases hcond with h1 | h2
          · rw [mem_survivingSeeds] at h1
            intro hf
            exact Option.not_isSome_iff_eq_none.mpr (Option.isNone_iff_eq_none.mp hf.2) h1
          · rw [mem_survivingSeeds] at h2
            intro hf
            exact h2 hf.1
        simp only [hcond, ↓reduceIte, Set.indicator_of_notMem hnotF, zero_mul, add_zero]
        push_cast
        exact le_of_eq (by ring)
      · have hmemF : θ ∈ F := by
          rw [not_or, Classical.not_not, mem_survivingSeeds, mem_survivingSeeds] at hcond
          exact ⟨hcond.2, Option.isNone_iff_eq_none.mpr
            (Option.not_isSome_iff_eq_none.mp hcond.1)⟩
        simp only [hcond, ↓reduceIte, Set.indicator_of_mem hmemF]
        have hw_eq : (insertWorstSteps n_max U : ℝ≥0∞) + 3 =
            (insertBaseSteps n_max U + 3 : ℝ≥0∞) + (R : ℝ≥0∞) := by
          dsimp only [insertWorstSteps, R]; push_cast; ring
        rw [hw_eq, mul_add]
        calc p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) + p θ * (R : ℝ≥0∞)
          _ = p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) + 0 + p θ * (R : ℝ≥0∞) := by simp
          _ ≤ p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) +
              (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max)
                (Dictionary.dom s) u : ℝ≥0∞)) * (evictIterSteps n_max U : ℝ≥0∞) +
              p θ * (R : ℝ≥0∞) :=
            add_le_add (add_le_add le_rfl zero_le) le_rfl
    calc (∑' θ : Seed U M, p θ * (insertSeedSteps n_max U ks θ s u + 3))
      _ ≤ ∑' θ : Seed U M,
            (p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞) +
            (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max)
              (Dictionary.dom s) u : ℝ≥0∞)) * (evictIterSteps n_max U : ℝ≥0∞) +
            F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞)) :=
          tsum_le_tsum hpw
      _ = (∑' θ : Seed U M, p θ * (insertBaseSteps n_max U + 3 : ℝ≥0∞)) +
          (∑' θ : Seed U M, (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ)
            (maxEvictions n_max) (Dictionary.dom s) u : ℝ≥0∞)) *
              (evictIterSteps n_max U : ℝ≥0∞)) +
          (∑' θ : Seed U M, F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞)) := by
          rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
            Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
      _ ≤ (insertBaseSteps n_max U + 3 : ℝ≥0∞) +
          (C_walk : ℝ≥0∞) * (evictIterSteps n_max U : ℝ≥0∞) +
          (C_reh : ℝ≥0∞) * (rehashAmortizedSteps n_max U : ℝ≥0∞) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
          · rw [ENNReal.tsum_mul_right]
            exact mul_le_mul' (hfam.expected_walk_le (Dictionary.dom s) u hcard_lt hu) le_rfl
          · rw [ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply]
            have hprob := hfam.step_rehash_prob_le ks u hnodup hlen_lt hu_ks
            set D := max n_max 1 * max (maxEvictions n_max) 1
            have hD_pos : 0 < D :=
              Nat.mul_pos (le_max_right n_max 1) (le_max_right (maxEvictions n_max) 1)
            have hR_le : R ≤ D * rehashAmortizedSteps n_max U := by
              dsimp only [rehashAmortizedSteps]
              exact le_of_lt (Nat.lt_mul_div_succ R hD_pos)
            have hD_ne_zero : (D : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hD_ne_top : (D : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top D
            have hcast_max (k : ℕ) : ((max k 1 : ℕ) : ℝ≥0∞) = max (k : ℝ≥0∞) 1 := by
              rcases eq_or_ne k 0 with rfl | hk
              · rw [max_eq_right (Nat.zero_le 1), Nat.cast_one, Nat.cast_zero,
                  max_eq_right zero_le]
              · rw [max_eq_left (Nat.one_le_iff_ne_zero.mpr hk),
                  max_eq_left (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hk))]
            have hD_cast : (D : ℝ≥0∞) =
                max (n_max : ℝ≥0∞) 1 * max (maxEvictions n_max : ℝ≥0∞) 1 := by
              dsimp only [D]
              simp only [Nat.cast_mul, hcast_max]
            have hprob' : p.toOuterMeasure F ≤ (C_reh : ℝ≥0∞) / (D : ℝ≥0∞) := by
              rw [hD_cast]
              exact hprob
            calc p.toOuterMeasure F * (R : ℝ≥0∞)
              _ ≤ ((C_reh : ℝ≥0∞) / (D : ℝ≥0∞)) *
                    ((D : ℝ≥0∞) * (rehashAmortizedSteps n_max U : ℝ≥0∞)) := by
                  refine mul_le_mul' hprob' ?_
                  exact_mod_cast hR_le
              _ = (C_reh : ℝ≥0∞) *
                    (((D : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)) * (rehashAmortizedSteps n_max U : ℝ≥0∞)) := by
                  rw [div_eq_mul_inv, mul_assoc, mul_assoc]
              _ = (C_reh : ℝ≥0∞) * (rehashAmortizedSteps n_max U : ℝ≥0∞) := by
                  rw [ENNReal.inv_mul_cancel hD_ne_zero hD_ne_top, one_mul]
      _ = (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
            C_reh * rehashAmortizedSteps n_max U : ℕ) := by
          push_cast; ring

/-- Relocatable `SubroutineCode` bundle for Pagh–Rodler cuckoo hashing over `Basis.exact`. -/
@[expose]
def cuckooCode : SubroutineCode .exact 19 2 where
  allocSpan := allocSpan
  initSetup := initSetup
  code := opCode
  frontierReg := 1
  baseReg := 0
  initParams := ![3, 4]
  curReg := 16
  zeroReg := 17
  oneReg := 18
  incCur := .exactBin .add 16 16 18
  input := fun i => decide (0 < i.val)
  output := 2

theorem initSetup_coupled_spec {w base n_max U V : ℕ} {x₁ : Data 19}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 1 = base + space n_max)
    (hpar : ∀ j : Fin 2, x₁.regs (![3, 4] j) = ![n_max, U] j)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1)) :
    ∃ ν₀ : PMF (Seed U (tableBits n_max) × Data 19),
      ExecCodeDist w initSetup x₁ (ν₀.map Prod.snd) (setupSteps n_max U) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 2 * seedLaw U (tableBits n_max) θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs 1 = base + space n_max ∧
        Rep w base n_max U V (Dictionary.empty U) p.2 ∧
        (0 : ℕ) ≤ 0 ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem p.2.mem := by
  have hd_pos : 0 < Probability.trinomialDeg U (tableBits n_max) :=
    lt_of_lt_of_le (tableBits_pos n_max) (Probability.le_trinomialDeg U (tableBits n_max))
  have hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max)) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨μ_init, hdist, hseed, hsupp⟩ :=
    initSetup_spec (V := V) hx₁ hb hfr (hpar 0) (hpar 1) hz hfit_ev hfit_U hfit_q
  let ν₀ : PMF (Seed U (tableBits n_max) × Data 19) :=
    μ_init.map (fun y => (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem, y))
  have hsnd : ν₀.map Prod.snd = μ_init := by
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact PMF.map_id _
  have hfst : ν₀.map Prod.fst = seedLaw U (tableBits n_max) := by
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact hseed
  refine ⟨ν₀, ?_, ?_, fun p hp => ?_⟩
  · rw [hsnd]; exact hdist
  · intro θ
    rw [hfst]
    calc seedLaw U (tableBits n_max) θ
      _ = 1 * seedLaw U (tableBits n_max) θ := (one_mul _).symm
      _ ≤ 2 * seedLaw U (tableBits n_max) θ := mul_le_mul' one_le_two le_rfl
  · dsimp only [ν₀] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    obtain ⟨hfr', hrep, hmod⟩ := hsupp y hy
    exact ⟨hfr', hrep.toRep, le_rfl, hmod⟩

theorem opCode_coupled_step_spec {w base n_max U V : ℕ}
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (ν : PMF (Seed U (tableBits n_max) × Data 19))
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw U (tableBits n_max)).toOuterMeasure
        {θ : Seed U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hv : (Dictionary.spec U V n_max).valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 2 * seedLaw U (tableBits n_max) θ)
    (hsupp : ∀ p ∈ ν.support, Rep w base n_max U V s p.2 ∧ argMatch o p.2.regs)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_V : Fits w V) :
    ∃ (μ_step : Seed U (tableBits n_max) × Data 19 → PMF (Seed U (tableBits n_max) × Data 19))
      (T_step : Seed U (tableBits n_max) × Data 19 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w cuckooCode.code p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decode (V := V) (n_max := n_max) o q.2.regs =
            some ((Dictionary.spec U V n_max).step s o).2 ∧
          Rep w base n_max U V ((Dictionary.spec U V n_max).step s o).1 q.2 ∧
          Modifies (Block.mk base (space n_max)).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤ 2 * seedLaw U (tableBits n_max) θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, (μ_step p) q * (0 : ℕ))) ≤
        (stepWorstCharge n_max U s o : ℝ≥0∞) + ∑' p, ν p * (0 : ℕ) := by
  classical
  have hd_pos : 0 < Probability.trinomialDeg U (tableBits n_max) :=
    lt_of_lt_of_le (tableBits_pos n_max) (Probability.le_trinomialDeg U (tableBits n_max))
  have hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max)) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  let μ_raw : Seed U (tableBits n_max) × Data 19 → PMF (Data 19) := fun p =>
    if hp : Rep w base n_max U V s p.2 ∧ argMatch o p.2.regs then
      Classical.choose
        (opCode_execCodeDist o hreh (Classical.choose_spec hp.1)
          hv hp.2 hfit_ev hw hfit_end hfit_V hfit_q)
    else PMF.pure p.2
  let μ_step : Seed U (tableBits n_max) × Data 19 →
      PMF (Seed U (tableBits n_max) × Data 19) :=
    fun p => (μ_raw p).map fun y => (p.1, y)
  let T_step : Seed U (tableBits n_max) × Data 19 → ℝ≥0∞ :=
    fun _ => (stepWorstCharge n_max U s o : ℝ≥0∞)
  refine ⟨μ_step, T_step, ?_, ?_, ?_⟩
  · intro p hp_mem
    have hp : Rep w base n_max U V s p.2 ∧ argMatch o p.2.regs := hsupp p hp_mem
    have hspec := Classical.choose_spec
      (opCode_execCodeDist o hreh (Classical.choose_spec hp.1)
        hv hp.2 hfit_ev hw hfit_end hfit_V hfit_q)
    obtain ⟨_, hex, _, hpost⟩ := hspec
    have hraw_eq : μ_raw p = Classical.choose
        (opCode_execCodeDist o hreh (Classical.choose_spec hp.1)
          hv hp.2 hfit_ev hw hfit_end hfit_V hfit_q) :=
      dite_eq_left_of_eq_true (eq_true hp)
    have hsnd_eq : (μ_step p).map Prod.snd = μ_raw p := by
      dsimp only [μ_step]
      rw [PMF.map_comp]
      exact PMF.map_id _
    refine ⟨?_, ?_⟩
    · rw [hsnd_eq, hraw_eq]
      exact hex.mono (opSeedSteps_le_stepWorstCharge _ _ _ _ _ _)
    · intro q hq
      dsimp only [μ_step] at hq
      rw [PMF.mem_support_map_iff] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      rw [hraw_eq] at hy
      obtain ⟨hdec, hrep', hmod⟩ := hpost y hy
      exact ⟨hdec, hrep'.toRep, hmod⟩
  · intro θ'
    have hfst : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
      dsimp only [μ_step]
      rw [PMF.map_bind, PMF.map]
      refine congrArg (ν.bind ·) (funext fun p => ?_)
      ext θ
      rw [PMF.map_comp]
      simp
    rw [hfst]
    exact hseed θ'
  · simp only [T_step, Nat.cast_zero, mul_zero, tsum_zero, add_zero]
    rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

theorem cuckoo_arguments_fit {w n_max U V : ℕ}
    (hfit_U : Fits w (max U 2 + 1)) (hfit_V : Fits w V)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o) (i : Fin 19) :
    Fits w (encode o i) := by
  cases o with
  | get u =>
    dsimp only [encode]
    split_ifs
    · exact hfit_U.of_le (Nat.zero_le _)
    · exact hfit_U.of_le (by have := u.isLt; omega)
    · exact hfit_U.of_le (Nat.zero_le _)
  | insert u v =>
    have hv_lt : v < V := hv.2
    dsimp only [encode]
    split_ifs
    · exact hfit_U.of_le (by omega)
    · exact hfit_U.of_le (by have := u.isLt; omega)
    · exact hfit_V.of_le (le_of_lt hv_lt)
    · exact hfit_U.of_le (Nat.zero_le _)

theorem cuckoo_span_exec {w base n_max U : ℕ}
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    {x : Data 19} (_hx : x.Bounded w) (hfr : x.regs 1 = base)
    (hpar : ∀ j : Fin 2, x.regs (![3, 4] j) = ![n_max, U] j) :
    ∃ x₁ : Data 19,
      ExecWithin w allocSpan x x₁ (spanSteps n_max) ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 1 = base + space n_max ∧
      ∀ j : Fin 2, x₁.regs (![3, 4] j) = ![n_max, U] j := by
  obtain ⟨x₁, he, hm, h0, h1, h3, h4⟩ :=
    allocSpan_execWithin hfr (hpar 0) (hpar 1) hfit_end hfit_ev
  refine ⟨x₁, he, hm, h0, h1, ?_⟩
  intro j
  fin_cases j
  · exact h3
  · exact h4

/-- Composable randomized Word-RAM `SubroutineDS` certificate for Pagh–Rodler cuckoo hashing over
`Basis.exact`, parameterized by any hash family satisfying `IsCuckooHashFamily`. -/
@[expose]
noncomputable def subroutineDS (w base n_max U V C_walk C_reh : ℕ)
    (hfam : IsCuckooHashFamily U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V) :
    Randomized.SubroutineDS cuckooCode (Dictionary.spec U V n_max)
      w base ![n_max, U] (Dictionary.empty U) where
  Seed := Seed U (tableBits n_max)
  seedLaw := seedLaw U (tableBits n_max)
  seedSlack := 2
  space := space n_max
  spanTime := spanSteps n_max
  setupTime := setupSteps n_max U
  initPotential := 0
  charge := stepWorstCharge n_max U
  rep _ := Rep w base n_max U V
  potential _ _ := 0
  encode := encode
  argMatch := argMatch
  decode := decode (V := V) (n_max := n_max)
  bounded h := h.bounded
  rep_unique h₁ h₂ := h₁.unique h₂
  arguments_fit {_s} o hv i _ := cuckoo_arguments_fit hfit_U hfit_V o hv i
  encode_matches o _regs := by cases o <;> simp +decide [argMatch, encode]
  rep_supported hreg hmem hbdd hrep := Rep.supported (hreg 0 rfl) hmem hbdd hrep
  potential_supported _ _ _ := rfl
  clear_nodup := by decide
  params_not_clear := by decide
  incCur_eval {x} h1 hfit := by
    change Data.put w x 16 (x.regs 16 + x.regs 18) =
      some (x.set cuckooCode.curReg (x.regs cuckooCode.curReg + 1))
    change x.regs 18 = 1 at h1
    rw [h1]
    exact Data.put_of_fits hfit
  span_exec hx hfr hpar := cuckoo_span_exec hfit_end hfit_ev hx hfr hpar
  setup_exec hx₁ hb hfr hpar hz :=
    initSetup_coupled_spec hx₁ hb hfr hpar hz hw hfit_ev hfit_U
  step_exec {_s} o ν hv hseed hsupp :=
    opCode_coupled_step_spec o ν hfam.rehash_prob_le_half hv hseed hsupp hw hfit_end hfit_ev hfit_V

/-- Standard-basis (`Basis.standard`) randomized `SubroutineDS` certificate for Pagh–Rodler cuckoo
hashing. -/
noncomputable abbrev subroutineDSStandard (w base n_max U V C_walk C_reh : ℕ)
    (hfam : IsCuckooHashFamily U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V) :
    Randomized.SubroutineDS cuckooCode.toStandard (Dictionary.spec U V n_max)
      w base ![n_max, U] (Dictionary.empty U) :=
  (subroutineDS w base n_max U V C_walk C_reh hfam hw hfit_end hfit_ev hfit_U hfit_V).toStandard

/-- Coupled multi-step execution telescope for Pagh–Rodler cuckoo hashing maintaining the exact
conditional-uniform in-memory seed marginal
`PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE` across an
operation sequence `ops`. -/
private theorem cuckoo_steps_expected_amortized (w base n_max U V C_walk C_reh : ℕ)
    (hfam : IsCuckooHashFamily U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V)
    (ops : List (Dictionary.Op U))
    {ks : List (Fin U)} {s : Dictionary.State U}
    (ν : PMF (Seed U (tableBits n_max) × Data 19))
    (hv : (Dictionary.spec U V n_max).ValidHistory s ops)
    (hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty)
    (hseed : ν.map Prod.fst =
      PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE)
    (hsupp : ∀ p ∈ ν.support,
      p.1 = extractSeed (hashBase base) n_max U (tableBits n_max) p.2.mem ∧
      RepWithKeys w base n_max U V ks s p.2) :
    let C := subroutineDS w base n_max U V C_walk C_reh hfam hw hfit_end hfit_ev hfit_U hfit_V
    ∃ (ν_final : PMF (Seed U (tableBits n_max) × Data 19)) (T_ops : ℝ≥0∞),
      C.ExecSteps s ops ν ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw U (tableBits n_max) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base n_max U V ((Dictionary.spec U V n_max).run s ops).1 p.2) ∧
      T_ops ≤
        ((Dictionary.spec U V n_max).totalCost (charge n_max U C_walk C_reh) s ops : ℝ≥0∞) := by
  classical
  intro C
  have hd_pos : 0 < Probability.trinomialDeg U (tableBits n_max) :=
    lt_of_lt_of_le (tableBits_pos n_max) (Probability.le_trinomialDeg U (tableBits n_max))
  have hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max)) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  induction ops generalizing ks s ν with
  | nil =>
    obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
    have hrep₀ := (hsupp p₀ hp₀).2
    have hcard := (survivingSeeds_card_and_nonempty (U := U) (n_max := n_max)
      hfam.rehash_prob_le_half hrep₀.2.2.2.2.1.1 hrep₀.2.2.2.2.1.2.1).1
    refine ⟨ν, 0, Randomized.SubroutineDS.ExecSteps.nil (C := C) s ν, ?_, ?_, by simp⟩
    · intro θ
      rw [hseed]
      exact uniformOfFinset_le_two_mul_uniformOfFintype hE hcard θ
    · intro p hp
      exact (hsupp p hp).2.toRep
  | cons o os ih =>
    obtain ⟨hvo, hvos⟩ := hv
    obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
    have hrep₀ := (hsupp p₀ hp₀).2
    have hnodup : ks.Nodup := hrep₀.2.2.2.2.1.1
    have hlen_le : ks.length ≤ n_max := hrep₀.2.2.2.2.1.2.1
    have hdom : ∀ x, x ∈ ks ↔ x ∈ Dictionary.dom s := hrep₀.2.2.2.2.1.2.2.2.1
    have hcard : Fintype.card (Seed U (tableBits n_max)) ≤
        2 * (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).card :=
      (survivingSeeds_card_and_nonempty (U := U) (n_max := n_max)
        hfam.rehash_prob_le_half hnodup hlen_le).1
    have hseed_le : ∀ θ, (ν.map Prod.fst) θ ≤ 2 * seedLaw U (tableBits n_max) θ := by
      intro θ
      rw [hseed]
      exact uniformOfFinset_le_two_mul_uniformOfFintype hE hcard θ
    have hprep_ok : ∀ p ∈ ν.support,
        p.1 = extractSeed (hashBase base) n_max U (tableBits n_max)
          (C.toDynamicProgram.prepare o p.2).mem ∧
        RepWithKeys w base n_max U V ks s (C.toDynamicProgram.prepare o p.2) ∧
        argMatch o (C.toDynamicProgram.prepare o p.2).regs := by
      intro p hp
      obtain ⟨hp1, hrep_p⟩ := hsupp p hp
      refine ⟨hp1, ?_, C.prepare_argMatch o p.2⟩
      exact RepWithKeys.supported
        (C.toDynamicProgram.prepare_regs_of_not_input (i := 0) rfl o p.2)
        (fun _ _ => rfl)
        (C.toDynamicProgram.prepare_bounded hrep_p.1 (C.arguments_fit o hvo))
        hrep_p
    have hE' :
        (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2 (maxEvictions n_max)
          (stepKeys ks o)).Nonempty := by
      obtain ⟨_, hrep_p₀, harg_p₀⟩ := hprep_ok p₀ hp₀
      obtain ⟨_, hE'_p₀, _⟩ :=
        opCode_execCodeDist o hfam.rehash_prob_le_half hrep_p₀ hvo harg_p₀
          hfit_ev hw hfit_end hfit_V hfit_q
      exact hE'_p₀
    let μ_raw : Seed U (tableBits n_max) × Data 19 → PMF (Data 19) := fun p =>
      if hp : RepWithKeys w base n_max U V ks s (C.toDynamicProgram.prepare o p.2) ∧
          argMatch o (C.toDynamicProgram.prepare o p.2).regs then
        Classical.choose
          (opCode_execCodeDist o hfam.rehash_prob_le_half hp.1 hvo hp.2
            hfit_ev hw hfit_end hfit_V hfit_q)
      else PMF.pure (C.toDynamicProgram.prepare o p.2)
    let μ_step : Seed U (tableBits n_max) × Data 19 →
        PMF (Seed U (tableBits n_max) × Data 19) :=
      fun p => (μ_raw p).map fun y =>
        (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem, y)
    let T_step : Seed U (tableBits n_max) × Data 19 → ℝ≥0∞ :=
      fun p => opSeedSteps n_max U ks p.1 s o
    have hstep_spec : ∀ p ∈ ν.support,
        ExecCodeDist w cuckooCode.code (C.toDynamicProgram.prepare o p.2)
          ((μ_step p).map Prod.snd) (T_step p) ∧
        (μ_step p).map Prod.fst =
          (if p.1 ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
            PMF.pure p.1
           else
            PMF.uniformOfFinset
              (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE') ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.2.regs = some ((Dictionary.spec U V n_max).step s o).2 ∧
          q.1 = extractSeed (hashBase base) n_max U (tableBits n_max) q.2.mem ∧
          RepWithKeys w base n_max U V (stepKeys ks o)
            ((Dictionary.spec U V n_max).step s o).1 q.2 ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem := by
      intro p hp_mem
      obtain ⟨hp1, hrep_prep, harg_prep⟩ := hprep_ok p hp_mem
      have hp : RepWithKeys w base n_max U V ks s (C.toDynamicProgram.prepare o p.2) ∧
          argMatch o (C.toDynamicProgram.prepare o p.2).regs := ⟨hrep_prep, harg_prep⟩
      have hspec := Classical.choose_spec
        (opCode_execCodeDist o hfam.rehash_prob_le_half hp.1 hvo hp.2
          hfit_ev hw hfit_end hfit_V hfit_q)
      obtain ⟨hE'_p, hex, hlaw, hpost⟩ := hspec
      have hraw_eq : μ_raw p = Classical.choose
          (opCode_execCodeDist o hfam.rehash_prob_le_half hp.1 hvo hp.2
            hfit_ev hw hfit_end hfit_V hfit_q) :=
        dite_eq_left_of_eq_true (eq_true hp)
      have hsnd_eq : (μ_step p).map Prod.snd = μ_raw p := by
        dsimp only [μ_step]
        rw [PMF.map_comp]
        exact PMF.map_id _
      have hfst_eq : (μ_step p).map Prod.fst =
          (μ_raw p).map (fun y => extractSeed (hashBase base) n_max U (tableBits n_max) y.mem) := by
        dsimp only [μ_step]
        rw [PMF.map_comp]
        rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hsnd_eq, hraw_eq]
        dsimp only [T_step]
        rw [hp1]
        exact hex
      · rw [hfst_eq, hraw_eq, hp1, hlaw]
      · intro q hq
        dsimp only [μ_step] at hq
        rw [PMF.mem_support_map_iff] at hq
        obtain ⟨y, hy, rfl⟩ := hq
        rw [hraw_eq] at hy
        obtain ⟨hdec, hrep', hmod⟩ := hpost y hy
        exact ⟨hdec, rfl, hrep', hmod⟩
    let ν₁ := ν.bind μ_step
    have hseed₁ : ν₁.map Prod.fst =
        PMF.uniformOfFinset
          (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE' := by
      let f : Seed U (tableBits n_max) → PMF (Seed U (tableBits n_max)) := fun θ =>
        if θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
          PMF.pure θ
        else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE'
      have hmap_bind : ν₁.map Prod.fst = (ν.map Prod.fst).bind f := by
        ext θ'
        rw [PMF.map_bind, PMF.bind_apply, PMF.bind_apply]
        have hcongr :
            (∑' p : Seed U (tableBits n_max) × Data 19, ν p * ((μ_step p).map Prod.fst) θ') =
              ∑' p : Seed U (tableBits n_max) × Data 19, ν p * f p.1 θ' := by
          refine tsum_congr fun p => ?_
          by_cases hp : p ∈ ν.support
          · rw [(hstep_spec p hp).2.1]
          · rw [(PMF.apply_eq_zero_iff _ _).mpr hp, zero_mul, zero_mul]
        rw [hcongr]
        exact (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst (fun θ => f θ θ')).symm
      rw [hmap_bind, hseed]
      exact unifOn_rehash_eq (survivingSeeds_stepKeys_subset n_max ks o) hE hE'
    have hsupp₁ : ∀ q ∈ ν₁.support,
        q.1 = extractSeed (hashBase base) n_max U (tableBits n_max) q.2.mem ∧
        RepWithKeys w base n_max U V (stepKeys ks o)
          ((Dictionary.spec U V n_max).step s o).1 q.2 := by
      intro q hq
      dsimp only [ν₁] at hq
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨p, hp, hq_step⟩ := hq
      obtain ⟨_, hq1, hrep', _⟩ := (hstep_spec p hp).2.2 q hq_step
      exact ⟨hq1, hrep'⟩
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hrep_final, hamort_rest⟩ :=
      ih ν₁ hvos hE' hseed₁ hsupp₁
    have hex_cons : C.ExecSteps s (o :: os) ν ν_final ((∑' p, ν p * T_step p) + T_rest) := by
      refine Randomized.SubroutineDS.ExecSteps.cons (C := C) (μ_step := μ_step) (T_step := T_step)
        (fun p hp => ?_) hex_rest
      obtain ⟨hex, _, hpost⟩ := hstep_spec p hp
      refine ⟨hex, fun q hq => ?_⟩
      obtain ⟨hdec, _, hrep', hmod⟩ := hpost q hq
      exact ⟨hdec, hrep'.toRep, hmod⟩
    have hstep_cost :
        (∑' p, ν p * T_step p) ≤ (charge n_max U C_walk C_reh s o : ℝ≥0∞) := by
      have hmap_lhs :
          (∑' p : Seed U (tableBits n_max) × Data 19, ν p * T_step p) =
            ∑' θ : Seed U (tableBits n_max),
              (ν.map Prod.fst) θ * opSeedSteps n_max U ks θ s o :=
        (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
          (fun θ => opSeedSteps n_max U ks θ s o)).symm
      rw [hmap_lhs]
      cases o with
      | get u =>
        dsimp only [opSeedSteps, charge]
        rw [ENNReal.tsum_mul_right, (ν.map Prod.fst).tsum_coe, one_mul]
      | insert u v =>
        dsimp only [opSeedSteps, charge, insertCharge]
        calc (∑' θ : Seed U (tableBits n_max),
              (ν.map Prod.fst) θ * (insertSeedSteps n_max U ks θ s u + 3))
          _ ≤ ∑' θ : Seed U (tableBits n_max),
                (2 * seedLaw U (tableBits n_max) θ) *
                  (insertSeedSteps n_max U ks θ s u + 3) :=
              tsum_le_tsum fun θ => mul_le_mul' (hseed_le θ) le_rfl
          _ = 2 * ∑' θ : Seed U (tableBits n_max),
                seedLaw U (tableBits n_max) θ * (insertSeedSteps n_max U ks θ s u + 3) := by
              simp_rw [mul_assoc]
              rw [ENNReal.tsum_mul_left]
          _ ≤ 2 * (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
                C_reh * rehashAmortizedSteps n_max U : ℕ) :=
              mul_le_mul' le_rfl (tsum_seedLaw_insertSeedSteps_le hfam hnodup hdom hvo)
          _ = (2 * (insertBaseSteps n_max U + 3 + C_walk * evictIterSteps n_max U +
                C_reh * rehashAmortizedSteps n_max U) : ℕ) := by
              push_cast; ring
    refine ⟨ν_final, (∑' p, ν p * T_step p) + T_rest, hex_cons, hseed_final, hrep_final, ?_⟩
    calc (∑' p, ν p * T_step p) + T_rest
      _ ≤ (charge n_max U C_walk C_reh s o : ℝ≥0∞) +
            ((Dictionary.spec U V n_max).totalCost (charge n_max U C_walk C_reh)
              ((Dictionary.spec U V n_max).step s o).1 os : ℝ≥0∞) :=
          add_le_add hstep_cost hamort_rest
      _ = ((Dictionary.spec U V n_max).totalCost (charge n_max U C_walk C_reh) s (o :: os) :
            ℝ≥0∞) :=
          (Nat.cast_add _ _).symm

/-- **End-to-end expected-amortized theorem for Pagh–Rodler cuckoo hashing.**
Starting from zeroed memory in `[base, base + space n_max)`, initializing `cuckooCode` and
executing any valid sequence `ops : List (Dictionary.Op U)` of `get` and `insert` operations takes
expected instruction cost at most
`spanSteps n_max + setupSteps n_max U +
  (Dictionary.spec U V n_max).totalCost (charge n_max U C_walk C_reh) (Dictionary.empty U) ops`. -/
theorem cuckoo_seq_expected_amortized (w base n_max U V C_walk C_reh : ℕ)
    (hfam : IsCuckooHashFamily U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V)
    {x : Data 19} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs 1 = base)
    (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := subroutineDS w base n_max U V C_walk C_reh hfam hw hfit_end hfit_ev hfit_U hfit_V
    ∃ (ν₀ ν_final : PMF (Seed U (tableBits n_max) × Data 19)) (T_ops : ℝ≥0∞),
      ExecCodeDist w cuckooCode.initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw U (tableBits n_max) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base n_max U V ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      C.initTime + T_ops ≤
        C.initTime +
          ((Dictionary.spec U V n_max).totalCost (charge n_max U C_walk C_reh)
            (Dictionary.empty U) ops : ℝ≥0∞) := by
  classical
  intro C
  have hd_pos : 0 < Probability.trinomialDeg U (tableBits n_max) :=
    lt_of_lt_of_le (tableBits_pos n_max) (Probability.le_trinomialDeg U (tableBits n_max))
  have hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max)) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  obtain ⟨x₁, ⟨t_span, ht_span, he_span⟩, hm₁, hb₁, hfr₁, h3₁, h4₁⟩ :=
    allocSpan_execWithin hfr h3 h4 hfit_end hfit_ev
  have hx₁_bdd : x₁.Bounded w := he_span.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0 := by
    intro a ha; rw [hm₁]; exact hz a ha
  obtain ⟨μ_init, hdist_setup, hseed_setup, hsupp_setup⟩ :=
    initSetup_spec (V := V) hx₁_bdd hb₁ hfr₁ h3₁ h4₁ hz₁ hfit_ev hfit_U hfit_q
  let ν₀ : PMF (Seed U (tableBits n_max) × Data 19) :=
    μ_init.map (fun y => (extractSeed (hashBase base) n_max U (tableBits n_max) y.mem, y))
  have hsnd₀ : ν₀.map Prod.snd = μ_init := by
    dsimp only [ν₀]
    rw [PMF.map_comp]
    exact PMF.map_id _
  have he_init : ExecCodeDist w cuckooCode.initFresh x (ν₀.map Prod.snd) C.initTime := by
    rw [hsnd₀]
    have hseq := (ExecCodeDist.of_exec he_span).seq_pure hdist_setup
    refine hseq.mono ?_
    dsimp only [C, subroutineDS, Randomized.SubroutineDS.initTime]
    exact add_le_add (by exact_mod_cast ht_span) le_rfl
  have hE₀ :
      (survivingSeeds (Θ := Seed U (tableBits n_max)) evalHash1 evalHash2 (maxEvictions n_max)
        ([] : List (Fin U))).Nonempty := by
    rw [survivingSeeds_nil]
    exact Finset.univ_nonempty
  have hseed₀ : ν₀.map Prod.fst =
      PMF.uniformOfFinset
        (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ([] : List (Fin U))) hE₀ := by
    have hfst : ν₀.map Prod.fst = seedLaw U (tableBits n_max) := by
      dsimp only [ν₀]
      rw [PMF.map_comp]
      exact hseed_setup
    rw [hfst]
    ext θ
    rw [seedLaw, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply]
    simp [survivingSeeds_nil]
  have hsupp₀ : ∀ p ∈ ν₀.support,
      p.1 = extractSeed (hashBase base) n_max U (tableBits n_max) p.2.mem ∧
      RepWithKeys w base n_max U V [] (Dictionary.empty U) p.2 := by
    intro p hp
    dsimp only [ν₀] at hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨rfl, (hsupp_setup y hy).2.1⟩
  obtain ⟨ν_final, T_ops, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    cuckoo_steps_expected_amortized w base n_max U V C_walk C_reh hfam hw hfit_end hfit_ev hfit_U
      hfit_V ops ν₀ hv hE₀ hseed₀ hsupp₀
  exact ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final,
    add_le_add le_rfl hamort⟩

end Cslib.Algorithms.WordRAM.Dictionary.CuckooHashing

