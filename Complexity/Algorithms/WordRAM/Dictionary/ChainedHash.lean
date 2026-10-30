/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Algorithms.WordRAM.Hashing.MultiplyShift
public import Complexity.Computability.WordRAM.ExactNotation
public import Complexity.Computability.WordRAM.Randomized.Subroutine
import Complexity.Probability.PMF.Expect
import Mathlib.Data.Nat.Log

/-!
# Chained Hash Table on the Randomized Word RAM

This file implements a textbook chained hash table ([CLRS2009], Sections 11.2 and 11.3.3,
Theorem 11.3 and Corollary 11.4) realizing the bounded-capacity insert-only dictionary specification
`Cslib.Algorithms.Lean.Dictionary.spec U V n_max` (`get` and `insert` up to `n_max` distinct keys,
with deletion deferred to a follow-up) on the randomized Word RAM over `Cslib.WordRAM.Basis.exact`
(and lifted to `Basis.standard` via `SubroutineDS.toStandard`).

## Model, specialization, and cost scope

* **Specialization and external word width:** For fixed universe `U` and capacity bound `n_max` and
  an admissible external machine word width `w` (`2 * hashBits U n_max ≤ w`,
  `Fits w (base + space n_max)`, `Fits w V`), the specialized program `subroutineCode U n_max` uses
  precomputed configuration literals (`bucketBits`, `hashBits`, bit masks, and layout offsets baked
  as instruction literals, with `initParams = Fin.elim0`).
* **Charged body cost and oblivious adversary:** The expected time bounds charge initialization and
  subroutine operation **bodies** across an operation history `ops` fixed independently of the
  sampled hash seed (oblivious adversary), excluding caller argument delivery, caller
  control/dispatch loops, and code/configuration construction.
* **Insert-only node pool:** Because `Dictionary.spec U V n_max` is insert-only, both the linear
  space bound `space n_max ≤ 5 * n_max + 8` and sequential bump allocation
  (`allocCount ∈ [0, n_max]`) rely on the absence of deletions; a future deletion extension would
  revisit node-pool slot recycling.

## Design and memory layout

Given key universe `Fin U` and capacity bound `n_max`, the data structure chooses:
* power-of-two bucket count `m = numBuckets n_max = 2 ^ M` with
  `M = bucketBits n_max = Nat.clog 2 (max n_max 2)`, so `max n_max 2 ≤ 2 ^ M ≤ 2 * max n_max 2`
  and the load factor satisfies `n / m ≤ n_max / 2 ^ M ≤ 1`;
* multiply-shift input bit-width `w₀ = hashBits U n_max = max M (Nat.clog 2 (max U 2))`, so
  `0 < w₀`, `M ≤ w₀`, and `U ≤ 2 ^ w₀`.

All state resides in a single contiguous memory block `[base, base + space n_max)` of
`space n_max = 4 + 2 ^ M + 3 * n_max ≤ 5 * n_max + 8 = O(n_max)` words:
* `[base, base + 4)`: 4-word header storing the sampled multiply-shift seed `b < 2 ^ (w₀ - 1)`,
  `M`, `w₀`, and the sequential node allocation counter `allocCount ∈ [0, n_max]`;
* `[base + 4, base + 4 + 2 ^ M)`: bucket head array `head[0 .. 2 ^ M - 1]` storing `0` for an
  empty chain and `idx + 1` for pool slot `idx ∈ [0, allocCount)` (so fresh zeroed memory already
  represents `2 ^ M` empty buckets in `O(1)` instructions);
* `[base + 4 + 2 ^ M, base + 4 + 2 ^ M + 3 * n_max)`: static `n_max`-slot node pool split into
  `key[0 .. n_max - 1]`, `val[0 .. n_max - 1]`, and `next[0 .. n_max - 1]`.

## Operations and expected complexity

* `initSetup`: invokes `MultiplyShift.initCode w₀` (`1` `Instr.rand` call) to sample a uniform odd
  multiplier seed `b ∈ Fin (2 ^ (w₀ - 1))` and writes the 4-word header (`16` instructions total
  for `initFresh` on zeroed memory, `O(n_max)` via `initClear` on arbitrary dirty memory).
* `get u` and `insert u v`: evaluate the bucket index `bk = multiplyShift w₀ M b (encodeKey u)` via
  `MultiplyShift.evalCode w₀ M`, traverse the singly-linked chain from `head[bk]` via
  `findInChain`, and either return `val[idx] + 1` / `0` (`get`), overwrite `val[idx] ← v` in place
  on a key hit (`insert`), or bump-allocate slot `allocCount` and prepend it to `head[bk]` on a
  key miss (`insert`).
* By linearity of expectation and the `(2 / 2 ^ M)`-universality of multiply-shift hashing
  (`Cslib.Probability.isUniversalHash_multiplyShift`, [DietzfelbingerHagerupKatajainenPenttonen1997]
  Lemma 2.4; [CLRS2009], Section 11.3.3, Theorem 11.3 and Corollary 11.4), the expected number of
  other keys in `dom s \ {u}` colliding with `u` is at most
  `((dom s).card : ℝ≥0∞) * (2 / 2 ^ M) ≤ n_max * (2 / 2 ^ M) ≤ 2`, giving worst-case expected
  `O(1)` (`chargeVal = 73`) body instructions per operation with zero potential (`potential = 0`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.bucketBits`, `numBuckets`, `hashBits`, `space`:
  table dimension parameters and `O(n_max)` memory footprint.
* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.subroutineCode`: relocatable `SubroutineCode`
  bundle over `Basis.exact`.
* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.Rep`: seed-coupled concrete representation
  invariant.
* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.subroutineDS`, `subroutineDSStandard`:
  `Cslib.WordRAM.Randomized.SubroutineDS` certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.space_le`: linear space bound
  `space n_max ≤ 5 * n_max + 8`.
* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.expect_collCount_le_card_mul`,
  `expect_collCount_le_two`: universal-hashing expected collision bounds.
* `Cslib.Algorithms.WordRAM.Dictionary.ChainedHash.seq_expected_amortized`: expected subroutine
  body step bound across any admissible oblivious sequence of `get` and `insert` operations.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Sections 11.2 and 11.3.3 (Theorem 11.3 and Corollary 11.4)][CLRS2009]
* [M. Dietzfelbinger, T. Hagerup, J. Katajainen and M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*, Lemma 2.4][DietzfelbingerHagerupKatajainenPenttonen1997]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dictionary.ChainedHash

open Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.Hashing
open Cslib.Probability
open scoped ENNReal

/-! ## 1. Table dimension parameters and arithmetic bounds -/

/-- Logarithmic bucket bit-width `M = ⌈log₂(max n_max 2)⌉`. -/
def bucketBits (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 2)

/-- Power-of-two bucket count `m = 2 ^ M`. -/
def numBuckets (n_max : ℕ) : ℕ :=
  2 ^ bucketBits n_max

/-- Multiply-shift input bit-width `w₀ = max M ⌈log₂(max U 2)⌉`. -/
def hashBits (U n_max : ℕ) : ℕ :=
  max (bucketBits n_max) (Nat.clog 2 (max U 2))

/-- Total contiguous memory footprint `4 + 2 ^ M + 3 * n_max` words. -/
def space (n_max : ℕ) : ℕ :=
  4 + numBuckets n_max + 3 * n_max

theorem bucketBits_pos (n_max : ℕ) : 0 < bucketBits n_max := by
  have h1 : 1 = Nat.clog 2 2 := by decide
  have h2 : Nat.clog 2 2 ≤ Nat.clog 2 (max n_max 2) :=
    Nat.clog_mono_right 2 (le_max_right n_max 2)
  unfold bucketBits
  omega

theorem bucketBits_le_hashBits (U n_max : ℕ) : bucketBits n_max ≤ hashBits U n_max :=
  le_max_left _ _

theorem hashBits_pos (U n_max : ℕ) : 0 < hashBits U n_max :=
  (bucketBits_pos n_max).trans_le (bucketBits_le_hashBits U n_max)

theorem max_le_numBuckets (n_max : ℕ) : max n_max 2 ≤ numBuckets n_max :=
  Nat.le_pow_clog (by decide : 1 < 2) (max n_max 2)

theorem le_numBuckets (n_max : ℕ) : n_max ≤ numBuckets n_max :=
  (le_max_left n_max 2).trans (max_le_numBuckets n_max)

theorem two_le_numBuckets (n_max : ℕ) : 2 ≤ numBuckets n_max :=
  (le_max_right n_max 2).trans (max_le_numBuckets n_max)

theorem numBuckets_pos (n_max : ℕ) : 0 < numBuckets n_max := by
  have := two_le_numBuckets n_max
  omega

/-- The power-of-two bucket count `numBuckets n_max` is at most `2 * n_max + 4`. -/
theorem numBuckets_le (n_max : ℕ) : numBuckets n_max ≤ 2 * n_max + 4 := by
  unfold numBuckets bucketBits
  set k := Nat.clog 2 (max n_max 2)
  have hk_pos : 0 < k := bucketBits_pos n_max
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hlt : m < Nat.clog 2 (max n_max 2) := by omega
  have hpow : 2 ^ m < max n_max 2 :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hlt
  have hpow' : 2 ^ k = 2 * 2 ^ m := by rw [hm, pow_succ']
  omega

/-- Linear `O(n_max)` space bound: `space n_max ≤ 5 * n_max + 8`. -/
theorem space_le (n_max : ℕ) : space n_max ≤ 5 * n_max + 8 := by
  unfold space
  have := numBuckets_le n_max
  omega

theorem le_two_pow_hashBits (U n_max : ℕ) : U ≤ 2 ^ hashBits U n_max := by
  calc
    U ≤ max U 2 := le_max_left U 2
    _ ≤ 2 ^ Nat.clog 2 (max U 2) := Nat.le_pow_clog (by decide : 1 < 2) (max U 2)
    _ ≤ 2 ^ hashBits U n_max :=
      Nat.pow_le_pow_right two_pos (le_max_right (bucketBits n_max) _)

/-- Canonical injection of keys `Fin U` into the multiply-shift domain `Fin (2 ^ hashBits U n_max)`.
-/
def encodeKey {U n_max : ℕ} (u : Fin U) : Fin (2 ^ hashBits U n_max) :=
  ⟨u.val, u.isLt.trans_le (le_two_pow_hashBits U n_max)⟩

@[simp]
theorem encodeKey_val {U n_max : ℕ} (u : Fin U) :
    (encodeKey (n_max := n_max) u).val = u.val := rfl

theorem encodeKey_injective (U n_max : ℕ) :
    Function.Injective (encodeKey (U := U) (n_max := n_max)) := by
  intro u₁ u₂ h
  exact Fin.ext (Fin.mk.inj_iff.mp h)

/-- Every multiply-shift hash value lies strictly below `2 ^ M`. -/
theorem multiplyShift_lt_two_pow {w₀ M : ℕ} (hM : M ≤ w₀)
    (b : Fin (2 ^ (w₀ - 1))) (x : Fin (2 ^ w₀)) :
    multiplyShift w₀ M b x < 2 ^ M := by
  unfold multiplyShift
  refine Nat.div_lt_of_lt_mul ?_
  rw [← pow_add, Nat.sub_add_cancel hM]
  exact Nat.mod_lt _ (by positivity)

theorem multiplyShift_lt_numBuckets {U n_max : ℕ}
    (b : Fin (2 ^ (hashBits U n_max - 1))) (u : Fin U) :
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) < numBuckets n_max :=
  multiplyShift_lt_two_pow (bucketBits_le_hashBits U n_max) b (encodeKey u)

/-! ## 2. Register layout, memory offsets, and structured Word-RAM code -/

/-- Total local register count of the chained hash table (`1` persistent + `21` scratch/caller). -/
abbrev rHash : ℕ := 22

namespace Reg

/-- Multiply-shift seed register (`0`). -/
abbrev regB : Fin rHash := 0
/-- Multiply-shift key register (`1`). -/
abbrev regX : Fin rHash := 1
/-- Multiply-shift bucket output register (`2`). -/
abbrev regOut : Fin rHash := 2
/-- Multiply-shift scratch register 1 (`3`, also `curReg` for `zeroFillCode`). -/
abbrev regT1 : Fin rHash := 3
/-- Multiply-shift scratch register 2 (`4`). -/
abbrev regT2 : Fin rHash := 4
/-- Persistent base address register (`5`). -/
abbrev baseReg : Fin rHash := 5
/-- Bump-allocation frontier register (`6`). -/
abbrev frontierReg : Fin rHash := 6
/-- Operation tag register (`7`: `0` = `get`, `≠ 0` = `insert`). -/
abbrev tagReg : Fin rHash := 7
/-- Input key register `u.val` (`8`). -/
abbrev argU : Fin rHash := 8
/-- Input value register `v` (`9`). -/
abbrev argV : Fin rHash := 9
/-- Output register (`10`: `0` = `none`, `v + 1` = `some v` on `get`). -/
abbrev outReg : Fin rHash := 10
/-- Constant `0` scratch register (`11`, also `zeroReg` for `zeroFillCode`). -/
abbrev zero : Fin rHash := 11
/-- Constant `1` scratch register (`12`, also `oneReg` for `zeroFillCode`). -/
abbrev one : Fin rHash := 12
/-- Bucket head array base `base + 4` (`13`). -/
abbrev headBaseReg : Fin rHash := 13
/-- Node key array base `base + 4 + numBuckets n_max` (`14`). -/
abbrev keyBaseReg : Fin rHash := 14
/-- Node value array base `base + 4 + numBuckets n_max + n_max` (`15`). -/
abbrev valBaseReg : Fin rHash := 15
/-- Node next-pointer array base `base + 4 + numBuckets n_max + 2 * n_max` (`16`). -/
abbrev nextBaseReg : Fin rHash := 16
/-- Current 1-based chain pointer (`17`). -/
abbrev cur : Fin rHash := 17
/-- Current 0-based pool slot index (`18`). -/
abbrev idx : Fin rHash := 18
/-- Key-hit indicator flag (`19`). -/
abbrev found : Fin rHash := 19
/-- Matched 0-based pool slot index (`20`). -/
abbrev matchIdx : Fin rHash := 20
/-- Scratch memory address / value register (`21`). -/
abbrev addr : Fin rHash := 21

end Reg

open Reg

/-- Embedding of the 5 multiply-shift registers (`Fin 5`) into `Fin rHash` (`0..4`). -/
def hashEmbed : Fin 5 → Fin rHash :=
  Fin.castLE (by decide : 5 ≤ rHash)

theorem hashEmbed_injective : Function.Injective hashEmbed :=
  Fin.castLE_injective (by decide : 5 ≤ rHash)

/-- Register classification: only `baseReg` (`5`) is persistent (`false`); all other registers are
caller-overwritable (`true`). -/
def inputMask (i : Fin rHash) : Bool :=
  decide (i ≠ baseReg)

/-- Memory address of the bucket head array `head[0 .. numBuckets n_max - 1]`. -/
def headBase (base : ℕ) : ℕ :=
  base + 4

/-- Memory address of the node key array `key[0 .. n_max - 1]`. -/
def keyBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max

/-- Memory address of the node value array `val[0 .. n_max - 1]`. -/
def valBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max + n_max

/-- Memory address of the node next-pointer array `next[0 .. n_max - 1]`. -/
def nextBase (base n_max : ℕ) : ℕ :=
  base + 4 + numBuckets n_max + 2 * n_max

/-- Bump-allocate `space n_max` words at `frontierReg`, recording `baseReg := frontierReg` and
advancing `frontierReg := baseReg + space n_max`. -/
def allocSpan (n_max : ℕ) : Code .exact rHash := ram_exact[
  baseReg ← frontierReg;
  addr ← #(space n_max);
  frontierReg ← baseReg + addr ]

/-- Store the sampled multiply-shift seed `regB`, `bucketBits n_max`, `hashBits U n_max`, and
initial allocation count `0` into the 4-word header `[base, base + 4)`. -/
def storeHeader (U n_max : ℕ) : Code .exact rHash := ram_exact[
  *baseReg ← regB;
  one ← #1;
  addr ← baseReg + one;
  idx ← #(bucketBits n_max);
  *addr ← idx;
  addr ← addr + one;
  idx ← #(hashBits U n_max);
  *addr ← idx;
  addr ← addr + one;
  zero ← #0;
  *addr ← zero ]

/-- Self-contained hash-table initialization: sample a uniform multiply-shift seed via
`MultiplyShift.initCode` and write the 4-word header. -/
def initSetup (U n_max : ℕ) : Code .exact rHash :=
  .seq ((MultiplyShift.initCode (hashBits U n_max)).rename hashEmbed)
       (storeHeader U n_max)

/-- Load the stored seed `b` into `regB` and copy key `argU` into `regX`. -/
def prepHash : Code .exact rHash := ram_exact[
  regB ← *baseReg;
  regX ← argU ]

/-- Compute array base pointers and load `cur := head[regOut]`, clearing `found` and `matchIdx`. -/
def loadBucketHead (n_max : ℕ) : Code .exact rHash := ram_exact[
  zero ← #0;
  one ← #1;
  addr ← #4;
  headBaseReg ← baseReg + addr;
  addr ← #(numBuckets n_max);
  keyBaseReg ← headBaseReg + addr;
  addr ← #n_max;
  valBaseReg ← keyBaseReg + addr;
  nextBaseReg ← valBaseReg + addr;
  addr ← headBaseReg + regOut;
  cur ← *addr;
  found ← zero;
  matchIdx ← zero ]

/-- Evaluate the bucket index `regOut = multiplyShift w₀ M b (encodeKey u)` and load `head[regOut]`
into `cur`. -/
def evalBucket (U n_max : ℕ) : Code .exact rHash :=
  .seq prepHash
    (.seq ((MultiplyShift.evalCode (hashBits U n_max) (bucketBits n_max)).rename hashEmbed)
      (loadBucketHead n_max))

/-- Single step of chain traversal: inspect slot `idx = cur - 1`; if `key[idx] = argU`, record
`found := 1, matchIdx := idx` and terminate the loop (`cur := 0`), else advance `cur := next[idx]`.
-/
def findInChainBody : Code .exact rHash := ram_exact[
  idx ← cur - one;
  addr ← keyBaseReg + idx;
  regT1 ← *addr;
  if regT1 = argU then [
    found ← one;
    matchIdx ← idx;
    cur ← zero
  ] else [
    addr ← nextBaseReg + idx;
    cur ← *addr
  ] ]

/-- Traverse the singly-linked bucket chain starting at `cur`. -/
def findInChain : Code .exact rHash := ram_exact[
  while zero < cur do [ ⟪findInChainBody⟫ ] ]

/-- Complete `get u` after `findInChain`: return `val[matchIdx] + 1` on a hit, or `0` on a miss. -/
def finishGet : Code .exact rHash := ram_exact[
  if zero < found then [
    addr ← valBaseReg + matchIdx;
    regT1 ← *addr;
    outReg ← regT1 + one
  ] else [
    outReg ← zero
  ] ]

/-- Complete `insert u v` on a key hit: overwrite `val[matchIdx] ← argV` in place. -/
def finishInsertHit : Code .exact rHash := ram_exact[
  addr ← valBaseReg + matchIdx;
  *addr ← argV ]

/-- Complete `insert u v` on a key miss: allocate slot `idx = allocCount`, increment `allocCount`,
write `key[idx] := argU`, `val[idx] := argV`, `next[idx] := head[regOut]`, and
`head[regOut] := idx + 1`. -/
def finishInsertMiss : Code .exact rHash := ram_exact[
  addr ← #3;
  addr ← baseReg + addr;
  idx ← *addr;
  regT1 ← idx + one;
  *addr ← regT1;
  addr ← keyBaseReg + idx;
  *addr ← argU;
  addr ← valBaseReg + idx;
  *addr ← argV;
  addr ← headBaseReg + regOut;
  regT2 ← *addr;
  addr ← nextBaseReg + idx;
  *addr ← regT2;
  addr ← headBaseReg + regOut;
  *addr ← regT1 ]

/-- Complete `insert u v` after `findInChain`. -/
def finishInsert : Code .exact rHash := ram_exact[
  if zero < found then [ ⟪finishInsertHit⟫ ] else [ ⟪finishInsertMiss⟫ ] ]

/-- Dispatch post-traversal completion between `get` (`tagReg = 0`) and `insert` (`tagReg ≠ 0`). -/
def finishOp : Code .exact rHash := ram_exact[
  if tagReg = zero then [ ⟪finishGet⟫ ] else [ ⟪finishInsert⟫ ] ]

/-- Unified operation dispatcher for `get` and `insert`. -/
def opCode (U n_max : ℕ) : Code .exact rHash :=
  .seq (evalBucket U n_max) (.seq findInChain finishOp)

/-- Relocatable `SubroutineCode` bundle for the chained hash table over `Basis.exact`. -/
def subroutineCode (U n_max : ℕ) : SubroutineCode .exact rHash 0 where
  allocSpan := allocSpan n_max
  initSetup := initSetup U n_max
  code := opCode U n_max
  frontierReg := frontierReg
  baseReg := baseReg
  initParams := Fin.elim0
  curReg := regT1
  zeroReg := zero
  oneReg := one
  incCur := .exactBin .add regT1 regT1 one
  input := inputMask
  output := outReg

/-- Standalone register encoding for `Dictionary.Op U`. -/
def encode {U : ℕ} : Dictionary.Op U → Fin rHash → ℕ
  | .get u => fun i => if i = tagReg then 0 else if i = argU then u.val else 0
  | .insert u v => fun i =>
      if i = tagReg then 1 else if i = argU then u.val else if i = argV then v else 0

/-- Partial argument-matching predicate for inline dictionary calls. -/
def argMatch {U : ℕ} : Dictionary.Op U → (Fin rHash → ℕ) → Prop
  | .get u => fun regs => regs tagReg = 0 ∧ regs argU = u.val
  | .insert u v => fun regs => regs tagReg ≠ 0 ∧ regs argU = u.val ∧ regs argV = v

/-- Output decoder for `Dictionary.spec U V n_max` (`0` = `none`, `v + 1` = `some v` on `get`). -/
def decode {U V n_max : ℕ} :
    (o : (Dictionary.spec U V n_max).Op) → (Fin rHash → ℕ) →
      Option ((Dictionary.spec U V n_max).Result o)
  | .get _, regs =>
      if regs outReg = 0 then some none else some (some (regs outReg - 1))
  | .insert _ _, _ => some ()

theorem arguments_fit {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o) (i : Fin rHash) :
    Fits w (encode o i) := by
  have h0 : Fits w 0 := fits_zero w
  have hsp : 4 ≤ space n_max := by unfold space; omega
  have h1 : Fits w 1 := hS.of_le (by omega)
  have hu_fit : ∀ u : Fin U, Fits w u.val := fun u => by
    rw [fits_iff]
    have hpow : 2 ^ hashBits U n_max ≤ 2 ^ w :=
      Nat.pow_le_pow_right two_pos (by omega)
    exact (u.isLt.trans_le (le_two_pow_hashBits U n_max)).trans_le hpow
  cases o with
  | get u =>
    simp only [encode]
    split_ifs
    · exact h0
    · exact hu_fit u
    · exact h0
  | insert u v =>
    have hv_lt : v < V := hv.2
    simp only [encode]
    split_ifs
    · exact h1
    · exact hu_fit u
    · exact hV.of_le (by omega)
    · exact h0

theorem encode_matches {U : ℕ} (o : Dictionary.Op U) (regs : Fin rHash → ℕ) :
    argMatch o (fun i => if inputMask i then encode o i else regs i) := by
  cases o <;> simp +decide [argMatch, encode]

/-! ## 3. Concrete representation invariant and chain length bound -/

/-- Inductive linked-list predicate for a bucket chain in `mem`: `IsChain mem nextBase sz ptr L`
states that following 1-based pointers from `ptr` through `next[idx]` (`mem (nextBase + idx)`)
visits the sequence `L` of 0-based pool indices `< sz` before reaching `0`. -/
inductive IsChain (mem : ℕ → ℕ) (nextBase sz : ℕ) : ℕ → List ℕ → Prop where
  | nil : IsChain mem nextBase sz 0 []
  | cons {idx nextPtr : ℕ} {rest : List ℕ} :
      idx < sz →
      mem (nextBase + idx) = nextPtr →
      IsChain mem nextBase sz nextPtr rest →
      IsChain mem nextBase sz (idx + 1) (idx :: rest)

theorem IsChain.lt_sz {mem : ℕ → ℕ} {nextBase sz ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L) : ∀ idx ∈ L, idx < sz := by
  induction h with
  | nil => intro _ hm; cases hm
  | cons hlt _ _ ih =>
    intro idx hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact hlt
    · exact ih idx hm'

theorem IsChain.unique {mem : ℕ → ℕ} {nextBase sz₁ sz₂ ptr : ℕ} {L₁ L₂ : List ℕ}
    (h₁ : IsChain mem nextBase sz₁ ptr L₁) (h₂ : IsChain mem nextBase sz₂ ptr L₂) :
    L₁ = L₂ := by
  induction h₁ generalizing L₂ with
  | nil =>
    cases h₂
    rfl
  | cons _ hn₁ _ ih =>
    cases h₂ with
    | cons _ hn₂ hc₂ =>
      have hn := hn₁.symm.trans hn₂
      subst hn
      exact congrArg _ (ih hc₂)

theorem IsChain.congr_mem {mem mem' : ℕ → ℕ} {nextBase sz ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L)
    (hmem : ∀ idx ∈ L, mem' (nextBase + idx) = mem (nextBase + idx)) :
    IsChain mem' nextBase sz ptr L := by
  induction h with
  | nil => exact .nil
  | cons hlt hn _ ih =>
    refine .cons hlt ((hmem _ List.mem_cons_self).trans hn) (ih fun i hi => ?_)
    exact hmem i (List.mem_cons_of_mem _ hi)

theorem IsChain.mono_sz {mem : ℕ → ℕ} {nextBase sz sz' ptr : ℕ} {L : List ℕ}
    (h : IsChain mem nextBase sz ptr L) (hsz : sz ≤ sz') :
    IsChain mem nextBase sz' ptr L := by
  induction h with
  | nil => exact .nil
  | cons hlt hn _ ih => exact .cons (hlt.trans_le hsz) hn ih

/-- Invariant for a single bucket `bk < numBuckets n_max` with chain `L : List ℕ`. -/
structure BucketInv (U n_max base : ℕ) (b : Fin (2 ^ (hashBits U n_max - 1)))
    (s : Dictionary.State U) (mem : ℕ → ℕ) (bk : ℕ) (L : List ℕ) : Prop where
  /-- `L` is the chain of 0-based slot indices starting at `head[bk]`. -/
  chain : IsChain mem (nextBase base n_max) (Dictionary.dom s).card (mem (headBase base + bk)) L
  /-- Keys stored along `L` are pairwise distinct. -/
  nodup : (L.map fun idx => mem (keyBase base n_max + idx)).Nodup
  /-- Every node `idx ∈ L` stores a key `u ∈ dom s` hashing to `bk` with value `val[idx]`. -/
  sound : ∀ idx ∈ L, ∃ u : Fin U,
    mem (keyBase base n_max + idx) = u.val ∧
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) = bk ∧
    s u = some (mem (valBase base n_max + idx))
  /-- Every key `u ∈ dom s` hashing to `bk` appears in `L`. -/
  complete : ∀ (u : Fin U) (v : ℕ),
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u) = bk →
    s u = some v →
    ∃ idx ∈ L, mem (keyBase base n_max + idx) = u.val

theorem BucketInv.congr_mem {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem mem' : ℕ → ℕ} {bk : ℕ} {L : List ℕ}
    (hb : BucketInv U n_max base b s mem bk L) (hbk : bk < numBuckets n_max)
    (hcard : (Dictionary.dom s).card ≤ n_max)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, mem' a = mem a) :
    BucketInv U n_max base b s mem' bk L := by
  have hhead : mem' (headBase base + bk) = mem (headBase base + bk) := by
    apply hmem
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, headBase, space]
    omega
  have hkey : ∀ idx ∈ L, mem' (keyBase base n_max + idx) = mem (keyBase base n_max + idx) := by
    intro idx hidx
    have hlt := hb.chain.lt_sz idx hidx
    apply hmem
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, keyBase, space]
    omega
  have hval : ∀ idx ∈ L, mem' (valBase base n_max + idx) = mem (valBase base n_max + idx) := by
    intro idx hidx
    have hlt := hb.chain.lt_sz idx hidx
    apply hmem
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, valBase, space]
    omega
  have hnext : ∀ idx ∈ L, mem' (nextBase base n_max + idx) = mem (nextBase base n_max + idx) := by
    intro idx hidx
    have hlt := hb.chain.lt_sz idx hidx
    apply hmem
    rw [Block.mem_footprint]
    dsimp only [Block.Owns, nextBase, space]
    omega
  have hmap : (L.map fun idx => mem' (keyBase base n_max + idx)) =
      (L.map fun idx => mem (keyBase base n_max + idx)) :=
    List.map_congr_left hkey
  refine ⟨hhead ▸ hb.chain.congr_mem hnext, hmap ▸ hb.nodup, ?_, ?_⟩
  · intro idx hidx
    obtain ⟨u, hu_key, hu_bk, hu_val⟩ := hb.sound idx hidx
    exact ⟨u, (hkey idx hidx).trans hu_key, hu_bk, (hval idx hidx) ▸ hu_val⟩
  · intro u v hu_bk hsv
    obtain ⟨idx, hidx, hu_key⟩ := hb.complete u v hu_bk hsv
    exact ⟨idx, hidx, (hkey idx hidx).trans hu_key⟩

/-- If `idx₁ ∈ L₁` (in bucket `bk₁`) and `idx₂ ∈ L₂` (in bucket `bk₂`) and `idx₁ = idx₂`, then
`bk₁ = bk₂` and `L₁ = L₂`. -/
theorem BucketInv.eq_of_mem_eq {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {bk₁ bk₂ idx : ℕ} {L₁ L₂ : List ℕ}
    (hb₁ : BucketInv U n_max base b s mem bk₁ L₁)
    (hb₂ : BucketInv U n_max base b s mem bk₂ L₂)
    (h₁ : idx ∈ L₁) (h₂ : idx ∈ L₂) :
    bk₁ = bk₂ ∧ L₁ = L₂ := by
  obtain ⟨u₁, hk₁, hbk₁, _⟩ := hb₁.sound idx h₁
  obtain ⟨u₂, hk₂, hbk₂, _⟩ := hb₂.sound idx h₂
  have hu : u₁ = u₂ := Fin.ext (hk₁.symm.trans hk₂)
  subst hu
  have hbk : bk₁ = bk₂ := hbk₁.symm.trans hbk₂
  subst hbk
  exact ⟨rfl, hb₁.chain.unique hb₂.chain⟩

private theorem idx_eq_of_nodup_map {α β : Type*} {f : α → β} {L : List α}
    (hnd : (L.map f).Nodup) {x y : α} (hx : x ∈ L) (hy : y ∈ L) (hxy : f x = f y) :
    x = y := by
  induction L with
  | nil => cases hx
  | cons a rest ih =>
    obtain ⟨hna, hnd'⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (hxy ▸ List.mem_map_of_mem hy') hna
    · exact absurd (hxy.symm ▸ List.mem_map_of_mem hx') hna
    · exact ih hnd' hx' hy'

/-- Within a single bucket `bk`, two slots `idx₁, idx₂ ∈ L` have the same stored key if and only if
`idx₁ = idx₂`. -/
theorem BucketInv.idx_eq_of_key_eq {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {bk idx₁ idx₂ : ℕ} {L : List ℕ}
    (hb : BucketInv U n_max base b s mem bk L)
    (h₁ : idx₁ ∈ L) (h₂ : idx₂ ∈ L)
    (hk : mem (keyBase base n_max + idx₁) = mem (keyBase base n_max + idx₂)) :
    idx₁ = idx₂ :=
  idx_eq_of_nodup_map hb.nodup h₁ h₂ hk

/-- **Chain length bound**: for any query key `u : Fin U`, the length of the chain `L` in bucket
`bk = multiplyShift w₀ M b (encodeKey u)` is at most `1` plus the number of other keys
`u' ∈ (dom s).erase u` that collide with `u` under `multiplyShift w₀ M b`. -/
theorem BucketInv.length_le {U n_max base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {mem : ℕ → ℕ} {L : List ℕ} (u : Fin U)
    (hb : BucketInv U n_max base b s mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L) :
    L.length ≤ 1 + (((Dictionary.dom s).erase u).filter fun u' =>
      multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') =
        multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)).card := by
  classical
  set bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
  set F : Finset (Fin U) := (Dictionary.dom s).filter fun u' =>
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') = bk
  set F' : Finset (Fin U) := ((Dictionary.dom s).erase u).filter fun u' =>
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') = bk
  set ks := L.map fun idx => mem (keyBase base n_max + idx)
  have hlen : L.length = ks.toFinset.card := by
    rw [List.toFinset_card_of_nodup hb.nodup, List.length_map]
  have hsub : ks.toFinset ⊆ F.image Fin.val := by
    intro k hk
    rw [List.mem_toFinset, List.mem_map] at hk
    obtain ⟨idx, hidx, rfl⟩ := hk
    obtain ⟨u', hu_key, hu_bk, hu_val⟩ := hb.sound idx hidx
    rw [Finset.mem_image]
    refine ⟨u', ?_, hu_key.symm⟩
    rw [Finset.mem_filter, Dictionary.mem_dom_iff]
    exact ⟨⟨_, hu_val⟩, hu_bk⟩
  have hF_sub : F ⊆ insert u F' := by
    intro u' hu'
    rw [Finset.mem_filter] at hu'
    rw [Finset.mem_insert]
    by_cases heq : u' = u
    · exact Or.inl heq
    · right
      rw [Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨heq, hu'.1⟩, hu'.2⟩
  calc
    L.length = ks.toFinset.card := hlen
    _ ≤ (F.image Fin.val).card := Finset.card_le_card hsub
    _ ≤ F.card := Finset.card_image_le
    _ ≤ (insert u F').card := Finset.card_le_card hF_sub
    _ ≤ F'.card + 1 := Finset.card_insert_le u F'
    _ = 1 + F'.card := Nat.add_comm _ _

/-- Seed-coupled concrete representation invariant for the chained hash table at `base`. -/
structure Rep (U V n_max w base : ℕ) (b : Fin (2 ^ (hashBits U n_max - 1)))
    (s : Dictionary.State U) (x : Data rHash) : Prop where
  /-- All registers and memory words fit in `w`-bit words. -/
  bounded : x.Bounded w
  /-- Persistent base-address register holds `base`. -/
  reg_base : x.regs baseReg = base
  /-- Header word `base + 0` stores the sampled multiply-shift seed `b.val`. -/
  mem_seed : x.mem base = b.val
  /-- Header word `base + 1` stores `bucketBits n_max`. -/
  mem_M : x.mem (base + 1) = bucketBits n_max
  /-- Header word `base + 2` stores `hashBits U n_max`. -/
  mem_w0 : x.mem (base + 2) = hashBits U n_max
  /-- Header word `base + 3` stores `allocCount = (dom s).card`. -/
  mem_sz : x.mem (base + 3) = (Dictionary.dom s).card
  /-- Current key count is at most `n_max`. -/
  card_le : (Dictionary.dom s).card ≤ n_max
  /-- Every stored value in `s` is strictly less than `V`. -/
  vals_lt : Dictionary.ValuesBounded V s
  /-- Every bucket `bk < numBuckets n_max` satisfies `BucketInv`. -/
  buckets : ∀ bk < numBuckets n_max, ∃ L : List ℕ, BucketInv U n_max base b s x.mem bk L

theorem Rep.unique {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s₁ s₂ : Dictionary.State U} {x : Data rHash}
    (hr₁ : Rep U V n_max w base b s₁ x) (hr₂ : Rep U V n_max w base b s₂ x) :
    s₁ = s₂ := by
  funext u
  set bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
  have hbk : bk < numBuckets n_max := multiplyShift_lt_numBuckets b u
  obtain ⟨L₁, hb₁⟩ := hr₁.buckets bk hbk
  obtain ⟨L₂, hb₂⟩ := hr₂.buckets bk hbk
  have hL : L₁ = L₂ := hb₁.chain.unique hb₂.chain
  subst hL
  cases h₁ : s₁ u with
  | none =>
    cases h₂ : s₂ u with
    | none => rfl
    | some v₂ =>
      obtain ⟨idx, hidx, hkey⟩ := hb₂.complete u v₂ rfl h₂
      obtain ⟨u', hkey', _, hsv₁⟩ := hb₁.sound idx hidx
      have hu : u' = u := Fin.ext (hkey'.symm.trans hkey)
      subst hu
      rw [h₁] at hsv₁
      cases hsv₁
  | some v₁ =>
    obtain ⟨idx, hidx, hkey⟩ := hb₁.complete u v₁ rfl h₁
    obtain ⟨u₁, hkey₁, _, hsv₁⟩ := hb₁.sound idx hidx
    obtain ⟨u₂, hkey₂, _, hsv₂⟩ := hb₂.sound idx hidx
    have hu₁ : u₁ = u := Fin.ext (hkey₁.symm.trans hkey)
    have hu₂ : u₂ = u := Fin.ext (hkey₂.symm.trans hkey)
    subst hu₁; subst hu₂
    exact h₁.symm.trans (hsv₁.trans hsv₂.symm)

theorem Rep.supported {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {x x' : Data rHash}
    (hreg : ∀ i, inputMask i = false → x'.regs i = x.regs i)
    (hmem : ∀ a ∈ (Block.mk base (space n_max)).footprint, x'.mem a = x.mem a)
    (hbx' : x'.Bounded w) (hr : Rep U V n_max w base b s x) :
    Rep U V n_max w base b s x' := by
  have hsp : 4 ≤ space n_max := by unfold space; omega
  have hm0 : x'.mem base = x.mem base :=
    hmem base (by rw [Block.mem_footprint]; dsimp [Block.Owns]; omega)
  have hm1 : x'.mem (base + 1) = x.mem (base + 1) :=
    hmem (base + 1) (by rw [Block.mem_footprint]; dsimp [Block.Owns]; omega)
  have hm2 : x'.mem (base + 2) = x.mem (base + 2) :=
    hmem (base + 2) (by rw [Block.mem_footprint]; dsimp [Block.Owns]; omega)
  have hm3 : x'.mem (base + 3) = x.mem (base + 3) :=
    hmem (base + 3) (by rw [Block.mem_footprint]; dsimp [Block.Owns]; omega)
  refine ⟨hbx', (hreg baseReg (by decide)).trans hr.reg_base,
    hm0.trans hr.mem_seed, hm1.trans hr.mem_M, hm2.trans hr.mem_w0, hm3.trans hr.mem_sz,
    hr.card_le, hr.vals_lt, fun bk hbk => ?_⟩
  obtain ⟨L, hb⟩ := hr.buckets bk hbk
  exact ⟨L, hb.congr_mem hbk hr.card_le hmem⟩

/-! ## 4. Initialization execution (`allocSpan`, `storeHeader`, `initSetup`) -/

private theorem fits_hashBits {U n_max w : ℕ} (hw : 2 * hashBits U n_max ≤ w) :
    Fits w (hashBits U n_max) := by
  rw [fits_iff]
  exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos (by omega))

private theorem fits_bucketBits {U n_max w : ℕ} (hw : 2 * hashBits U n_max ≤ w) :
    Fits w (bucketBits n_max) :=
  (fits_hashBits hw).of_le (bucketBits_le_hashBits U n_max)

private theorem allocSpan_spec {n_max w base : ℕ} (hS : Fits w (base + space n_max))
    {x : Data rHash} (hfr : x.regs frontierReg = base) :
    ∃ x₁, ExecWithin w (allocSpan n_max) x x₁ 3 ∧ x₁.mem = x.mem ∧
      x₁.regs baseReg = base ∧ x₁.regs frontierReg = base + space n_max := by
  have f₁ : Fits w (space n_max) := hS.of_le (by omega)
  refine ⟨?z, ?e, ?_, ?_, ?_⟩
  case e => ram_exact_eval [allocSpan, hfr, f₁, hS]
  · rfl
  · simp +decide
  · simp +decide

private theorem storeHeader_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {x : Data rHash}
    (hx : x.Bounded w) (hbase : x.regs baseReg = base)
    (hfr : x.regs frontierReg = base + space n_max)
    (hb : x.regs regB = b.val)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x.mem a = 0) :
    ∃ y, Exec w (storeHeader U n_max) x y 11 ∧
      y.regs frontierReg = base + space n_max ∧
      Rep U V n_max w base b (Dictionary.empty U) y ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem y.mem := by
  have hsp : 4 ≤ space n_max := by unfold space; omega
  have f0 : Fits w 0 := fits_zero w
  have f1 : Fits w 1 := hS.of_le (by omega)
  have fb1 : Fits w (base + 1) := hS.of_le (by omega)
  have fb2 : Fits w (base + 1 + 1) := hS.of_le (by omega)
  have fb3 : Fits w (base + 1 + 1 + 1) := hS.of_le (by omega)
  have fM : Fits w (bucketBits n_max) := fits_bucketBits hw
  have fw0 : Fits w (hashBits U n_max) := fits_hashBits hw
  obtain ⟨y, he, hyfr, hybase, hym⟩ :
      ∃ y, Exec w (storeHeader U n_max) x y 11 ∧
        y.regs frontierReg = base + space n_max ∧
        y.regs baseReg = base ∧
        y.mem = Function.update (Function.update (Function.update
          (Function.update x.mem base b.val)
          (base + 1) (bucketBits n_max))
          (base + 1 + 1) (hashBits U n_max))
          (base + 1 + 1 + 1) 0 := by
    refine ⟨?z, ?e, ?_, ?_, ?_⟩
    case e =>
      ram_exact_eval [storeHeader, hbase, hb, f0, f1, fb1, fb2, fb3, fM, fw0]
    · simp +decide [hfr]
    · simp +decide [hbase]
    · rfl
  refine ⟨y, he, hyfr, ?_, ?_⟩
  · refine ⟨he.within.bounded hx, hybase, ?_, ?_, ?_, ?_, by simp,
      Dictionary.valuesBounded_empty U V, ?_⟩
    · rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_self]
    · rw [hym, Function.update_of_ne (by omega),
        show base + 2 = base + 1 + 1 by omega, Function.update_self]
    · rw [hym, show base + 3 = base + 1 + 1 + 1 by omega, Function.update_self,
        Dictionary.card_dom_empty]
    · intro bk hbk
      refine ⟨[], ?_⟩
      have hhead0 : y.mem (headBase base + bk) = 0 := by
        dsimp only [headBase]
        rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hz (base + 4 + bk) (by rw [Block.mem_footprint]; dsimp [Block.Owns, space]; omega)
      refine ⟨hhead0 ▸ IsChain.nil, List.nodup_nil, ?_, ?_⟩
      · intro _ h; cases h
      · intro u v _ h; simp [Dictionary.empty] at h
  · rw [Modifies.block_iff]
    intro a ha
    dsimp only [Block.Owns] at ha
    rw [hym, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem initSetup_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {x₁ : Data rHash} (hx₁ : x₁.Bounded w) (hbase : x₁.regs baseReg = base)
    (hfr : x₁.regs frontierReg = base + space n_max)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x₁.mem a = 0) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    ∃ ν₀ : PMF (Seed × Data rHash),
      ExecCodeDist w (initSetup U n_max) x₁ (ν₀.map Prod.snd) 13 ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 1 * seedLaw θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs frontierReg = base + space n_max ∧
        Rep U V n_max w base p.1 (Dictionary.empty U) p.2 ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem p.2.mem := by
  classical
  set w₀ := hashBits U n_max
  set Seed := Fin (2 ^ (w₀ - 1))
  set seedLaw := PMF.uniformOfFintype Seed
  have hw₀ : w₀ ≤ w := by omega
  let d₁ : Data 5 := x₁.comap hashEmbed
  let x_mid : Seed → Data rHash :=
    fun b => (MultiplyShift.initData w₀ d₁ b.val).extend hashEmbed x₁
  have hmid_spec : ∀ b : Seed,
      (x_mid b).Bounded w ∧ (x_mid b).regs baseReg = base ∧
      (x_mid b).regs frontierReg = base + space n_max ∧
      (x_mid b).regs regB = b.val ∧ (x_mid b).mem = x₁.mem := by
    intro b
    have hd₁_bdd : (MultiplyShift.initData w₀ d₁ b.val).Bounded w := by
      have hfit1 : Fits w (2 ^ (w₀ - 1) - 1) := by
        rw [fits_iff]
        have hlt : 2 ^ (w₀ - 1) - 1 < 2 ^ (w₀ - 1) := Nat.sub_lt (by positivity) one_pos
        exact hlt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
      have hfitb : Fits w b.val := by
        rw [fits_iff]
        exact b.isLt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
      exact ((hx₁.comap hashEmbed).set hfit1).set hfitb
    have hbase_out : baseReg ∉ Set.range hashEmbed := by
      rintro ⟨i, hi⟩; revert hi; fin_cases i <;> decide
    have hfr_out : frontierReg ∉ Set.range hashEmbed := by
      rintro ⟨i, hi⟩; revert hi; fin_cases i <;> decide
    refine ⟨hd₁_bdd.extend hashEmbed_injective hx₁,
      (Data.extend_regs_of_notMem _ _ hbase_out).trans hbase,
      (Data.extend_regs_of_notMem _ _ hfr_out).trans hfr, ?_, rfl⟩
    change ((x_mid b).comap hashEmbed).regs MultiplyShift.regB = b.val
    dsimp only [x_mid]
    rw [Data.comap_extend hashEmbed_injective]
    simp [MultiplyShift.initData]
  have hstep2 : ∀ b : Seed,
      ∃ y, Exec w (storeHeader U n_max) (x_mid b) y 11 ∧
        y.regs frontierReg = base + space n_max ∧
        Rep U V n_max w base b (Dictionary.empty U) y ∧
        Modifies (Block.mk base (space n_max)).footprint x₁.mem y.mem := by
    intro b
    obtain ⟨hbdd, hb_reg, hfr_reg, hregB, hmem_eq⟩ := hmid_spec b
    have hz_b : ∀ a ∈ (Block.mk base (space n_max)).footprint, (x_mid b).mem a = 0 := by
      rwa [hmem_eq]
    simpa only [hmem_eq] using storeHeader_spec hw hS hbdd hb_reg hfr_reg hregB hz_b
  let y_init : Seed → Data rHash := fun b => Classical.choose (hstep2 b)
  have hy_spec : ∀ b : Seed,
      Exec w (storeHeader U n_max) (x_mid b) (y_init b) 11 ∧
      (y_init b).regs frontierReg = base + space n_max ∧
      Rep U V n_max w base b (Dictionary.empty U) (y_init b) ∧
      Modifies (Block.mk base (space n_max)).footprint x₁.mem (y_init b).mem :=
    fun b => Classical.choose_spec (hstep2 b)
  have hinit1 : ExecCodeDist w ((MultiplyShift.initCode w₀).rename hashEmbed)
      x₁ (seedLaw.map x_mid) 2 := by
    have hr := (ExecCodeDist.of_execRand (MultiplyShift.initCode_execRand hw₀ d₁)).rename
      hashEmbed_injective (x := x₁)
    refine hr.congr_dist ?_ ?_
    · have hev : (Prod.fst <$> MultiplyShift.initComp w₀ d₁).eval =
          seedLaw.map (fun b : Seed => MultiplyShift.initData w₀ d₁ b.val) := by
        have h1 : (Prod.fst <$> MultiplyShift.initComp w₀ d₁).eval =
            (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).map
              (fun k => MultiplyShift.initData w₀ d₁ k.val) := by
          rw [MultiplyShift.initComp, bind_pure_comp, Functor.map_map, ProbComp.eval_map,
            ProbComp.eval_unifFin]
        have h2 : seedLaw =
            (PMF.uniformOfFintype (Fin (2 ^ (w₀ - 1) - 1 + 1))).map
              (finCongr (Nat.sub_add_cancel Nat.one_le_two_pow)) :=
          (PMF.uniformOfFintype_map_equiv
            (finCongr (Nat.sub_add_cancel Nat.one_le_two_pow))).symm
        rw [h1, h2, PMF.map_comp]
        rfl
      rw [hev, PMF.map_comp]
      rfl
    · simp [MultiplyShift.initComp, bind_pure_comp, ProbComp.expect_map, ProbComp.expect_const]
  let ν₀ : PMF (Seed × Data rHash) := seedLaw.map fun b => (b, y_init b)
  refine ⟨ν₀, ?_, ?_, ?_⟩
  · have hseq := hinit1.seq_const
      (c₂ := storeHeader U n_max)
      (μ₂ := fun z =>
        if h : ∃ b : Seed, z = x_mid b then PMF.pure (y_init (Classical.choose h))
        else PMF.pure z)
      (T₂ := fun _ => 11) (B₂ := 11)
      (fun z hz => by
        rw [PMF.mem_support_map_iff] at hz
        obtain ⟨b, _, rfl⟩ := hz
        have hex : ∃ b' : Seed, x_mid b = x_mid b' := ⟨b, rfl⟩
        have hb_eq : Classical.choose hex = b := by
          have hchoose : x_mid (Classical.choose hex) = x_mid b :=
            (Classical.choose_spec hex).symm
          have hreg := congrArg (fun d => d.regs regB) hchoose
          rw [(hmid_spec (Classical.choose hex)).2.2.2.1, (hmid_spec b).2.2.2.1] at hreg
          exact Fin.ext hreg
        simp only [hex, ↓reduceDIte, hb_eq]
        exact ExecCodeDist.of_exec (hy_spec b).1)
      (fun _ _ => le_rfl)
    refine hseq.congr_dist ?_ (by norm_num)
    rw [PMF.bind_map]
    ext z
    simp only [ν₀, PMF.map_comp, PMF.map_apply, PMF.bind_apply, Function.comp_apply]
    refine tsum_congr fun b => ?_
    have hex : ∃ b' : Seed, x_mid b = x_mid b' := ⟨b, rfl⟩
    have hb_eq : Classical.choose hex = b := by
      have hchoose : x_mid (Classical.choose hex) = x_mid b :=
        (Classical.choose_spec hex).symm
      have hreg := congrArg (fun d => d.regs regB) hchoose
      rw [(hmid_spec (Classical.choose hex)).2.2.2.1, (hmid_spec b).2.2.2.1] at hreg
      exact Fin.ext hreg
    simp [hex, hb_eq, PMF.pure_apply]
  · intro θ
    dsimp only [ν₀]
    rw [PMF.map_comp, show Prod.fst ∘ (fun b : Seed => (b, y_init b)) = id from rfl,
      PMF.map_id, one_mul]
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨b, _, rfl⟩ := hp
    exact ⟨(hy_spec b).2.1, (hy_spec b).2.2.1, (hy_spec b).2.2.2⟩

/-! ## 5. Deterministic operation execution (`evalBucket`, `findInChain`, `finishOp`, `opCode`) -/

private theorem not_mem_range_hashEmbed {r : Fin rHash} (hr : 5 ≤ r.val) :
    r ∉ Set.range hashEmbed := by
  rintro ⟨i, rfl⟩
  revert hr
  fin_cases i <;> decide

private theorem evalBucket_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x : Data rHash}
    (hr : Rep U V n_max w base b s x) {u : Fin U} (hu : x.regs argU = u.val) :
    let bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
    ∃ y, Exec w (evalBucket U n_max) x y 24 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs baseReg = base ∧
      y.regs tagReg = x.regs tagReg ∧
      y.regs argU = u.val ∧
      y.regs argV = x.regs argV ∧
      y.regs regOut = bk ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs headBaseReg = headBase base ∧
      y.regs keyBaseReg = keyBase base n_max ∧
      y.regs valBaseReg = valBase base n_max ∧
      y.regs nextBaseReg = nextBase base n_max ∧
      y.regs cur = x.mem (headBase base + bk) ∧
      y.regs found = 0 := by
  intro bk
  have hbase := hr.reg_base
  have hseed := hr.mem_seed
  have fb : Fits w b.val := hseed ▸ hr.bounded.2 base
  have fu : Fits w u.val := hu ▸ hr.bounded.1 argU
  obtain ⟨x₁, he1, hm1, hregB1, hregX1, hbase1, htag1, hargU1, hargV1⟩ :
      ∃ x₁, Exec w prepHash x x₁ 2 ∧ x₁.mem = x.mem ∧
        x₁.regs regB = b.val ∧ x₁.regs regX = u.val ∧
        x₁.regs baseReg = base ∧ x₁.regs tagReg = x.regs tagReg ∧
        x₁.regs argU = u.val ∧ x₁.regs argV = x.regs argV := by
    refine ⟨?z, ?e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e => ram_exact_eval [prepHash, hbase, hseed, hu, fb, fu]
    · rfl
    · simp +decide
    · simp +decide
    · simp +decide [hbase]
    · simp +decide
    · simp +decide [hu]
    · simp +decide
  have hx₁_bdd : x₁.Bounded w := he1.within.bounded hr.bounded
  let d₁ : Data 5 := x₁.comap hashEmbed
  have hd₁_B : d₁.regs MultiplyShift.regB = b.val := hregB1
  have hd₁_X : d₁.regs MultiplyShift.regX = (@encodeKey U n_max u).val := hregX1
  have hd₁_B_lt : d₁.regs MultiplyShift.regB < 2 ^ (hashBits U n_max - 1) := hd₁_B ▸ b.isLt
  have hd₁_X_lt : d₁.regs MultiplyShift.regX < 2 ^ hashBits U n_max :=
    hd₁_X ▸ (@encodeKey U n_max u).isLt
  have he2_raw := (MultiplyShift.evalCode_exec (M := bucketBits n_max)
    (hashBits_pos U n_max) hw hd₁_B_lt hd₁_X_lt).rename hashEmbed_injective (x := x₁)
  let x₂ := (MultiplyShift.evalData (hashBits U n_max) (bucketBits n_max) d₁).extend hashEmbed x₁
  have hx₂_bdd : x₂.Bounded w := he2_raw.within.bounded hx₁_bdd
  have hm2 : x₂.mem = x.mem := hm1
  have hout2 : x₂.regs regOut = bk := by
    change (x₂.comap hashEmbed).regs MultiplyShift.regOut = bk
    dsimp only [x₂]
    rw [Data.comap_extend hashEmbed_injective]
    exact MultiplyShift.evalData_regs_out_eq_multiplyShift (hashBits U n_max) (bucketBits n_max)
      d₁ b (encodeKey u) hd₁_B hd₁_X
  have hbase2 : x₂.regs baseReg = base :=
    (Data.extend_regs_of_notMem _ _ (not_mem_range_hashEmbed (by decide))).trans hbase1
  have htag2 : x₂.regs tagReg = x.regs tagReg :=
    (Data.extend_regs_of_notMem _ _ (not_mem_range_hashEmbed (by decide))).trans htag1
  have hargU2 : x₂.regs argU = u.val :=
    (Data.extend_regs_of_notMem _ _ (not_mem_range_hashEmbed (by decide))).trans hargU1
  have hargV2 : x₂.regs argV = x.regs argV :=
    (Data.extend_regs_of_notMem _ _ (not_mem_range_hashEmbed (by decide))).trans hargV1
  have hbk_lt : bk < numBuckets n_max := multiplyShift_lt_numBuckets b u
  have hsp : 4 + numBuckets n_max + 3 * n_max = space n_max := rfl
  have f0 : Fits w 0 := fits_zero w
  have f1 : Fits w 1 := hS.of_le (by omega)
  have f4 : Fits w 4 := hS.of_le (by omega)
  have fhb : Fits w (base + 4) := hS.of_le (by omega)
  have fnb : Fits w (numBuckets n_max) := hS.of_le (by omega)
  have fkb : Fits w (base + 4 + numBuckets n_max) := hS.of_le (by omega)
  have fnm : Fits w n_max := hS.of_le (by omega)
  have fvb : Fits w (base + 4 + numBuckets n_max + n_max) := hS.of_le (by omega)
  have fxb : Fits w (base + 4 + numBuckets n_max + n_max + n_max) := hS.of_le (by omega)
  have fhbk : Fits w (base + 4 + bk) := hS.of_le (by omega)
  have fcur : Fits w (x₂.mem (base + 4 + bk)) := hx₂_bdd.2 _
  obtain ⟨y, he3, hmy, hbase3, htag3, hargU3, hargV3, hout3, hz3, ho3,
      hhb3, hkb3, hvb3, hxb3, hcur3, hfnd3⟩ :
      ∃ y, Exec w (loadBucketHead n_max) x₂ y 13 ∧
        y.mem = x₂.mem ∧
        y.regs baseReg = base ∧
        y.regs tagReg = x.regs tagReg ∧
        y.regs argU = u.val ∧
        y.regs argV = x.regs argV ∧
        y.regs regOut = bk ∧
        y.regs zero = 0 ∧
        y.regs one = 1 ∧
        y.regs headBaseReg = headBase base ∧
        y.regs keyBaseReg = keyBase base n_max ∧
        y.regs valBaseReg = valBase base n_max ∧
        y.regs nextBaseReg = nextBase base n_max ∧
        y.regs cur = x₂.mem (headBase base + bk) ∧
        y.regs found = 0 := by
    refine ⟨?_, ?e3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e3 =>
      ram_exact_eval [loadBucketHead, hbase2, hout2, f0, f1, f4, fhb, fnb, fkb, fnm, fvb, fxb,
        fhbk, fcur]
    · rfl
    · simp +decide [hbase2]
    · simp +decide [htag2]
    · simp +decide [hargU2]
    · simp +decide [hargV2]
    · simp +decide [hout2]
    · simp +decide
    · simp +decide
    · simp +decide [headBase]
    · simp +decide [keyBase]
    · simp +decide [valBase]
    · simp +decide [nextBase]; omega
    · simp +decide [headBase]
    · simp +decide
  have he23 := Exec.seq he2_raw he3
  have he123 := Exec.seq he1 he23
  refine ⟨y, he123, he123.within.bounded hr.bounded, hmy.trans hm2,
    hbase3, htag3, hargU3, hargV3, hout3, hz3, ho3, hhb3, hkb3, hvb3, hxb3, ?_, hfnd3⟩
  rw [hm2] at hcur3
  exact hcur3

private theorem findInChain_spec {U n_max w base sz : ℕ}
    (hS : Fits w (base + space n_max)) (hsz : sz ≤ n_max)
    {mem : ℕ → ℕ} {u : Fin U} {ptr : ℕ} {L : List ℕ} {x : Data rHash}
    (hc : IsChain mem (nextBase base n_max) sz ptr L)
    (hmem : x.mem = mem)
    (hx : x.Bounded w)
    (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hkb : x.regs keyBaseReg = keyBase base n_max)
    (hxb : x.regs nextBaseReg = nextBase base n_max)
    (hu : x.regs argU = u.val)
    (hcur : x.regs cur = ptr) :
    ∃ y, ExecWithin w findInChain x y (9 * L.length + 2) ∧
      y.Bounded w ∧
      y.mem = mem ∧
      y.regs baseReg = x.regs baseReg ∧
      y.regs tagReg = x.regs tagReg ∧
      y.regs argU = u.val ∧
      y.regs argV = x.regs argV ∧
      y.regs regOut = x.regs regOut ∧
      y.regs zero = 0 ∧
      y.regs one = 1 ∧
      y.regs headBaseReg = x.regs headBaseReg ∧
      y.regs keyBaseReg = keyBase base n_max ∧
      y.regs valBaseReg = x.regs valBaseReg ∧
      y.regs nextBaseReg = nextBase base n_max ∧
      ((∃ i ∈ L, mem (keyBase base n_max + i) = u.val ∧ y.regs found = 1 ∧ y.regs matchIdx = i) ∨
        ((∀ i ∈ L, mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = x.regs found)) := by
  induction hc generalizing x with
  | nil =>
    have he : Exec w findInChain x x 2 :=
      Exec.loop_exit (by simp [Cond.Holds, hz, hcur])
    refine ⟨x, he.within, hx, hmem, rfl, rfl, hu, rfl, rfl, hz, ho, rfl, hkb, rfl, hxb,
      Or.inr ⟨?_, rfl⟩⟩
    intro i hi; cases hi
  | @cons idx₀ ptr' L' hidx hnext hc' ih =>
    have hsp : 4 + numBuckets n_max + 3 * n_max = space n_max := rfl
    have fidx : Fits w idx₀ := hS.of_le (by omega)
    have fkaddr : Fits w (keyBase base n_max + idx₀) := hS.of_le (by unfold keyBase; omega)
    have fkey : Fits w (x.mem (keyBase base n_max + idx₀)) := hx.2 _
    by_cases hhit : mem (keyBase base n_max + idx₀) = u.val
    · have hhit_x : x.mem (keyBase base n_max + idx₀) = u.val := hmem ▸ hhit
      obtain ⟨x₁, he1, hm1, hbase1, htag1, hargU1, hargV1, hout1, hz1, ho1,
          hhb1, hkb1, hvb1, hxb1, hcur1, hfnd1, hmidx1⟩ :
          ∃ x₁, Exec w findInChainBody x x₁ 7 ∧
            x₁.mem = x.mem ∧
            x₁.regs baseReg = x.regs baseReg ∧
            x₁.regs tagReg = x.regs tagReg ∧
            x₁.regs argU = u.val ∧
            x₁.regs argV = x.regs argV ∧
            x₁.regs regOut = x.regs regOut ∧
            x₁.regs zero = 0 ∧
            x₁.regs one = 1 ∧
            x₁.regs headBaseReg = x.regs headBaseReg ∧
            x₁.regs keyBaseReg = keyBase base n_max ∧
            x₁.regs valBaseReg = x.regs valBaseReg ∧
            x₁.regs nextBaseReg = nextBase base n_max ∧
            x₁.regs cur = 0 ∧
            x₁.regs found = 1 ∧
            x₁.regs matchIdx = idx₀ := by
        refine ⟨?_, ?e1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        case e1 =>
          ram_exact_eval [findInChainBody, hcur, ho, hz, hkb, hu, hhit_x, Nat.add_sub_cancel,
            fidx, fkaddr, fkey]
        · rfl
        · simp +decide
        · simp +decide
        · simp +decide [hu]
        · simp +decide
        · simp +decide
        · simp +decide [hz]
        · simp +decide [ho]
        · simp +decide
        · simp +decide [hkb]
        · simp +decide
        · simp +decide [hxb]
        · simp +decide
        · simp +decide
        · simp +decide
      have he2 : Exec w findInChain x₁ x₁ 2 :=
        Exec.loop_exit (by simp [Cond.Holds, hz1, hcur1])
      have he_tot : Exec w findInChain x x₁ (7 + 2 + 2) :=
        Exec.loop_iter (by simp [Cond.Holds, hz, hcur]) he1 he2
      refine ⟨x₁, he_tot.within.mono (by simp), he_tot.within.bounded hx,
        hm1.trans hmem, hbase1, htag1, hargU1, hargV1, hout1, hz1, ho1, hhb1, hkb1, hvb1, hxb1,
        Or.inl ⟨idx₀, List.mem_cons_self, hhit, hfnd1, hmidx1⟩⟩
    · have hhit_x : x.mem (keyBase base n_max + idx₀) ≠ u.val := hmem ▸ hhit
      have hnext_x : x.mem (nextBase base n_max + idx₀) = ptr' := hmem ▸ hnext
      have fnaddr : Fits w (nextBase base n_max + idx₀) := hS.of_le (by unfold nextBase; omega)
      have fnext : Fits w (x.mem (nextBase base n_max + idx₀)) := hx.2 _
      obtain ⟨x₁, he1, hm1, hbase1, htag1, hargU1, hargV1, hout1, hz1, ho1,
          hhb1, hkb1, hvb1, hxb1, hcur1, hfnd1⟩ :
          ∃ x₁, Exec w findInChainBody x x₁ 7 ∧
            x₁.mem = x.mem ∧
            x₁.regs baseReg = x.regs baseReg ∧
            x₁.regs tagReg = x.regs tagReg ∧
            x₁.regs argU = u.val ∧
            x₁.regs argV = x.regs argV ∧
            x₁.regs regOut = x.regs regOut ∧
            x₁.regs zero = 0 ∧
            x₁.regs one = 1 ∧
            x₁.regs headBaseReg = x.regs headBaseReg ∧
            x₁.regs keyBaseReg = keyBase base n_max ∧
            x₁.regs valBaseReg = x.regs valBaseReg ∧
            x₁.regs nextBaseReg = nextBase base n_max ∧
            x₁.regs cur = ptr' ∧
            x₁.regs found = x.regs found := by
        refine ⟨?_, ?e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        case e2 =>
          ram_exact_eval [findInChainBody, hcur, ho, hz, hkb, hxb, hu, hhit_x, Nat.add_sub_cancel,
            fidx, fkaddr, fkey, fnaddr, fnext]
        · rfl
        · simp +decide
        · simp +decide
        · simp +decide [hu]
        · simp +decide
        · simp +decide
        · simp +decide [hz]
        · simp +decide [ho]
        · simp +decide
        · simp +decide [hkb]
        · simp +decide
        · simp +decide [hxb]
        · simp +decide [hnext_x]
        · simp +decide
      have hx₁_bdd : x₁.Bounded w := he1.within.bounded hx
      obtain ⟨y, ⟨m₂, hm₂_le, he2⟩, hy_bdd, hmy, hbase2, htag2, hargU2, hargV2, hout2,
          hz2, ho2, hhb2, hkb2, hvb2, hxb2, hres⟩ :=
        ih (hm1.trans hmem) hx₁_bdd hz1 ho1 hkb1 hxb1 hargU1 hcur1
      have he_tot : Exec w findInChain x y (7 + m₂ + 2) :=
        Exec.loop_iter (by simp [Cond.Holds, hz, hcur]) he1 he2
      refine ⟨y, ⟨7 + m₂ + 2, by simp; omega, he_tot⟩, hy_bdd, hmy,
        hbase2.trans hbase1, htag2.trans htag1, hargU2, hargV2.trans hargV1,
        hout2.trans hout1, hz2, ho2, hhb2.trans hhb1, hkb2, hvb2.trans hvb1, hxb2, ?_⟩
      rcases hres with ⟨i, hi, hki, hyf, hym⟩ | ⟨hmiss, hyf⟩
      · exact Or.inl ⟨i, List.mem_cons_of_mem _ hi, hki, hyf, hym⟩
      · refine Or.inr ⟨?_, hyf.trans hfnd1⟩
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact hhit
        · exact hmiss i hi'

private theorem IsChain.mono_congr {mem mem' : ℕ → ℕ} {nb sz sz' ptr : ℕ} {L : List ℕ}
    (hc : IsChain mem nb sz ptr L) (hsz : sz ≤ sz')
    (hmem : ∀ j < sz, mem' (nb + j) = mem (nb + j)) :
    IsChain mem' nb sz' ptr L := by
  induction hc with
  | nil => exact .nil
  | @cons idx nextPtr rest hidx hnext _ ih =>
    exact .cons (hidx.trans_le hsz) ((hmem idx hidx).trans hnext) ih

private theorem Rep.of_mem_eq {U V n_max w base : ℕ} {b : Fin (2 ^ (hashBits U n_max - 1))}
    {s : Dictionary.State U} {x z : Data rHash}
    (hr : Rep U V n_max w base b s x) (hz : z.Bounded w)
    (hbase : z.regs baseReg = base) (hmem : z.mem = x.mem) :
    Rep U V n_max w base b s z := by
  refine hr.supported (fun i hi => ?_) (fun a _ => by rw [hmem]) hz
  have : i = baseReg := Decidable.of_not_not (of_decide_eq_false hi)
  subst this
  exact hbase.trans hr.reg_base.symm

private theorem finishGet_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg = 0)
    (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (hvb : y.regs valBaseReg = valBase base n_max)
    (hres : (∃ i ∈ L, x.mem (keyBase base n_max + i) = u.val ∧
        y.regs found = 1 ∧ y.regs matchIdx = i) ∨
      ((∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = 0)) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b s z ∧
      @decode U V n_max (.get u) z.regs = some (s u) ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  have hsp : 4 + numBuckets n_max + 3 * n_max = space n_max := rfl
  have hsz_le : (Dictionary.dom s).card ≤ n_max := hr.card_le
  rcases hres with ⟨i, hi, hki, hyf, hym⟩ | ⟨hmiss, hyf⟩
  · have hi_lt : i < (Dictionary.dom s).card := hbL.chain.lt_sz i hi
    obtain ⟨u', hku', _, hsu'⟩ := hbL.sound i hi
    have hu'_eq : u = u' := Fin.ext (hki.symm.trans hku')
    subst hu'_eq
    let v := x.mem (valBase base n_max + i)
    have hv_lt : v < V := hr.vals_lt u v hsu'
    have fvaddr : Fits w (valBase base n_max + i) := hS.of_le (by unfold valBase; omega)
    have fv : Fits w (y.mem (valBase base n_max + i)) := hy_bdd.2 _
    have fv1 : Fits w (y.mem (valBase base n_max + i) + 1) := by
      rw [hmy]
      exact hV.of_le (by omega)
    obtain ⟨z, he, hmz, hbasez, houtz⟩ :
        ∃ z, Exec w finishOp y z 5 ∧ z.mem = y.mem ∧
          z.regs baseReg = base ∧ z.regs outReg = y.mem (valBase base n_max + i) + 1 := by
      refine ⟨?_, ?e, ?_, ?_, ?_⟩
      case e =>
        ram_exact_eval [finishOp, finishGet, htag, hz, ho, hyf, hvb, hym, fvaddr, fv, fv1]
      · rfl
      · simp +decide [hbase]
      · simp +decide
    have hmz' : z.mem = x.mem := hmz.trans hmy
    refine ⟨z, he.within.mono (by omega),
      hr.of_mem_eq (he.within.bounded hy_bdd) hbasez hmz',
      ?_, fun a _ => congrFun hmz' a⟩
    simp [decode, houtz, hmy, hsu', Dictionary.spec]
  · have hsu : s u = none := by
      cases h : s u with
      | none => rfl
      | some v =>
        obtain ⟨i, hi, hki⟩ := hbL.complete u v rfl h
        exact absurd hki (hmiss i hi)
    obtain ⟨z, he, hmz, hbasez, houtz⟩ :
        ∃ z, Exec w finishOp y z 4 ∧ z.mem = y.mem ∧
          z.regs baseReg = base ∧ z.regs outReg = 0 := by
      refine ⟨?_, ?e, ?_, ?_, ?_⟩
      case e =>
        ram_exact_eval [finishOp, finishGet, htag, hz, hyf]
      · rfl
      · simp +decide [hbase]
      · simp +decide
    have hmz' : z.mem = x.mem := hmz.trans hmy
    refine ⟨z, he.within.mono (by omega),
      hr.of_mem_eq (he.within.bounded hy_bdd) hbasez hmz',
      ?_, fun a _ => congrFun hmz' a⟩
    simp [decode, houtz, hsu, Dictionary.spec]

private theorem finishInsertHit_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {v : ℕ} (hv : (Dictionary.spec U V n_max).valid s (.insert u v))
    {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem
      (multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)) L)
    {i : ℕ} (hi : i ∈ L) (hki : x.mem (keyBase base n_max + i) = u.val)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg ≠ 0) (hargV : y.regs argV = v)
    (hz : y.regs zero = 0) (hvb : y.regs valBaseReg = valBase base n_max)
    (hyf : y.regs found = 1) (hym : y.regs matchIdx = i) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b (Function.update s u (some v)) z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let s' := Function.update s u (some v)
  have hsp : 4 + numBuckets n_max + 3 * n_max = space n_max := rfl
  let sz := (Dictionary.dom s).card
  have hsz_le : sz ≤ n_max := hr.card_le
  have hi_lt : i < sz := hbL.chain.lt_sz i hi
  obtain ⟨u₀, hku₀, _, hsu₀⟩ := hbL.sound i hi
  have hu₀_eq : u = u₀ := Fin.ext (hki.symm.trans hku₀)
  subst hu₀_eq
  have hisSome : (s u).isSome := by simp [hsu₀]
  have hcard_eq : (Dictionary.dom s').card = sz :=
    Dictionary.card_dom_insert_eq_of_isSome hisSome v
  have fvaddr : Fits w (valBase base n_max + i) := hS.of_le (by unfold valBase; omega)
  obtain ⟨z, he, hmz, hbasez⟩ :
      ∃ z, Exec w finishOp y z 5 ∧
        z.mem = Function.update y.mem (valBase base n_max + i) v ∧
        z.regs baseReg = base := by
    refine ⟨?_, ?e, ?_, ?_⟩
    case e =>
      ram_exact_eval [finishOp, finishInsert, finishInsertHit, htag, hz, hyf, hvb, hym, hargV,
        fvaddr]
    · rfl
    · simp +decide [hbase]
  rw [hmy] at hmz
  have hz_bdd : z.Bounded w := he.within.bounded hy_bdd
  have hne_val : ∀ a, a < valBase base n_max ∨ valBase base n_max + n_max ≤ a →
      z.mem a = x.mem a := by
    intro a ha
    rw [hmz, Function.update_of_ne (by unfold valBase at *; omega)]
  refine ⟨z, he.within.mono (by omega), ?_, ?_⟩
  · refine ⟨hz_bdd, hbasez,
      (hne_val base (Or.inl (by unfold valBase; omega))).trans hr.mem_seed,
      (hne_val (base + 1) (Or.inl (by unfold valBase; omega))).trans hr.mem_M,
      (hne_val (base + 2) (Or.inl (by unfold valBase; omega))).trans hr.mem_w0,
      (hne_val (base + 3) (Or.inl (by unfold valBase; omega))).trans
        (hr.mem_sz.trans hcard_eq.symm),
      hcard_eq ▸ hsz_le,
      Dictionary.valuesBounded_step_of_valid hr.vals_lt hv,
      fun bk' hbk' => ?_⟩
    obtain ⟨L', hbL'⟩ := hr.buckets bk' hbk'
    refine ⟨L', ?_⟩
    have hhead_eq : z.mem (headBase base + bk') = x.mem (headBase base + bk') :=
      hne_val _ (Or.inl (by unfold headBase valBase; omega))
    have hc_z : IsChain z.mem (nextBase base n_max) (Dictionary.dom s').card
        (z.mem (headBase base + bk')) L' := by
      rw [hcard_eq, hhead_eq]
      exact hbL'.chain.congr_mem (fun j hj =>
        hne_val _ (Or.inr (by unfold nextBase valBase; omega)))
    have hkey_eq : ∀ j ∈ L', z.mem (keyBase base n_max + j) = x.mem (keyBase base n_max + j) := by
      intro j hj
      have hj_lt : j < sz := hbL'.chain.lt_sz j hj
      exact hne_val _ (Or.inl (by unfold keyBase valBase; omega))
    have hnodup_z : (L'.map fun idx => z.mem (keyBase base n_max + idx)).Nodup := by
      rw [List.map_congr_left hkey_eq]
      exact hbL'.nodup
    refine ⟨hc_z, hnodup_z, fun j hj => ?_, fun u' v' hbk_u' hsv' => ?_⟩
    · obtain ⟨u', hku', hbk_u', hsu'⟩ := hbL'.sound j hj
      refine ⟨u', (hkey_eq j hj).trans hku', hbk_u', ?_⟩
      by_cases hji : j = i
      · subst hji
        have hu'_eq : u' = u := Fin.ext (hku'.symm.trans hki)
        subst hu'_eq
        simp [hmz]
      · have hu'_ne : u' ≠ u := by
          rintro rfl
          subst hbk_u'
          have hL_eq : L' = L := hbL'.chain.unique hbL.chain
          subst hL_eq
          exact hji (hbL.idx_eq_of_key_eq hj hi (hku'.trans hki.symm))
        rw [Function.update_of_ne hu'_ne, hmz, Function.update_of_ne (by omega)]
        exact hsu'
    · by_cases hu' : u' = u
      · subst hu'
        subst hbk_u'
        have hL_eq : L' = L := hbL'.chain.unique hbL.chain
        subst hL_eq
        exact ⟨i, hi, (hkey_eq i hi).trans hki⟩
      · rw [Function.update_of_ne hu'] at hsv'
        obtain ⟨j, hj, hkj⟩ := hbL'.complete u' v' hbk_u' hsv'
        exact ⟨j, hj, (hkey_eq j hj).trans hkj⟩
  · rw [Modifies.block_iff]
    intro a ha
    dsimp only [Block.Owns] at ha
    rw [hmz, Function.update_of_ne (by unfold valBase space at *; omega)]

private theorem finishInsertMiss_spec {U V n_max w base : ℕ}
    (hS : Fits w (base + space n_max))
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x y : Data rHash}
    (hr : Rep U V n_max w base b s x)
    {u : Fin U} {v : ℕ} {bk : ℕ}
    (hbk_def : bk = multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u))
    (hv : (Dictionary.spec U V n_max).valid s (.insert u v))
    {L : List ℕ}
    (hbL : BucketInv U n_max base b s x.mem bk L)
    (hmiss : ∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val)
    (hy_bdd : y.Bounded w) (hmy : y.mem = x.mem)
    (hbase : y.regs baseReg = base) (htag : y.regs tagReg ≠ 0)
    (hargU : y.regs argU = u.val) (hargV : y.regs argV = v)
    (hout : y.regs regOut = bk)
    (hz : y.regs zero = 0) (ho : y.regs one = 1)
    (hhb : y.regs headBaseReg = headBase base)
    (hkb : y.regs keyBaseReg = keyBase base n_max)
    (hvb : y.regs valBaseReg = valBase base n_max)
    (hxb : y.regs nextBaseReg = nextBase base n_max)
    (hyf : y.regs found = 0) :
    ∃ z, ExecWithin w finishOp y z 20 ∧
      Rep U V n_max w base b (Function.update s u (some v)) z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let s' := Function.update s u (some v)
  have hsp : 4 + numBuckets n_max + 3 * n_max = space n_max := rfl
  have hbk_lt : bk < numBuckets n_max := hbk_def ▸ multiplyShift_lt_numBuckets b u
  let sz := (Dictionary.dom s).card
  have hsu : s u = none := by
    cases h : s u with
    | none => rfl
    | some v₀ =>
      obtain ⟨i, hi, hki⟩ := hbL.complete u v₀ hbk_def.symm h
      exact absurd hki (hmiss i hi)
  have hsz_lt : sz < n_max := by
    rcases hv.1 with hlt | hisSome
    · exact hlt
    · simp [hsu] at hisSome
  have hcard_eq : (Dictionary.dom s').card = sz + 1 :=
    Dictionary.card_dom_insert_eq_of_eq_none hsu v
  have hmsz : y.mem (base + 3) = sz := hmy ▸ hr.mem_sz
  have f3 : Fits w 3 := hS.of_le (by omega)
  have fb3 : Fits w (base + 3) := hS.of_le (by omega)
  have fsz : Fits w sz := hS.of_le (by omega)
  have fsz1 : Fits w (sz + 1) := hS.of_le (by omega)
  have fkaddr : Fits w (keyBase base n_max + sz) := hS.of_le (by unfold keyBase; omega)
  have fvaddr : Fits w (valBase base n_max + sz) := hS.of_le (by unfold valBase; omega)
  have fhaddr : Fits w (headBase base + bk) := hS.of_le (by unfold headBase; omega)
  have fnaddr : Fits w (nextBase base n_max + sz) := hS.of_le (by unfold nextBase; omega)
  let m₁ := Function.update (Function.update (Function.update y.mem (base + 3) (sz + 1))
    (keyBase base n_max + sz) u.val) (valBase base n_max + sz) v
  have hne1 : headBase base + bk ≠ valBase base n_max + sz := by unfold headBase valBase; omega
  have hne2 : headBase base + bk ≠ keyBase base n_max + sz := by unfold headBase keyBase; omega
  have hne3 : headBase base + bk ≠ base + 3 := by unfold headBase; omega
  obtain ⟨z, he, hmz, hbasez⟩ :
      ∃ z, Exec w finishOp y z 19 ∧
        z.mem = Function.update (Function.update m₁
          (nextBase base n_max + sz) (y.mem (headBase base + bk)))
          (headBase base + bk) (sz + 1) ∧
        z.regs baseReg = base := by
    refine ⟨?_, ?e, ?_, ?_⟩
    case e =>
      ram_exact_eval [finishOp, finishInsert, finishInsertMiss,
        hbase, htag, hargU, hargV, hout, hz, ho, hhb, hkb, hvb, hxb, hyf,
        hmsz, hne1, hne2, hne3, f3, fb3, fsz, fsz1, fkaddr, fvaddr, fhaddr, fnaddr]
    · rfl
    · simp +decide [hbase]
  have hz_bdd : z.Bounded w := he.within.bounded hy_bdd
  have hz_hdr : z.mem base = b.val ∧ z.mem (base + 1) = bucketBits n_max ∧
      z.mem (base + 2) = hashBits U n_max ∧ z.mem (base + 3) = sz + 1 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmz, Function.update_of_ne (by unfold headBase; omega),
        Function.update_of_ne (by unfold nextBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase; omega),
        Function.update_of_ne (by unfold keyBase; omega),
        Function.update_of_ne (by omega), hmy, hr.mem_seed]
    · rw [hmz, Function.update_of_ne (by unfold headBase; omega),
        Function.update_of_ne (by unfold nextBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase; omega),
        Function.update_of_ne (by unfold keyBase; omega),
        Function.update_of_ne (by omega), hmy, hr.mem_M]
    · rw [hmz, Function.update_of_ne (by unfold headBase; omega),
        Function.update_of_ne (by unfold nextBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase; omega),
        Function.update_of_ne (by unfold keyBase; omega),
        Function.update_of_ne (by omega), hmy, hr.mem_w0]
    · rw [hmz, Function.update_of_ne (by unfold headBase; omega),
        Function.update_of_ne (by unfold nextBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase; omega),
        Function.update_of_ne (by unfold keyBase; omega),
        Function.update_self]
  have hz_head_eq : z.mem (headBase base + bk) = sz + 1 := by
    rw [hmz, Function.update_self]
  have hz_head_ne : ∀ bk' < numBuckets n_max, bk' ≠ bk →
      z.mem (headBase base + bk') = x.mem (headBase base + bk') := by
    intro bk' hbk' hne
    rw [hmz, Function.update_of_ne (by unfold headBase; omega),
      Function.update_of_ne (by unfold nextBase headBase; omega)]
    dsimp only [m₁]
    rw [Function.update_of_ne (by unfold valBase headBase; omega),
      Function.update_of_ne (by unfold keyBase headBase; omega),
      Function.update_of_ne (by unfold headBase; omega), hmy]
  have hz_slot_sz : z.mem (keyBase base n_max + sz) = u.val ∧
      z.mem (valBase base n_max + sz) = v ∧
      z.mem (nextBase base n_max + sz) = x.mem (headBase base + bk) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmz, Function.update_of_ne (by unfold headBase keyBase; omega),
        Function.update_of_ne (by unfold nextBase keyBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase keyBase; omega), Function.update_self]
    · rw [hmz, Function.update_of_ne (by unfold headBase valBase; omega),
        Function.update_of_ne (by unfold nextBase valBase; omega)]
      dsimp only [m₁]
      rw [Function.update_self]
    · rw [hmz, Function.update_of_ne (by unfold headBase nextBase; omega),
        Function.update_self, hmy]
  have hz_slot_lt : ∀ j < sz,
      z.mem (keyBase base n_max + j) = x.mem (keyBase base n_max + j) ∧
      z.mem (valBase base n_max + j) = x.mem (valBase base n_max + j) ∧
      z.mem (nextBase base n_max + j) = x.mem (nextBase base n_max + j) := by
    intro j hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hmz, Function.update_of_ne (by unfold headBase keyBase; omega),
        Function.update_of_ne (by unfold nextBase keyBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase keyBase; omega),
        Function.update_of_ne (by unfold keyBase; omega),
        Function.update_of_ne (by unfold keyBase; omega), hmy]
    · rw [hmz, Function.update_of_ne (by unfold headBase valBase; omega),
        Function.update_of_ne (by unfold nextBase valBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase; omega),
        Function.update_of_ne (by unfold keyBase valBase; omega),
        Function.update_of_ne (by unfold valBase; omega), hmy]
    · rw [hmz, Function.update_of_ne (by unfold headBase nextBase; omega),
        Function.update_of_ne (by unfold nextBase; omega)]
      dsimp only [m₁]
      rw [Function.update_of_ne (by unfold valBase nextBase; omega),
        Function.update_of_ne (by unfold keyBase nextBase; omega),
        Function.update_of_ne (by unfold nextBase; omega), hmy]
  refine ⟨z, he.within.mono (by omega), ?_, ?_⟩
  · refine ⟨hz_bdd, hbasez, hz_hdr.1, hz_hdr.2.1, hz_hdr.2.2.1,
      hz_hdr.2.2.2.trans hcard_eq.symm,
      by rw [hcard_eq]; omega,
      Dictionary.valuesBounded_step_of_valid hr.vals_lt hv,
      fun bk' hbk' => ?_⟩
    by_cases hbk_eq : bk = bk'
    · subst hbk_eq
      refine ⟨sz :: L, ?_⟩
      have hc_tail : IsChain z.mem (nextBase base n_max) (Dictionary.dom s').card
          (x.mem (headBase base + bk)) L :=
        hbL.chain.mono_congr (by rw [hcard_eq]; omega) (fun j hj => (hz_slot_lt j hj).2.2)
      have hc_cons : IsChain z.mem (nextBase base n_max) (Dictionary.dom s').card
          (z.mem (headBase base + bk)) (sz :: L) := by
        rw [hz_head_eq]
        exact .cons (by rw [hcard_eq]; omega) hz_slot_sz.2.2 hc_tail
      have hmap_tail : (L.map fun idx => z.mem (keyBase base n_max + idx)) =
          (L.map fun idx => x.mem (keyBase base n_max + idx)) :=
        List.map_congr_left (fun j hj => (hz_slot_lt j (hbL.chain.lt_sz j hj)).1)
      have hnodup : ((sz :: L).map fun idx => z.mem (keyBase base n_max + idx)).Nodup := by
        rw [List.map_cons, hz_slot_sz.1, hmap_tail, List.nodup_cons]
        refine ⟨?_, hbL.nodup⟩
        rw [List.mem_map]
        rintro ⟨j, hj, hkj⟩
        exact hmiss j hj hkj
      refine ⟨hc_cons, hnodup, fun j hj => ?_, fun u' v' hbk_u' hsv' => ?_⟩
      · rcases List.mem_cons.mp hj with rfl | hj'
        · refine ⟨u, hz_slot_sz.1, hbk_def.symm, ?_⟩
          simp [hz_slot_sz.2.1]
        · have hj_lt : j < sz := hbL.chain.lt_sz j hj'
          obtain ⟨u', hku', hbk_u', hsu'⟩ := hbL.sound j hj'
          have hu'_ne : u' ≠ u := by
            rintro rfl
            exact hmiss j hj' hku'
          refine ⟨u', (hz_slot_lt j hj_lt).1.trans hku', hbk_u', ?_⟩
          rw [Function.update_of_ne hu'_ne, (hz_slot_lt j hj_lt).2.1]
          exact hsu'
      · by_cases hu' : u' = u
        · subst hu'
          exact ⟨sz, List.mem_cons_self, hz_slot_sz.1⟩
        · rw [Function.update_of_ne hu'] at hsv'
          obtain ⟨j, hj, hkj⟩ := hbL.complete u' v' hbk_u' hsv'
          have hj_lt : j < sz := hbL.chain.lt_sz j hj
          exact ⟨j, List.mem_cons_of_mem _ hj, (hz_slot_lt j hj_lt).1.trans hkj⟩
    · obtain ⟨L', hbL'⟩ := hr.buckets bk' hbk'
      refine ⟨L', ?_⟩
      have hc_z : IsChain z.mem (nextBase base n_max) (Dictionary.dom s').card
          (z.mem (headBase base + bk')) L' := by
        rw [hz_head_ne bk' hbk' (Ne.symm hbk_eq)]
        exact hbL'.chain.mono_congr (by rw [hcard_eq]; omega) (fun j hj => (hz_slot_lt j hj).2.2)
      have hmap_L' : (L'.map fun idx => z.mem (keyBase base n_max + idx)) =
          (L'.map fun idx => x.mem (keyBase base n_max + idx)) :=
        List.map_congr_left (fun j hj => (hz_slot_lt j (hbL'.chain.lt_sz j hj)).1)
      have hnodup_z : (L'.map fun idx => z.mem (keyBase base n_max + idx)).Nodup := by
        rw [hmap_L']
        exact hbL'.nodup
      refine ⟨hc_z, hnodup_z, fun j hj => ?_, fun u' v' hbk_u' hsv' => ?_⟩
      · have hj_lt : j < sz := hbL'.chain.lt_sz j hj
        obtain ⟨u', hku', hbk_u', hsu'⟩ := hbL'.sound j hj
        have hu'_ne : u' ≠ u := by
          rintro rfl
          exact hbk_eq (hbk_def.trans hbk_u')
        refine ⟨u', (hz_slot_lt j hj_lt).1.trans hku', hbk_u', ?_⟩
        rw [Function.update_of_ne hu'_ne, (hz_slot_lt j hj_lt).2.1]
        exact hsu'
      · have hu'_ne : u' ≠ u := by
          rintro rfl
          exact hbk_eq (hbk_def.trans hbk_u')
        rw [Function.update_of_ne hu'_ne] at hsv'
        obtain ⟨j, hj, hkj⟩ := hbL'.complete u' v' hbk_u' hsv'
        have hj_lt : j < sz := hbL'.chain.lt_sz j hj
        exact ⟨j, hj, (hz_slot_lt j hj_lt).1.trans hkj⟩
  · rw [Modifies.block_iff]
    intro a ha
    dsimp only [Block.Owns] at ha
    rw [hmz, Function.update_of_ne (by unfold headBase space at *; omega),
      Function.update_of_ne (by unfold nextBase space at *; omega)]
    dsimp only [m₁]
    rw [Function.update_of_ne (by unfold valBase space at *; omega),
      Function.update_of_ne (by unfold keyBase space at *; omega),
      Function.update_of_ne (by unfold space at *; omega), hmy]

/-- Number of keys `u' ∈ (dom s).erase u` that collide with `u` under `multiplyShift w₀ M b`. -/
def collCount {U : ℕ} (n_max : ℕ) (s : Dictionary.State U) (u : Fin U)
    (b : Fin (2 ^ (hashBits U n_max - 1))) : ℕ :=
  (((Dictionary.dom s).erase u).filter fun u' =>
    multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u') =
      multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)).card

/-- Key queried or inserted by a dictionary operation `o : Dictionary.Op U`. -/
def opKey {U : ℕ} : Dictionary.Op U → Fin U
  | .get u => u
  | .insert u _ => u

/-- Deterministic execution of `opCode U n_max` for a fixed seed `b`: executes in at most
`55 + 9 * collCount n_max s (opKey o) b` instructions, preserves `Rep`, decodes the abstract
result, and modifies memory only within `[base, base + space n_max)`. -/
theorem opCode_spec {U V n_max w base : ℕ}
    (hw : 2 * hashBits U n_max ≤ w) (hS : Fits w (base + space n_max)) (hV : Fits w V)
    {b : Fin (2 ^ (hashBits U n_max - 1))} {s : Dictionary.State U} {x : Data rHash}
    (hr : Rep U V n_max w base b s x) (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatch o x.regs) :
    ∃ z, ExecWithin w (opCode U n_max) x z (55 + 9 * collCount n_max s (opKey o) b) ∧
      @decode U V n_max o z.regs = some ((Dictionary.spec U V n_max).step s o).2 ∧
      Rep U V n_max w base b ((Dictionary.spec U V n_max).step s o).1 z ∧
      Modifies (Block.mk base (space n_max)).footprint x.mem z.mem := by
  let u := opKey o
  have hu_reg : x.regs argU = u.val := by
    cases o with
    | get u => exact harg.2
    | insert u v => exact harg.2.1
  let bk := multiplyShift (hashBits U n_max) (bucketBits n_max) b (encodeKey u)
  have hbk_lt : bk < numBuckets n_max := multiplyShift_lt_numBuckets b u
  obtain ⟨L, hbL⟩ := hr.buckets bk hbk_lt
  have hL_le : L.length ≤ 1 + collCount n_max s u b := hbL.length_le u
  obtain ⟨x₁, he1, hx₁_bdd, hmx₁, hbase1, htag1, hargU1, hargV1, hout1,
      hz1, ho1, hhb1, hkb1, hvb1, hxb1, hcur1, hfnd1⟩ :=
    evalBucket_spec hw hS hr hu_reg
  obtain ⟨y, he2, hy_bdd, hmy, hbase2, htag2, hargU2, hargV2, hout2,
      hz2, ho2, hhb2, hkb2, hvb2, hxb2, hres⟩ :=
    findInChain_spec hS hr.card_le hbL.chain hmx₁ hx₁_bdd hz1 ho1 hkb1 hxb1 hargU1 hcur1
  have hres' :
      (∃ i ∈ L, x.mem (keyBase base n_max + i) = u.val ∧ y.regs found = 1 ∧ y.regs matchIdx = i) ∨
        ((∀ i ∈ L, x.mem (keyBase base n_max + i) ≠ u.val) ∧ y.regs found = 0) := by
    rcases hres with hhit | ⟨hmiss, hyf⟩
    · exact Or.inl hhit
    · exact Or.inr ⟨hmiss, hyf.trans hfnd1⟩
  cases o with
  | get u₀ =>
    have hu_eq : u = u₀ := rfl
    have htag_y : y.regs tagReg = 0 := htag2.trans (htag1.trans harg.1)
    obtain ⟨z, he3, hrep_z, hdec_z, hmod_z⟩ :=
      finishGet_spec hS hV hr hbL hy_bdd hmy (hbase2.trans hbase1) htag_y hz2 ho2
        (hvb2.trans hvb1) hres'
    have he_tot : ExecWithin w (opCode U n_max) x z (24 + (9 * L.length + 2 + 20)) :=
      he1.within.seq (he2.seq he3)
    refine ⟨z, he_tot.mono ?_, hdec_z, hrep_z, hmod_z⟩
    change 24 + (9 * L.length + 2 + 20) ≤ 55 + 9 * collCount n_max s u b
    omega
  | insert u₀ v =>
    have hu_eq : u = u₀ := rfl
    have htag_y : y.regs tagReg ≠ 0 := by
      rw [htag2, htag1]
      exact harg.1
    have hargV_y : y.regs argV = v := hargV2.trans (hargV1.trans harg.2.2)
    rcases hres' with ⟨i, hi, hki, hyf, hym⟩ | ⟨hmiss, hyf⟩
    · obtain ⟨z, he3, hrep_z, hmod_z⟩ :=
        finishInsertHit_spec hS hr hv hbL hi hki hy_bdd hmy (hbase2.trans hbase1) htag_y hargV_y
          hz2 (hvb2.trans hvb1) hyf hym
      have he_tot : ExecWithin w (opCode U n_max) x z (24 + (9 * L.length + 2 + 20)) :=
        he1.within.seq (he2.seq he3)
      refine ⟨z, he_tot.mono ?_, rfl, hrep_z, hmod_z⟩
      change 24 + (9 * L.length + 2 + 20) ≤ 55 + 9 * collCount n_max s u b
      omega
    · obtain ⟨z, he3, hrep_z, hmod_z⟩ :=
        finishInsertMiss_spec hS hr rfl hv hbL hmiss hy_bdd hmy (hbase2.trans hbase1) htag_y
          hargU2 hargV_y (hout2.trans hout1) hz2 ho2 (hhb2.trans hhb1) hkb2 (hvb2.trans hvb1)
          hxb2 hyf
      have he_tot : ExecWithin w (opCode U n_max) x z (24 + (9 * L.length + 2 + 20)) :=
        he1.within.seq (he2.seq he3)
      refine ⟨z, he_tot.mono ?_, rfl, hrep_z, hmod_z⟩
      change 24 + (9 * L.length + 2 + 20) ≤ 55 + 9 * collCount n_max s u b
      omega

/-! ## 6. Expected collision bounds and `SubroutineDS` certificate -/

/-- By linearity of expectation and `(2 / 2 ^ M)`-universality of multiply-shift hashing
(`isUniversalHash_multiplyShift`), the expected number of keys in `(dom s).erase u` colliding with
`u` under a uniform seed `b ∈ Fin (2 ^ (hashBits U n_max - 1))` is at most
`((dom s).erase u).card * (2 / 2 ^ bucketBits n_max)`. -/
theorem expect_collCount_le_card_mul (U n_max : ℕ) (s : Dictionary.State U) (u : Fin U) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    (∑' b : Seed, seedLaw b * (collCount n_max s u b : ℝ≥0∞)) ≤
      (((Dictionary.dom s).erase u).card : ℝ≥0∞) * (2 / 2 ^ bucketBits n_max) := by
  classical
  let w₀ := hashBits U n_max
  let M := bucketBits n_max
  let Seed := Fin (2 ^ (w₀ - 1))
  let seedLaw := PMF.uniformOfFintype Seed
  let S := (Dictionary.dom s).erase u
  have huniv : IsUniversalHash seedLaw
      (fun (b : Seed) (u' : Fin U) => multiplyShift w₀ M b (encodeKey u')) (2 / 2 ^ M) :=
    (isUniversalHash_multiplyShift (hashBits_pos U n_max)
      (bucketBits_le_hashBits U n_max)).precompose (encodeKey_injective U n_max)
  have hpoint : ∀ b : Seed,
      seedLaw b * (collCount n_max s u b : ℝ≥0∞) =
        ∑ u' ∈ S,
          {b' : Seed | multiplyShift w₀ M b' (encodeKey u') =
            multiplyShift w₀ M b' (encodeKey u)}.indicator seedLaw b := by
    intro b
    change seedLaw b *
        (((S.filter fun u' =>
          multiplyShift w₀ M b (encodeKey u') = multiplyShift w₀ M b (encodeKey u)).card : ℕ) :
            ℝ≥0∞) = _
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u' _ => ?_
    by_cases h : multiplyShift w₀ M b (encodeKey u') = multiplyShift w₀ M b (encodeKey u)
    · rw [Set.indicator_of_mem h]
      simp [h]
    · rw [Set.indicator_of_notMem h]
      simp [h]
  calc
    (∑' b : Seed, seedLaw b * (collCount n_max s u b : ℝ≥0∞))
      = ∑' b : Seed, ∑ u' ∈ S,
          {b' : Seed | multiplyShift w₀ M b' (encodeKey u') =
            multiplyShift w₀ M b' (encodeKey u)}.indicator seedLaw b :=
        tsum_congr hpoint
    _ = ∑ u' ∈ S, ∑' b : Seed,
          {b' : Seed | multiplyShift w₀ M b' (encodeKey u') =
            multiplyShift w₀ M b' (encodeKey u)}.indicator seedLaw b := by
        rw [tsum_fintype, Finset.sum_comm]
        exact Finset.sum_congr rfl fun u' _ => (tsum_fintype _).symm
    _ = ∑ u' ∈ S,
          seedLaw.toOuterMeasure {b' : Seed | multiplyShift w₀ M b' (encodeKey u') =
            multiplyShift w₀ M b' (encodeKey u)} := by
        refine Finset.sum_congr rfl fun u' _ => ?_
        rw [PMF.toOuterMeasure_apply]
    _ ≤ ∑ _u' ∈ S, (2 / (2 : ℝ≥0∞) ^ M) := by
        refine Finset.sum_le_sum fun u' hu' => ?_
        exact huniv u' u (Finset.mem_erase.mp hu').1
    _ = (S.card : ℝ≥0∞) * (2 / 2 ^ M) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- When `(dom s).card ≤ n_max`, the expected collision count is at most `2`. -/
theorem expect_collCount_le_two {U n_max : ℕ} {s : Dictionary.State U}
    (hcard : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    (∑' b : Seed, seedLaw b * (collCount n_max s u b : ℝ≥0∞)) ≤ 2 := by
  have hcard_erase : ((Dictionary.dom s).erase u).card ≤ numBuckets n_max :=
    (Finset.card_erase_le.trans hcard).trans (le_numBuckets n_max)
  have hcast : (((Dictionary.dom s).erase u).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ bucketBits n_max := by
    exact_mod_cast hcard_erase
  have hpow_ne_zero : (2 : ℝ≥0∞) ^ bucketBits n_max ≠ 0 := by positivity
  have hpow_ne_top : (2 : ℝ≥0∞) ^ bucketBits n_max ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  calc
    (∑' b : Fin (2 ^ (hashBits U n_max - 1)),
        PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1))) b *
          (collCount n_max s u b : ℝ≥0∞))
      ≤ (((Dictionary.dom s).erase u).card : ℝ≥0∞) * (2 / 2 ^ bucketBits n_max) :=
        expect_collCount_le_card_mul U n_max s u
    _ ≤ (2 : ℝ≥0∞) ^ bucketBits n_max * (2 / 2 ^ bucketBits n_max) := by
        gcongr
    _ = 2 := by
        rw [div_eq_mul_inv, mul_comm (2 : ℝ≥0∞), ← mul_assoc,
          ENNReal.mul_inv_cancel hpow_ne_zero hpow_ne_top, one_mul]

/-- Worst-case expected instruction charge per dictionary operation (`55 + 9 * 2 = 73`). -/
def chargeVal : ℕ := 73

/-- Constant `O(1)` expected instruction charge for `Dictionary.spec U V n_max`. -/
def charge (U V n_max : ℕ) :
    (Dictionary.spec U V n_max).State → (Dictionary.spec U V n_max).Op → ℕ :=
  fun _ _ => chargeVal

/-- **Chained hash table `SubroutineDS` certificate over `Basis.exact`.**
Realizes `Dictionary.spec U V n_max` in `space n_max = 4 + 2 ^ M + 3 * n_max = O(n_max)` words of
memory, `O(1)` (`16`-instruction) initialization on zeroed memory (`O(n_max)` via `initClear` on
dirty memory), and `chargeVal = 73 = O(1)` worst-case expected instructions per `get` or `insert`
operation with zero potential (`potential = 0`). -/
noncomputable def subroutineDS (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V) :
    Randomized.SubroutineDS (subroutineCode U n_max) (Dictionary.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) where
  Seed := Fin (2 ^ (hashBits U n_max - 1))
  seedLaw := PMF.uniformOfFintype (Fin (2 ^ (hashBits U n_max - 1)))
  seedSlack := 1
  space := space n_max
  spanTime := 3
  setupTime := 13
  initPotential := 0
  charge := charge U V n_max
  rep := Rep U V n_max w base
  potential := fun _ _ => 0
  encode := encode
  argMatch := argMatch
  decode := decode
  bounded hr := hr.bounded
  rep_unique hr₁ hr₂ := hr₁.unique hr₂
  arguments_fit o hv i _ := arguments_fit hw hS hV o hv i
  encode_matches := encode_matches
  rep_supported hreg hmem hbx hr := hr.supported hreg hmem hbx
  potential_supported _ _ _ := rfl
  clear_nodup := by dsimp [subroutineCode]; decide
  params_not_clear j := Fin.elim0 j
  incCur_eval {x} hone hfit := by
    change Data.put w x regT1 (x.regs regT1 + x.regs one) =
      some (x.set (subroutineCode U n_max).curReg (x.regs (subroutineCode U n_max).curReg + 1))
    change x.regs one = 1 at hone
    rw [hone]
    exact Data.put_of_fits hfit
  span_exec {x} _ hfr _ := by
    obtain ⟨x₁, he, hm, hb, hf⟩ := allocSpan_spec hS hfr
    exact ⟨x₁, he, hm, hb, hf, fun j => Fin.elim0 j⟩
  setup_exec {x₁} hx₁ hbase hfr _ hz := by
    obtain ⟨ν₀, he, hseed, hsupp⟩ := initSetup_spec (V := V) hw hS hx₁ hbase hfr hz
    exact ⟨ν₀, he, hseed, fun p hp =>
      ⟨(hsupp p hp).1, (hsupp p hp).2.1, le_rfl, (hsupp p hp).2.2⟩⟩
  step_exec {s} o ν hv hseed hsupp := by
    classical
    let Seed := Fin (2 ^ (hashBits U n_max - 1))
    let seedLaw := PMF.uniformOfFintype Seed
    have hstep_ex : ∀ p : Seed × Data rHash,
        ∃ z : Data rHash,
          (p ∈ ν.support →
            ExecWithin w (opCode U n_max) p.2 z (55 + 9 * collCount n_max s (opKey o) p.1) ∧
            @decode U V n_max o z.regs = some ((Dictionary.spec U V n_max).step s o).2 ∧
            Rep U V n_max w base p.1 ((Dictionary.spec U V n_max).step s o).1 z ∧
            Modifies (Block.mk base (space n_max)).footprint p.2.mem z.mem) := by
      intro p
      by_cases hp : p ∈ ν.support
      · obtain ⟨hr, harg⟩ := hsupp p hp
        obtain ⟨z, he, hdec, hrep, hmod⟩ := opCode_spec hw hS hV hr o hv harg
        exact ⟨z, fun _ => ⟨he, hdec, hrep, hmod⟩⟩
      · exact ⟨p.2, fun h => absurd h hp⟩
    let z_of : Seed × Data rHash → Data rHash := fun p => Classical.choose (hstep_ex p)
    have hz_spec : ∀ p ∈ ν.support,
        ExecWithin w (opCode U n_max) p.2 (z_of p) (55 + 9 * collCount n_max s (opKey o) p.1) ∧
        @decode U V n_max o (z_of p).regs = some ((Dictionary.spec U V n_max).step s o).2 ∧
        Rep U V n_max w base p.1 ((Dictionary.spec U V n_max).step s o).1 (z_of p) ∧
        Modifies (Block.mk base (space n_max)).footprint p.2.mem (z_of p).mem :=
      fun p hp => (Classical.choose_spec (hstep_ex p)) hp
    let μ_step : Seed × Data rHash → PMF (Seed × Data rHash) :=
      fun p => PMF.pure (p.1, z_of p)
    let T_step : Seed × Data rHash → ℝ≥0∞ :=
      fun p => ((55 + 9 * collCount n_max s (opKey o) p.1 : ℕ) : ℝ≥0∞)
    refine ⟨μ_step, T_step, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨he, hdec, hrep, hmod⟩ := hz_spec p hp
      refine ⟨?_, ?_⟩
      · dsimp only [μ_step, T_step]
        rw [PMF.pure_map]
        exact ExecCodeDist.of_execWithin he
      · intro q hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        exact ⟨hdec, hrep, hmod⟩
    · intro θ'
      have hmap : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
        rw [PMF.map_bind]
        simp only [μ_step, PMF.pure_map]
        rfl
      rw [hmap]
      exact hseed θ'
    · simp only [Nat.cast_zero, mul_zero, tsum_zero, add_zero]
      by_cases hsupp_nonempty : ∃ p₀, p₀ ∈ ν.support
      · obtain ⟨p₀, hp₀⟩ := hsupp_nonempty
        have hcard_le : (Dictionary.dom s).card ≤ n_max := (hsupp p₀ hp₀).1.card_le
        have hfactor : ∀ p : Seed × Data rHash,
            ν p * T_step p =
              ν p * 55 + 9 * (ν p * (collCount n_max s (opKey o) p.1 : ℝ≥0∞)) := by
          intro p
          dsimp only [T_step]
          push_cast
          ring
        have hsum_split :
            (∑' p, ν p * T_step p) =
              55 + 9 * ∑' p, ν p * (collCount n_max s (opKey o) p.1 : ℝ≥0∞) := by
          simp_rw [hfactor]
          rw [tsum_add, ENNReal.tsum_mul_right, ν.tsum_coe, one_mul,
            ENNReal.tsum_mul_left]
        have hcoll_fst :
            (∑' p : Seed × Data rHash, ν p * (collCount n_max s (opKey o) p.1 : ℝ≥0∞)) =
              ∑' b : Seed, (ν.map Prod.fst) b * (collCount n_max s (opKey o) b : ℝ≥0∞) :=
          (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
            (fun b => (collCount n_max s (opKey o) b : ℝ≥0∞))).symm
        have hcoll_le :
            (∑' b : Seed, (ν.map Prod.fst) b * (collCount n_max s (opKey o) b : ℝ≥0∞)) ≤
              ∑' b : Seed, seedLaw b * (collCount n_max s (opKey o) b : ℝ≥0∞) := by
          refine tsum_le_tsum fun b => ?_
          have hb := hseed b
          rw [one_mul] at hb
          gcongr
        have hexp_two :
            (∑' b : Seed, seedLaw b * (collCount n_max s (opKey o) b : ℝ≥0∞)) ≤ 2 :=
          expect_collCount_le_two hcard_le (opKey o)
        calc
          (∑' p, ν p * T_step p)
            = 55 + 9 * ∑' p, ν p * (collCount n_max s (opKey o) p.1 : ℝ≥0∞) := hsum_split
          _ ≤ 55 + 9 * (2 : ℝ≥0∞) := by
              rw [hcoll_fst]
              gcongr
              exact hcoll_le.trans hexp_two
          _ = (charge U V n_max s o : ℝ≥0∞) := by
              dsimp [charge, chargeVal]
              norm_num
      · obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
        exact absurd ⟨p₀, hp₀⟩ hsupp_nonempty

/-- **Chained hash table `SubroutineDS` certificate over `Basis.standard`.**
Obtained from `subroutineDS` by basis transport (`SubroutineDS.toStandard`). -/
noncomputable def subroutineDSStandard (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V) :
    Randomized.SubroutineDS (subroutineCode U n_max).toStandard (Dictionary.spec U V n_max)
      w base Fin.elim0 (Dictionary.empty U) :=
  (subroutineDS U V n_max w base hw hS hV).toStandard

/-- **Expected subroutine body time across an oblivious operation sequence
(`seq_expected_amortized`).**
For fixed `U`, `n_max` and admissible word width `w`, `subroutineCode U n_max` uses precomputed
configuration literals (`initParams = Fin.elim0`). For a valid operation history
`ops : List (Dictionary.Op U)` fixed independently of the sampled seed (oblivious adversary),
running `initFresh` (`16` body instructions on zeroed `[base, base + space n_max)`) and
`C.ExecSteps` across `ops` (which receives each operation's prepared arguments and charges
subroutine operation bodies rather than a complete client/dispatch driver or configuration
construction) has total expected body cost `16 + T_ops ≤ 16 + 73 * ops.length`. -/
theorem seq_expected_amortized (U V n_max w base : ℕ)
    (hw : 2 * hashBits U n_max ≤ w)
    (hS : Fits w (base + space n_max))
    (hV : Fits w V)
    {x : Data rHash} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs frontierReg = base)
    (hz : ∀ a ∈ (Block.mk base (space n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := subroutineDS U V n_max w base hw hS hV
    ∃ (ν₀ ν_final : PMF (C.Seed × Data rHash)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (subroutineCode U n_max).initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecSteps (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ C.seedSlack * C.seedLaw θ) ∧
      (∀ p ∈ ν_final.support,
        C.rep p.1 ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      C.initTime + T_ops ≤ 16 + (chargeVal * ops.length : ℕ) := by
  intro C
  obtain ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, hbound⟩ :=
    C.seq_expected_amortized ops hx hfr (fun j => Fin.elim0 j) hz hv
  have htotal : (Dictionary.spec U V n_max).totalCost C.charge (Dictionary.empty U) ops =
      chargeVal * ops.length := by
    have hconst : ∀ s (os : List (Dictionary.Op U)),
        (Dictionary.spec U V n_max).totalCost (charge U V n_max) s os = chargeVal * os.length := by
      intro s os
      induction os generalizing s with
      | nil => rfl
      | cons o rest ih =>
        change chargeVal +
          (Dictionary.spec U V n_max).totalCost (charge U V n_max)
            ((Dictionary.spec U V n_max).step s o).1 rest = chargeVal * (rest.length + 1)
        rw [ih]
        ring
    exact hconst (Dictionary.empty U) ops
  refine ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final, ?_⟩
  have hpot0 : (∑' q, ν_final q * (C.potential q.1 q.2 : ℝ≥0∞)) = 0 := by
    change (∑' q : C.Seed × Data rHash, ν_final q * ((0 : ℕ) : ℝ≥0∞)) = 0
    simp
  have hinit : C.initTime = 16 := by
    change (3 : ℝ≥0∞) + 13 = 16
    norm_num
  have hinitPot : (C.initPotential : ℝ≥0∞) = 0 := by
    change ((0 : ℕ) : ℝ≥0∞) = 0
    exact Nat.cast_zero
  rw [hpot0, add_zero, hinitPot, add_zero, htotal] at hbound
  exact hbound.trans_eq (by rw [hinit])

end Cslib.Algorithms.WordRAM.Dictionary.ChainedHash
