/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.SuccinctBucket
public import Complexity.DataStructure.Dictionary.WordRAM.BitPackedArray
public import Complexity.DataStructure.HashFamily.WordRAM.Basic
public import Complexity.DataStructure.HashFamily.WordRAM.KWise

/-!
# Bit-Packed Memory Layout and Slab/Tail Slot Store for Succinct Dictionaries

This module implements the word-level memory layout and primitive read/write wrappers for the
fixed-capacity succinct dynamic dictionary, together with the full-slab and tail-item slot
allocator (`SlotStoreInv`).

## Memory layout (`[base, base + totalSpace)`)

1. `[base, base + h_space)`: Seeded hash family `QuotientHashImpl` mapping quotients in
   `Fin (2 ^ quotientBits U n_max)` to micro-bucket hashes in `Fin (2 ^ totalMicroBits n_max)`.
2. `Quotients`: `packedWords n_max (quotientBits U n_max) w` words storing `n_max` quotients of
   `quotientBits U n_max` bits (`offQuot`).
3. `Values`: `packedWords n_max (valBits V) w` words storing `n_max` values of `valBits V` bits
   (`offVal`).
4. `LocalMeta`: `packedWords (localMetaLen n_max) (effBucketPosBits n_max) w` words storing
   per-bucket micro-bucket heads and doubly-linked list `next`/`prev` pointers (`offLM`).
5. `GlobalMeta`: `packedWords (globalMetaLen n_max) (globalPtrBits n_max) w` words storing global
   counts, per-bucket slab/tail counts, direct slab directories, tail pointers, tail back-pointers,
   and the logical/physical slab pool bijection (`offGM`).
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: `QuotientHashImpl`, array offsets, and extraction functions -/

/-- A Word-RAM hash family implementation mapping quotients in `Fin (2 ^ quotientBits U n_max)` to
`Fin (2 ^ totalMicroBits n_max)`, using register `0` as base register, register `1` as key
register, and register `2` as output register, with expected `probeExcess` bounded by `C_probe` on
every active set `S` of size at most `n_max`. -/
structure QuotientHashImpl (r_hash : ℕ) [NeZero r_hash] (w base U n_max : ℕ) : Type 1 where
  /-- Underlying Word-RAM hash family implementation on quotients. -/
  impl : Impl .exact r_hash 0 w base (2 ^ quotientBits U n_max) (2 ^ totalMicroBits n_max) Fin.elim0
  /-- Register `0` is the base address register. -/
  hbase : impl.baseReg.val = 0
  /-- Register `1` is the input quotient register. -/
  hkey : impl.keyReg.val = 1
  /-- Register `2` is the output hash register. -/
  hout : impl.outReg.val = 2
  /-- `tableRep` depends only on memory inside `[base, base + impl.space)`. -/
  tableRep_congr : ∀ {mem₁ mem₂ : ℕ → ℕ},
    (∀ a, base ≤ a → a < base + impl.space → mem₁ a = mem₂ a) →
    impl.tableRep mem₁ → impl.tableRep mem₂
  /-- `seedRep` depends only on memory inside `[base, base + impl.space)`. -/
  seedRep_congr : ∀ (s : impl.Seed) {mem₁ mem₂ : ℕ → ℕ},
    (∀ a, base ≤ a → a < base + impl.space → mem₁ a = mem₂ a) →
    impl.seedRep s mem₁ → impl.seedRep s mem₂
  /-- Expected `probeExcess` constant (`3` for exact 9-wise hashing, `4` for two-stage
  universe-reduced 9-wise hashing). -/
  C_probe : ℕ
  /-- For every active set `S` of size at most `n_max` and every query key `u : Fin U`, the sum of
  `probeExcess` over all seeds `s : impl.Seed` is at most `C_probe * Fintype.card impl.Seed`. -/
  sum_probeExcess_le : ∀ (S : Finset (Fin U)), S.card ≤ n_max → ∀ u : Fin U,
    (∑ s : impl.Seed, probeExcess n_max (quotientFin U n_max) impl.eval s S u) ≤
      C_probe * Fintype.card impl.Seed

/-- Word offset of `Quotients` relative to `base`. -/
@[expose]
def offQuot (h_space : ℕ) : ℕ :=
  h_space

/-- Word offset of `Values` relative to `base`. -/
@[expose]
def offVal (U w n_max h_space : ℕ) : ℕ :=
  offQuot h_space + packedWords n_max (quotientBits U n_max) w

/-- Word offset of `LocalMeta` relative to `base`. -/
@[expose]
def offLM (U V w n_max h_space : ℕ) : ℕ :=
  offVal U w n_max h_space + packedWords n_max (valBits V) w

/-- Word size of each of the 9 `LocalMeta` sub-arrays of length `totalMicroBuckets n_max`. -/
@[expose]
def lmSubWords (n_max w : ℕ) : ℕ :=
  packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w

/-- Word offset of the `c`-th `LocalMeta` sub-array (`c < 9`) relative to `base`. -/
@[expose]
def offLMSub (U V w n_max h_space c : ℕ) : ℕ :=
  offLM U V w n_max h_space + c * lmSubWords n_max w

/-- Word offset of `GlobalMeta` relative to `base`. -/
@[expose]
def offGM (U V w n_max h_space : ℕ) : ℕ :=
  offLM U V w n_max h_space + 9 * lmSubWords n_max w

/-- Total word footprint of the succinct dictionary block starting at `base`. -/
@[expose]
def totalSpace (U V w n_max h_space : ℕ) : ℕ :=
  offGM U V w n_max h_space + packedWords (globalMetaLen n_max) (globalPtrBits n_max) w

/-- `totalSpace` is bounded by `Dynamic.succinctWords 79 (35 + h_space) U V w n_max` for all `w`
whenever `n_max ≤ U`. -/
theorem totalSpace_le_succinctWords {U V w n_max h_space : ℕ} (hnU : n_max ≤ U) :
    totalSpace U V w n_max h_space ≤
      Dynamic.succinctWords 79 (35 + h_space) U V w n_max := by
  have h := tableArrays_words_le_succinctWords (U := U) (V := V) (w := w) (n_max := n_max)
    (C_hdr := h_space) hnU
  unfold totalSpace offGM offLM offVal offQuot lmSubWords
  omega

/-- Pure extraction function for `Quotients[idx]` (`0` for `idx ≥ n_max`). -/
@[expose]
def quotAt (base U w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < n_max then
    readPacked (base + offQuot h_space) (quotientBits U n_max) w mem idx
  else 0

/-- Pure extraction function for `Values[idx]` (`0` for `idx ≥ n_max`). -/
@[expose]
def valAt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < n_max then
    readPacked (base + offVal U w n_max h_space) (valBits V) w mem idx
  else 0

/-- Pure extraction function for `LocalMeta` sub-array `p.1 < 9` at index
`p.2 < totalMicroBuckets n_max` (`0` out of bounds). -/
@[expose]
def lmAt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 < 9 ∧ p.2 < totalMicroBuckets n_max then
    readPacked (base + offLMSub U V w n_max h_space p.1) (effBucketPosBits n_max) w mem p.2
  else 0

/-- Pure extraction function for `GlobalMeta[idx]` (`0` for `idx ≥ globalMetaLen n_max`). -/
@[expose]
def gmAt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < globalMetaLen n_max then
    readPacked (base + offGM U V w n_max h_space) (globalPtrBits n_max) w mem idx
  else 0

/-- Value range invariant for `quotAt`: every entry is `< 2 ^ quotientBits U n_max`. -/
theorem quotAt_lt (base U w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    quotAt base U w n_max h_space mem idx < 2 ^ quotientBits U n_max := by
  unfold quotAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `valAt`: every entry is `< 2 ^ valBits V`. -/
theorem valAt_lt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    valAt base U V w n_max h_space mem idx < 2 ^ valBits V := by
  unfold valAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `lmAt`: every entry is `< 2 ^ effBucketPosBits n_max`. -/
theorem lmAt_lt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) :
    lmAt base U V w n_max h_space mem p < 2 ^ effBucketPosBits n_max := by
  unfold lmAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- Value range invariant for `gmAt`: every entry is `< 2 ^ globalPtrBits n_max`. -/
theorem gmAt_lt (base U V w n_max h_space : ℕ) (mem : ℕ → ℕ) (idx : ℕ) :
    gmAt base U V w n_max h_space mem idx < 2 ^ globalPtrBits n_max := by
  unfold gmAt
  split_ifs
  · exact readPacked_lt _ _ _ _ _
  · positivity

/-- On zero-initialized table memory `[base + h_space, base + totalSpace)`, `quotAt` is identically
zero. -/
theorem quotAt_zero_of_init {base U V w n_max h_space : ℕ} (hw : 0 < w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space → mem a = 0) :
    quotAt base U w n_max h_space mem = fun _ => 0 := by
  funext idx
  unfold quotAt
  split_ifs with hidx
  · have hlt1 : wordOffset (quotientBits U n_max) w idx + 1 <
        packedWords n_max (quotientBits U n_max) w :=
      wordOffset_add_one_lt_packedWords hw hidx
    exact readPacked_zero
      (hzero _ (by unfold offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
      (hzero _ (by unfold offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
  · rfl

/-- On zero-initialized table memory `[base + h_space, base + totalSpace)`, `valAt` is identically
zero. -/
theorem valAt_zero_of_init {base U V w n_max h_space : ℕ} (hw : 0 < w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space → mem a = 0) :
    valAt base U V w n_max h_space mem = fun _ => 0 := by
  funext idx
  unfold valAt
  split_ifs with hidx
  · have hlt1 : wordOffset (valBits V) w idx + 1 < packedWords n_max (valBits V) w :=
      wordOffset_add_one_lt_packedWords hw hidx
    exact readPacked_zero
      (hzero _ (by unfold offVal offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
      (hzero _ (by unfold offVal offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
  · rfl

/-- On zero-initialized table memory `[base + h_space, base + totalSpace)`, `lmAt` is identically
zero. -/
theorem lmAt_zero_of_init {base U V w n_max h_space : ℕ} (hw : 0 < w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space → mem a = 0) :
    lmAt base U V w n_max h_space mem = fun _ => 0 := by
  funext ⟨c, idx⟩
  unfold lmAt
  dsimp only
  split_ifs with hp
  · rcases hp with ⟨hc, hidx⟩
    have hlt1 : wordOffset (effBucketPosBits n_max) w idx + 1 < lmSubWords n_max w :=
      wordOffset_add_one_lt_packedWords hw hidx
    have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
      Nat.mul_le_mul_right _ hc
    rw [Nat.add_one_mul] at hsub
    exact readPacked_zero
      (hzero _ (by unfold offLMSub offLM offVal offQuot; omega)
        (by unfold totalSpace offGM offLMSub offLM offVal offQuot; omega))
      (hzero _ (by unfold offLMSub offLM offVal offQuot; omega)
        (by unfold totalSpace offGM offLMSub offLM offVal offQuot; omega))
  · rfl

/-- On zero-initialized table memory `[base + h_space, base + totalSpace)`, `gmAt` is identically
zero. -/
theorem gmAt_zero_of_init {base U V w n_max h_space : ℕ} (hw : 0 < w) {mem : ℕ → ℕ}
    (hzero : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space → mem a = 0) :
    gmAt base U V w n_max h_space mem = fun _ => 0 := by
  funext idx
  unfold gmAt
  split_ifs with hidx
  · have hlt1 : wordOffset (globalPtrBits n_max) w idx + 1 <
        packedWords (globalMetaLen n_max) (globalPtrBits n_max) w :=
      wordOffset_add_one_lt_packedWords hw hidx
    exact readPacked_zero
      (hzero _ (by unfold offGM offLM offVal offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
      (hzero _ (by unfold offGM offLM offVal offQuot; omega)
        (by unfold totalSpace offGM offLM offVal offQuot; omega))
  · rfl

/-- If two memories agree on `[base + h_space, base + totalSpace)`, they have identical `quotAt`,
`valAt`, `lmAt`, and `gmAt`. -/
theorem arrays_congr_of_eq_on {base U V w n_max h_space : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a, base + h_space ≤ a → a < base + totalSpace U V w n_max h_space →
      mem₁ a = mem₂ a) :
    quotAt base U w n_max h_space mem₁ = quotAt base U w n_max h_space mem₂ ∧
      valAt base U V w n_max h_space mem₁ = valAt base U V w n_max h_space mem₂ ∧
      lmAt base U V w n_max h_space mem₁ = lmAt base U V w n_max h_space mem₂ ∧
      gmAt base U V w n_max h_space mem₁ = gmAt base U V w n_max h_space mem₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext idx; unfold quotAt; split_ifs with hidx
    · exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by dsimp only [offQuot] at ha1; omega)
          (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha2 ⊢; omega)) hidx
    · rfl
  · funext idx; unfold valAt; split_ifs with hidx
    · exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by dsimp only [offVal, offQuot] at ha1; omega)
          (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha2 ⊢; omega)) hidx
    · rfl
  · funext ⟨c, idx⟩; unfold lmAt; split_ifs with hp
    · rcases hp with ⟨hc, hidx⟩
      have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.add_one_mul] at hsub
      exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by dsimp only [offLMSub, offLM, offVal, offQuot] at ha1; omega)
          (by dsimp only [totalSpace, offGM, offLMSub, offLM, offVal, offQuot, lmSubWords]
                at ha2 hsub ⊢; omega)) hidx
    · rfl
  · funext idx; unfold gmAt; split_ifs with hidx
    · exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ =>
        heq a (by dsimp only [offGM, offLM, offVal, offQuot] at ha1; omega)
          (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot] at ha2 ⊢; omega)) hidx
    · rfl

/-! ## Section 2: Register allocation and primitive read/write wrappers -/

/-- Total register count `r_hash + 28` for the succinct dictionary machine.
Registers `0 .. r_hash - 1` belong to `QuotientHashImpl` (with `0 = base`, `1 = key/arg1`,
`2 = val/out/arg2`); registers `r_hash .. r_hash + 8` are dedicated scratch registers for
`readPackedCode` / `writePackedCode`; registers `r_hash + 9 .. r_hash + 27` are working registers
`wReg r_hash 0 .. wReg r_hash 18`. -/
@[expose]
def numRegs (r_hash : ℕ) : ℕ :=
  r_hash + 28

instance instNeZeroNumRegs (r_hash : ℕ) : NeZero (numRegs r_hash) :=
  ⟨by unfold numRegs; omega⟩

/-- Base register `0`. -/
@[expose]
def rBase (r_hash : ℕ) : Fin (numRegs r_hash) :=
  ⟨0, by unfold numRegs; omega⟩

/-- Argument 1 / hash input register `1`. -/
@[expose]
def rArg1 (r_hash : ℕ) : Fin (numRegs r_hash) :=
  ⟨1, by unfold numRegs; omega⟩

/-- Argument 2 / hash output / query return register `2`. -/
@[expose]
def rArg2 (r_hash : ℕ) : Fin (numRegs r_hash) :=
  ⟨2, by unfold numRegs; omega⟩

/-- Working register `i` (`r_hash + 9 + i` for `i < 19`), disjoint from both `0 .. r_hash - 1` and
the bit-packed array scratch registers `r_hash .. r_hash + 8`. -/
@[expose]
def wReg (r_hash : ℕ) (i : ℕ) (hi : i < 19 := by omega) : Fin (numRegs r_hash) :=
  ⟨r_hash + 9 + i, by unfold numRegs; omega⟩

/-- Register embedding `Fin r_hash → Fin (numRegs r_hash)` for `QuotientHashImpl`. -/
@[expose]
def hashRegMap (r_hash : ℕ) (j : Fin r_hash) : Fin (numRegs r_hash) :=
  ⟨j.val, by unfold numRegs; omega⟩

theorem hashRegMap_injective (r_hash : ℕ) : Function.Injective (hashRegMap r_hash) := by
  intro a b h
  exact Fin.ext (by simpa [hashRegMap] using congrArg Fin.val h)

theorem wReg_notMem_range_hashRegMap (r_hash : ℕ) (i : ℕ) (hi : i < 19) :
    ¬∃ j : Fin r_hash, hashRegMap r_hash j = wReg r_hash i hi := by
  rintro ⟨j, hj⟩
  have hval := congrArg Fin.val hj
  dsimp only [hashRegMap, wReg] at hval
  omega

/-- Dedicated scratch register `r_hash` holding the bit-packed array index (`j = 1` of
`readPackedCode` / `writePackedCode`). -/
@[expose]
def rPackIdx (r_hash : ℕ) : Fin (numRegs r_hash) :=
  ⟨r_hash, by unfold numRegs; omega⟩

/-- Dedicated scratch register `r_hash + 1` holding the bit-packed array value or output (`j = 2` of
`readPackedCode` / `writePackedCode`). -/
@[expose]
def rPackVal (r_hash : ℕ) : Fin (numRegs r_hash) :=
  ⟨r_hash + 1, by unfold numRegs; omega⟩

/-- Fixed register embedding `Fin 10 → Fin (numRegs r_hash)` for `readPackedCode` and
`writePackedCode`, mapping `0 ↦ rBase r_hash` and `j ↦ r_hash + (j - 1)` for `1 ≤ j ≤ 9`.
Its image is `{0} ∪ {r_hash .. r_hash + 8}`, which is completely disjoint from all working
registers `wReg r_hash 0 .. wReg r_hash 18` (`r_hash + 9 .. r_hash + 27`). -/
@[expose]
def packRegMap (r_hash : ℕ) (j : Fin 10) : Fin (numRegs r_hash) :=
  if j.val = 0 then rBase r_hash
  else ⟨r_hash + (j.val - 1), by unfold numRegs; omega⟩

theorem packRegMap_injective {r_hash : ℕ} [NeZero r_hash] :
    Function.Injective (packRegMap r_hash) := by
  have hr : 0 < r_hash := NeZero.pos r_hash
  intro a b h
  have hval := congrArg Fin.val h
  dsimp only [packRegMap, rBase] at hval
  rcases a with ⟨va, hva⟩
  rcases b with ⟨vb, hvb⟩
  apply Fin.ext
  dsimp only at hval ⊢
  split_ifs at hval <;> · dsimp only at hval; omega

theorem wReg_notMem_range_packRegMap (r_hash : ℕ) (i : ℕ) (hi : i < 19) :
    ¬∃ j : Fin 10, packRegMap r_hash j = wReg r_hash i hi := by
  rintro ⟨⟨vj, hvj⟩, hj⟩
  have hval := congrArg Fin.val hj
  dsimp only [packRegMap, rBase, wReg] at hval
  split_ifs at hval <;> · dsimp only at hval; omega

/-- Evaluate the quotient hash `H.impl` on the quotient in `wReg r_hash i_q`, storing the
`totalMicroBits n_max`-bit hash output into `wReg r_hash i_out`. -/
def evalHashCode {r_hash : ℕ} [NeZero r_hash]
    {w base U n_max : ℕ} (H : QuotientHashImpl r_hash w base U n_max)
    (i_q i_out : ℕ) (hq : i_q < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq
    (.op (.copy (rArg1 r_hash) (wReg r_hash i_q hq)))
    (.seq
      (H.impl.evalCode.rename (hashRegMap r_hash))
      (.op (.copy (wReg r_hash i_out hout) (rArg2 r_hash))))

/-- Specification of `evalHashCode`: evaluates `(H.impl.eval s ⟨q, hq_lt⟩).val` into
`wReg r_hash i_out`, preserving all working registers `wReg r_hash i` (`i ≠ i_out`), `rBase`,
`x.Bounded w`, and `x.mem`. -/
theorem evalHashCode_execWithin {r_hash : ℕ} [NeZero r_hash]
    {w base U n_max : ℕ} (H : QuotientHashImpl r_hash w base U n_max)
    (i_q i_out : ℕ) (hq : i_q < 19) (hout : i_out < 19)
    (s : H.impl.Seed) (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (htab : H.impl.tableRep x.mem)
    (hseed : H.impl.seedRep s x.mem)
    (hq_lt : x.regs (wReg r_hash i_q hq) < 2 ^ quotientBits U n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (evalHashCode H i_q i_out hq hout) x y (H.impl.evalSteps + 2) ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        (H.impl.eval s ⟨x.regs (wReg r_hash i_q hq), hq_lt⟩).val ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  unfold evalHashCode
  let x₁ := x.set (rArg1 r_hash) (x.regs (wReg r_hash i_q hq))
  have hex1 :
      ExecWithin (B := .exact) w (.op (.copy (rArg1 r_hash) (wReg r_hash i_q hq))) x x₁ 1 :=
    ExecWithin.copy
  have hx₁_bdd : x₁.Bounded w := hex1.bounded hx_bdd
  have hsub_base : (x₁.comap (hashRegMap r_hash)).regs H.impl.baseReg = base := by
    have hb_eq : hashRegMap r_hash H.impl.baseReg = rBase r_hash := Fin.ext H.hbase
    change x₁.regs (hashRegMap r_hash H.impl.baseReg) = base
    rw [hb_eq]
    dsimp only [x₁, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rBase, rArg1] at this; omega)]
    exact hbase_reg
  have hsub_key : (x₁.comap (hashRegMap r_hash)).regs H.impl.keyReg =
      x.regs (wReg r_hash i_q hq) := by
    have hk_eq : hashRegMap r_hash H.impl.keyReg = rArg1 r_hash := Fin.ext H.hkey
    change x₁.regs (hashRegMap r_hash H.impl.keyReg) = _
    rw [hk_eq]
    dsimp only [x₁, Data.set]
    rw [Function.update_self]
  let u_key : Fin (2 ^ quotientBits U n_max) := ⟨x.regs (wReg r_hash i_q hq), hq_lt⟩
  obtain ⟨y_core, hex_sub, hy_mem, hy_base, hy_out⟩ :=
    H.impl.eval_exec s u_key (hx₁_bdd.comap (hashRegMap r_hash)) hsub_base hsub_key htab hseed
  have hex2 := hex_sub.rename (hashRegMap_injective r_hash)
  let x₂ := y_core.extend (hashRegMap r_hash) x₁
  let x₃ := x₂.set (wReg r_hash i_out hout) (x₂.regs (rArg2 r_hash))
  have hex3 :
      ExecWithin (B := .exact) w (.op (.copy (wReg r_hash i_out hout) (rArg2 r_hash))) x₂ x₃ 1 :=
    ExecWithin.copy
  have hex123 := (hex1.seq (hex2.seq hex3)).mono
    (by omega : 1 + (H.impl.evalSteps + 1) ≤ H.impl.evalSteps + 2)
  refine ⟨x₃, hex123, hex123.bounded hx_bdd, hy_mem, ?_, ?_, ?_⟩
  · -- rBase
    dsimp only [x₃, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rBase, wReg] at this; omega)]
    have hb_eq : rBase r_hash = hashRegMap r_hash H.impl.baseReg := Fin.ext H.hbase.symm
    rw [hb_eq]
    change (x₂.comap (hashRegMap r_hash)).regs H.impl.baseReg = base
    rw [Data.comap_extend (hashRegMap_injective r_hash)]
    exact hy_base
  · -- wReg i_out
    dsimp only [x₃, Data.set]
    rw [Function.update_self]
    have ho_eq : rArg2 r_hash = hashRegMap r_hash H.impl.outReg := Fin.ext H.hout.symm
    rw [ho_eq]
    change (x₂.comap (hashRegMap r_hash)).regs H.impl.outReg = _
    rw [Data.comap_extend (hashRegMap_injective r_hash)]
    exact hy_out
  · -- other wReg
    intro i hi hne
    dsimp only [x₃, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [wReg] at this; omega)]
    change Function.extend (hashRegMap r_hash) y_core.regs x₁.regs (wReg r_hash i hi) = _
    rw [Function.extend_apply' _ _ _ (wReg_notMem_range_hashRegMap r_hash i hi)]
    dsimp only [x₁, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rArg1, wReg] at this; omega)]

/-- Generic read program for a bit-packed array at offset `off` with entry width `k`, reading index
`wReg r_hash i_idx` into `wReg r_hash i_out`. -/
def readPackedWrapCode (r_hash off k w : ℕ) (i_idx i_out : ℕ)
    (hidx : i_idx < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq
    (.op (.copy (rPackIdx r_hash) (wReg r_hash i_idx hidx)))
    (.seq
      ((readPackedCode off k w).rename (packRegMap r_hash))
      (.op (.copy (wReg r_hash i_out hout) (rPackVal r_hash))))

/-- Generic specification for `readPackedWrapCode`. -/
theorem readPackedWrapCode_execWithin {r_hash w base off N k : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hkw : k ≤ w)
    (hfit : Fits w (base + off + packedWords N k w))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < N) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readPackedWrapCode r_hash off k w i_idx i_out hidx hout) x y 38 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        readPacked (base + off) k w x.mem (x.regs (wReg r_hash i_idx hidx)) ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  unfold readPackedWrapCode
  have hr : 0 < r_hash := NeZero.pos r_hash
  let x₁ := x.set (rPackIdx r_hash) (x.regs (wReg r_hash i_idx hidx))
  have hex1 :
      ExecWithin (B := .exact) w (.op (.copy (rPackIdx r_hash) (wReg r_hash i_idx hidx))) x x₁ 1 :=
    ExecWithin.copy
  have hx₁_bdd : x₁.Bounded w := hex1.bounded hx_bdd
  have hsub0 : (x₁.comap (packRegMap r_hash)).regs 0 = base := by
    change x₁.regs (rBase r_hash) = base
    dsimp only [x₁, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rBase, rPackIdx] at this; omega)]
    exact hbase_reg
  have hsub1 : (x₁.comap (packRegMap r_hash)).regs 1 = x.regs (wReg r_hash i_idx hidx) := by
    change x₁.regs (rPackIdx r_hash) = _
    dsimp only [x₁, Data.set]
    rw [Function.update_self]
  obtain ⟨y_sub, hex_sub, hmem_sub, h0_sub, _, h2_sub⟩ :=
    readPackedCode_execWithin hw hkw hidx_lt (hx₁_bdd.comap (packRegMap r_hash)) hsub0 hsub1 hfit
  have hex2 := hex_sub.rename packRegMap_injective
  let x₂ := y_sub.extend (packRegMap r_hash) x₁
  let x₃ := x₂.set (wReg r_hash i_out hout) (x₂.regs (rPackVal r_hash))
  have hex3 :
      ExecWithin (B := .exact) w (.op (.copy (wReg r_hash i_out hout) (rPackVal r_hash))) x₂ x₃ 1 :=
    ExecWithin.copy
  have hex123 := (hex1.seq (hex2.seq hex3)).mono (by omega : 1 + (36 + 1) ≤ 38)
  refine ⟨x₃, hex123, hex123.bounded hx_bdd, hmem_sub, ?_, ?_, ?_⟩
  · -- rBase
    dsimp only [x₃, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rBase, wReg] at this; omega)]
    change (x₂.comap (packRegMap r_hash)).regs 0 = base
    rw [Data.comap_extend packRegMap_injective]
    exact h0_sub
  · -- wReg i_out
    dsimp only [x₃, Data.set]
    rw [Function.update_self]
    change (x₂.comap (packRegMap r_hash)).regs 2 = _
    rw [Data.comap_extend packRegMap_injective]
    exact h2_sub
  · -- other wReg
    intro i hi hne
    dsimp only [x₃, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [wReg] at this; omega)]
    change Function.extend (packRegMap r_hash) y_sub.regs x₁.regs (wReg r_hash i hi) = _
    rw [Function.extend_apply' _ _ _ (wReg_notMem_range_packRegMap r_hash i hi)]
    dsimp only [x₁, Data.set]
    rw [Function.update_of_ne
      (by intro h; have := congrArg Fin.val h; dsimp [rPackIdx, wReg] at this; omega)]

/-- Generic write program for a bit-packed array at offset `off` with entry width `k`, writing
`wReg r_hash i_val` at index `wReg r_hash i_idx`. -/
def writePackedWrapCode (r_hash off k w : ℕ) (i_idx i_val : ℕ)
    (hidx : i_idx < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  .seq
    (.op (.copy (rPackIdx r_hash) (wReg r_hash i_idx hidx)))
    (.seq
      (.op (.copy (rPackVal r_hash) (wReg r_hash i_val hval)))
      ((writePackedCode off k w).rename (packRegMap r_hash)))

/-- Generic specification for `writePackedWrapCode`. -/
theorem writePackedWrapCode_execWithin {r_hash w base off N k : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hkw : k ≤ w)
    (hfit : Fits w (base + off + packedWords N k w))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < N) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writePackedWrapCode r_hash off k w i_idx i_val hidx hval) x y 49 ∧
      y.Bounded w ∧
      y.mem = writePacked (base + off) k w x.mem
        (x.regs (wReg r_hash i_idx hidx))
        (x.regs (wReg r_hash i_val hval)) ∧
      y.regs (rBase r_hash) = base ∧
      (∀ i (hi : i < 19),
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  unfold writePackedWrapCode
  have hr : 0 < r_hash := NeZero.pos r_hash
  let x₁ := x.set (rPackIdx r_hash) (x.regs (wReg r_hash i_idx hidx))
  have hex1 :
      ExecWithin (B := .exact) w (.op (.copy (rPackIdx r_hash) (wReg r_hash i_idx hidx))) x x₁ 1 :=
    ExecWithin.copy
  let x₂ := x₁.set (rPackVal r_hash) (x₁.regs (wReg r_hash i_val hval))
  have hex2 :
      ExecWithin (B := .exact) w (.op (.copy (rPackVal r_hash) (wReg r_hash i_val hval))) x₁ x₂ 1 :=
    ExecWithin.copy
  have hx₂_bdd : x₂.Bounded w := hex2.bounded (hex1.bounded hx_bdd)
  have hsub0 : (x₂.comap (packRegMap r_hash)).regs 0 = base := by
    change x₂.regs (rBase r_hash) = base
    dsimp only [x₂, x₁, Data.set]
    rw [Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rBase, rPackVal] at this; omega),
      Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rBase, rPackIdx] at this; omega)]
    exact hbase_reg
  have hsub1 : (x₂.comap (packRegMap r_hash)).regs 1 = x.regs (wReg r_hash i_idx hidx) := by
    change x₂.regs (rPackIdx r_hash) = _
    dsimp only [x₂, x₁, Data.set]
    rw [Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rPackIdx, rPackVal] at this; omega),
      Function.update_self]
  have hsub2 : (x₂.comap (packRegMap r_hash)).regs 2 = x.regs (wReg r_hash i_val hval) := by
    change x₂.regs (rPackVal r_hash) = _
    dsimp only [x₂, x₁, Data.set]
    rw [Function.update_self,
      Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rPackIdx, wReg] at this; omega)]
  obtain ⟨y_sub, hex_sub, hmem_sub, h0_sub, _, _⟩ :=
    writePackedCode_execWithin hw hkw hidx_lt (hx₂_bdd.comap (packRegMap r_hash))
      hsub0 hsub1 hsub2 hfit
  have hex3 := hex_sub.rename packRegMap_injective
  let x₃ := y_sub.extend (packRegMap r_hash) x₂
  have hex123 := (hex1.seq (hex2.seq hex3)).mono (by omega : 1 + (1 + 47) ≤ 49)
  refine ⟨x₃, hex123, hex123.bounded hx_bdd, hmem_sub, ?_, ?_⟩
  · -- rBase
    change (x₃.comap (packRegMap r_hash)).regs 0 = base
    rw [Data.comap_extend packRegMap_injective]
    exact h0_sub
  · -- all wReg
    intro i hi
    change Function.extend (packRegMap r_hash) y_sub.regs x₂.regs (wReg r_hash i hi) = _
    rw [Function.extend_apply' _ _ _ (wReg_notMem_range_packRegMap r_hash i hi)]
    dsimp only [x₂, x₁, Data.set]
    rw [Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rPackVal, wReg] at this; omega),
      Function.update_of_ne
        (by intro h; have := congrArg Fin.val h; dsimp [rPackIdx, wReg] at this; omega)]

/-- Read `Quotients[wReg r_hash i_idx]` into `wReg r_hash i_out`. -/
def readQuotCode (r_hash U w n_max h_space : ℕ) (i_idx i_out : ℕ)
    (hidx : i_idx < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  readPackedWrapCode r_hash (offQuot h_space) (quotientBits U n_max) w i_idx i_out hidx hout

/-- Write `wReg r_hash i_val` into `Quotients[wReg r_hash i_idx]`. -/
def writeQuotCode (r_hash U w n_max h_space : ℕ) (i_idx i_val : ℕ)
    (hidx : i_idx < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  writePackedWrapCode r_hash (offQuot h_space) (quotientBits U n_max) w i_idx i_val hidx hval

/-- Read `Values[wReg r_hash i_idx]` into `wReg r_hash i_out`. -/
def readValCode (r_hash U V w n_max h_space : ℕ) (i_idx i_out : ℕ)
    (hidx : i_idx < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  readPackedWrapCode r_hash (offVal U w n_max h_space) (valBits V) w i_idx i_out hidx hout

/-- Write `wReg r_hash i_val` into `Values[wReg r_hash i_idx]`. -/
def writeValCode (r_hash U V w n_max h_space : ℕ) (i_idx i_val : ℕ)
    (hidx : i_idx < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  writePackedWrapCode r_hash (offVal U w n_max h_space) (valBits V) w i_idx i_val hidx hval

/-- Read `LocalMeta` sub-array `c < 9` at `wReg r_hash i_idx` into `wReg r_hash i_out`. -/
def readLMCode (r_hash U V w n_max h_space c : ℕ) (i_idx i_out : ℕ)
    (hidx : i_idx < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  readPackedWrapCode r_hash (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w
    i_idx i_out hidx hout

/-- Write `wReg r_hash i_val` into `LocalMeta` sub-array `c < 9` at `wReg r_hash i_idx`. -/
def writeLMCode (r_hash U V w n_max h_space c : ℕ) (i_idx i_val : ℕ)
    (hidx : i_idx < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  writePackedWrapCode r_hash (offLMSub U V w n_max h_space c) (effBucketPosBits n_max) w
    i_idx i_val hidx hval

/-- Read `GlobalMeta[wReg r_hash i_idx]` into `wReg r_hash i_out`. -/
def readGMCode (r_hash U V w n_max h_space : ℕ) (i_idx i_out : ℕ)
    (hidx : i_idx < 19 := by omega) (hout : i_out < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  readPackedWrapCode r_hash (offGM U V w n_max h_space) (globalPtrBits n_max) w
    i_idx i_out hidx hout

/-- Write `wReg r_hash i_val` into `GlobalMeta[wReg r_hash i_idx]`. -/
def writeGMCode (r_hash U V w n_max h_space : ℕ) (i_idx i_val : ℕ)
    (hidx : i_idx < 19 := by omega) (hval : i_val < 19 := by omega) :
    Code .exact (numRegs r_hash) :=
  writePackedWrapCode r_hash (offGM U V w n_max h_space) (globalPtrBits n_max) w
    i_idx i_val hidx hval

/-- Specification of `readQuotCode`. -/
theorem readQuotCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readQuotCode r_hash U w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        quotAt base U w n_max h_space x.mem (x.regs (wReg r_hash i_idx hidx)) ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  have hkw : quotientBits U n_max ≤ w := quotientBits_le_of_le_pow hU
  have hfit : Fits w (base + offQuot h_space + packedWords n_max (quotientBits U n_max) w) :=
    hspace.of_le (by unfold totalSpace offGM offLM offVal offQuot; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hout', hregs'⟩ :=
    readPackedWrapCode_execWithin hw hkw hfit i_idx i_out hidx hout x hx_bdd hbase_reg hidx_lt
  refine ⟨y, hex, hbdd, hmem, hbase', ?_, hregs'⟩
  rw [hout']
  unfold quotAt
  simp only [hidx_lt, ↓reduceIte]

/-- Specification of `writeQuotCode`. -/
theorem writeQuotCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hU : U ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < n_max)
    (hval_lt : x.regs (wReg r_hash i_val hval) < 2 ^ quotientBits U n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeQuotCode r_hash U w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      y.Bounded w ∧
      y.regs (rBase r_hash) = base ∧
      (∀ i (hi : i < 19),
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) ∧
      (∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem =
        Function.update (quotAt base U w n_max h_space x.mem)
          (x.regs (wReg r_hash i_idx hidx))
          (x.regs (wReg r_hash i_val hval)) ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  have hkw : quotientBits U n_max ≤ w := quotientBits_le_of_le_pow hU
  have hfit : Fits w (base + offQuot h_space + packedWords n_max (quotientBits U n_max) w) :=
    hspace.of_le (by dsimp only [totalSpace, offGM, offLM, offVal, offQuot]; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hregs'⟩ :=
    writePackedWrapCode_execWithin hw hkw hfit i_idx i_val hidx hval x hx_bdd hbase_reg hidx_lt
  have hout_mem : ∀ a, ¬(base + offQuot h_space ≤ a ∧ a < base + offVal U w n_max h_space) →
      y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw x.mem hidx_lt _ (by dsimp only [offVal] at ha; omega)
  refine ⟨y, hex, hbdd, hbase', hregs', hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j
    unfold quotAt
    by_cases hj : j = x.regs (wReg r_hash i_idx hidx)
    · subst hj
      rw [Function.update_self]
      simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]
      split_ifs with hj_lt
      · rw [hmem]
        exact readPacked_writePacked_of_ne hw x.mem hj _
      · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ => hout_mem a (by omega)) hj_lt
    · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offLMSub, offLM] at ha1; omega)) hp.2
    · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offGM, offLM] at ha1; omega)) hj_lt
    · rfl

/-- Specification of `readValCode`. -/
theorem readValCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readValCode r_hash U V w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        valAt base U V w n_max h_space x.mem (x.regs (wReg r_hash i_idx hidx)) ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  have hkw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hfit : Fits w (base + offVal U w n_max h_space + packedWords n_max (valBits V) w) :=
    hspace.of_le (by dsimp only [totalSpace, offGM, offLM, offVal]; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hout', hregs'⟩ :=
    readPackedWrapCode_execWithin hw hkw hfit i_idx i_out hidx hout x hx_bdd hbase_reg hidx_lt
  refine ⟨y, hex, hbdd, hmem, hbase', ?_, hregs'⟩
  rw [hout']
  unfold valAt
  simp only [hidx_lt, ↓reduceIte]

/-- Specification of `writeValCode`. -/
theorem writeValCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hV : V ≤ 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < n_max)
    (hval_lt : x.regs (wReg r_hash i_val hval) < 2 ^ valBits V) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeValCode r_hash U V w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      y.Bounded w ∧
      y.regs (rBase r_hash) = base ∧
      (∀ i (hi : i < 19),
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) ∧
      (∀ a, ¬(base + offVal U w n_max h_space ≤ a ∧ a < base + offLM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem =
        Function.update (valAt base U V w n_max h_space x.mem)
          (x.regs (wReg r_hash i_idx hidx))
          (x.regs (wReg r_hash i_val hval)) ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  have hkw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hfit : Fits w (base + offVal U w n_max h_space + packedWords n_max (valBits V) w) :=
    hspace.of_le (by dsimp only [totalSpace, offGM, offLM, offVal]; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hregs'⟩ :=
    writePackedWrapCode_execWithin hw hkw hfit i_idx i_val hidx hval x hx_bdd hbase_reg hidx_lt
  have hout_mem : ∀ a, ¬(base + offVal U w n_max h_space ≤ a ∧
      a < base + offLM U V w n_max h_space) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw x.mem hidx_lt _ (by dsimp only [offLM] at ha; omega)
  refine ⟨y, hex, hbdd, hbase', hregs', hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j
    unfold valAt
    by_cases hj : j = x.regs (wReg r_hash i_idx hidx)
    · subst hj
      rw [Function.update_self]
      simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]
      split_ifs with hj_lt
      · rw [hmem]
        exact readPacked_writePacked_of_ne hw x.mem hj _
      · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offLMSub] at ha1; omega)) hp.2
    · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ =>
        hout_mem a (by dsimp only [offGM] at ha1; omega)) hj_lt
    · rfl

/-- Specification of `readLMCode`. -/
theorem readLMCode_execWithin {r_hash w base U V n_max h_space c : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c < 9)
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < totalMicroBuckets n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readLMCode r_hash U V w n_max h_space c i_idx i_out hidx hout) x y 38 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        lmAt base U V w n_max h_space x.mem (c, x.regs (wReg r_hash i_idx hidx)) ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  have hkw : effBucketPosBits n_max ≤ w := effBucketPosBits_le_of_lt_pow hnU hU
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  have hfit : Fits w (base + offLMSub U V w n_max h_space c +
      packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) :=
    hspace.of_le (by dsimp only [totalSpace, offGM, offLMSub, offLM, lmSubWords] at hsub ⊢; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hout', hregs'⟩ :=
    readPackedWrapCode_execWithin hw hkw hfit i_idx i_out hidx hout x hx_bdd hbase_reg hidx_lt
  refine ⟨y, hex, hbdd, hmem, hbase', ?_, hregs'⟩
  rw [hout']
  unfold lmAt
  simp only [hc, hidx_lt, and_self, ↓reduceIte]

/-- Specification of `writeLMCode`. -/
theorem writeLMCode_execWithin {r_hash w base U V n_max h_space c : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (hc : c < 9)
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < totalMicroBuckets n_max)
    (hval_lt : x.regs (wReg r_hash i_val hval) < 2 ^ effBucketPosBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeLMCode r_hash U V w n_max h_space c i_idx i_val hidx hval) x y 49 ∧
      y.Bounded w ∧
      y.regs (rBase r_hash) = base ∧
      (∀ i (hi : i < 19),
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) ∧
      (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem =
        Function.update (lmAt base U V w n_max h_space x.mem)
          (c, x.regs (wReg r_hash i_idx hidx))
          (x.regs (wReg r_hash i_val hval)) ∧
      gmAt base U V w n_max h_space y.mem = gmAt base U V w n_max h_space x.mem := by
  have hkw : effBucketPosBits n_max ≤ w := effBucketPosBits_le_of_lt_pow hnU hU
  have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
    Nat.mul_le_mul_right _ hc
  rw [Nat.add_one_mul] at hsub
  have hfit : Fits w (base + offLMSub U V w n_max h_space c +
      packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) :=
    hspace.of_le (by dsimp only [totalSpace, offGM, offLMSub, offLM, lmSubWords] at hsub ⊢; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hregs'⟩ :=
    writePackedWrapCode_execWithin hw hkw hfit i_idx i_val hidx hval x hx_bdd hbase_reg hidx_lt
  have hout_sub : ∀ a, ¬(base + offLMSub U V w n_max h_space c ≤ a ∧
      a < base + offLMSub U V w n_max h_space c + lmSubWords n_max w) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw x.mem hidx_lt _ ha
  have hout_mem : ∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧
      a < base + offGM U V w n_max h_space) → y.mem a = x.mem a := by
    intro a ha
    exact hout_sub a (by dsimp only [offGM, offLMSub] at ha hsub ⊢; omega)
  refine ⟨y, hex, hbdd, hbase', hregs', hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offLM, offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offLM, offVal] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext ⟨c', j⟩
    unfold lmAt
    by_cases hp_eq : (c', j) = (c, x.regs (wReg r_hash i_idx hidx))
    · injection hp_eq with hc_eq hj_eq
      subst hc_eq hj_eq
      rw [Function.update_self]
      simp only [hc, hidx_lt, and_self, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hp_eq]
      split_ifs with hp_lt
      · rcases hp_lt with ⟨hc', hj_lt⟩
        by_cases hc_eq : c' = c
        · subst hc_eq
          have hj_ne : j ≠ x.regs (wReg r_hash i_idx hidx) := fun h => hp_eq (congrArg _ h)
          rw [hmem]
          exact readPacked_writePacked_of_ne hw x.mem hj_ne _
        · exact readPacked_congr hw (fun a ⟨ha1, ha2⟩ => by
            apply hout_sub
            dsimp only [offLMSub, lmSubWords] at ha1 ha2 ⊢
            rcases lt_trichotomy c' c with hlt | hlt | hlt
            · have := Nat.mul_le_mul_right
                (packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) hlt
              rw [Nat.add_one_mul] at this; omega
            · exact absurd hlt hc_eq
            · have := Nat.mul_le_mul_right
                (packedWords (totalMicroBuckets n_max) (effBucketPosBits n_max) w) hlt
              rw [Nat.add_one_mul] at this; omega) hj_lt
      · rfl
  · funext j; unfold gmAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨ha1, _⟩ => hout_mem a (by omega)) hj_lt
    · rfl

/-- Specification of `readGMCode`. -/
theorem readGMCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_out : ℕ) (hidx : i_idx < 19) (hout : i_out < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < globalMetaLen n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (readGMCode r_hash U V w n_max h_space i_idx i_out hidx hout) x y 38 ∧
      y.Bounded w ∧
      y.mem = x.mem ∧
      y.regs (rBase r_hash) = base ∧
      y.regs (wReg r_hash i_out hout) =
        gmAt base U V w n_max h_space x.mem (x.regs (wReg r_hash i_idx hidx)) ∧
      (∀ i (hi : i < 19), i ≠ i_out →
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) := by
  have hkw : globalPtrBits n_max ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hfit : Fits w (base + offGM U V w n_max h_space +
      packedWords (globalMetaLen n_max) (globalPtrBits n_max) w) :=
    hspace.of_le (by dsimp only [totalSpace]; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hout', hregs'⟩ :=
    readPackedWrapCode_execWithin hw hkw hfit i_idx i_out hidx hout x hx_bdd hbase_reg hidx_lt
  refine ⟨y, hex, hbdd, hmem, hbase', ?_, hregs'⟩
  rw [hout']
  unfold gmAt
  simp only [hidx_lt, ↓reduceIte]

/-- Specification of `writeGMCode`. -/
theorem writeGMCode_execWithin {r_hash w base U V n_max h_space : ℕ} [NeZero r_hash]
    (hw : 0 < w) (hnU : n_max ≤ U) (hU : U < 2 ^ w)
    (hspace : Fits w (base + totalSpace U V w n_max h_space))
    (i_idx i_val : ℕ) (hidx : i_idx < 19) (hval : i_val < 19)
    (x : Data (numRegs r_hash))
    (hx_bdd : x.Bounded w)
    (hbase_reg : x.regs (rBase r_hash) = base)
    (hidx_lt : x.regs (wReg r_hash i_idx hidx) < globalMetaLen n_max)
    (hval_lt : x.regs (wReg r_hash i_val hval) < 2 ^ globalPtrBits n_max) :
    ∃ y : Data (numRegs r_hash),
      ExecWithin w (writeGMCode r_hash U V w n_max h_space i_idx i_val hidx hval) x y 49 ∧
      y.Bounded w ∧
      y.regs (rBase r_hash) = base ∧
      (∀ i (hi : i < 19),
        y.regs (wReg r_hash i hi) = x.regs (wReg r_hash i hi)) ∧
      (∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
          a < base + totalSpace U V w n_max h_space) →
        y.mem a = x.mem a) ∧
      quotAt base U w n_max h_space y.mem = quotAt base U w n_max h_space x.mem ∧
      valAt base U V w n_max h_space y.mem = valAt base U V w n_max h_space x.mem ∧
      lmAt base U V w n_max h_space y.mem = lmAt base U V w n_max h_space x.mem ∧
      gmAt base U V w n_max h_space y.mem =
        Function.update (gmAt base U V w n_max h_space x.mem)
          (x.regs (wReg r_hash i_idx hidx))
          (x.regs (wReg r_hash i_val hval)) := by
  have hkw : globalPtrBits n_max ≤ w := globalPtrBits_le_of_lt_pow hnU hU
  have hfit : Fits w (base + offGM U V w n_max h_space +
      packedWords (globalMetaLen n_max) (globalPtrBits n_max) w) :=
    hspace.of_le (by dsimp only [totalSpace]; omega)
  obtain ⟨y, hex, hbdd, hmem, hbase', hregs'⟩ :=
    writePackedWrapCode_execWithin hw hkw hfit i_idx i_val hidx hval x hx_bdd hbase_reg hidx_lt
  have hout_mem : ∀ a, ¬(base + offGM U V w n_max h_space ≤ a ∧
      a < base + totalSpace U V w n_max h_space) → y.mem a = x.mem a := by
    intro a ha
    rw [hmem]
    exact writePacked_outside hw x.mem hidx_lt _ (by dsimp only [totalSpace] at ha; omega)
  refine ⟨y, hex, hbdd, hbase', hregs', hout_mem, ?_, ?_, ?_, ?_⟩
  · funext j; unfold quotAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offGM, offLM, offVal, offQuot] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext j; unfold valAt; split_ifs with hj_lt
    · exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offGM, offLM, offVal] at ha2 ⊢; omega)) hj_lt
    · rfl
  · funext ⟨c, j⟩; unfold lmAt; split_ifs with hp
    · rcases hp with ⟨hc, hj_lt⟩
      have hsub : (c + 1) * lmSubWords n_max w ≤ 9 * lmSubWords n_max w :=
        Nat.mul_le_mul_right _ hc
      rw [Nat.add_one_mul] at hsub
      exact readPacked_congr hw (fun a ⟨_, ha2⟩ =>
        hout_mem a (by dsimp only [offGM, offLMSub, offLM, lmSubWords] at ha2 hsub ⊢; omega)) hj_lt
    · rfl
  · funext j
    unfold gmAt
    by_cases hj : j = x.regs (wReg r_hash i_idx hidx)
    · subst hj
      rw [Function.update_self]
      simp only [hidx_lt, ↓reduceIte, hmem]
      exact readPacked_writePacked_self _ _ _ _ _ hval_lt
    · rw [Function.update_of_ne hj]
      split_ifs with hj_lt
      · rw [hmem]
        exact readPacked_writePacked_of_ne hw x.mem hj _
      · rfl


end Cslib.DataStructure.Dictionary.WordRAM.Succinct
