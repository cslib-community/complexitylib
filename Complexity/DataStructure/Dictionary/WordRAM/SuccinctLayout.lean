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

/-!
# Bit-Packed Memory Layout for Succinct Dictionaries

This module defines the word-level memory layout and pure array extraction functions for the
fixed-capacity succinct dynamic dictionary.

## Memory layout (`[base, base + totalSpace)`)

1. `[base, base + h_space)`: Seeded 3-wise quotient hash table and seed (`h_space` words,
   instantiated in `SuccinctHash.lean` with `ReducedKWise.TableRep` and `ReducedKWise.SeedRep` at
   `h_space = hashSpace U w n_max`) mapping quotients in `Fin (2 ^ quotientBits U n_max)` to
   micro-bucket hashes in `Fin (2 ^ totalMicroBits n_max)`.
2. `Quotients`: `packedWords n_max (quotientBits U n_max) w` words storing `n_max` quotients of
   `quotientBits U n_max` bits (`offQuot`).
3. `Values`: `packedWords n_max (valBits V) w` words storing `n_max` values of `valBits V` bits
   (`offVal`).
4. `LocalMeta`: `9 * lmSubWords n_max w` words (`9` bit-packed sub-arrays of
   `totalMicroBuckets n_max` entries of `effBucketPosBits n_max` bits each) storing per-bucket
   micro-bucket heads and doubly-linked list `next`/`prev` pointers (`offLM`).
5. `GlobalMeta`: `packedWords (globalMetaLen n_max) (globalPtrBits n_max) w` words storing global
   counts, per-bucket slab/tail counts, direct slab directories, tail pointers, tail back-pointers,
   and the logical/physical slab pool bijection (`offGM`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.offQuot`, `offVal`, `offLM`, `lmSubWords`,
  `offLMSub`, `offGM`, `totalSpace`: word offsets and total footprint of the succinct dictionary
  block.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.quotAt`, `valAt`, `lmAt`, `gmAt`: pure extraction
  functions for `Quotients`, `Values`, `LocalMeta`, and `GlobalMeta`.

## Main results

* `totalSpace_le_succinctWords`: `totalSpace U V w n_max h_space` is at most
  `Dynamic.succinctWords 79 (35 + h_space) U V w n_max` whenever `n_max ≤ U`.
* `quotAt_lt`, `valAt_lt`, `lmAt_lt`, `gmAt_lt`: bit-width bounds on extracted array entries.
* `quotAt_zero_of_init`, `valAt_zero_of_init`, `lmAt_zero_of_init`, `gmAt_zero_of_init`: extracted
  arrays are identically zero on zero-initialized table memory.
* `arrays_congr_of_eq_on`: extracted arrays depend only on words inside
  `[base + h_space, base + totalSpace U V w n_max h_space)`.
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

/-! ## Section 1: Array offsets and extraction functions -/

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

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
