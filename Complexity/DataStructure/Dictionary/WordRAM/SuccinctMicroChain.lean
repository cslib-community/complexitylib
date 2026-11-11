/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import Complexity.Tactic.Realize

/-!
# Per-Micro-Bucket Doubly-Linked Chains and Phase 1 Search in `Memory.Prog`

This module implements the `LocalMeta` doubly-linked list primitives and Phase 1 micro-chain search
in `Memory.Prog`, certified via the `realize` tactic:
* `lmHead`, `lmPrev`, `lmNext`: functional views of the 9 sub-arrays of `LocalMeta`;
* `readLMHeadProg`, `writeLMHeadProg`, `readLMPrevProg`, `writeLMPrevProg`, `readLMNextProg`,
  `writeLMNextProg`: constant-time `Memory.Prog` accessors with frame lemmas isolating `(b, m)` and
  `(b, j)`;
* `IsDLChainAux`, `IsDLChain`: recursive doubly-linked chain invariant for a micro-bucket chain
  `L : List ℕ`;
* `lmPrependProg`, `lmUnlinkProg`: `O(1)` doubly-linked list insertion and deletion preserving
  `IsDLChain`;
* `searchMicroChainProg`: Phase 1 micro-chain traversal via `boundedWhile`, taking `O(1 + |L|)`
  memory accesses and instructions.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmHead`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmPrev`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmNext`: functional views of the 9 `LocalMeta`
  sub-arrays.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.IsDLChainAux`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.IsDLChain`: doubly-linked list invariant for a
  per-micro-bucket chain `L : List ℕ`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmPrependProg`: `Memory.Prog` operation
  prepending a local slot `j_new` to micro-chain `(b, m)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmUnlinkProg`: `Memory.Prog` operation unlinking
  a local slot `j_del` from micro-chain `(b, m)`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchMicroChainProg`: `Memory.Prog` operation
  scanning micro-chain `(b, m)` for a target quotient `q_target`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.isDLChain_prepend`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.isDLChain_unlink`: pure preservation of
  `IsDLChain` under prepend and unlink.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmPrependProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_lmPrependGen`: effect and `Realizes`
  certificate for `lmPrependProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.lmUnlinkProg_effect`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_lmUnlinkGen`: effect and `Realizes`
  certificate for `lmUnlinkProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.Succinct.searchMicroChainProg_spec`,
  `Cslib.DataStructure.Dictionary.WordRAM.Succinct.realizes_searchMicroChainGen`: correctness,
  `O(1 + |L|)` `memoryCost`, and `Realizes` certificate for `searchMicroChainProg`.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.Succinct

open Cslib.WordRAM Cslib.WordRAM.ExactLog Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Finset

/-! ## Section 1: Functional views `lmHead`, `lmPrev`, `lmNext` and `Memory.Prog` accessors -/

/-- 1-based head pointer (`0` = empty, `j + 1` = local slot `j < effBucketCap n_max`) of
micro-bucket `(b, m)` in `lm : ℕ × ℕ → ℕ`. -/
@[expose]
def lmHead (n_max : ℕ) (lm : ℕ × ℕ → ℕ) (b m : ℕ) : ℕ :=
  lm (0, b * numMicroPerBucket n_max + m)

/-- 1-based previous pointer (`0` = head of chain, `j_prev + 1` = predecessor `j_prev`) of local
slot `j < effBucketCap n_max` in bucket `b`. -/
@[expose]
def lmPrev (n_max : ℕ) (lm : ℕ × ℕ → ℕ) (b j : ℕ) : ℕ :=
  lm (1 + j % 4, b * numMicroPerBucket n_max + j / 4)

/-- 1-based next pointer (`0` = tail of chain, `j_next + 1` = successor `j_next`) of local slot
`j < effBucketCap n_max` in bucket `b`. -/
@[expose]
def lmNext (n_max : ℕ) (lm : ℕ × ℕ → ℕ) (b j : ℕ) : ℕ :=
  lm (5 + j % 4, b * numMicroPerBucket n_max + j / 4)

theorem lmHeadIdx_lt {n_max b m : ℕ}
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    b * numMicroPerBucket n_max + m < totalMicroBuckets n_max := by
  have htot := totalMicroBuckets_eq_mul n_max
  have hmul : (b + 1) * numMicroPerBucket n_max ≤ numBuckets n_max * numMicroPerBucket n_max :=
    Nat.mul_le_mul_right _ hb
  rw [Nat.add_one_mul] at hmul
  omega

theorem lmSlotIdx_lt {n_max b j : ℕ} (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    b * numMicroPerBucket n_max + j / 4 < totalMicroBuckets n_max := by
  apply lmHeadIdx_lt hb
  unfold effBucketCap at hj
  omega

theorem fits_of_le_totalMicroBuckets {U V w₀ n_max h_space w base x : ℕ}
    (h : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hw : 0 < w₀) (hnU : n_max ≤ U) (hU : U < 2 ^ w₀)
    (hx : x ≤ totalMicroBuckets n_max) : Fits w x :=
  fits_of_le_max_n_one h hw hnU hU (hx.trans (totalMicroBuckets_le n_max))

theorem numMicroPerBucket_le_totalMicroBuckets (n_max : ℕ) :
    numMicroPerBucket n_max ≤ totalMicroBuckets n_max := by
  rw [totalMicroBuckets_eq_mul]
  exact Nat.le_mul_of_pos_left _ (numBuckets_pos n_max)

/-- Parameter-free `Memory.Prog` operation reading `lmHead n_max lm b m` at
`d = (dp, ((base, b), m))`. -/
@[expose]
def readLMHeadGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  readLMGenProg ⟨0, by decide⟩ (d.1, (d.2.1.1, d.2.1.2 * dpNumMicro d.1 + d.2.2))

/-- Read `lmHead n_max lm b m` at `d = ((base, b), m)` in `Memory.Prog`. -/
@[expose]
def readLMHeadProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  readLMProg U V w n_max h_space 0 (d.1.1, d.1.2 * numMicroPerBucket n_max + d.2)

@[simp] theorem readLMHeadGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    readLMHeadGenProg (mkDictParams U V w n_max h_space, d) =
      readLMHeadProg U V w n_max h_space d := by
  simp only [readLMHeadGenProg, readLMHeadProg, readLMGenProg_mk, p_numMicro_mk]

/-- Parameter-free `Memory.Prog` operation writing `val = d.2.2` to `lmHead n_max lm b m` at
`d = (dp, (((base, b), m), val))`. -/
@[expose]
def writeLMHeadGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit :=
  writeLMGenProg ⟨0, by decide⟩ (d.1, ((d.2.1.1.1, d.2.1.1.2 * dpNumMicro d.1 + d.2.1.2), d.2.2))

/-- Write `val = d.2` to `lmHead n_max lm b m` at `d = (((base, b), m), val)` in `Memory.Prog`. -/
@[expose]
def writeLMHeadProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  writeLMProg U V w n_max h_space 0 ((d.1.1.1, d.1.1.2 * numMicroPerBucket n_max + d.1.2), d.2)

@[simp] theorem writeLMHeadGenProg_mk (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    writeLMHeadGenProg (mkDictParams U V w n_max h_space, d) =
      writeLMHeadProg U V w n_max h_space d := by
  simp only [writeLMHeadGenProg, writeLMHeadProg, writeLMGenProg_mk, p_numMicro_mk]

theorem clientState_readLMHeadProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readLMHeadProg U V w n_max h_space d) = s := rfl

@[simp]
theorem memoryCost_readLMHeadProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readLMHeadProg U V w n_max h_space d) s = 2 := rfl

@[simp]
theorem memoryCost_writeLMHeadProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (writeLMHeadProg U V w n_max h_space d) s = 4 := rfl

theorem clientResult_readLMHeadProg {U V w n_max h_space base b m : ℕ} (s : Memory.State)
    (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max) :
    (Memory.spec 0).clientResult s (readLMHeadProg U V w n_max h_space ((base, b), m)) =
      lmHead n_max (lmAt base U V w n_max h_space s.mem) b m :=
  clientResult_readLMProg s (by decide) (lmHeadIdx_lt hb hm)

theorem realizes_readLMHeadGen :
    Realizes .exact readLMHeadGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1 ∧
        d.2.1.2 < numBuckets (dpNMax d.1) ∧ d.2.2 < numMicroPerBucket (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrl := realizes_readLMGen ⟨0, by decide⟩
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) => do
      let idx ← pure (d.2.1.2 * dpNumMicro d.1 + d.2.2)
      readLMGenProg ⟨0, by decide⟩ (d.1, (d.2.1.1, idx))) ?_
    (fun _ => rfl)
  realizeDict
  · exact fits_of_le_totalMicroBuckets h.1 hw hnU hU (le_of_lt (lmHeadIdx_lt h.2.1 h.2.2))
  · exact h.1
  · exact lmHeadIdx_lt h.2.1 h.2.2

theorem realizes_writeLMHeadGen :
    Realizes .exact writeLMHeadGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1.1 ∧
        d.2.1.1.2 < numBuckets (dpNMax d.1) ∧ d.2.1.2 < numMicroPerBucket (dpNMax d.1))
      (fun _ _ => 0) := by
  have hwl := realizes_writeLMGen ⟨0, by decide⟩
  refine Realizes.congr (p := fun d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ) => do
      let idx ← pure (d.2.1.1.2 * dpNumMicro d.1 + d.2.1.2)
      writeLMGenProg ⟨0, by decide⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))) ?_
    (fun _ => rfl)
  realizeDict
  · exact fits_of_le_totalMicroBuckets h.1 hw hnU hU (le_of_lt (lmHeadIdx_lt h.2.1 h.2.2))
  · exact h.1
  · exact lmHeadIdx_lt h.2.1 h.2.2

/-- Parameter-free `Memory.Prog` operation reading
`lmAt (c_base + j % 4, b * numMicroPerBucket n_max + j / 4)` at `d = (dp, ((base, b), j))`. -/
def readLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ := do
  let idx ← pure (d.2.1.2 * dpNumMicro d.1 + d.2.2 / 4)
  let r ← pure (d.2.2 % 4)
  if r = 0 then
    readLMGenProg ⟨c_base, by omega⟩ (d.1, (d.2.1.1, idx))
  else if r = 1 then
    readLMGenProg ⟨c_base + 1, by omega⟩ (d.1, (d.2.1.1, idx))
  else if r = 2 then
    readLMGenProg ⟨c_base + 2, by omega⟩ (d.1, (d.2.1.1, idx))
  else
    readLMGenProg ⟨c_base + 3, by omega⟩ (d.1, (d.2.1.1, idx))

/-- Read `lmAt (c_base + j % 4, b * numMicroPerBucket n_max + j / 4)` at `d = ((base, b), j)`. -/
@[expose]
def readLMMod4Prog (U V w n_max h_space c_base : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let idx ← pure (d.1.2 * numMicroPerBucket n_max + d.2 / 4)
  let r ← pure (d.2 % 4)
  if r = 0 then
    readLMProg U V w n_max h_space c_base (d.1.1, idx)
  else if r = 1 then
    readLMProg U V w n_max h_space (c_base + 1) (d.1.1, idx)
  else if r = 2 then
    readLMProg U V w n_max h_space (c_base + 2) (d.1.1, idx)
  else
    readLMProg U V w n_max h_space (c_base + 3) (d.1.1, idx)

@[simp] theorem readLMMod4GenProg_mk (U V w n_max h_space c_base : ℕ) (hc : c_base + 3 < 9)
    (d : (ℕ × ℕ) × ℕ) :
    readLMMod4GenProg c_base hc (mkDictParams U V w n_max h_space, d) =
      readLMMod4Prog U V w n_max h_space c_base d := by
  simp only [readLMMod4GenProg, readLMMod4Prog, p_numMicro_mk, readLMGenProg_mk]

/-- Parameter-free `Memory.Prog` operation writing `val = d.2.2` to
`lmAt (c_base + j % 4, b * numMicroPerBucket n_max + j / 4)` at
`d = (dp, (((base, b), j), val))`. -/
def writeLMMod4GenProg (c_base : ℕ) (hc : c_base + 3 < 9)
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let idx ← pure (d.2.1.1.2 * dpNumMicro d.1 + d.2.1.2 / 4)
  let r ← pure (d.2.1.2 % 4)
  if r = 0 then
    writeLMGenProg ⟨c_base, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
  else if r = 1 then
    writeLMGenProg ⟨c_base + 1, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
  else if r = 2 then
    writeLMGenProg ⟨c_base + 2, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
  else
    writeLMGenProg ⟨c_base + 3, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))

/-- Write `val = d.2` to `lmAt (c_base + j % 4, b * numMicroPerBucket n_max + j / 4)` at
`d = (((base, b), j), val)`. -/
@[expose]
def writeLMMod4Prog (U V w n_max h_space c_base : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    Memory.Prog Unit := do
  let idx ← pure (d.1.1.2 * numMicroPerBucket n_max + d.1.2 / 4)
  let r ← pure (d.1.2 % 4)
  if r = 0 then
    writeLMProg U V w n_max h_space c_base ((d.1.1.1, idx), d.2)
  else if r = 1 then
    writeLMProg U V w n_max h_space (c_base + 1) ((d.1.1.1, idx), d.2)
  else if r = 2 then
    writeLMProg U V w n_max h_space (c_base + 2) ((d.1.1.1, idx), d.2)
  else
    writeLMProg U V w n_max h_space (c_base + 3) ((d.1.1.1, idx), d.2)

@[simp] theorem writeLMMod4GenProg_mk (U V w n_max h_space c_base : ℕ) (hc : c_base + 3 < 9)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    writeLMMod4GenProg c_base hc (mkDictParams U V w n_max h_space, d) =
      writeLMMod4Prog U V w n_max h_space c_base d := by
  simp only [writeLMMod4GenProg, writeLMMod4Prog, p_numMicro_mk, writeLMGenProg_mk]

/-- Parameter-free `Memory.Prog` operation reading `lmPrev n_max lm b j` at
`d = (dp, ((base, b), j))`. -/
def readLMPrevGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  readLMMod4GenProg 1 (by decide) d

/-- Read `lmPrev n_max lm b j` at `d = ((base, b), j)`. -/
@[expose]
def readLMPrevProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  readLMMod4Prog U V w n_max h_space 1 d

@[simp] theorem readLMPrevGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    readLMPrevGenProg (mkDictParams U V w n_max h_space, d) =
      readLMPrevProg U V w n_max h_space d :=
  readLMMod4GenProg_mk U V w n_max h_space 1 (by decide) d

/-- Parameter-free `Memory.Prog` operation writing `val = d.2.2` to `lmPrev n_max lm b j` at
`d = (dp, (((base, b), j), val))`. -/
def writeLMPrevGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit :=
  writeLMMod4GenProg 1 (by decide) d

/-- Write `val = d.2` to `lmPrev n_max lm b j` at `d = (((base, b), j), val)`. -/
@[expose]
def writeLMPrevProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  writeLMMod4Prog U V w n_max h_space 1 d

@[simp] theorem writeLMPrevGenProg_mk (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    writeLMPrevGenProg (mkDictParams U V w n_max h_space, d) =
      writeLMPrevProg U V w n_max h_space d :=
  writeLMMod4GenProg_mk U V w n_max h_space 1 (by decide) d

/-- Parameter-free `Memory.Prog` operation reading `lmNext n_max lm b j` at
`d = (dp, ((base, b), j))`. -/
def readLMNextGenProg (d : DictParams × ((ℕ × ℕ) × ℕ)) : Memory.Prog ℕ :=
  readLMMod4GenProg 5 (by decide) d

/-- Read `lmNext n_max lm b j` at `d = ((base, b), j)`. -/
@[expose]
def readLMNextProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ :=
  readLMMod4Prog U V w n_max h_space 5 d

@[simp] theorem readLMNextGenProg_mk (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) :
    readLMNextGenProg (mkDictParams U V w n_max h_space, d) =
      readLMNextProg U V w n_max h_space d :=
  readLMMod4GenProg_mk U V w n_max h_space 5 (by decide) d

/-- Parameter-free `Memory.Prog` operation writing `val = d.2.2` to `lmNext n_max lm b j` at
`d = (dp, (((base, b), j), val))`. -/
def writeLMNextGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit :=
  writeLMMod4GenProg 5 (by decide) d

/-- Write `val = d.2` to `lmNext n_max lm b j` at `d = (((base, b), j), val)`. -/
@[expose]
def writeLMNextProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit :=
  writeLMMod4Prog U V w n_max h_space 5 d

@[simp] theorem writeLMNextGenProg_mk (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    writeLMNextGenProg (mkDictParams U V w n_max h_space, d) =
      writeLMNextProg U V w n_max h_space d :=
  writeLMMod4GenProg_mk U V w n_max h_space 5 (by decide) d

theorem clientState_readLMMod4Prog (U V w n_max h_space c_base : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (readLMMod4Prog U V w n_max h_space c_base d) = s := by
  simp only [readLMMod4Prog, pure_bind]
  split_ifs <;> rfl

theorem clientState_readLMPrevProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readLMPrevProg U V w n_max h_space d) = s :=
  clientState_readLMMod4Prog U V w n_max h_space 1 d s

theorem clientState_readLMNextProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (readLMNextProg U V w n_max h_space d) = s :=
  clientState_readLMMod4Prog U V w n_max h_space 5 d s

@[simp]
theorem memoryCost_readLMMod4Prog (U V w n_max h_space c_base : ℕ) (d : (ℕ × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (readLMMod4Prog U V w n_max h_space c_base d) s = 2 := by
  simp only [readLMMod4Prog, pure_bind]
  split_ifs <;> rfl

@[simp]
theorem memoryCost_readLMPrevProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readLMPrevProg U V w n_max h_space d) s = 2 :=
  memoryCost_readLMMod4Prog U V w n_max h_space 1 d s

@[simp]
theorem memoryCost_readLMNextProg (U V w n_max h_space : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readLMNextProg U V w n_max h_space d) s = 2 :=
  memoryCost_readLMMod4Prog U V w n_max h_space 5 d s

@[simp]
theorem memoryCost_writeLMMod4Prog (U V w n_max h_space c_base : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (writeLMMod4Prog U V w n_max h_space c_base d) s = 4 := by
  simp only [writeLMMod4Prog, pure_bind]
  split_ifs <;> rfl

@[simp]
theorem memoryCost_writeLMPrevProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (writeLMPrevProg U V w n_max h_space d) s = 4 :=
  memoryCost_writeLMMod4Prog U V w n_max h_space 1 d s

@[simp]
theorem memoryCost_writeLMNextProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (writeLMNextProg U V w n_max h_space d) s = 4 :=
  memoryCost_writeLMMod4Prog U V w n_max h_space 5 d s

theorem clientResult_readLMMod4Prog {U V w n_max h_space c_base base b j : ℕ} (s : Memory.State)
    (hc : c_base + 3 < 9) (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    (Memory.spec 0).clientResult s (readLMMod4Prog U V w n_max h_space c_base ((base, b), j)) =
      lmAt base U V w n_max h_space s.mem
        (c_base + j % 4, b * numMicroPerBucket n_max + j / 4) := by
  have hidx := lmSlotIdx_lt hb hj
  have hmod : j % 4 < 4 := Nat.mod_lt j (by decide)
  simp only [readLMMod4Prog, pure_bind]
  split_ifs with h0 h1 h2
  · rw [h0, Nat.add_zero]
    exact clientResult_readLMProg s (by omega) hidx
  · rw [h1]
    exact clientResult_readLMProg s (by omega) hidx
  · rw [h2]
    exact clientResult_readLMProg s (by omega) hidx
  · have h3 : j % 4 = 3 := by omega
    rw [h3]
    exact clientResult_readLMProg s (by omega) hidx

theorem clientResult_readLMPrevProg {U V w n_max h_space base b j : ℕ} (s : Memory.State)
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    (Memory.spec 0).clientResult s (readLMPrevProg U V w n_max h_space ((base, b), j)) =
      lmPrev n_max (lmAt base U V w n_max h_space s.mem) b j :=
  clientResult_readLMMod4Prog s (by decide) hb hj

theorem clientResult_readLMNextProg {U V w n_max h_space base b j : ℕ} (s : Memory.State)
    (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max) :
    (Memory.spec 0).clientResult s (readLMNextProg U V w n_max h_space ((base, b), j)) =
      lmNext n_max (lmAt base U V w n_max h_space s.mem) b j :=
  clientResult_readLMMod4Prog s (by decide) hb hj

theorem realizes_readLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) :
    Realizes .exact (readLMMod4GenProg c_base hc)
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1 ∧
        d.2.1.2 < numBuckets (dpNMax d.1) ∧ d.2.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) := by
  have hrl0 := realizes_readLMGen ⟨c_base, by omega⟩
  have hrl1 := realizes_readLMGen ⟨c_base + 1, by omega⟩
  have hrl2 := realizes_readLMGen ⟨c_base + 2, by omega⟩
  have hrl3 := realizes_readLMGen ⟨c_base + 3, by omega⟩
  refine Realizes.congr (p := fun d : DictParams × ((ℕ × ℕ) × ℕ) => do
      let idx ← pure (d.2.1.2 * dpNumMicro d.1 + d.2.2 / 4)
      let r ← pure (d.2.2 % 4)
      let c0 ← pure 0
      let c1 ← pure 1
      let c2 ← pure 2
      if r = c0 then
        readLMGenProg ⟨c_base, by omega⟩ (d.1, (d.2.1.1, idx))
      else if r = c1 then
        readLMGenProg ⟨c_base + 1, by omega⟩ (d.1, (d.2.1.1, idx))
      else if r = c2 then
        readLMGenProg ⟨c_base + 2, by omega⟩ (d.1, (d.2.1.1, idx))
      else
        readLMGenProg ⟨c_base + 3, by omega⟩ (d.1, (d.2.1.1, idx))) ?_
    (fun _ => rfl)
  realizeDict
  · decide
  · exact fits_of_le_totalMicroBuckets h.1 hw hnU hU (le_of_lt (lmSlotIdx_lt h.2.1 h.2.2))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2

theorem realizes_writeLMMod4Gen {c_base : ℕ} (hc : c_base + 3 < 9) :
    Realizes .exact (writeLMMod4GenProg c_base hc)
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1.1 ∧
        d.2.1.1.2 < numBuckets (dpNMax d.1) ∧ d.2.1.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) := by
  have hwl0 := realizes_writeLMGen ⟨c_base, by omega⟩
  have hwl1 := realizes_writeLMGen ⟨c_base + 1, by omega⟩
  have hwl2 := realizes_writeLMGen ⟨c_base + 2, by omega⟩
  have hwl3 := realizes_writeLMGen ⟨c_base + 3, by omega⟩
  refine Realizes.congr (p := fun d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ) => do
      let idx ← pure (d.2.1.1.2 * dpNumMicro d.1 + d.2.1.2 / 4)
      let r ← pure (d.2.1.2 % 4)
      let c0 ← pure 0
      let c1 ← pure 1
      let c2 ← pure 2
      if r = c0 then
        writeLMGenProg ⟨c_base, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
      else if r = c1 then
        writeLMGenProg ⟨c_base + 1, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
      else if r = c2 then
        writeLMGenProg ⟨c_base + 2, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))
      else
        writeLMGenProg ⟨c_base + 3, by omega⟩ (d.1, ((d.2.1.1.1, idx), d.2.2))) ?_
    (fun _ => rfl)
  realizeDict
  · decide
  · exact fits_of_le_totalMicroBuckets h.1 hw hnU hU (le_of_lt (lmSlotIdx_lt h.2.1 h.2.2))
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact fits_const_of_dictEnv h.1 (by decide)
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2
  · exact h.1
  · exact lmSlotIdx_lt h.2.1 h.2.2

theorem realizes_readLMPrevGen :
    Realizes .exact readLMPrevGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1 ∧
        d.2.1.2 < numBuckets (dpNMax d.1) ∧ d.2.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) :=
  realizes_readLMMod4Gen (by decide)

theorem realizes_writeLMPrevGen :
    Realizes .exact writeLMPrevGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1.1 ∧
        d.2.1.1.2 < numBuckets (dpNMax d.1) ∧ d.2.1.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) :=
  realizes_writeLMMod4Gen (by decide)

theorem realizes_readLMNextGen :
    Realizes .exact readLMNextGenProg
      (WordEncoding.encode (α := DictParams × ((ℕ × ℕ) × ℕ))) (WordEncoding.encode (α := ℕ))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1 ∧
        d.2.1.2 < numBuckets (dpNMax d.1) ∧ d.2.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) :=
  realizes_readLMMod4Gen (by decide)

theorem realizes_writeLMNextGen :
    Realizes .exact writeLMNextGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      (fun w d _ => DictEnvGen w d.1 d.2.1.1.1 ∧
        d.2.1.1.2 < numBuckets (dpNMax d.1) ∧ d.2.1.2 < effBucketCap (dpNMax d.1))
      (fun _ _ => 0) :=
  realizes_writeLMMod4Gen (by decide)

/-! ## Section 2: Pure state effects and frame lemmas for `lmHead`, `lmPrev`, `lmNext` -/

private theorem mul_numMicro_add_inj {n_max b₁ m₁ b₂ m₂ : ℕ}
    (hm₁ : m₁ < numMicroPerBucket n_max) (hm₂ : m₂ < numMicroPerBucket n_max)
    (heq : b₁ * numMicroPerBucket n_max + m₁ = b₂ * numMicroPerBucket n_max + m₂) :
    b₁ = b₂ ∧ m₁ = m₂ := by
  have hM : 0 < numMicroPerBucket n_max := numMicroPerBucket_pos n_max
  have hb : b₁ = b₂ := by
    have h1 : (b₁ * numMicroPerBucket n_max + m₁) / numMicroPerBucket n_max = b₁ := by
      rw [Nat.mul_comm, Nat.mul_add_div hM, Nat.div_eq_of_lt hm₁, Nat.add_zero]
    have h2 : (b₂ * numMicroPerBucket n_max + m₂) / numMicroPerBucket n_max = b₂ := by
      rw [Nat.mul_comm, Nat.mul_add_div hM, Nat.div_eq_of_lt hm₂, Nat.add_zero]
    rw [← h1, ← h2, heq]
  subst hb
  exact ⟨rfl, by omega⟩

private theorem slot_mod4_div4_inj {n_max b₁ j₁ b₂ j₂ c : ℕ}
    (hj₁ : j₁ < effBucketCap n_max) (hj₂ : j₂ < effBucketCap n_max)
    (heq : (c + j₁ % 4, b₁ * numMicroPerBucket n_max + j₁ / 4) =
      (c + j₂ % 4, b₂ * numMicroPerBucket n_max + j₂ / 4)) :
    b₁ = b₂ ∧ j₁ = j₂ := by
  injection heq with hmod hdiv
  have hq₁ : j₁ / 4 < numMicroPerBucket n_max := by unfold effBucketCap at hj₁; omega
  have hq₂ : j₂ / 4 < numMicroPerBucket n_max := by unfold effBucketCap at hj₂; omega
  obtain ⟨hb, hq⟩ := mul_numMicro_add_inj hq₁ hq₂ hdiv
  refine ⟨hb, ?_⟩
  have h1 := Nat.div_add_mod j₁ 4
  have h2 := Nat.div_add_mod j₂ 4
  omega

/-- Pure state effect of `writeLMHeadProg`. -/
theorem writeLMHeadProg_effect {U V w n_max h_space base b m val : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hval_lt : val < 2 ^ effBucketPosBits n_max) (s : Memory.State) :
    let s' :=
      (Memory.spec 0).clientState s (writeLMHeadProg U V w n_max h_space (((base, b), m), val))
    let lm := lmAt base U V w n_max h_space s.mem
    let lm' := lmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    lmHead n_max lm' b m = val ∧
    (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max,
      (b' ≠ b ∨ m' ≠ m) → lmHead n_max lm' b' m' = lmHead n_max lm b' m') ∧
    lmPrev n_max lm' = lmPrev n_max lm ∧
    lmNext n_max lm' = lmNext n_max lm := by
  intro s' lm lm'
  obtain ⟨hf, hout, hq, hv, hlm, hgm⟩ :=
    writeLMProg_effect (U := U) (V := V) (w := w) (n_max := n_max) (h_space := h_space)
      (c := 0) (base := base) (idx := b * numMicroPerBucket n_max + m) (val := val)
      hw (by decide) (lmHeadIdx_lt hb hm) hval_lt s
  have hlm' : lm' = Function.update lm (0, b * numMicroPerBucket n_max + m) val := hlm
  refine ⟨hf, hout, hq, hv, hgm, ?_, ?_, ?_, ?_⟩
  · unfold lmHead; rw [hlm', Function.update_self]
  · intro b' _ m' hm' hne
    unfold lmHead; rw [hlm', Function.update_of_ne]
    intro heq
    injection heq with _ hidx
    obtain ⟨hb_eq, hm_eq⟩ := mul_numMicro_add_inj hm' hm hidx
    rcases hne with hne | hne <;> exact absurd (by assumption) hne
  · funext b' j'
    unfold lmPrev; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega
  · funext b' j'
    unfold lmNext; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega

/-- Pure state effect of `writeLMMod4Prog`. -/
theorem writeLMMod4Prog_effect {U V w n_max h_space c_base base b j val : ℕ}
    (hw : 0 < w) (hc : c_base + 3 < 9) (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max)
    (hval_lt : val < 2 ^ effBucketPosBits n_max) (s : Memory.State) :
    let s' := (Memory.spec 0).clientState s
      (writeLMMod4Prog U V w n_max h_space c_base (((base, b), j), val))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    lmAt base U V w n_max h_space s'.mem =
      Function.update (lmAt base U V w n_max h_space s.mem)
        (c_base + j % 4, b * numMicroPerBucket n_max + j / 4) val ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem := by
  have hidx := lmSlotIdx_lt hb hj
  have hmod : j % 4 < 4 := Nat.mod_lt j (by decide)
  change let s' := (Memory.spec 0).clientState s _
    s'.frontier = _ ∧ _
  simp only [writeLMMod4Prog, pure_bind]
  split_ifs with h0 h1 h2
  · rw [h0, Nat.add_zero]
    exact writeLMProg_effect hw (by omega) hidx hval_lt s
  · rw [h1]
    exact writeLMProg_effect hw (by omega) hidx hval_lt s
  · rw [h2]
    exact writeLMProg_effect hw (by omega) hidx hval_lt s
  · have h3 : j % 4 = 3 := by omega
    rw [h3]
    exact writeLMProg_effect hw (by omega) hidx hval_lt s

/-- Pure state effect of `writeLMPrevProg`. -/
theorem writeLMPrevProg_effect {U V w n_max h_space base b j val : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max)
    (hval_lt : val < 2 ^ effBucketPosBits n_max) (s : Memory.State) :
    let s' :=
      (Memory.spec 0).clientState s (writeLMPrevProg U V w n_max h_space (((base, b), j), val))
    let lm := lmAt base U V w n_max h_space s.mem
    let lm' := lmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    lmHead n_max lm' = lmHead n_max lm ∧
    lmPrev n_max lm' b j = val ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      (b' ≠ b ∨ j' ≠ j) → lmPrev n_max lm' b' j' = lmPrev n_max lm b' j') ∧
    lmNext n_max lm' = lmNext n_max lm := by
  intro s' lm lm'
  obtain ⟨hf, hout, hq, hv, hlm, hgm⟩ :=
    writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := n_max) (h_space := h_space)
      (c_base := 1) (base := base) (b := b) (j := j) (val := val)
      hw (by decide) hb hj hval_lt s
  have hlm' : lm' = Function.update lm (1 + j % 4, b * numMicroPerBucket n_max + j / 4) val := hlm
  refine ⟨hf, hout, hq, hv, hgm, ?_, ?_, ?_, ?_⟩
  · funext b' m'
    unfold lmHead; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega
  · unfold lmPrev; rw [hlm', Function.update_self]
  · intro b' _ j' hj' hne
    unfold lmPrev; rw [hlm', Function.update_of_ne]
    intro heq
    obtain ⟨hb_eq, hj_eq⟩ := slot_mod4_div4_inj hj' hj heq
    rcases hne with hne | hne <;> exact absurd (by assumption) hne
  · funext b' j'
    have hmod : j % 4 < 4 := Nat.mod_lt j (by decide)
    unfold lmNext; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega

/-- Pure state effect of `writeLMNextProg`. -/
theorem writeLMNextProg_effect {U V w n_max h_space base b j val : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hj : j < effBucketCap n_max)
    (hval_lt : val < 2 ^ effBucketPosBits n_max) (s : Memory.State) :
    let s' :=
      (Memory.spec 0).clientState s (writeLMNextProg U V w n_max h_space (((base, b), j), val))
    let lm := lmAt base U V w n_max h_space s.mem
    let lm' := lmAt base U V w n_max h_space s'.mem
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    lmHead n_max lm' = lmHead n_max lm ∧
    lmPrev n_max lm' = lmPrev n_max lm ∧
    lmNext n_max lm' b j = val ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      (b' ≠ b ∨ j' ≠ j) → lmNext n_max lm' b' j' = lmNext n_max lm b' j') := by
  intro s' lm lm'
  obtain ⟨hf, hout, hq, hv, hlm, hgm⟩ :=
    writeLMMod4Prog_effect (U := U) (V := V) (w := w) (n_max := n_max) (h_space := h_space)
      (c_base := 5) (base := base) (b := b) (j := j) (val := val)
      hw (by decide) hb hj hval_lt s
  have hlm' : lm' = Function.update lm (5 + j % 4, b * numMicroPerBucket n_max + j / 4) val := hlm
  refine ⟨hf, hout, hq, hv, hgm, ?_, ?_, ?_, ?_⟩
  · funext b' m'
    unfold lmHead; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega
  · funext b' j'
    have hmod' : j' % 4 < 4 := Nat.mod_lt j' (by decide)
    unfold lmPrev; rw [hlm', Function.update_of_ne]
    intro heq; injection heq; omega
  · unfold lmNext; rw [hlm', Function.update_self]
  · intro b' _ j' hj' hne
    unfold lmNext; rw [hlm', Function.update_of_ne]
    intro heq
    obtain ⟨hb_eq, hj_eq⟩ := slot_mod4_div4_inj hj' hj heq
    rcases hne with hne | hne <;> exact absurd (by assumption) hne

/-! ## Section 3: Doubly-linked chain invariant (`IsDLChain`) and `lmPrependProg` / `lmUnlinkProg`
-/

/-- Auxiliary doubly-linked chain invariant starting with expected previous pointer `prev_ptr`
(`0` for the head node, `j_prev + 1` after node `j_prev`). -/
@[expose]
def IsDLChainAux (n_max prev_ptr : ℕ) (prev next : ℕ → ℕ) : List ℕ → Prop
  | [] => True
  | j :: rest =>
      j < effBucketCap n_max ∧
      j ∉ rest ∧
      prev j = prev_ptr ∧
      next j = (rest.head?.map (· + 1)).getD 0 ∧
      IsDLChainAux n_max (j + 1) prev next rest

/-- Doubly-linked chain invariant for a single micro-bucket chain `L : List ℕ` with head pointer
`head`, `prev` map, and `next` map. -/
@[expose]
def IsDLChain (n_max head : ℕ) (prev next : ℕ → ℕ) (L : List ℕ) : Prop :=
  head = (L.head?.map (· + 1)).getD 0 ∧
  IsDLChainAux n_max 0 prev next L

theorem isDLChain_nil (n_max : ℕ) (prev next : ℕ → ℕ) :
    IsDLChain n_max 0 prev next [] :=
  ⟨rfl, trivial⟩

theorem IsDLChainAux.congr {n_max prev_ptr : ℕ} {prev prev' next next' : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L)
    (hp : ∀ x ∈ L, prev' x = prev x) (hn : ∀ x ∈ L, next' x = next x) :
    IsDLChainAux n_max prev_ptr prev' next' L := by
  induction L generalizing prev_ptr with
  | nil => trivial
  | cons j rest ih =>
    rcases h with ⟨hj, hnot, hpj, hnj, hrest⟩
    refine ⟨hj, hnot, ?_, ?_, ih hrest
      (fun x hx => hp x (List.mem_cons_of_mem j hx))
      (fun x hx => hn x (List.mem_cons_of_mem j hx))⟩
    · rw [hp j List.mem_cons_self, hpj]
    · rw [hn j List.mem_cons_self, hnj]

theorem IsDLChain.congr {n_max head head' : ℕ} {prev prev' next next' : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) (hh : head' = head)
    (hp : ∀ x ∈ L, prev' x = prev x) (hn : ∀ x ∈ L, next' x = next x) :
    IsDLChain n_max head' prev' next' L :=
  ⟨hh.trans h.1, h.2.congr hp hn⟩

theorem IsDLChainAux.lt_cap_of_mem {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L) {x : ℕ} (hx : x ∈ L) :
    x < effBucketCap n_max := by
  induction L generalizing prev_ptr with
  | nil => contradiction
  | cons j rest ih =>
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact h.1
    · exact ih h.2.2.2.2 hmem

theorem IsDLChain.lt_cap_of_mem {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) {x : ℕ} (hx : x ∈ L) :
    x < effBucketCap n_max :=
  h.2.lt_cap_of_mem hx

theorem IsDLChainAux.nodup {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L) : L.Nodup := by
  induction L generalizing prev_ptr with
  | nil => exact List.nodup_nil
  | cons j rest ih =>
    exact List.nodup_cons.mpr ⟨h.2.1, ih h.2.2.2.2⟩

theorem IsDLChain.nodup {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) : L.Nodup :=
  h.2.nodup

theorem IsDLChain.head_le_cap {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) :
    head ≤ effBucketCap n_max := by
  rcases L with _ | ⟨j, rest⟩
  · simp [IsDLChain] at h; omega
  · have hj : j < effBucketCap n_max := h.2.1
    have hhead : head = j + 1 := h.1
    omega

theorem IsDLChain.head_sub_one_mem {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) (hpos : 0 < head) :
    head - 1 ∈ L ∧ head - 1 < effBucketCap n_max := by
  rcases L with _ | ⟨j, rest⟩
  · have : head = 0 := h.1
    omega
  · have hhead : head = j + 1 := h.1
    have hj : j < effBucketCap n_max := h.2.1
    refine ⟨?_, by omega⟩
    rw [show head - 1 = j by omega]
    exact List.mem_cons_self

theorem IsDLChainAux.prev_pos_of_mem {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L) (hpos : 0 < prev_ptr)
    {x : ℕ} (hx : x ∈ L) :
    0 < prev x ∧ (prev x = prev_ptr ∨ prev x - 1 ∈ L) := by
  induction L generalizing prev_ptr with
  | nil => contradiction
  | cons j rest ih =>
    rcases h with ⟨_, _, hpj, _, hrest⟩
    rcases List.mem_cons.mp hx with rfl | hmem
    · rw [hpj]
      exact ⟨hpos, Or.inl rfl⟩
    · obtain ⟨hp_pos, hp_or⟩ := ih hrest (by omega) hmem
      refine ⟨hp_pos, ?_⟩
      rcases hp_or with hpeq | hpmem
      · right
        rw [hpeq, Nat.add_sub_cancel]
        exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem j hpmem)

theorem IsDLChainAux.prev_sub_one_mem {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L)
    {x : ℕ} (hx : x ∈ L) (_hpos : 0 < prev x) :
    prev x = prev_ptr ∨ prev x - 1 ∈ L := by
  induction L generalizing prev_ptr with
  | nil => contradiction
  | cons j rest _ =>
    rcases h with ⟨_, _, hpj, _, hrest⟩
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact Or.inl hpj
    · obtain ⟨_, hp_or⟩ := hrest.prev_pos_of_mem (by omega) hmem
      rcases hp_or with hpeq | hpmem
      · right
        rw [hpeq, Nat.add_sub_cancel]
        exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem j hpmem)

theorem IsDLChainAux.next_sub_one_mem {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L)
    {x : ℕ} (hx : x ∈ L) (hpos : 0 < next x) :
    next x - 1 ∈ L ∧ next x - 1 ≠ x := by
  induction L generalizing prev_ptr with
  | nil => contradiction
  | cons j rest ih =>
    rcases h with ⟨_, hnot, _, hnj, hrest⟩
    rcases List.mem_cons.mp hx with rfl | hmem
    · rcases rest with _ | ⟨j₁, rest'⟩
      · simp at hnj; omega
      · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hnj
        have heq : next x - 1 = j₁ := by omega
        rw [heq]
        exact ⟨List.mem_cons_of_mem x List.mem_cons_self,
          fun h_eq => hnot (h_eq ▸ List.mem_cons_self)⟩
    · obtain ⟨hn_mem, hn_ne⟩ := ih hrest hmem
      exact ⟨List.mem_cons_of_mem j hn_mem, hn_ne⟩

theorem IsDLChain.prev_le_cap {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) {x : ℕ} (hx : x ∈ L) :
    prev x ≤ effBucketCap n_max := by
  rcases Nat.eq_zero_or_pos (prev x) with hp0 | hp_pos
  · omega
  · rcases h.2.prev_sub_one_mem hx hp_pos with hpeq | hpmem
    · omega
    · have := h.lt_cap_of_mem hpmem
      omega

theorem IsDLChain.next_le_cap {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) {x : ℕ} (hx : x ∈ L) :
    next x ≤ effBucketCap n_max := by
  rcases Nat.eq_zero_or_pos (next x) with hn0 | hn_pos
  · omega
  · obtain ⟨hn_mem, _⟩ := h.2.next_sub_one_mem hx hn_pos
    have := h.lt_cap_of_mem hn_mem
    omega

/-- Prepending `j_new ∉ L` establishes `IsDLChain` on `j_new :: L`. -/
theorem isDLChain_prepend {n_max head j_new : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L)
    (hj_cap : j_new < effBucketCap n_max) (hj_not : j_new ∉ L) :
    let prev₁ := Function.update prev j_new 0
    let next' := Function.update next j_new head
    let prev' := if 0 < head then Function.update prev₁ (head - 1) (j_new + 1) else prev₁
    IsDLChain n_max (j_new + 1) prev' next' (j_new :: L) := by
  intro prev₁ next' prev'
  rcases h with ⟨hhead, haux⟩
  refine ⟨rfl, hj_cap, hj_not, ?_, ?_, ?_⟩
  · dsimp only [prev', prev₁]
    split_ifs with hpos
    · rcases L with _ | ⟨j₀, rest⟩
      · simp at hhead; omega
      · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hhead
        have hne : j_new ≠ head - 1 := by
          intro heq
          apply hj_not
          rw [heq, hhead, Nat.add_sub_cancel]
          exact List.mem_cons_self
        rw [Function.update_of_ne hne, Function.update_self]
    · rw [Function.update_self]
  · dsimp only [next']
    rw [Function.update_self, hhead]
  · rcases L with _ | ⟨j₀, rest⟩
    · trivial
    · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hhead
      have hpos : 0 < head := by omega
      have hsub : head - 1 = j₀ := by omega
      rcases haux with ⟨hj₀_cap, hj₀_not, _, hnj₀, hrest⟩
      have hne_new_0 : j₀ ≠ j_new := fun heq => hj_not (heq ▸ List.mem_cons_self)
      refine ⟨hj₀_cap, hj₀_not, ?_, ?_, ?_⟩
      · dsimp only [prev', prev₁]
        rw [ite_eq_left hpos, hsub, Function.update_self]
      · dsimp only [next']
        rw [Function.update_of_ne hne_new_0, hnj₀]
      · refine hrest.congr (fun x hx => ?_) (fun x hx => ?_)
        · have hx_ne_0 : x ≠ j₀ := fun heq => hj₀_not (heq ▸ hx)
          have hx_ne_new : x ≠ j_new := fun heq => hj_not (List.mem_cons_of_mem j₀ (heq ▸ hx))
          dsimp only [prev', prev₁]
          rw [ite_eq_left hpos, hsub, Function.update_of_ne hx_ne_0,
            Function.update_of_ne hx_ne_new]
        · have hx_ne_new : x ≠ j_new := fun heq => hj_not (List.mem_cons_of_mem j₀ (heq ▸ hx))
          dsimp only [next']
          rw [Function.update_of_ne hx_ne_new]

/-- Unlinking the head element of `j_del :: rest` establishes `IsDLChainAux` on `rest`. -/
private theorem isDLChainAux_erase_head {n_max prev_ptr j_del : ℕ} {prev next : ℕ → ℕ}
    {rest : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next (j_del :: rest))
    (hprev_not : ∀ x ∈ j_del :: rest, x + 1 ≠ prev_ptr) :
    let p := prev j_del
    let n := next j_del
    let next' := if 0 < p then Function.update next (p - 1) n else next
    let prev' := if 0 < n then Function.update prev (n - 1) p else prev
    IsDLChainAux n_max prev_ptr prev' next' rest := by
  intro p n next' prev'
  rcases h with ⟨_, hnot, hp, hn, hrest⟩
  have hnext_rest : ∀ x ∈ rest, next' x = next x := by
    intro x hx
    dsimp only [next']
    split_ifs with hp_pos
    · rw [Function.update_of_ne]
      intro heq
      apply hprev_not x (List.mem_cons_of_mem j_del hx)
      dsimp only [p] at hp_pos ⊢
      omega
    · rfl
  rcases rest with _ | ⟨j₁, rest'⟩
  · trivial
  · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hn
    have hn_pos : 0 < n := by dsimp only [n]; omega
    have hn_sub : n - 1 = j₁ := by dsimp only [n]; omega
    rcases hrest with ⟨hj₁_cap, hj₁_not, _, hnj₁, hrest'⟩
    refine ⟨hj₁_cap, hj₁_not, ?_, ?_, ?_⟩
    · dsimp only [prev', p]
      rw [ite_eq_left hn_pos, hn_sub, Function.update_self, hp]
    · rw [hnext_rest j₁ List.mem_cons_self, hnj₁]
    · refine hrest'.congr (fun x hx => ?_)
        (fun x hx => hnext_rest x (List.mem_cons_of_mem j₁ hx))
      have hx_ne : x ≠ j₁ := fun heq => hj₁_not (heq ▸ hx)
      dsimp only [prev']
      rw [ite_eq_left hn_pos, hn_sub, Function.update_of_ne hx_ne]

/-- Unlinking `j_del ∈ L` establishes `IsDLChainAux` on `L.erase j_del`. -/
theorem isDLChainAux_erase {n_max prev_ptr j_del : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L)
    (hmem : j_del ∈ L)
    (hprev_not : ∀ x ∈ L, x + 1 ≠ prev_ptr) :
    let p := prev j_del
    let n := next j_del
    let next' := if 0 < p then Function.update next (p - 1) n else next
    let prev' := if 0 < n then Function.update prev (n - 1) p else prev
    IsDLChainAux n_max prev_ptr prev' next' (L.erase j_del) := by
  induction L generalizing prev_ptr with
  | nil => contradiction
  | cons j rest ih =>
    by_cases hjeq : j = j_del
    · subst hjeq
      rw [List.erase_cons_head]
      exact isDLChainAux_erase_head h hprev_not
    · have hj_ne : ¬(j == j_del) = true := by simp [hjeq]
      rw [List.erase_cons_tail hj_ne]
      have hmem_rest : j_del ∈ rest := (List.mem_cons.mp hmem).resolve_left (Ne.symm hjeq)
      rcases h with ⟨hj_cap, hj_not, hpj, hnj, hrest⟩
      obtain ⟨hp_pos, hp_or⟩ := hrest.prev_pos_of_mem (by omega) hmem_rest
      have hprev_j : (if 0 < next j_del then
          Function.update prev (next j_del - 1) (prev j_del) else prev) j = prev_ptr := by
        split_ifs with hn_pos
        · obtain ⟨hn_mem, _⟩ := hrest.next_sub_one_mem hmem_rest hn_pos
          have hne : j ≠ next j_del - 1 := fun heq => hj_not (heq ▸ hn_mem)
          rw [Function.update_of_ne hne, hpj]
        · exact hpj
      have hnot_erase : j ∉ rest.erase j_del :=
        fun hx => hj_not (List.mem_of_mem_erase hx)
      have hprev_not' : ∀ x ∈ rest, x + 1 ≠ j + 1 :=
        fun x hx heq => hj_not (Nat.succ.inj heq ▸ hx)
      refine ⟨hj_cap, hnot_erase, hprev_j, ?_, ih hrest hmem_rest hprev_not'⟩
      rcases rest with _ | ⟨j₁, rest'⟩
      · contradiction
      · by_cases hj1 : j₁ = j_del
        · rw [hj1, List.erase_cons_head]
          have hp_eq : prev j_del = j + 1 := hj1 ▸ hrest.2.2.1
          have hn_eq : next j_del = (rest'.head?.map (· + 1)).getD 0 := hj1 ▸ hrest.2.2.2.1
          rw [ite_eq_left hp_pos, hp_eq, Nat.add_sub_cancel, Function.update_self, hn_eq]
        · have hj1_ne : ¬(j₁ == j_del) = true := by simp [hj1]
          rw [List.erase_cons_tail hj1_ne]
          have hmem_rest' : j_del ∈ rest' :=
            (List.mem_cons.mp hmem_rest).resolve_left (Ne.symm hj1)
          obtain ⟨_, hp_or'⟩ := hrest.2.2.2.2.prev_pos_of_mem (by omega) hmem_rest'
          have hp_ne_j : j ≠ prev j_del - 1 := by
            intro heq
            apply hj_not
            rw [heq]
            rcases hp_or' with hpeq | hpmem
            · rw [hpeq, Nat.add_sub_cancel]
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem j₁ hpmem
          rw [ite_eq_left hp_pos, Function.update_of_ne hp_ne_j, hnj]
          rfl

/-- Unlinking `j_del ∈ L` establishes `IsDLChain` on `L.erase j_del`. -/
theorem isDLChain_unlink {n_max head j_del : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) (hmem : j_del ∈ L) :
    let p := prev j_del
    let n := next j_del
    let head' := if 0 < p then head else n
    let next' := if 0 < p then Function.update next (p - 1) n else next
    let prev' := if 0 < n then Function.update prev (n - 1) p else prev
    IsDLChain n_max head' prev' next' (L.erase j_del) := by
  intro p n head' next' prev'
  rcases h with ⟨hhead, haux⟩
  refine ⟨?_, isDLChainAux_erase haux hmem (fun x _ => Nat.succ_ne_zero x)⟩
  rcases L with _ | ⟨j₀, rest⟩
  · contradiction
  · by_cases hj0 : j₀ = j_del
    · subst hj0
      rw [List.erase_cons_head]
      have hp0 : p = 0 := haux.2.2.1
      have hn0 : n = (rest.head?.map (· + 1)).getD 0 := haux.2.2.2.1
      dsimp only [head']
      rw [hp0, ite_eq_right (by omega), hn0]
    · have hj0_ne : ¬(j₀ == j_del) = true := by simp [hj0]
      rw [List.erase_cons_tail hj0_ne]
      have hmem_rest : j_del ∈ rest := (List.mem_cons.mp hmem).resolve_left (Ne.symm hj0)
      obtain ⟨hp_pos, _⟩ := haux.2.2.2.2.prev_pos_of_mem (by omega) hmem_rest
      dsimp only [head']
      rw [ite_eq_left hp_pos, hhead]
      rfl

/-- Parameter-free `Memory.Prog` operation prepending local slot `j_new = d.2.2` to micro-bucket
chain `(b, m) = (d.2.1.1.2, d.2.1.2)` at `base = d.2.1.1.1`. -/
def lmPrependGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let old_h ← readLMHeadGenProg (d.1, d.2.1)
  let z ← pure 0
  let ptr_new ← pure (d.2.2 + 1)
  writeLMPrevGenProg (d.1, ((d.2.1.1, d.2.2), z))
  writeLMNextGenProg (d.1, ((d.2.1.1, d.2.2), old_h))
  if z < old_h then do
    let old_idx ← pure (old_h - 1)
    writeLMPrevGenProg (d.1, ((d.2.1.1, old_idx), ptr_new))
    writeLMHeadGenProg (d.1, (d.2.1, ptr_new))
  else
    writeLMHeadGenProg (d.1, (d.2.1, ptr_new))

/-- `Memory.Prog` operation prepending local slot `j_new = d.2` to micro-bucket chain
`(b, m) = (d.1.1.2, d.1.2)` at `base = d.1.1.1`. -/
@[expose]
def lmPrependProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let old_h ← readLMHeadProg U V w n_max h_space d.1
  let z ← pure 0
  let ptr_new ← pure (d.2 + 1)
  writeLMPrevProg U V w n_max h_space ((d.1.1, d.2), z)
  writeLMNextProg U V w n_max h_space ((d.1.1, d.2), old_h)
  if z < old_h then do
    let old_idx ← pure (old_h - 1)
    writeLMPrevProg U V w n_max h_space ((d.1.1, old_idx), ptr_new)
    writeLMHeadProg U V w n_max h_space (d.1, ptr_new)
  else
    writeLMHeadProg U V w n_max h_space (d.1, ptr_new)

@[simp]
theorem lmPrependGenProg_mk (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    lmPrependGenProg (mkDictParams U V w n_max h_space, d) =
      lmPrependProg U V w n_max h_space d := by
  unfold lmPrependGenProg lmPrependProg
  simp only [readLMHeadGenProg_mk, writeLMPrevGenProg_mk, writeLMNextGenProg_mk,
    writeLMHeadGenProg_mk]

@[simp]
theorem memoryCost_lmPrependProg_le (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (lmPrependProg U V w n_max h_space d) s ≤ 18 := by
  unfold lmPrependProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readLMHeadProg, memoryCost_writeLMPrevProg, memoryCost_writeLMNextProg]
  split_ifs
  · simp only [memoryCost_bind, memoryCost_writeLMPrevProg, memoryCost_writeLMHeadProg]
    omega
  · simp only [memoryCost_writeLMHeadProg]
    omega

/-- Precondition for `lmPrependProg` in `Realizes`. -/
@[expose]
def LMPrependPre (U V w₀ n_max h_space w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1 ∧
  d.1.1.2 < numBuckets n_max ∧
  d.1.2 < numMicroPerBucket n_max ∧
  d.2 < effBucketCap n_max ∧
  d.2 < n_max ∧
  lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.1.2 ≤ effBucketCap n_max

/-- Parameter-free precondition for `lmPrependGenProg`. -/
@[expose]
def LMPrependGenPre (w : ℕ) (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1.1 ∧
  d.2.1.1.2 < numBuckets (dpNMax d.1) ∧
  d.2.1.2 < numMicroPerBucket (dpNMax d.1) ∧
  d.2.2 < effBucketCap (dpNMax d.1) ∧
  d.2.2 < dpNMax d.1 ∧
  lmHead (dpNMax d.1)
    (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    d.2.1.1.2 d.2.1.2 ≤ effBucketCap (dpNMax d.1)

@[simp]
theorem lmPrependGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    LMPrependGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      LMPrependPre U V w₀ n_max h_space w d s := Iff.rfl

/-- The length of any chain satisfying `IsDLChainAux` is at most `effBucketCap n_max`. -/
theorem IsDLChainAux.length_le {n_max prev_ptr : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChainAux n_max prev_ptr prev next L) :
    L.length ≤ effBucketCap n_max := by
  rw [← List.toFinset_card_of_nodup h.nodup, ← Finset.card_range (effBucketCap n_max)]
  refine Finset.card_le_card fun j hj => Finset.mem_range.mpr ?_
  exact h.lt_cap_of_mem (List.mem_toFinset.mp hj)

/-- The length of any chain satisfying `IsDLChain` is at most `effBucketCap n_max`. -/
theorem IsDLChain.length_le {n_max head : ℕ} {prev next : ℕ → ℕ} {L : List ℕ}
    (h : IsDLChain n_max head prev next L) :
    L.length ≤ effBucketCap n_max :=
  h.2.length_le

theorem realizes_lmPrependGen :
    Realizes .exact lmPrependGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      LMPrependGenPre
      (fun _ _ => 0) := by
  have hrh := realizes_readLMHeadGen
  have hwh := realizes_writeLMHeadGen
  have hwp := realizes_writeLMPrevGen
  have hwn := realizes_writeLMNextGen
  realizeDictWith [lmPrependGenPre_mk, LMPrependPre, readLMHeadGenProg_mk, writeLMHeadGenProg_mk,
    writeLMPrevGenProg_mk, writeLMNextGenProg_mk]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact fits_of_le_max_n_one h.1 hw hnU hU (by have := h.2.2.2.2.1; omega)
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.1
  · omega
  · exact h.1
  · exact h.2.1
  · have hh : (Memory.spec 0).clientResult s (readLMHeadProg U V w₀ n_max h_space d.1) =
        lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.1.2 :=
      clientResult_readLMHeadProg s h.2.1 h.2.2.1
    rw [hh] at hc ⊢
    have := h.2.2.2.2.2
    omega
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1

/-- Pure state effect of `lmPrependProg`. -/
theorem lmPrependProg_effect {U V w n_max h_space base b m j_new : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hj : j_new < effBucketCap n_max) (hj_n : j_new < n_max)
    {s : Memory.State}
    (hold : lmHead n_max (lmAt base U V w n_max h_space s.mem) b m ≤ effBucketCap n_max) :
    let old_h := lmHead n_max (lmAt base U V w n_max h_space s.mem) b m
    let s' := (Memory.spec 0).clientState s
      (lmPrependProg U V w n_max h_space (((base, b), m), j_new))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max,
      lmHead n_max (lmAt base U V w n_max h_space s'.mem) b' m' =
        if b' = b ∧ m' = m then j_new + 1
        else lmHead n_max (lmAt base U V w n_max h_space s.mem) b' m') ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      lmNext n_max (lmAt base U V w n_max h_space s'.mem) b' j' =
        if b' = b then
          Function.update (lmNext n_max (lmAt base U V w n_max h_space s.mem) b) j_new old_h j'
        else lmNext n_max (lmAt base U V w n_max h_space s.mem) b' j') ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      lmPrev n_max (lmAt base U V w n_max h_space s'.mem) b' j' =
        if b' = b then
          (if 0 < old_h then
            Function.update
              (Function.update (lmPrev n_max (lmAt base U V w n_max h_space s.mem) b) j_new 0)
              (old_h - 1) (j_new + 1)
          else
            Function.update (lmPrev n_max (lmAt base U V w n_max h_space s.mem) b) j_new 0) j'
        else lmPrev n_max (lmAt base U V w n_max h_space s.mem) b' j') := by
  intro old_h s'
  have hval_lt : j_new + 1 < 2 ^ effBucketPosBits n_max :=
    (Nat.succ_le_of_lt (lt_min hj_n hj)).trans_lt
      (min_effBucketCap_lt_two_pow_effBucketPosBits n_max)
  have h0_lt : 0 < 2 ^ effBucketPosBits n_max := Nat.two_pow_pos _
  -- Step 1: writeLMPrevProg j_new := 0
  let s₁ := (Memory.spec 0).clientState s
    (writeLMPrevProg U V w n_max h_space (((base, b), j_new), 0))
  have eff₁ := writeLMPrevProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := base) (b := b) (j := j_new) (val := 0) hw hb hj h0_lt s
  have hold_lt : old_h < 2 ^ effBucketPosBits n_max :=
    lmAt_lt base U V w n_max h_space s.mem (0, b * numMicroPerBucket n_max + m)
  -- Step 2: writeLMNextProg j_new := old_h
  let s₂ := (Memory.spec 0).clientState s₁
    (writeLMNextProg U V w n_max h_space (((base, b), j_new), old_h))
  have eff₂ := writeLMNextProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
    (h_space := h_space) (base := base) (b := b) (j := j_new) (val := old_h) hw hb hj hold_lt s₁
  have hs'_def : s' = (if 0 < old_h then
      (Memory.spec 0).clientState
        ((Memory.spec 0).clientState s₂
          (writeLMPrevProg U V w n_max h_space (((base, b), old_h - 1), j_new + 1)))
        (writeLMHeadProg U V w n_max h_space (((base, b), m), j_new + 1))
    else
      (Memory.spec 0).clientState s₂
        (writeLMHeadProg U V w n_max h_space (((base, b), m), j_new + 1))) := by
    dsimp only [s', s₂, s₁, old_h]
    unfold lmPrependProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readLMHeadProg,
      clientResult_readLMHeadProg _ hb hm,
      StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]
    split_ifs
    · rw [StateTransitionSpec.clientState_bind]
    · rfl
  rw [hs'_def]
  split_ifs with hpos
  · have hold_idx : old_h - 1 < effBucketCap n_max := by omega
    let s₃ := (Memory.spec 0).clientState s₂
      (writeLMPrevProg U V w n_max h_space (((base, b), old_h - 1), j_new + 1))
    have eff₃ := writeLMPrevProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (j := old_h - 1) (val := j_new + 1)
      hw hb hold_idx hval_lt s₂
    have eff₄ := writeLMHeadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (val := j_new + 1)
      hw hb hm hval_lt s₃
    refine ⟨by rw [eff₄.1, eff₃.1, eff₂.1, eff₁.1],
      fun a ha => by rw [eff₄.2.1 a ha, eff₃.2.1 a ha, eff₂.2.1 a ha, eff₁.2.1 a ha],
      by rw [eff₄.2.2.1, eff₃.2.2.1, eff₂.2.2.1, eff₁.2.2.1],
      by rw [eff₄.2.2.2.1, eff₃.2.2.2.1, eff₂.2.2.2.1, eff₁.2.2.2.1],
      by rw [eff₄.2.2.2.2.1, eff₃.2.2.2.2.1, eff₂.2.2.2.2.1, eff₁.2.2.2.2.1],
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · by_cases hbm : b' = b ∧ m' = m
      · rcases hbm with ⟨rfl, rfl⟩
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact eff₄.2.2.2.2.2.1
      · rw [ite_eq_right hbm, eff₄.2.2.2.2.2.2.1 b' hb' m' hm' (not_and_or.mp hbm),
          eff₃.2.2.2.2.2.1, eff₂.2.2.2.2.2.1, eff₁.2.2.2.2.2.1]
    · rw [eff₄.2.2.2.2.2.2.2.2, eff₃.2.2.2.2.2.2.2.2]
      by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_eq : j' = j_new
        · subst hj_eq
          rw [Function.update_self]
          exact eff₂.2.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_eq, eff₂.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inr hj_eq),
            eff₁.2.2.2.2.2.2.2.2]
      · rw [ite_eq_right hb_eq, eff₂.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inl hb_eq),
          eff₁.2.2.2.2.2.2.2.2]
    · rw [eff₄.2.2.2.2.2.2.2.1]
      by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_old : j' = old_h - 1
        · subst hj_old
          rw [Function.update_self]
          exact eff₃.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_old, eff₃.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inr hj_old),
            eff₂.2.2.2.2.2.2.1]
          by_cases hj_new : j' = j_new
          · subst hj_new
            rw [Function.update_self]
            exact eff₁.2.2.2.2.2.2.1
          · rw [Function.update_of_ne hj_new]
            exact eff₁.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inr hj_new)
      · rw [ite_eq_right hb_eq, eff₃.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inl hb_eq),
          eff₂.2.2.2.2.2.2.1, eff₁.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inl hb_eq)]
  · have eff₄ := writeLMHeadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (val := j_new + 1)
      hw hb hm hval_lt s₂
    refine ⟨by rw [eff₄.1, eff₂.1, eff₁.1],
      fun a ha => by rw [eff₄.2.1 a ha, eff₂.2.1 a ha, eff₁.2.1 a ha],
      by rw [eff₄.2.2.1, eff₂.2.2.1, eff₁.2.2.1],
      by rw [eff₄.2.2.2.1, eff₂.2.2.2.1, eff₁.2.2.2.1],
      by rw [eff₄.2.2.2.2.1, eff₂.2.2.2.2.1, eff₁.2.2.2.2.1],
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · by_cases hbm : b' = b ∧ m' = m
      · rcases hbm with ⟨rfl, rfl⟩
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact eff₄.2.2.2.2.2.1
      · rw [ite_eq_right hbm, eff₄.2.2.2.2.2.2.1 b' hb' m' hm' (not_and_or.mp hbm),
          eff₂.2.2.2.2.2.1, eff₁.2.2.2.2.2.1]
    · rw [eff₄.2.2.2.2.2.2.2.2]
      by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_eq : j' = j_new
        · subst hj_eq
          rw [Function.update_self]
          exact eff₂.2.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_eq, eff₂.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inr hj_eq),
            eff₁.2.2.2.2.2.2.2.2]
      · rw [ite_eq_right hb_eq, eff₂.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inl hb_eq),
          eff₁.2.2.2.2.2.2.2.2]
    · rw [eff₄.2.2.2.2.2.2.2.1, eff₂.2.2.2.2.2.2.1]
      by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_new : j' = j_new
        · subst hj_new
          rw [Function.update_self]
          exact eff₁.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_new]
          exact eff₁.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inr hj_new)
      · rw [ite_eq_right hb_eq]
        exact eff₁.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inl hb_eq)

/-- Parameter-free `Memory.Prog` operation unlinking local slot `j_del = d.2.2` from micro-bucket
chain `(b, m) = (d.2.1.1.2, d.2.1.2)` at `base = d.2.1.1.1`. -/
def lmUnlinkGenProg (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog Unit := do
  let p ← readLMPrevGenProg (d.1, (d.2.1.1, d.2.2))
  let n ← readLMNextGenProg (d.1, (d.2.1.1, d.2.2))
  let z ← pure 0
  if z < p then do
    let p_idx ← pure (p - 1)
    writeLMNextGenProg (d.1, ((d.2.1.1, p_idx), n))
  else
    writeLMHeadGenProg (d.1, (d.2.1, n))
  if z < n then do
    let n_idx ← pure (n - 1)
    writeLMPrevGenProg (d.1, ((d.2.1.1, n_idx), p))
  else
    pure ()

/-- `Memory.Prog` operation unlinking local slot `j_del = d.2` from micro-bucket chain
`(b, m) = (d.1.1.2, d.1.2)` at `base = d.1.1.1`. -/
@[expose]
def lmUnlinkProg (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog Unit := do
  let p ← readLMPrevProg U V w n_max h_space (d.1.1, d.2)
  let n ← readLMNextProg U V w n_max h_space (d.1.1, d.2)
  let z ← pure 0
  if z < p then do
    let p_idx ← pure (p - 1)
    writeLMNextProg U V w n_max h_space ((d.1.1, p_idx), n)
  else
    writeLMHeadProg U V w n_max h_space (d.1, n)
  if z < n then do
    let n_idx ← pure (n - 1)
    writeLMPrevProg U V w n_max h_space ((d.1.1, n_idx), p)
  else
    pure ()

@[simp]
theorem lmUnlinkGenProg_mk (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    lmUnlinkGenProg (mkDictParams U V w n_max h_space, d) =
      lmUnlinkProg U V w n_max h_space d := by
  unfold lmUnlinkGenProg lmUnlinkProg
  simp only [readLMPrevGenProg_mk, readLMNextGenProg_mk, writeLMNextGenProg_mk,
    writeLMHeadGenProg_mk, writeLMPrevGenProg_mk]

@[simp]
theorem memoryCost_lmUnlinkProg_le (U V w n_max h_space : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ)
    (s : Memory.State) :
    memoryCost (lmUnlinkProg U V w n_max h_space d) s ≤ 12 := by
  unfold lmUnlinkProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readLMPrevProg, memoryCost_readLMNextProg]
  split_ifs <;>
    simp only [memoryCost_bind, memoryCost_writeLMNextProg, memoryCost_writeLMHeadProg,
      memoryCost_writeLMPrevProg, memoryCost_pure] <;>
    omega

/-- Precondition for `lmUnlinkProg` in `Realizes`. -/
@[expose]
def LMUnlinkPre (U V w₀ n_max h_space w : ℕ) (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1 ∧
  d.1.1.2 < numBuckets n_max ∧
  d.1.2 < numMicroPerBucket n_max ∧
  d.2 < effBucketCap n_max ∧
  lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 ≤ effBucketCap n_max ∧
  lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 ≤ effBucketCap n_max

/-- Parameter-free precondition for `lmUnlinkGenProg`. -/
@[expose]
def LMUnlinkGenPre (w : ℕ) (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1.1 ∧
  d.2.1.1.2 < numBuckets (dpNMax d.1) ∧
  d.2.1.2 < numMicroPerBucket (dpNMax d.1) ∧
  d.2.2 < effBucketCap (dpNMax d.1) ∧
  lmPrev (dpNMax d.1)
    (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    d.2.1.1.2 d.2.2 ≤ effBucketCap (dpNMax d.1) ∧
  lmNext (dpNMax d.1)
    (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
    d.2.1.1.2 d.2.2 ≤ effBucketCap (dpNMax d.1)

@[simp]
theorem lmUnlinkGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    LMUnlinkGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      LMUnlinkPre U V w₀ n_max h_space w d s := Iff.rfl

theorem realizes_lmUnlinkGen :
    Realizes .exact lmUnlinkGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := Unit))
      LMUnlinkGenPre
      (fun _ _ => 0) := by
  have hrp := realizes_readLMPrevGen
  have hrn := realizes_readLMNextGen
  have hwh := realizes_writeLMHeadGen
  have hwp := realizes_writeLMPrevGen
  have hwn := realizes_writeLMNextGen
  realizeDictWith [lmUnlinkGenPre_mk, LMUnlinkPre, readLMPrevGenProg_mk, readLMNextGenProg_mk,
    writeLMHeadGenProg_mk, writeLMPrevGenProg_mk, writeLMNextGenProg_mk]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.1
  · omega
  · exact h.1
  · exact h.2.1
  · have hp : (Memory.spec 0).clientResult s (readLMPrevProg U V w₀ n_max h_space (d.1.1, d.2)) =
        lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 :=
      clientResult_readLMPrevProg s h.2.1 h.2.2.2.1
    rw [hp] at hc ⊢
    have := h.2.2.2.2.1
    omega
  · omega
  · exact h.1
  · exact h.2.1
  · have hn : (Memory.spec 0).clientResult s (readLMNextProg U V w₀ n_max h_space (d.1.1, d.2)) =
        lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 :=
      clientResult_readLMNextProg s h.2.1 h.2.2.2.1
    rw [clientState_readLMPrevProg] at hc ⊢
    rw [hn] at hc ⊢
    have := h.2.2.2.2.2
    omega
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · omega
  · exact h.1
  · exact h.2.1
  · have hn : (Memory.spec 0).clientResult s (readLMNextProg U V w₀ n_max h_space (d.1.1, d.2)) =
        lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2 :=
      clientResult_readLMNextProg s h.2.1 h.2.2.2.1
    rw [clientState_readLMPrevProg] at hc ⊢
    rw [hn] at hc ⊢
    have := h.2.2.2.2.2
    omega

/-- Pure state effect of `lmUnlinkProg`. -/
theorem lmUnlinkProg_effect {U V w n_max h_space base b m j_del : ℕ}
    (hw : 0 < w) (hb : b < numBuckets n_max) (hm : m < numMicroPerBucket n_max)
    (hj : j_del < effBucketCap n_max) {s : Memory.State}
    (hp_le : lmPrev n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max)
    (hn_le : lmNext n_max (lmAt base U V w n_max h_space s.mem) b j_del ≤ effBucketCap n_max) :
    let p := lmPrev n_max (lmAt base U V w n_max h_space s.mem) b j_del
    let n := lmNext n_max (lmAt base U V w n_max h_space s.mem) b j_del
    let s' := (Memory.spec 0).clientState s
      (lmUnlinkProg U V w n_max h_space (((base, b), m), j_del))
    s'.frontier = s.frontier ∧
    (∀ a, ¬(base + offLM U V w n_max h_space ≤ a ∧ a < base + offGM U V w n_max h_space) →
      s'.mem a = s.mem a) ∧
    quotAt base U w n_max h_space s'.mem = quotAt base U w n_max h_space s.mem ∧
    valAt base U V w n_max h_space s'.mem = valAt base U V w n_max h_space s.mem ∧
    gmAt base U V w n_max h_space s'.mem = gmAt base U V w n_max h_space s.mem ∧
    (∀ b' < numBuckets n_max, ∀ m' < numMicroPerBucket n_max,
      lmHead n_max (lmAt base U V w n_max h_space s'.mem) b' m' =
        if b' = b ∧ m' = m then
          if 0 < p then lmHead n_max (lmAt base U V w n_max h_space s.mem) b m else n
        else lmHead n_max (lmAt base U V w n_max h_space s.mem) b' m') ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      lmNext n_max (lmAt base U V w n_max h_space s'.mem) b' j' =
        if b' = b then
          (if 0 < p then
            Function.update (lmNext n_max (lmAt base U V w n_max h_space s.mem) b) (p - 1) n
          else lmNext n_max (lmAt base U V w n_max h_space s.mem) b) j'
        else lmNext n_max (lmAt base U V w n_max h_space s.mem) b' j') ∧
    (∀ b' < numBuckets n_max, ∀ j' < effBucketCap n_max,
      lmPrev n_max (lmAt base U V w n_max h_space s'.mem) b' j' =
        if b' = b then
          (if 0 < n then
            Function.update (lmPrev n_max (lmAt base U V w n_max h_space s.mem) b) (n - 1) p
          else lmPrev n_max (lmAt base U V w n_max h_space s.mem) b) j'
        else lmPrev n_max (lmAt base U V w n_max h_space s.mem) b' j') := by
  intro p n s'
  have hp_lt : p < 2 ^ effBucketPosBits n_max :=
    lmAt_lt base U V w n_max h_space s.mem (1 + j_del % 4, b * numMicroPerBucket n_max + j_del / 4)
  have hn_lt : n < 2 ^ effBucketPosBits n_max :=
    lmAt_lt base U V w n_max h_space s.mem (5 + j_del % 4, b * numMicroPerBucket n_max + j_del / 4)
  have hs'_def : s' =
      (if 0 < p then
         if 0 < n then
           (Memory.spec 0).clientState
             ((Memory.spec 0).clientState s
               (writeLMNextProg U V w n_max h_space (((base, b), p - 1), n)))
             (writeLMPrevProg U V w n_max h_space (((base, b), n - 1), p))
         else
           (Memory.spec 0).clientState s
             (writeLMNextProg U V w n_max h_space (((base, b), p - 1), n))
       else
         if 0 < n then
           (Memory.spec 0).clientState
             ((Memory.spec 0).clientState s
               (writeLMHeadProg U V w n_max h_space (((base, b), m), n)))
             (writeLMPrevProg U V w n_max h_space (((base, b), n - 1), p))
         else
           (Memory.spec 0).clientState s
             (writeLMHeadProg U V w n_max h_space (((base, b), m), n))) := by
    dsimp only [s', p, n]
    unfold lmUnlinkProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readLMPrevProg,
      clientResult_readLMPrevProg _ hb hj,
      StateTransitionSpec.clientState_bind, clientState_readLMNextProg,
      clientResult_readLMNextProg _ hb hj]
    split_ifs <;>
      rw [StateTransitionSpec.clientState_bind] <;>
      rfl
  rw [hs'_def]
  split_ifs with hp_pos hn_pos hn_pos
  · have hp_idx : p - 1 < effBucketCap n_max := by omega
    have hn_idx : n - 1 < effBucketCap n_max := by omega
    let s₁ := (Memory.spec 0).clientState s
      (writeLMNextProg U V w n_max h_space (((base, b), p - 1), n))
    have eff₁ := writeLMNextProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (j := p - 1) (val := n) hw hb hp_idx hn_lt s
    have eff₂ := writeLMPrevProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (j := n - 1) (val := p) hw hb hn_idx hp_lt s₁
    refine ⟨by rw [eff₂.1, eff₁.1],
      fun a ha => by rw [eff₂.2.1 a ha, eff₁.2.1 a ha],
      by rw [eff₂.2.2.1, eff₁.2.2.1],
      by rw [eff₂.2.2.2.1, eff₁.2.2.2.1],
      by rw [eff₂.2.2.2.2.1, eff₁.2.2.2.2.1],
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · rw [eff₂.2.2.2.2.2.1, eff₁.2.2.2.2.2.1]
      split_ifs with hbm
      · rcases hbm with ⟨rfl, rfl⟩; rfl
      · rfl
    · rw [eff₂.2.2.2.2.2.2.2.2]
      by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_p : j' = p - 1
        · subst hj_p
          rw [Function.update_self]
          exact eff₁.2.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_p]
          exact eff₁.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inr hj_p)
      · rw [ite_eq_right hb_eq]
        exact eff₁.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inl hb_eq)
    · by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_n : j' = n - 1
        · subst hj_n
          rw [Function.update_self]
          exact eff₂.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_n, eff₂.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inr hj_n),
            eff₁.2.2.2.2.2.2.1]
      · rw [ite_eq_right hb_eq, eff₂.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inl hb_eq),
          eff₁.2.2.2.2.2.2.1]
  · have hp_idx : p - 1 < effBucketCap n_max := by omega
    have eff₁ := writeLMNextProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (j := p - 1) (val := n) hw hb hp_idx hn_lt s
    refine ⟨eff₁.1, eff₁.2.1, eff₁.2.2.1, eff₁.2.2.2.1, eff₁.2.2.2.2.1,
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · rw [eff₁.2.2.2.2.2.1]
      split_ifs with hbm
      · rcases hbm with ⟨rfl, rfl⟩; rfl
      · rfl
    · by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_p : j' = p - 1
        · subst hj_p
          rw [Function.update_self]
          exact eff₁.2.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_p]
          exact eff₁.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inr hj_p)
      · rw [ite_eq_right hb_eq]
        exact eff₁.2.2.2.2.2.2.2.2 b' hb' j' hj' (Or.inl hb_eq)
    · rw [eff₁.2.2.2.2.2.2.1]
      split_ifs with hb_eq
      · subst hb_eq; rfl
      · rfl
  · have hn_idx : n - 1 < effBucketCap n_max := by omega
    let s₁ := (Memory.spec 0).clientState s
      (writeLMHeadProg U V w n_max h_space (((base, b), m), n))
    have eff₁ := writeLMHeadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (val := n) hw hb hm hn_lt s
    have eff₂ := writeLMPrevProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (j := n - 1) (val := p) hw hb hn_idx hp_lt s₁
    refine ⟨by rw [eff₂.1, eff₁.1],
      fun a ha => by rw [eff₂.2.1 a ha, eff₁.2.1 a ha],
      by rw [eff₂.2.2.1, eff₁.2.2.1],
      by rw [eff₂.2.2.2.1, eff₁.2.2.2.1],
      by rw [eff₂.2.2.2.2.1, eff₁.2.2.2.2.1],
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · rw [eff₂.2.2.2.2.2.1]
      by_cases hbm : b' = b ∧ m' = m
      · rcases hbm with ⟨rfl, rfl⟩
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact eff₁.2.2.2.2.2.1
      · rw [ite_eq_right hbm]
        exact eff₁.2.2.2.2.2.2.1 b' hb' m' hm' (not_and_or.mp hbm)
    · rw [eff₂.2.2.2.2.2.2.2.2, eff₁.2.2.2.2.2.2.2.2]
      split_ifs with hb_eq
      · subst hb_eq; rfl
      · rfl
    · by_cases hb_eq : b' = b
      · subst hb_eq
        rw [ite_eq_left rfl]
        by_cases hj_n : j' = n - 1
        · subst hj_n
          rw [Function.update_self]
          exact eff₂.2.2.2.2.2.2.1
        · rw [Function.update_of_ne hj_n, eff₂.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inr hj_n),
            eff₁.2.2.2.2.2.2.2.1]
      · rw [ite_eq_right hb_eq, eff₂.2.2.2.2.2.2.2.1 b' hb' j' hj' (Or.inl hb_eq),
          eff₁.2.2.2.2.2.2.2.1]
  · have eff₁ := writeLMHeadProg_effect (U := U) (V := V) (w := w) (n_max := n_max)
      (h_space := h_space) (base := base) (b := b) (m := m) (val := n) hw hb hm hn_lt s
    refine ⟨eff₁.1, eff₁.2.1, eff₁.2.2.1, eff₁.2.2.2.1, eff₁.2.2.2.2.1,
      fun b' hb' m' hm' => ?_, fun b' hb' j' hj' => ?_, fun b' hb' j' hj' => ?_⟩
    · by_cases hbm : b' = b ∧ m' = m
      · rcases hbm with ⟨rfl, rfl⟩
        rw [ite_eq_left ⟨rfl, rfl⟩]
        exact eff₁.2.2.2.2.2.1
      · rw [ite_eq_right hbm]
        exact eff₁.2.2.2.2.2.2.1 b' hb' m' hm' (not_and_or.mp hbm)
    · rw [eff₁.2.2.2.2.2.2.2.2]
      split_ifs with hb_eq
      · subst hb_eq; rfl
      · rfl
    · rw [eff₁.2.2.2.2.2.2.2.1]
      split_ifs with hb_eq
      · subst hb_eq; rfl
      · rfl

/-! ## Section 4: Phase 1 micro-chain search (`searchMicroChainProg`) -/

/-- Parameter-free single step of Phase 1 micro-chain traversal:
given `x.1.1 = (dp, ((base, b), q_target))`, `x.1.2 = z0`, and
`x.2 = (((ptr, found), j_found), phys_found)` with `0 < ptr`, inspects `j = ptr - 1`,
resolves its physical slot `phys`, reads `quotAt phys`, and either stops with
`(((0, 1), j), phys)` on match or advances to `next_ptr`. -/
def microStepGenProg
    (x : ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let j ← pure (x.2.1.1.1 - 1)
  let next_ptr ← readLMNextGenProg (x.1.1.1, (x.1.1.2.1, j))
  let phys ← resolveIndexedSlotGenProg (x.1.1.1, (x.1.1.2.1, j))
  let q_val ← readQuotGenProg (x.1.1.1, (x.1.1.2.1.1, phys))
  let z0 ← pure 0
  let one ← pure 1
  if q_val = x.1.1.2.2 then
    return (((z0, one), j), phys)
  else
    return (((next_ptr, z0), x.2.1.2), x.2.2)

/-- Single step of Phase 1 micro-chain traversal:
given `x.1 = (((base, b), q_target), z0)` and `x.2 = (((ptr, found), j_found), phys_found)`
with `0 < ptr`, inspects `j = ptr - 1`, resolves its physical slot `phys`, reads `quotAt phys`,
and either stops with `(((0, 1), j), phys)` on match or advances to `next_ptr`. -/
@[expose]
def microStepProg (U V w n_max h_space : ℕ)
    (x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let j ← pure (x.2.1.1.1 - 1)
  let next_ptr ← readLMNextProg U V w n_max h_space (x.1.1.1, j)
  let phys ← resolveIndexedSlotProg U V w n_max h_space (x.1.1.1, j)
  let q_val ← readQuotProg U w n_max h_space (x.1.1.1.1, phys)
  let z0 ← pure 0
  let one ← pure 1
  if q_val = x.1.1.2 then
    return (((z0, one), j), phys)
  else
    return (((next_ptr, z0), x.2.1.2), x.2.2)

@[simp]
theorem microStepGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (z0 : ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    microStepGenProg (((mkDictParams U V w n_max h_space, d1), z0), a) =
      microStepProg U V w n_max h_space ((d1, z0), a) := by
  unfold microStepGenProg microStepProg
  simp only [readLMNextGenProg_mk, resolveIndexedSlotGenProg_mk, readQuotGenProg_mk]

theorem clientState_microStepProg (U V w n_max h_space : ℕ)
    (x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    (Memory.spec 0).clientState s (microStepProg U V w n_max h_space x) = s := by
  unfold microStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientState_bind, clientState_readLMNextProg,
    StateTransitionSpec.clientState_bind, clientState_resolveIndexedSlotProg,
    StateTransitionSpec.clientState_bind, clientState_readQuotProg]
  split_ifs <;> rfl

theorem memoryCost_microStepGenProg_pos
    (x : ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    1 ≤ memoryCost (microStepGenProg x) s := by
  unfold microStepGenProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind]
  have : 1 ≤ memoryCost (readLMNextGenProg (x.1.1.1, (x.1.1.2.1, x.2.1.1.1 - 1))) s := by
    unfold readLMNextGenProg readLMMod4GenProg
    simp only [pure_bind]
    split_ifs <;> simp [readLMGenProg, readPackedGenProg]
  omega

theorem memoryCost_microStepProg_le (U V w n_max h_space : ℕ)
    (x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) :
    memoryCost (microStepProg U V w n_max h_space x) s ≤ 8 := by
  unfold microStepProg
  simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind,
    memoryCost_readLMNextProg, memoryCost_readQuotProg]
  have hres := memoryCost_resolveIndexedSlotProg_le (U := U) (V := V) (w := w)
    (n_max := n_max) (h_space := h_space) (x.1.1.1, x.2.1.1.1 - 1)
    ((Memory.spec 0).clientState s (readLMNextProg U V w n_max h_space (x.1.1.1, x.2.1.1.1 - 1)))
  split_ifs <;> simp only [memoryCost_pure] <;> omega

theorem clientResult_microStepProg {U V w n_max h_space : ℕ}
    {x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)} (s : Memory.State)
    (hinv : SlotStoreInv n_max (gmAt x.1.1.1.1 U V w n_max h_space s.mem))
    (hb : x.1.1.1.2 < numBuckets n_max)
    (hj_bc : x.2.1.1.1 - 1 < bCount n_max (gmAt x.1.1.1.1 U V w n_max h_space s.mem) x.1.1.1.2)
    (hj_cap : x.2.1.1.1 - 1 < effBucketCap n_max) :
    (Memory.spec 0).clientResult s (microStepProg U V w n_max h_space x) =
      let j := x.2.1.1.1 - 1
      let next_ptr := lmNext n_max (lmAt x.1.1.1.1 U V w n_max h_space s.mem) x.1.1.1.2 j
      let phys := slotOf n_max (gmAt x.1.1.1.1 U V w n_max h_space s.mem) x.1.1.1.2 j
      let q_val := quotAt x.1.1.1.1 U w n_max h_space s.mem phys
      if q_val = x.1.1.2 then (((0, 1), j), phys)
      else (((next_ptr, 0), x.2.1.2), x.2.2) := by
  have hphys : slotOf n_max (gmAt x.1.1.1.1 U V w n_max h_space s.mem)
      x.1.1.1.2 (x.2.1.1.1 - 1) < n_max :=
    (slotOf_lt_and_injective hinv).1 x.1.1.1.2 hb (x.2.1.1.1 - 1) hj_bc
  unfold microStepProg
  simp only [pure_bind]
  rw [StateTransitionSpec.clientResult_bind, clientState_readLMNextProg,
    clientResult_readLMNextProg _ hb hj_cap,
    StateTransitionSpec.clientResult_bind, clientState_resolveIndexedSlotProg,
    clientResult_resolveIndexedSlotProg (x.1.1.1, x.2.1.1.1 - 1) s hinv hb hj_bc hj_cap,
    StateTransitionSpec.clientResult_bind, clientState_readQuotProg,
    clientResult_readQuotProg s hphys]
  split_ifs <;> rfl

/-- Step precondition for `microStepProg` in `Realizes`. -/
@[expose]
def MicroStepPre (U V w₀ n_max h_space w : ℕ)
    (x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) x.1.1.1.1 ∧
  x.1.1.1.2 < numBuckets n_max ∧
  0 < x.2.1.1.1 ∧
  x.2.1.1.1 - 1 < effBucketCap n_max ∧
  x.2.1.1.1 - 1 < bCount n_max (gmAt x.1.1.1.1 U V w₀ n_max h_space s.mem) x.1.1.1.2 ∧
  SlotStoreInv n_max (gmAt x.1.1.1.1 U V w₀ n_max h_space s.mem)

/-- Parameter-free step precondition for `microStepGenProg`. -/
@[expose]
def MicroStepGenPre (w : ℕ)
    (x : ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w x.1.1.1 x.1.1.2.1.1 ∧
  x.1.1.2.1.2 < numBuckets (dpNMax x.1.1.1) ∧
  0 < x.2.1.1.1 ∧
  x.2.1.1.1 - 1 < effBucketCap (dpNMax x.1.1.1) ∧
  x.2.1.1.1 - 1 < bCount (dpNMax x.1.1.1)
    (gmAt x.1.1.2.1.1 (dpU x.1.1.1) (dpV x.1.1.1) (dpW x.1.1.1) (dpNMax x.1.1.1)
      (dpHSpace x.1.1.1) s.mem) x.1.1.2.1.2 ∧
  SlotStoreInv (dpNMax x.1.1.1)
    (gmAt x.1.1.2.1.1 (dpU x.1.1.1) (dpV x.1.1.1) (dpW x.1.1.1) (dpNMax x.1.1.1)
      (dpHSpace x.1.1.1) s.mem)

@[simp]
theorem microStepGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (z0 : ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    MicroStepGenPre w (((mkDictParams U V w₀ n_max h_space, d1), z0), a) s ↔
      MicroStepPre U V w₀ n_max h_space w ((d1, z0), a) s := Iff.rfl

theorem realizes_microStepGen :
    Realizes .exact microStepGenProg
      (WordEncoding.encode (α := ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      MicroStepGenPre
      (fun _ _ => 0) := by
  have hrn := realizes_readLMNextGen
  have hres := realizes_resolveIndexedSlotGen
  have hrq := realizes_readQuotGen
  unfold microStepGenProg
  realize
  all_goals (
    rcases d with ⟨⟨⟨dp, d1⟩, z0⟩, a⟩
    let d := ((d1, z0), a)
    obtain ⟨⟨U, V, w₀, n_max, h_space, hw, hnU, hU, hV, rfl⟩, henv⟩ := h.1
    simpDictParamsWith [microStepGenPre_mk, MicroStepPre, readLMNextGenProg_mk]
  )
  · have := h.2.2.1; omega
  · exact h.1
  · exact h.2.1
  · exact h.2.2.2.1
  · rw [clientState_readLMNextProg]; exact h.2.2.2.2.2
  · rw [clientState_readLMNextProg]; exact h.2.2.2.2.1
  · exact h.1
  · rw [clientState_readLMNextProg,
      clientResult_resolveIndexedSlotProg (d1.1, a.1.1.1 - 1) s
        h.2.2.2.2.2 h.2.1 h.2.2.2.2.1 h.2.2.2.1]
    exact (slotOf_lt_and_injective h.2.2.2.2.2).1 d1.1.2 h.2.1 (a.1.1.1 - 1) h.2.2.2.2.1
  · exact fits_const_of_dictEnv h.1 (by decide)

/-- Native loop guard for `microLoopGenProg`: tests `d.2 < a.1.1.1` (`z0 < ptr`). -/
@[expose]
def microLoopGenGuard (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) : Prop :=
  test (Cond.lt (39 : Fin 44) (40 : Fin 44))
    ((appendWords (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))) (d, a))

instance (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    Decidable (microLoopGenGuard d a) := by
  unfold microLoopGenGuard
  infer_instance

@[simp]
theorem microLoopGenGuard_iff (d : (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    microLoopGenGuard d a ↔ d.2 < a.1.1.1 := Iff.rfl

/-- Native loop guard for `microLoopProg`: tests `d.2 < a.1.1.1` (`z0 < ptr`). -/
@[expose]
def microLoopGuard (d : ((ℕ × ℕ) × ℕ) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) : Prop :=
  test (Cond.lt (3 : Fin 8) (4 : Fin 8))
    ((appendWords (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))) (d, a))

instance (d : ((ℕ × ℕ) × ℕ) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) : Decidable (microLoopGuard d a) := by
  unfold microLoopGuard
  infer_instance

@[simp]
theorem microLoopGuard_iff (d : ((ℕ × ℕ) × ℕ) × ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    microLoopGuard d a ↔ d.2 < a.1.1.1 := Iff.rfl

/-- Parameter-free Phase 1 bounded while loop over a micro-bucket chain with ghost cutoff
`effBucketCap (dpNMax x.1.1.1)`. -/
@[expose]
def microLoopGenProg
    (x : ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) :=
  boundedWhile microLoopGenGuard microStepGenProg
    x.1 (effBucketCap (dpNMax x.1.1.1)) x.2

/-- Phase 1 bounded while loop over a micro-bucket chain with ghost cutoff `effBucketCap n_max`. -/
@[expose]
def microLoopProg (U V w n_max h_space : ℕ)
    (x : (((ℕ × ℕ) × ℕ) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)) :
    Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) :=
  boundedWhile microLoopGuard (microStepProg U V w n_max h_space)
    x.1 (effBucketCap n_max) x.2

theorem boundedWhile_microStepGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (z0 : ℕ) (k : ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    boundedWhile microLoopGenGuard microStepGenProg
      ((mkDictParams U V w n_max h_space, d1), z0) k a =
    boundedWhile microLoopGuard (microStepProg U V w n_max h_space)
      (d1, z0) k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [boundedWhile, microLoopGenGuard_iff, microLoopGuard_iff, microStepGenProg_mk]
    split_ifs
    · exact congrArg (Bind.bind _) (funext ih)
    · rfl

@[simp]
theorem microLoopGenProg_mk (U V w n_max h_space : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (z0 : ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) :
    microLoopGenProg (((mkDictParams U V w n_max h_space, d1), z0), a) =
      microLoopProg U V w n_max h_space ((d1, z0), a) := by
  unfold microLoopGenProg microLoopProg
  rw [p_nMax_mk, boundedWhile_microStepGenProg_mk]

@[simp]
theorem whileSafe_microStepGenProg_mk (U V w₀ n_max h_space w : ℕ)
    (d1 : (ℕ × ℕ) × ℕ) (z0 : ℕ) (k : ℕ) (a : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    whileSafe microLoopGenGuard microStepGenProg MicroStepGenPre w
      ((mkDictParams U V w₀ n_max h_space, d1), z0) k a s ↔
    whileSafe microLoopGuard (microStepProg U V w₀ n_max h_space)
      (MicroStepPre U V w₀ n_max h_space) w (d1, z0) k a s := by
  induction k generalizing a s with
  | zero => simp [whileSafe]
  | succ k ih =>
    simp only [whileSafe, microLoopGenGuard_iff, microLoopGuard_iff,
      microStepGenPre_mk, microStepGenProg_mk]
    split_ifs
    · exact and_congr_right fun _ => ih _ _
    · exact Iff.rfl

theorem realizes_microLoopGen :
    Realizes .exact microLoopGenProg
      (WordEncoding.encode (α := ((DictParams × ((ℕ × ℕ) × ℕ)) × ℕ) × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      (fun w x s => whileSafe microLoopGenGuard microStepGenProg
        MicroStepGenPre w x.1 (effBucketCap (dpNMax x.1.1.1)) x.2 s)
      (fun _ _ => 0) :=
  Realizes.while₀
    (WordEncoding.encode (α := (DictParams × ((ℕ × ℕ) × ℕ)) × ℕ))
    (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
    (Cond.lt (39 : Fin 44) (40 : Fin 44))
    (fun d => effBucketCap (dpNMax d.1.1.1))
    realizes_microStepGen
    memoryCost_microStepGenProg_pos

/-- Structural induction lemma for `boundedWhile microLoopGuard (microStepProg ...)` along a
valid doubly-linked chain suffix `L`. -/
theorem boundedWhile_microStep_spec {U V w₀ n_max h_space w base b q_target prev_ptr : ℕ}
    {L : List ℕ} {n ptr found j_found phys_found : ℕ} {s : Memory.State}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) base)
    (hb : b < numBuckets n_max)
    (hinv : SlotStoreInv n_max (gmAt base U V w₀ n_max h_space s.mem))
    (hchain : IsDLChainAux n_max prev_ptr
      (lmPrev n_max (lmAt base U V w₀ n_max h_space s.mem) b)
      (lmNext n_max (lmAt base U V w₀ n_max h_space s.mem) b) L)
    (hc_lt : ∀ j ∈ L, j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b)
    (hn : L.length ≤ n)
    (hptr : ptr = (L.head?.map (· + 1)).getD 0) :
    let d := (((base, b), q_target), 0)
    let a := (((ptr, found), j_found), phys_found)
    let prog := boundedWhile microLoopGuard (microStepProg U V w₀ n_max h_space) d n a
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤ 8 * L.length ∧
    whileSafe microLoopGuard (microStepProg U V w₀ n_max h_space)
      (MicroStepPre U V w₀ n_max h_space) w d n a s ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j ∈ L, quotAt base U w₀ n_max h_space s.mem
         (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target then
       res.1.1 = (0, 1) ∧ res.1.2 ∈ L ∧
       quotAt base U w₀ n_max h_space s.mem
         (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b res.1.2) = q_target ∧
       res.2 = slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b res.1.2
     else
       res.1.1 = (0, if L = [] then found else 0)) := by
  induction L generalizing n prev_ptr ptr found j_found phys_found with
  | nil =>
    intro d a prog
    simp only [List.head?_nil, Option.map_none, Option.getD_none] at hptr
    subst hptr
    rcases n with _ | n' <;>
      refine ⟨by simp [prog, boundedWhile, d, a]; rfl, by simp [prog, boundedWhile, d, a],
        by simp [whileSafe, d, a], by simp [prog, boundedWhile, d, a]; rfl⟩
  | cons j rest ih =>
    intro d a prog
    rcases n with _ | n'
    · simp at hn
    · simp only [List.head?_cons, Option.map_some, Option.getD_some] at hptr
      subst hptr
      have hg : microLoopGuard d a := by simp [d, a]
      rcases hchain with ⟨hj_cap, _, _, hnj, hrest⟩
      have hj_c : j < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b :=
        hc_lt j List.mem_cons_self
      have hrest_c : ∀ x ∈ rest, x < bCount n_max (gmAt base U V w₀ n_max h_space s.mem) b :=
        fun x hx => hc_lt x (List.mem_cons_of_mem j hx)
      have hpre : MicroStepPre U V w₀ n_max h_space w (d, a) s :=
        ⟨henv, hb, by simp [a], by simpa [a] using hj_cap, by simpa [a] using hj_c, hinv⟩
      have hstep_res := clientResult_microStepProg s (x := (d, a)) hinv hb
        (by simpa [a] using hj_c) (by simpa [a] using hj_cap)
      simp only [d, a, Nat.add_sub_cancel] at hstep_res
      have hstep_state := clientState_microStepProg U V w₀ n_max h_space (d, a) s
      have hstep_cost := memoryCost_microStepProg_le U V w₀ n_max h_space (d, a) s
      by_cases hmatch : quotAt base U w₀ n_max h_space s.mem
          (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) = q_target
      · have hres_eq : (Memory.spec 0).clientResult s (microStepProg U V w₀ n_max h_space (d, a)) =
            (((0, 1), j), slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j) := by
          rw [hstep_res, ite_eq_left hmatch]
        let a' := (((0, 1), j), slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b j)
        have hbw_nil : ∀ m,
            boundedWhile microLoopGuard (microStepProg U V w₀ n_max h_space) d m a' =
              pure a' := fun m => by
          rcases m with _ | m' <;> simp [boundedWhile, d, a']
        have hws_nil : ∀ m, whileSafe microLoopGuard (microStepProg U V w₀ n_max h_space)
            (MicroStepPre U V w₀ n_max h_space) w d m a' s := fun m => by
          rcases m with _ | m' <;> simp [whileSafe, d, a']
        refine ⟨?_, ?_, ?_, ?_⟩
        · unfold prog boundedWhile
          rw [ite_eq_left hg, StateTransitionSpec.clientState_bind, hstep_state, hres_eq, hbw_nil]
          rfl
        · unfold prog boundedWhile
          rw [ite_eq_left hg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_state,
            hres_eq, hbw_nil]
          simp only [memoryCost_pure, List.length_cons]
          omega
        · simp only [whileSafe, hg, ↓reduceIte, hstep_state, hres_eq]
          exact ⟨hpre, hws_nil n'⟩
        · dsimp only
          unfold prog boundedWhile
          rw [ite_eq_left hg, StateTransitionSpec.clientResult_bind, hstep_state, hres_eq, hbw_nil]
          change if ∃ x ∈ j :: rest, quotAt base U w₀ n_max h_space s.mem
              (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b x) = q_target then
              a'.1.1 = (0, 1) ∧ a'.1.2 ∈ j :: rest ∧
              quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b a'.1.2) = q_target ∧
              a'.2 = slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b a'.1.2
            else a'.1.1 = (0, if j :: rest = [] then found else 0)
          have hex : ∃ x ∈ j :: rest, quotAt base U w₀ n_max h_space s.mem
              (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b x) = q_target :=
            ⟨j, List.mem_cons_self, hmatch⟩
          rw [ite_eq_left hex]
          exact ⟨rfl, List.mem_cons_self, hmatch, rfl⟩
      · have hres_eq : (Memory.spec 0).clientResult s (microStepProg U V w₀ n_max h_space (d, a)) =
            (((lmNext n_max (lmAt base U V w₀ n_max h_space s.mem) b j, 0), j_found),
              phys_found) := by
          rw [hstep_res, ite_eq_right hmatch]
        have hn' : rest.length ≤ n' := by simp only [List.length_cons] at hn; omega
        have hih := ih hrest hrest_c hn' hnj (found := 0) (j_found := j_found)
          (phys_found := phys_found)
        refine ⟨?_, ?_, ?_, ?_⟩
        · unfold prog boundedWhile
          rw [ite_eq_left hg, StateTransitionSpec.clientState_bind, hstep_state, hres_eq]
          exact hih.1
        · unfold prog boundedWhile
          rw [ite_eq_left hg, ← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hstep_state, hres_eq]
          dsimp only [d] at hstep_cost ⊢
          have := hih.2.1
          simp only [List.length_cons]
          omega
        · simp only [whileSafe, hg, ↓reduceIte, hstep_state, hres_eq]
          exact ⟨hpre, hih.2.2.1⟩
        · dsimp only
          unfold prog boundedWhile
          rw [ite_eq_left hg, StateTransitionSpec.clientResult_bind, hstep_state, hres_eq]
          have hih_res := hih.2.2.2
          dsimp only [d] at hih_res ⊢
          by_cases hex_rest : ∃ x ∈ rest, quotAt base U w₀ n_max h_space s.mem
              (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b x) = q_target
          · have hex_cons : ∃ x ∈ j :: rest, quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b x) = q_target := by
              obtain ⟨x, hx, hqx⟩ := hex_rest
              exact ⟨x, List.mem_cons_of_mem j hx, hqx⟩
            rw [ite_eq_left hex_rest] at hih_res
            rw [ite_eq_left hex_cons]
            exact ⟨hih_res.1, List.mem_cons_of_mem j hih_res.2.1, hih_res.2.2.1, hih_res.2.2.2⟩
          · have hno_cons : ¬∃ x ∈ j :: rest, quotAt base U w₀ n_max h_space s.mem
                (slotOf n_max (gmAt base U V w₀ n_max h_space s.mem) b x) = q_target := by
              rintro ⟨x, hx, hqx⟩
              rcases List.mem_cons.mp hx with rfl | hx_rest
              · exact hmatch hqx
              · exact hex_rest ⟨x, hx_rest, hqx⟩
            rw [ite_eq_right hex_rest] at hih_res
            rw [ite_eq_right hno_cons, ite_eq_right (List.cons_ne_nil j rest)]
            split_ifs at hih_res <;> exact hih_res

/-- Parameter-free Phase 1 micro-chain search `searchMicroChainGenProg`:
reads `h0 = lmHead b m` (`d = (dp, (((base, b), q_target), m))`) and runs `microLoopGenProg`
from `h0`. -/
def searchMicroChainGenProg
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let h0 ← readLMHeadGenProg (d.1, (d.2.1.1, d.2.2))
  let z0 ← pure 0
  microLoopGenProg (((d.1, d.2.1), z0), (((h0, z0), z0), z0))

/-- Phase 1 micro-chain search `searchMicroChainProg`:
reads `h0 = lmHead b m` (`d = (((base, b), q_target), m)`) and runs `microLoopProg` from `h0`. -/
@[expose]
def searchMicroChainProg (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) : Memory.Prog (((ℕ × ℕ) × ℕ) × ℕ) := do
  let h0 ← readLMHeadProg U V w n_max h_space (d.1.1, d.2)
  let z0 ← pure 0
  microLoopProg U V w n_max h_space ((d.1, z0), (((h0, z0), z0), z0))

@[simp]
theorem searchMicroChainGenProg_mk (U V w n_max h_space : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) :
    searchMicroChainGenProg (mkDictParams U V w n_max h_space, d) =
      searchMicroChainProg U V w n_max h_space d := by
  unfold searchMicroChainGenProg searchMicroChainProg
  simp only [readLMHeadGenProg_mk, microLoopGenProg_mk]

/-- Precondition for `searchMicroChainProg`: `d = (((base, b), q_target), m)` with a valid
doubly-linked micro-bucket chain `L` at `(b, m)` whose slots are all `< bCount b`. -/
@[expose]
def SearchMicroChainPre (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) : Prop :=
  DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1 ∧
  d.1.1.2 < numBuckets n_max ∧
  d.2 < numMicroPerBucket n_max ∧
  SlotStoreInv n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) ∧
  ∃ L : List ℕ,
    IsDLChain n_max (lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2)
      (lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2)
      (lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) L ∧
    ∀ j ∈ L, j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2

/-- Parameter-free precondition for `searchMicroChainGenProg`. -/
@[expose]
def SearchMicroChainGenPre (w : ℕ)
    (d : DictParams × (((ℕ × ℕ) × ℕ) × ℕ)) (s : Memory.State) : Prop :=
  DictEnvGen w d.1 d.2.1.1.1 ∧
  d.2.1.1.2 < numBuckets (dpNMax d.1) ∧
  d.2.2 < numMicroPerBucket (dpNMax d.1) ∧
  SlotStoreInv (dpNMax d.1)
    (gmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem) ∧
  ∃ L : List ℕ,
    IsDLChain (dpNMax d.1)
      (lmHead (dpNMax d.1)
        (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
        d.2.1.1.2 d.2.2)
      (lmPrev (dpNMax d.1)
        (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
        d.2.1.1.2)
      (lmNext (dpNMax d.1)
        (lmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
        d.2.1.1.2) L ∧
    ∀ j ∈ L, j < bCount (dpNMax d.1)
      (gmAt d.2.1.1.1 (dpU d.1) (dpV d.1) (dpW d.1) (dpNMax d.1) (dpHSpace d.1) s.mem)
      d.2.1.1.2

@[simp]
theorem searchMicroChainGenPre_mk (U V w₀ n_max h_space w : ℕ)
    (d : ((ℕ × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    SearchMicroChainGenPre w (mkDictParams U V w₀ n_max h_space, d) s ↔
      SearchMicroChainPre U V w₀ n_max h_space w d s := Iff.rfl

theorem searchMicroChainProg_spec {U V w₀ n_max h_space w : ℕ}
    {d : ((ℕ × ℕ) × ℕ) × ℕ} {s : Memory.State} {L : List ℕ}
    (henv : DictEnvGen w (mkDictParams U V w₀ n_max h_space) d.1.1.1)
    (hb : d.1.1.2 < numBuckets n_max)
    (hm : d.2 < numMicroPerBucket n_max)
    (hinv : SlotStoreInv n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem))
    (hchain : IsDLChain n_max (lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2)
      (lmPrev n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2)
      (lmNext n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) L)
    (hc_lt : ∀ j ∈ L, j < bCount n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2) :
    let prog := searchMicroChainProg U V w₀ n_max h_space d
    (Memory.spec 0).clientState s prog = s ∧
    memoryCost prog s ≤ 2 + 8 * L.length ∧
    whileSafe microLoopGuard (microStepProg U V w₀ n_max h_space)
      (MicroStepPre U V w₀ n_max h_space) w
      (d.1, 0) (effBucketCap n_max)
      (((lmHead n_max (lmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 d.2, 0), 0), 0) s ∧
    (let res := (Memory.spec 0).clientResult s prog
     if ∃ j ∈ L, quotAt d.1.1.1 U w₀ n_max h_space s.mem
         (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 j) = d.1.2 then
       res.1.1 = (0, 1) ∧ res.1.2 ∈ L ∧
       quotAt d.1.1.1 U w₀ n_max h_space s.mem
         (slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 res.1.2) = d.1.2 ∧
       res.2 = slotOf n_max (gmAt d.1.1.1 U V w₀ n_max h_space s.mem) d.1.1.2 res.1.2
     else
       res.1.1 = (0, 0)) := by
  rcases d with ⟨⟨⟨base, b⟩, q_target⟩, m⟩
  dsimp only at henv hb hm hinv hchain hc_lt ⊢
  let prog := searchMicroChainProg U V w₀ n_max h_space (((base, b), q_target), m)
  have hbw := boundedWhile_microStep_spec (q_target := q_target)
    (found := 0) (j_found := 0) (phys_found := 0)
    henv hb hinv hchain.2 hc_lt hchain.length_le hchain.1
  have hst : (Memory.spec 0).clientState s prog = s := by
    unfold prog searchMicroChainProg microLoopProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientState_bind, clientState_readLMHeadProg,
      clientResult_readLMHeadProg _ hb hm]
    exact hbw.1
  have hcost : memoryCost prog s ≤ 2 + 8 * L.length := by
    unfold prog searchMicroChainProg microLoopProg
    simp only [pure_bind, ← PFunctor.FreeM.bind_eq_bind]
    rw [memoryCost_bind, memoryCost_readLMHeadProg, clientState_readLMHeadProg,
      clientResult_readLMHeadProg _ hb hm]
    have := hbw.2.1
    omega
  have hres_eq : (Memory.spec 0).clientResult s prog =
      (Memory.spec 0).clientResult s
        (boundedWhile microLoopGuard (microStepProg U V w₀ n_max h_space)
          (((base, b), q_target), 0) (effBucketCap n_max)
          (((lmHead n_max (lmAt base U V w₀ n_max h_space s.mem) b m, 0), 0), 0)) := by
    unfold prog searchMicroChainProg microLoopProg
    simp only [pure_bind]
    rw [StateTransitionSpec.clientResult_bind, clientState_readLMHeadProg,
      clientResult_readLMHeadProg _ hb hm]
  refine ⟨hst, hcost, hbw.2.2.1, ?_⟩
  have hres := hbw.2.2.2
  dsimp only at hres ⊢
  simp only [ite_self] at hres
  rw [hres_eq]
  exact hres

theorem realizes_searchMicroChainGen :
    Realizes .exact searchMicroChainGenProg
      (WordEncoding.encode (α := DictParams × (((ℕ × ℕ) × ℕ) × ℕ)))
      (WordEncoding.encode (α := ((ℕ × ℕ) × ℕ) × ℕ))
      SearchMicroChainGenPre
      (fun _ _ => 0) := by
  have hrh := realizes_readLMHeadGen
  have hloop := realizes_microLoopGen
  realizeDictWith [searchMicroChainGenPre_mk, SearchMicroChainPre,
    readLMHeadGenProg_mk, microLoopGenProg_mk, whileSafe_microStepGenProg_mk]
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · rw [clientState_readLMHeadProg, clientResult_readLMHeadProg _ h.2.1 h.2.2.1]
    obtain ⟨L, hchain, hc_lt⟩ := h.2.2.2.2
    exact (searchMicroChainProg_spec h.1 h.2.1 h.2.2.1 h.2.2.2.1 hchain hc_lt).2.2.1

end Cslib.DataStructure.Dictionary.WordRAM.Succinct
