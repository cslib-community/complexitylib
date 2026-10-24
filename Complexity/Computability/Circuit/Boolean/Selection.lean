/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Block

/-!
# Selecting and packing bit-string records

A record has a prefix key of `k` bits followed by a payload of `p` bits. Keys are unsigned
numbers with the least significant bit first. Pairwise minimum selection retains the first
record on equal keys, including empty keys. Packing places records in consecutive blocks.

## Main definitions

* `Cslib.BitString.recordKey`: the prefix key.
* `Cslib.BitString.keyedMinFn`: a least-key record, the first on ties.
* `Cslib.BitString.packRecords`: concatenate a finite family of records.

## Main results

* `Cslib.BitString.keyedMinFn_eq_or_eq`: selection returns one of its inputs.
* `Cslib.BitString.equivFin_recordKey_keyedMinFn_le_left`,
  `Cslib.BitString.equivFin_recordKey_keyedMinFn_le_right`: the selected key is least.
* `Cslib.BitString.packRecords_comp`: recover a record from its packed block.

## References

Adapted from Samuel Schlesinger's earlier Complexitylib modules
`Circuits/{KeyedMinimum,KeyedMinimumTournament}`.
-/

@[expose] public section

namespace Cslib.BitString

variable {k p m : ℕ}

/-- The key of a record: its first `k` bits. -/
def recordKey (r : BitString (k + p)) : BitString k :=
  fstBits r

/-- Of two records, the one with the smaller key, the first on ties. -/
def keyedMinFn (r s : BitString (k + p)) : BitString (k + p) :=
  if BitString.equivFin k (recordKey r) ≤ BitString.equivFin k (recordKey s) then r else s

/-- The selected record is one of the two inputs. -/
theorem keyedMinFn_eq_or_eq (r s : BitString (k + p)) :
    keyedMinFn r s = r ∨ keyedMinFn r s = s := by
  unfold keyedMinFn
  split_ifs <;> simp

/-- The key of the selected record is at most the key of the first record. -/
theorem equivFin_recordKey_keyedMinFn_le_left (r s : BitString (k + p)) :
    BitString.equivFin k (recordKey (keyedMinFn r s)) ≤ BitString.equivFin k (recordKey r) := by
  unfold keyedMinFn
  split_ifs with h
  · exact le_rfl
  · exact (not_le.1 h).le

/-- The key of the selected record is at most the key of the second record. -/
theorem equivFin_recordKey_keyedMinFn_le_right (r s : BitString (k + p)) :
    BitString.equivFin k (recordKey (keyedMinFn r s)) ≤ BitString.equivFin k (recordKey s) := by
  unfold keyedMinFn
  split_ifs with h
  · exact h
  · exact le_rfl

/-- `m` records of `r` bits packed one after the other: bit `j` of record `i` is input
`finProdFinEquiv (i, j)`, that is `i r + j`. -/
def packRecords {r : ℕ} (records : Fin m → BitString r) : BitString (m * r) :=
  blocksEquiv.symm records

/-- Reading block `i` of the packed records recovers record `i`. -/
theorem packRecords_comp {r : ℕ} (records : Fin m → BitString r) (i : Fin m) :
    packRecords records ∘ (fun j => finProdFinEquiv (i, j)) = records i :=
  congrFun (block_blocksEquiv_symm records) i

end Cslib.BitString
