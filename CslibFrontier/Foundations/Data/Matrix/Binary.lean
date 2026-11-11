/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.Nat.Bits
import Mathlib.Data.Nat.Size

/-!
# Binary words for power-of-two residue matrices

A rectangular matrix over `ZMod (2 ^ w)` is represented row by row, with `w` low-order-first
bits per entry. The dimensions are external parameters. Decoding arbitrary words pads missing
bits with `false` and ignores excess bits, including when a dimension or the width is zero.

## Main definitions

* `Cslib.Matrix.toBinary`, `Cslib.Matrix.ofBinary`: fixed-width row-major encoding and total
  decoding.
* `Cslib.Matrix.binaryEntry`: the number read from the entry bits at an arbitrary row and
  column of a word, with missing bits `false`.
* `Cslib.Matrix.encBinary`: the injective encoding of matrices with fixed dimensions and width.

## Main results

* `Cslib.Matrix.ofBinary_toBinary`: decoding a matrix's word recovers the matrix.
* `Cslib.Matrix.length_toBinary`: the exact complete output length is `rows * cols * w`.
-/

@[expose] public section

namespace Cslib.Matrix

open Cslib.BitString

/-- Fixed-width row-major encoding; the digits of each residue are least significant first. -/
def toBinary {rows cols w : ℕ} (A : Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) : List Bool :=
  List.ofFn (blocksEquiv.symm fun i =>
    blocksEquiv.symm fun j => fun k : Fin w => (A i j).val.testBit k.val)

/-- Read the declared matrix dimensions, padding missing bits with `false` and ignoring excess
bits. Zero-width entries are the unique residue modulo one. -/
def ofBinary (rows cols w : ℕ) (word : List Bool) :
    Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)) :=
  fun i j => ((List.ofFn (block (block (ofList (rows * (cols * w)) word) i) j)).foldr
    Nat.bit 0 : ℕ)

/-- Read one low-order-first residue word at an arbitrary row and column. Missing bits are
`false`; the declared column count determines the stride. -/
def binaryEntry (cols w : ℕ) (word : List Bool) (i j : ℕ) : ℕ :=
  (listRow w (i * cols + j) word).foldr Nat.bit 0

/-- List slicing and the finite matrix decoder use the same coordinates. -/
theorem ofBinary_apply (rows cols w : ℕ) (word : List Bool) (i : Fin rows) (j : Fin cols) :
    ofBinary rows cols w word i j = (binaryEntry cols w word i.val j.val : ZMod (2 ^ w)) := by
  unfold ofBinary binaryEntry
  congr 2
  rw [show i.val * cols + j.val = (finProdFinEquiv (i, j)).val by
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]]
  rw [listRow_eq_ofFn w (finProdFinEquiv (i, j)) word]
  congr 1
  funext k
  simp [block, ofList, finProdFinEquiv, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_comm, Nat.mul_left_comm]

/-- Encoding writes every entry's declared width, including leading zero digits. -/
@[simp] theorem length_toBinary {rows cols w : ℕ}
    (A : Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) :
    (toBinary A).length = rows * cols * w := by
  simp [toBinary, Nat.mul_assoc]

/-- The row-major representation is the concatenation of each row's low-order-first words. -/
theorem toBinary_eq {rows cols w : ℕ} (A : Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) :
    toBinary A = (List.ofFn fun i => (List.ofFn fun j =>
      List.ofFn fun k : Fin w => (A i j).val.testBit k.val).flatten).flatten := by
  simp [toBinary, ofFn_blocksEquiv_symm]

/-- Canonical fixed-width words decode exactly, including empty dimensions and width zero. -/
@[simp] theorem ofBinary_toBinary {rows cols w : ℕ}
    (A : Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w))) :
    ofBinary rows cols w (toBinary A) = A := by
  ext i j
  simp only [ofBinary, toBinary, ofList_ofFn, block_blocksEquiv_symm]
  have h := Nat.foldr_bit_testBit (Nat.size_le.2 (ZMod.val_lt (A i j)))
  rw [show (List.ofFn fun k : Fin w => (A i j).val.testBit k.val) =
    (List.range w).map (A i j).val.testBit by
      rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
      rfl]
  rw [h, ZMod.natCast_zmod_val]

/-- Fixed-dimensional matrices inject into their complete binary words. This fixed-type
embedding alone makes no claim of uniform computational efficiency in the dimensions. -/
def encBinary (rows cols w : ℕ) : Matrix (Fin rows) (Fin cols) (ZMod (2 ^ w)) ↪ List Bool :=
  ⟨toBinary, Function.LeftInverse.injective ofBinary_toBinary⟩

end Cslib.Matrix
