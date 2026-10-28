/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandParameters
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandSplit

/-!
# Guarded native matrix reads for band arrays

## Main definitions

* `BandPreparation.matrixAddress`: real row-major matrix addresses in the protected input.

## Main results

* `BandPreparation.exec_readCell`: the actual guarded read returns exactly one encoded
  band value; padded rows are rejected before row-major multiplication.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open BandDigits

/-- Offset in the concatenated original matrix inputs. The right matrix has `D` rows and
`N` columns, while its band specification labels a column by `r`. -/
def matrixOffset (m N : ℕ) (rightSide : Bool) (r k : ℕ) : ℕ :=
  if rightSide then k * N + r + N * D m else r * D m + k

/-- Address of an original signed input word in its protected snapshot. -/
def matrixAddress (L m N : ℕ) (rightSide : Bool) (r k : ℕ) : ℕ :=
  snapshotBase L m N + (matrixOffset m N rightSide r k + 4)

private theorem matrix_indices_lt {m N r k : ℕ} (hr : r < N) (hk : k < D m) :
    r * D m + k < N * D m ∧ k * N + r < N * D m := by
  have hleft := Nat.mul_le_mul_right (D m) (Nat.succ_le_of_lt hr)
  have hright := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hk)
  rw [Nat.succ_mul] at hleft hright
  rw [Nat.mul_comm (D m) N] at hright
  constructor <;> omega

/-- A real matrix cell lies strictly inside its protected snapshot. This uses the
real row/column guard, before constructing its flat address. -/
theorem matrixAddress_lt_inverse {L m N r k : ℕ} (side : Bool)
    (hr : r < N) (hk : k < D m) :
    matrixAddress L m N side r k < inverseBase L m N := by
  obtain ⟨hl, hr'⟩ := matrix_indices_lt hr hk
  unfold matrixAddress matrixOffset inverseBase inputEnd
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The complete guarded load uses at most twenty-four actual target instructions.
All intermediate products are bounded using the original parameters and the real `r<N`
guard. No hypothesis bounds an arbitrary intermediate machine state. -/
theorem exec_readCell {w L m N : ℕ} (side : Bool) (a : Fin (7 ^ L)) (β : ℕ)
    (x : Data 96) (hx : BandParameters L m N x) (hβ : β < numBands L m N)
    (hb : x.regs band = β) (hm : x.regs maskAcc = (parts L a.val).mask)
    (ho : x.regs outerAcc = (parts L a.val).outer)
    (hi : x.regs innerAcc = (parts L a.val).inner)
    (htable : ∀ t < 2 ^ L, x.mem (inverseBase L m N + t) = MaskTable.lookup L m t)
    (matrix : ℕ → ℕ → ℤ)
    (hmat : ∀ r < N, ∀ k < D m,
      x.mem (matrixAddress L m N side r k) = encode (matrix r k))
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w (readCell side) x y 24 ∧
      y.regs value = encode (bandValue L m N β side matrix a.val) ∧ y.mem = x.mem := by
  let p := parts L a.val
  let q := MaskTable.lookup L m p.mask
  change x.regs maskAcc = p.mask at hm
  change x.regs outerAcc = p.outer at ho
  change x.regs innerAcc = p.inner at hi
  have hp : p.mask < 2 ^ L ∧ p.outer < 3 ^ L ∧ p.inner < 4 ^ L := parts_bounds L a.val
  have hlookup : x.mem (inverseBase L m N + p.mask) = q := htable _ hp.1
  have haddr : Fits w (inverseBase L m N + p.mask) :=
    ((memory_fits hfit).of_le (table_le_memoryEnd L m N)).of_le (by
      unfold tableBase
      have := hp.1
      omega)
  let u := ((x.set address (inverseBase L m N + p.mask)).set rank q).set value 0
  by_cases hq : q = 0
  · let y := u.set value 0
    refine ⟨y, ?_, ?_, rfl⟩
    · ram_eval [readCell, y, u, hx.inverse, hx.fixed.zero, hm, hlookup, haddr,
        small_fits hfit (by decide : 0 ≤ 256), hq,
        inverse, maskAcc, address, rank, value, zero, Fin.mk.injEq]
    · change y.regs value = encode (if q = 0 then 0 else _)
      rw [ite_eq_left hq]
      simp only [y, Data.set_regs, Function.update_self]
      rfl
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let b := if side then (q - 1) % K0 L m else (q - 1) / K0 L m
    let r := (β * K0 L m + b) * N0 L m + p.outer
    have hb_lt : b < K0 L m := MaskTable.lookup_block_lt hq side
    have hparts : p.outer < N0 L m ∧ p.inner < D m := selected_parts_bounds a hq
    have hbounds := band_position_bounds hβ hb_lt hparts.1
    have h7 : 7 ^ L ≤ 10 ^ L := Nat.pow_le_pow_left (by decide) _
    have hlocal : Fits w (N + 7 ^ L + 2 ^ L + 4) := (local_fits hfit).of_le (by
      nlinarith only [h7, Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
        Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
    have hqbound : q ≤ p.mask + 1 := MaskTable.lookup_le L m p.mask
    have hqfit : Fits w (q - 1) := hlocal.of_le (by have := hp.1; omega)
    have hbfit : Fits w b := hlocal.of_le (by have := hbounds.2.1; omega)
    have hβfit : Fits w (β * K0 L m) := hlocal.of_le (by have := hbounds.1; omega)
    have hblockfit : Fits w (β * K0 L m + b) := hlocal.of_le (by have := hbounds.2.1; omega)
    have hrowfit : Fits w ((β * K0 L m + b) * N0 L m) :=
      hlocal.of_le (by have := hbounds.2.2.1; omega)
    have hrfit : Fits w r := hlocal.of_le (by have := hbounds.2.2.2; dsimp [r]; omega)
    let v := ((((((u.set rank (q - 1)).set block b).set temporary (β * K0 L m)).set
      block (β * K0 L m + b)).set row ((β * K0 L m + b) * N0 L m)).set row r)
    by_cases hr : r < N
    · obtain ⟨hleft, hright⟩ := matrix_indices_lt hr hparts.2
      have hinput : Fits w (inputEnd m N) :=
        (memory_fits hfit).of_le (input_le_memoryEnd L m N)
      have hnd : Fits w (N * D m) := hinput.of_le (by unfold inputEnd; omega)
      have hleftMul : Fits w (r * D m) := hnd.of_le (by omega)
      have hleftAdd : Fits w (r * D m + p.inner) := hnd.of_le hleft.le
      have hrightMul : Fits w (p.inner * N) := hnd.of_le (by omega)
      have hrightAdd : Fits w (p.inner * N + r) := hnd.of_le hright.le
      have hrightOff : Fits w (p.inner * N + r + N * D m) :=
        hinput.of_le (by unfold inputEnd; omega)
      have hleftFour : Fits w (r * D m + p.inner + 4) :=
        hinput.of_le (by unfold inputEnd; omega)
      have hrightFour : Fits w (p.inner * N + r + N * D m + 4) :=
        hinput.of_le (by unfold inputEnd; omega)
      have hleftAddress : Fits w (snapshotBase L m N + (r * D m + p.inner + 4)) :=
        ((memory_fits hfit).of_le (inverse_le_memoryEnd L m N)).of_le (by
          unfold inverseBase inputEnd
          omega)
      have hrightAddress : Fits w (snapshotBase L m N + (p.inner * N + r + N * D m + 4)) :=
        ((memory_fits hfit).of_le (inverse_le_memoryEnd L m N)).of_le (by
          unfold inverseBase inputEnd
          omega)
      have hcell := hmat r hr p.inner hparts.2
      dsimp only [matrixAddress, matrixOffset] at hcell
      dsimp only [b, r] at hbfit hblockfit hrowfit hrfit hr
      dsimp only [b, r] at hleftMul hleftAdd hrightAdd hrightOff hleftFour hrightFour
      dsimp only [b, r] at hleftAddress hrightAddress hcell
      let y := if side then
          (((((((v.set address (p.inner * N)).set address (p.inner * N + r)).set
            temporary (N * D m)).set address (p.inner * N + r + N * D m)).set
            address (p.inner * N + r + N * D m + 4)).set
            address (snapshotBase L m N + (p.inner * N + r + N * D m + 4))).set
            value (encode (matrix r p.inner)))
        else
          (((((v.set address (r * D m)).set address (r * D m + p.inner)).set
            address (r * D m + p.inner + 4)).set
            address (snapshotBase L m N + (r * D m + p.inner + 4))).set
            value (encode (matrix r p.inner)))
      refine ⟨y, ?_, ?_, ?_⟩
      · cases side <;>
          simp only [Bool.false_eq_true, ↓reduceIte] at hbfit hblockfit hrowfit hrfit hr <;>
          simp only [Bool.false_eq_true, ↓reduceIte] at hleftMul hleftAdd hrightAdd
            <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrightOff hleftFour hrightFour
            <;> simp only [Bool.false_eq_true, ↓reduceIte] at hleftAddress hrightAddress hcell <;>
          ram_eval [readCell, y, v, u, b, r, hx.inverse, hx.snapshot, hx.root, hx.outerSize,
            hx.columns, hx.fixed.zero, hx.fixed.one, hx.fixed.four, hx.fixed.rows,
            hm, ho, hi, hb, hlookup, haddr, hqpos, hr,
            small_fits hfit (by decide : 0 ≤ 256), hqfit, hbfit, hβfit, hblockfit,
            hrowfit, hrfit, hnd, hleftMul, hleftAdd, hrightMul, hrightAdd,
            hrightOff, hleftFour, hrightFour, hleftAddress, hrightAddress,
            hcell, matrixAddress, matrixOffset,
            inverse, snapshot, root, outerSize, columns, zero, one, four, rows,
            maskAcc, outerAcc, innerAcc, band, address, rank, value, block, temporary,
            row, Fin.mk.injEq]
      · change y.regs value = encode (if q = 0 then 0 else
          if r < N then matrix r p.inner else 0)
        rw [ite_eq_right hq, ite_eq_left hr]
        cases side <;> simp [y]
      · cases side <;> rfl
    · let y := v.set value 0
      dsimp only [b, r] at hbfit hblockfit hrowfit hrfit hr
      refine ⟨y, ?_, ?_, rfl⟩
      · cases side <;>
          simp only [Bool.false_eq_true, ↓reduceIte] at hbfit hblockfit hrowfit hrfit hr <;>
          ram_eval [readCell, y, v, u, b, r, hx.inverse, hx.root, hx.outerSize,
            hx.fixed.zero, hx.fixed.one, hx.fixed.rows, hm, ho, hi, hb,
            hlookup, haddr, hqpos, hr, small_fits hfit (by decide : 0 ≤ 256),
            hqfit, hbfit, hβfit, hblockfit, hrowfit, hrfit,
            inverse, root, outerSize, zero, one, rows, maskAcc, outerAcc, band,
            address, rank, value, block, temporary, row, Fin.mk.injEq]
      · change y.regs value = encode (if q = 0 then 0 else
          if r < N then matrix r p.inner else 0)
        rw [ite_eq_right hq, ite_eq_right hr]
        simp only [y, Data.set_regs, Function.update_self]
        rfl

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
