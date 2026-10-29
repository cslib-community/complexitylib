/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup

/-!
# Native stable-scatter stores

## Main results

* `Wanted.exec_scatterWrite`: store one computed code and original position at the actual
  cursor, then increment that cursor and the original-input counter.

This is an internal implementation API. The scatter position is the existing counting-sort
formula, whose range follows from the original input length, rather than an execution oracle.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Three actual memory stores suffice for one stable occurrence. Address fits and
separation follow from the original query length and the proved counting-sort position. -/
theorem exec_scatterWrite {w L m N Q n v : ℕ} (key : ℕ → ℕ) (hn : n < Q)
    (hk : key n < numBands L m N ^ 2) (x : Data 96) (hx : Parameters L m N Q x)
    (hi : x.regs index = n) (ht : x.regs tile = key n)
    (hv : x.regs (packRegisters code) = v)
    (hc : x.mem (cursorAddressBase L m N Q + key n) = CountingSort.position key Q n)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w scatterWrite x y 9 ∧ Parameters L m N Q y ∧ y.regs index = n + 1 ∧
      y.mem (codeAddress L m N Q + CountingSort.position key Q n) = v ∧
      y.mem (originalAddress L m N Q + CountingSort.position key Q n) = n ∧
      y.mem (cursorAddressBase L m N Q + key n) = CountingSort.position key Q n + 1 ∧
      (∀ a, a ≠ cursorAddressBase L m N Q + key n →
        a ≠ codeAddress L m N Q + CountingSort.position key Q n →
        a ≠ originalAddress L m N Q + CountingSort.position key Q n → y.mem a = x.mem a) := by
  let p := CountingSort.position key Q n
  have hp : p < Q := CountingSort.position_lt key hn
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have h2 := Nat.zero_le (2 ^ L)
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q) : Fits w v := hl.of_le (by omega)
  have hcursor : Fits w (cursorAddressBase L m N Q + key n) := hf _ (by
    unfold cursorAddressBase offsetAddress countAddress tableAddress inputLimit
    omega)
  have hcode : Fits w (codeAddress L m N Q + p) := hf _ (by
    unfold memoryLimit originalAddress
    omega)
  have horig : Fits w (originalAddress L m N Q + p) := hf _ (by
    unfold memoryLimit
    omega)
  have hnext : Fits w (p + 1) := hf _ (by omega)
  have hnnext : Fits w (n + 1) := hf _ (by omega)
  have hcurcode : cursorAddressBase L m N Q + key n < codeAddress L m N Q := by
    unfold codeAddress
    omega
  have hcodeorig : codeAddress L m N Q + p < originalAddress L m N Q := by
    unfold originalAddress
    omega
  let y := (((((((((x.set cursorAddress (cursorAddressBase L m N Q + key n)).set position p).set
    pointer (codeAddress L m N Q + p)).write (codeAddress L m N Q + p) v).set
    pointer (originalAddress L m N Q + p)).write (originalAddress L m N Q + p) n).set
    position (p + 1)).write (cursorAddressBase L m N Q + key n) (p + 1)).set index (n + 1))
  have he : ExecWithin w scatterWrite x y 9 := by
    dsimp only [p] at hcode horig hnext
    simp only [packRegisters, code] at hv
    ram_eval [scatterWrite, y, hx.cursors, hx.codes, hx.originals, hx.tables.one,
      hi, ht, hv, hc, hcursor, hcode, horig, hnext, hnnext, p,
      cursorAddress, position, pointer, cursors, codes, originals, tile, index,
      packRegisters, code, BandPreparation.one, Fin.reduceFinMk, Fin.mk.injEq]
  have hy : Parameters L m N Q y := hx.reframe (by
    intro i hi
    apply he.regs_eq
    have h : ∀ i ∈ parameterRegisters, scatterWrite.Preserves i := by decide +kernel
    exact h i hi)
  refine ⟨y, he, hy, by simp [y, index], ?_, ?_, ?_, ?_⟩
  · change Function.update (Function.update
      (Function.update x.mem (codeAddress L m N Q + p) v)
      (originalAddress L m N Q + p) n)
      (cursorAddressBase L m N Q + key n) (p + 1) (codeAddress L m N Q + p) = v
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  · change Function.update (Function.update
      (Function.update x.mem (codeAddress L m N Q + p) v)
      (originalAddress L m N Q + p) n)
      (cursorAddressBase L m N Q + key n) (p + 1) (originalAddress L m N Q + p) = n
    rw [Function.update_of_ne (by omega), Function.update_self]
  · exact Function.update_self _ _ _
  · intro a hc hk ho
    change Function.update (Function.update
      (Function.update x.mem (codeAddress L m N Q + p) v)
      (originalAddress L m N Q + p) n)
      (cursorAddressBase L m N Q + key n) (p + 1) a = x.mem a
    rw [Function.update_of_ne hc, Function.update_of_ne ho, Function.update_of_ne hk]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
