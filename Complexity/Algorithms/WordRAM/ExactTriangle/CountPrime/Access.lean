/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Spread

/-!
# Charged native modular-counter matrix accesses

The Morton block reads two actual words from the previously computed spread table. The
residue block computes the actual row-major address, transposing BC when requested. These
are internal stage contracts; the composed counter supplies the table through its proved
construction and the residues through the existing native signed-remainder loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Six actual instructions read the table and compute the Morton index. The input row and
column and the original table pointer are preserved. -/
theorem exec_morton {w k : ℕ} (x : Data 128) (h2 : x.regs Reg.two = 2)
    (hr : x.regs Reg.row < 2 ^ k) (hc : x.regs Reg.column < 2 ^ k)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + 4 ^ k + 2 ^ k)) :
    ∃ y, ExecWithin w morton x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.position = Nat.Morton.index (x.regs Reg.row) (x.regs Reg.column) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.rowSpread → i ≠ Reg.columnSpread →
        i ≠ Reg.position → y.regs i = x.regs i := by
  have hreadr := htable _ hr
  have hreadc := htable _ hc
  have hi := Nat.Morton.index_lt hr hc
  have hsum : Fits w
      (Nat.Morton.spread (x.regs Reg.row) * 2 + Nat.Morton.spread (x.regs Reg.column)) :=
    hw.of_le (by unfold Nat.Morton.index at hi; omega)
  have hprod : Fits w (Nat.Morton.spread (x.regs Reg.row) * 2) := hw.of_le (by
    unfold Nat.Morton.index at hi
    omega)
  have haddrR : Fits w (x.regs Reg.spread + x.regs Reg.row) := hw.of_le (by omega)
  have haddrC : Fits w (x.regs Reg.spread + x.regs Reg.column) := hw.of_le (by omega)
  refine ⟨?y, ?run, ?mem, ?position, ?regs⟩
  case run =>
    ram_eval [morton, h2, hreadr, hreadc, hsum, hprod, haddrR, haddrC,
      Reg.address, Reg.spread, Reg.rowSpread, Reg.columnSpread, Reg.position,
      Reg.row, Reg.column, Reg.two]
  case mem => rfl
  case position => simp only [Data.set, Function.update_self, Nat.Morton.index, Nat.mul_comm]
  case regs =>
    intro i ha hr hc hp
    simp only [Data.set, Function.update_of_ne ha, Function.update_of_ne hr,
      Function.update_of_ne hc, Function.update_of_ne hp]

/-- Four actual instructions perform an admitted original-matrix residue read. The
transpose is fixed code selection, while both coordinates and the pointer are runtime data. -/
theorem exec_readResidue {w : ℕ} (transpose : Bool) (x : Data 128)
    (hr : x.regs Reg.row < x.regs Reg.side) (hc : x.regs Reg.column < x.regs Reg.side)
    (hw : Fits w (x.regs Reg.residueSource + x.regs Reg.side * x.regs Reg.side)) :
    ∃ y, ExecWithin w (readResidue transpose) x y 4 ∧ y.mem = x.mem ∧
      y.regs Reg.residue = x.mem (x.regs Reg.residueSource +
        if transpose then x.regs Reg.column * x.regs Reg.side + x.regs Reg.row
        else x.regs Reg.row * x.regs Reg.side + x.regs Reg.column) ∧
      ∀ i, i ≠ Reg.address → i ≠ Reg.temporary → i ≠ Reg.residue → y.regs i = x.regs i := by
  have hrow := Nat.mul_le_mul_right (x.regs Reg.side) (Nat.succ_le_of_lt hr)
  have hcol := Nat.mul_le_mul_right (x.regs Reg.side) (Nat.succ_le_of_lt hc)
  rw [Nat.succ_mul] at hrow hcol
  have hpr : Fits w (x.regs Reg.row * x.regs Reg.side) := hw.of_le (by omega)
  have hpc : Fits w (x.regs Reg.column * x.regs Reg.side) := hw.of_le (by omega)
  have hir : Fits w (x.regs Reg.row * x.regs Reg.side + x.regs Reg.column) :=
    hw.of_le (by omega)
  have hic : Fits w (x.regs Reg.column * x.regs Reg.side + x.regs Reg.row) :=
    hw.of_le (by omega)
  have har : Fits w (x.regs Reg.residueSource +
      (x.regs Reg.row * x.regs Reg.side + x.regs Reg.column)) := hw.of_le (by omega)
  have hac : Fits w (x.regs Reg.residueSource +
      (x.regs Reg.column * x.regs Reg.side + x.regs Reg.row)) := hw.of_le (by omega)
  cases transpose with
  | false =>
    refine ⟨?y, ?run, ?mem, ?residue, ?regs⟩
    case run =>
      ram_eval [readResidue, hpr, hir, har, Reg.row, Reg.column,
        Reg.side, Reg.residueSource, Reg.address, Reg.temporary, Reg.residue]
    case mem => rfl
    case residue => rfl
    case regs =>
      intro i ha ht hr
      simp only [Data.set, Function.update_of_ne ha, Function.update_of_ne ht,
        Function.update_of_ne hr]
  | true =>
    refine ⟨?yTrue, ?runTrue, ?memTrue, ?residueTrue, ?regsTrue⟩
    case runTrue =>
      ram_eval [readResidue, hpc, hic, hac, Reg.row, Reg.column,
        Reg.side, Reg.residueSource, Reg.address, Reg.temporary, Reg.residue]
    case memTrue => rfl
    case residueTrue => rfl
    case regsTrue =>
      intro i ha ht hr
      simp only [Data.set, Function.update_of_ne ha, Function.update_of_ne ht,
        Function.update_of_ne hr]

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
