/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Prepare
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.InputLevel
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableBox.Program

/-!
# Actual threshold-aware patch of a prepared record's original input

The existing record preparer copies original zero/one matrices and coordinates.
Sixteen actual instructions replace its level and length words and append `m/9`.
No copied matrix/coordinate position changes. All producer/selection registers and
all memory outside the new local original-input span are preserved.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

namespace PatchReg
/-- Scratch slot holding the new level multiplier. -/
abbrev factor : Fin 320 := 84
/-- Scratch slot holding the threshold divisor. -/
abbrev divisor : Fin 320 := 85
end PatchReg

/-- Rewrite the actual level and length headers, and store the ordinary threshold. -/
@[expose] def patchInput : Code .standard 320 := ram[
  Reg.one ← #1; Reg.two ← #2; PatchReg.divisor ← #9; PatchReg.factor ← #21;
  Reg.address ← Reg.base + Reg.two; Reg.depth ← *Reg.address;
  Reg.level ← Reg.depth * PatchReg.factor;
  Reg.address ← Reg.base + Reg.one; *Reg.address ← Reg.level;
  Reg.address ← Reg.base; Reg.payloadLength ← *Reg.address;
  Reg.payloadLength ← Reg.payloadLength + Reg.one; *Reg.address ← Reg.payloadLength;
  Reg.address ← Reg.base + Reg.payloadLength;
  Reg.depth ← Reg.depth / PatchReg.divisor; *Reg.address ← Reg.depth ]

/-- The patch executes sixteen instructions and writes exactly three original words. -/
theorem exec_patchInput {W b m I : ℕ} (x : Data 320)
    (hb : x.regs Reg.base = b) (hm : x.mem (b + 2) = m)
    (hlen : x.mem b = I - 1) (hI : 5 ≤ I)
    (hfit : Fits W (b + I + 21 * m + 32)) :
    ∃ y, ExecWithin W patchInput x y 16 ∧
      y.mem = Function.update (Function.update (Function.update x.mem (b + 1) (21 * m))
        b I) (b + I) (m / 9) ∧
      y.regs Reg.base = b ∧
      ∀ j : Fin 320, j.val < 65 → y.regs j = x.regs j := by
  have hL : Fits W (m * 21) := hfit.of_le (by omega)
  have hbI : Fits W (b + I) := hfit.of_le (by omega)
  have hquot : Fits W (m / 9) := hfit.of_le (by omega)
  have hsucc : I - 1 + 1 = I := by omega
  have hne : b ≠ b + 1 := by omega
  let y := x.set Reg.one 1 |>.set Reg.two 2 |>.set PatchReg.divisor 9
    |>.set PatchReg.factor 21 |>.set Reg.address (b + 2) |>.set Reg.depth m
    |>.set Reg.level (m * 21) |>.set Reg.address (b + 1) |>.write (b + 1) (m * 21)
    |>.set Reg.address b |>.set Reg.payloadLength (I - 1) |>.set Reg.payloadLength I
    |>.write b I |>.set Reg.address (b + I) |>.set Reg.depth (m / 9)
    |>.write (b + I) (m / 9)
  have he : ExecWithin W patchInput x y 16 := by
    ram_eval [patchInput, y, hb, hm, hlen, hsucc, hL,
      hbI, hquot, Reg.one, Reg.two, PatchReg.divisor, PatchReg.factor, Reg.address,
      Reg.base, Reg.depth, Reg.level, Reg.payloadLength, hne, Fin.mk.injEq]
  refine ⟨y, he, ?_, ?_, ?_⟩
  · simp only [y, Data.set_mem, Data.write_mem, Nat.mul_comm m 21]
  · simpa +decide [y, Reg.base, Reg.one, Reg.two, PatchReg.divisor, PatchReg.factor,
      Reg.address, Reg.depth, Reg.level, Reg.payloadLength, Function.update_apply] using hb
  · intro j hj
    have hne (i : Fin 320) (hi : 65 ≤ i.val) : j ≠ i := by
      intro h
      subst i
      omega
    simp only [y, Data.write_regs, Data.set_regs,
      Function.update_of_ne (hne Reg.one (by decide)),
      Function.update_of_ne (hne Reg.two (by decide)),
      Function.update_of_ne (hne PatchReg.divisor (by decide)),
      Function.update_of_ne (hne PatchReg.factor (by decide)),
      Function.update_of_ne (hne Reg.address (by decide)),
      Function.update_of_ne (hne Reg.depth (by decide)),
      Function.update_of_ne (hne Reg.level (by decide)),
      Function.update_of_ne (hne Reg.payloadLength (by decide))]

/-- Patched memory realizes the complete new input, including the appended threshold. -/
theorem patch_input_readback {b m n : ℕ}
    (X : Matrix (Fin n) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin n) ℤ)
    (qs : List (Fin n × Fin n)) (x : Data 320)
    (hin : ∀ a, a < QueriedProduct.inputEnd m n qs.length → x.mem (b + a) =
      (State.init (QueriedProduct.input true (19 * m) X Y qs) : State 160).data.mem a)
    (a : ℕ) (ha : a < QueriedProduct.inputEnd m n qs.length + 1) :
    (Function.update (Function.update (Function.update x.mem (b + 1) (21 * m))
        b (QueriedProduct.inputEnd m n qs.length))
      (b + QueriedProduct.inputEnd m n qs.length) (m / 9)) (b + a) =
        (State.init (BoxProduct.input true (21 * m) (m / 9) X Y qs) : State 160).data.mem a := by
  have hI : 5 ≤ QueriedProduct.inputEnd m n qs.length := by unfold QueriedProduct.inputEnd; omega
  by_cases he : a = QueriedProduct.inputEnd m n qs.length
  · subst a
    rw [Function.update_self, BoxProduct.input_threshold]
  · rw [Function.update_of_ne (by omega)]
    by_cases h0 : a = 0
    · subst a
      simp only [Nat.add_zero, Function.update_self, State.init, Data.init_mem_zero,
        BoxProduct.input_length]
    · rw [Function.update_of_ne (by omega)]
      by_cases h1 : a = 1
      · subst a
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne (by omega), hin a (by omega)]
        exact (QueriedProduct.input_change_level true (19 * m) (21 * m) X Y qs a h1).trans
          (BoxProduct.input_prefix true X Y qs a (by omega) (by omega)).symm

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
