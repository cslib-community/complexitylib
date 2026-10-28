/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandHeader

/-!
# Native copies used by the band-preparation caller

## Main results

* `BandPreparation.exec_copyKernel`: reuse the actual array-copy program in its fixed low
  register bank, preserving every persistent register and permitting both address orders.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM

/-- The seven low copy registers are embedded injectively. -/
theorem copyRegisters_injective : Function.Injective copyRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 96 => i.val) h)

/-- The unchanged encoder occupies precisely its original low register bank. -/
theorem encoderRegisters_injective : Function.Injective encoderRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 96 => i.val) h)

/-- Copying uses only the original seven-register routine and its actual native cost.
The persistent high register bank is untouched; arbitrary outside memory is preserved
by the explicit `copyPrefix` result. -/
theorem exec_copyKernel {w : ℕ} (x : Data 96) (h1 : Fits w 1)
    (hs : Fits w (x.regs copySrc + x.regs copyLen))
    (hd : Fits w (x.regs copyDst + x.regs copyLen))
    (hsep : x.regs copySrc + x.regs copyLen ≤ x.regs copyDst ∨
      x.regs copyDst + x.regs copyLen ≤ x.regs copySrc ∨ x.regs copySrc = x.regs copyDst) :
    ∃ y, ExecWithin w (ArrayCopy.program.rename copyRegisters) x y (7 * x.regs copyLen + 4) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (x.regs copySrc) (x.regs copyDst) (x.regs copyLen) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  obtain ⟨z, hz, hm, _, _, _⟩ := ArrayCopy.exec_of_separated_or_eq (x.comap copyRegisters)
    h1 hs hd hsep
  have he := hz.rename copyRegisters_injective
  refine ⟨z.extend copyRegisters x, he, hm, ?_⟩
  intro i hi
  apply he.regs_eq
  have hf : ∀ i : Fin 96, 7 ≤ i.val → (ArrayCopy.program.rename copyRegisters).Preserves i := by
    simp only [ArrayCopy.program, ArrayCopy.body, Code.rename, Code.Preserves,
      Op.rename, Op.bin, Op.dest, copyRegisters]
    decide
  exact hf i hi

private theorem lowSetup_regs (x : Data 96) (s d n : ℕ) (i : Fin 96) (hi : 7 ≤ i.val) :
    (((x.set copySrc s).set copyDst d).set copyLen n).regs i = x.regs i := by
  have hs : i ≠ copySrc := by intro h; subst i; norm_num [copySrc] at hi
  have hd : i ≠ copyDst := by intro h; subst i; norm_num [copyDst] at hi
  have hn : i ≠ copyLen := by intro h; subst i; norm_num [copyLen] at hi
  simp only [Data.set_regs, Function.update_of_ne hs, Function.update_of_ne hd,
    Function.update_of_ne hn]

/-- Protect the entire original initialized prefix, including header zero, with the actual
native copy. Source words and all memory outside the snapshot block remain untouched. -/
theorem exec_saveInput {w L m N : ℕ} (x : Data 96) (hx : HeaderPost L m N x)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w saveInput x y (7 * inputEnd m N + 7) ∧
      y.mem = ArrayCopy.copyPrefix x.mem 0 (snapshotBase L m N) (inputEnd m N) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  let start := ((x.set copySrc 0).set copyDst (snapshotBase L m N)).set copyLen (inputEnd m N)
  have hb : Fits w (inputEnd m N) := (memory_fits hfit).of_le (input_le_memoryEnd L m N)
  have hi : Fits w (inverseBase L m N) :=
    (memory_fits hfit).of_le (inverse_le_memoryEnd L m N)
  obtain ⟨y, hy, hm, hf⟩ := exec_copyKernel start (small_fits hfit (by decide))
    (by simpa [start, copySrc, copyDst, copyLen] using hb)
    (by simpa [start, copySrc, copyDst, copyLen, inverseBase] using hi)
    (Or.inl (by simpa [start, copySrc, copyDst, copyLen] using input_le_snapshot L m N))
  have h0 : ExecWithin (B := .standard) w (.op (.const copySrc 0))
      x (x.set copySrc 0) 1 := ExecWithin.const (fits_zero w)
  have h1 : ExecWithin (B := .standard) w (.op (.copy copyDst snapshot))
      (x.set copySrc 0) ((x.set copySrc 0).set copyDst (snapshotBase L m N)) 1 := by
    ram_eval [hx.snapshot, copySrc, copyDst, snapshot, Fin.mk.injEq]
  have h2 : ExecWithin (B := .standard) w (.op (.copy copyLen prefixSize))
      ((x.set copySrc 0).set copyDst (snapshotBase L m N)) start 1 := by
    ram_eval [start, hx.prefixSize, copySrc, copyDst, copyLen, prefixSize, Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_⟩
  · apply (h0.seq (h1.seq (h2.seq hy))).mono
    have hn : start.regs copyLen = inputEnd m N := by simp [start]
    rw [hn]
    omega
  · simpa [start, copySrc, copyDst, copyLen] using hm
  · intro i hi
    exact (hf i hi).trans (lowSetup_regs x _ _ _ i hi)

/-- Restore the complete original input using the reverse disjoint-copy case. This copies
the actual protected words rather than reconstructing or assuming the input is unchanged. -/
theorem exec_restoreInput {w L m N : ℕ} (x : Data 96) (hx : HeaderPost L m N x)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w restoreInput x y (7 * inputEnd m N + 7) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (snapshotBase L m N) 0 (inputEnd m N) ∧
      (∀ i, 7 ≤ i.val → y.regs i = x.regs i) := by
  let start := ((x.set copySrc (snapshotBase L m N)).set copyDst 0).set copyLen (inputEnd m N)
  have hb : Fits w (inputEnd m N) := (memory_fits hfit).of_le (input_le_memoryEnd L m N)
  have hi : Fits w (inverseBase L m N) :=
    (memory_fits hfit).of_le (inverse_le_memoryEnd L m N)
  obtain ⟨y, hy, hm, hf⟩ := exec_copyKernel start (small_fits hfit (by decide))
    (by simpa [start, copySrc, copyDst, copyLen, inverseBase] using hi)
    (by simpa [start, copySrc, copyDst, copyLen] using hb)
    (Or.inr (Or.inl (by
      simpa [start, copySrc, copyDst, copyLen] using input_le_snapshot L m N)))
  have h0 : ExecWithin (B := .standard) w (.op (.copy copySrc snapshot))
      x (x.set copySrc (snapshotBase L m N)) 1 := by ram_eval [hx.snapshot]
  have h1 : ExecWithin (B := .standard) w (.op (.const copyDst 0))
      (x.set copySrc (snapshotBase L m N))
      ((x.set copySrc (snapshotBase L m N)).set copyDst 0) 1 := ExecWithin.const (fits_zero w)
  have h2 : ExecWithin (B := .standard) w (.op (.copy copyLen prefixSize))
      ((x.set copySrc (snapshotBase L m N)).set copyDst 0) start 1 := by
    ram_eval [start, hx.prefixSize, copySrc, copyDst, copyLen, prefixSize, Fin.mk.injEq]
  refine ⟨y, ?_, ?_, ?_⟩
  · apply (h0.seq (h1.seq (h2.seq hy))).mono
    have hn : start.regs copyLen = inputEnd m N := by simp [start]
    rw [hn]
    omega
  · simpa [start, copySrc, copyDst, copyLen] using hm
  · intro i hi
    exact (hf i hi).trans (lowSetup_regs x _ _ _ i hi)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
