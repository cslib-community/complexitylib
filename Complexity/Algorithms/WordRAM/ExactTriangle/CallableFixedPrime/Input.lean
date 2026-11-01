/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Exec

/-!
# Actual initialized entry for the callable fixed-prime solver

The input convention is exactly `PreparationInput.input`: four raw scalar headers followed
by three canonical signed squares. Four actual loads and native pointer arithmetic deliver
the high-bank caller arguments. Workspace starts immediately after the original input;
the subsequent adapter leaves the entire original block intact.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- Workspace after the original input's length word, four headers and three squares. -/
@[expose] def workspaceBase (n : ℕ) : ℕ := 5 + 3 * (n * n)

/-- An original-input bound for the initialized caller's words. No scan or clearing of this
reservation is performed; the actual copy loop computes the source modulus later. -/
@[expose] def inputWordBound (n D g p : ℕ) (values : List ℤ) : ℕ :=
  4 * windowSize n D g p (rawTotal n values)

/-- Positive initialized physical threshold, independent of a larger chosen width. -/
@[expose] def inputWidth (n D g p : ℕ) (values : List ℤ) : ℕ :=
  admissionWidth n D g p (rawTotal n values) (workspaceBase n) (inputWordBound n D g p values)

open Reg in
/-- Read the original raw headers and compute all actual caller pointers. -/
@[expose] def entryHeader : Code .standard 640 := ram[
  one ← #1; address ← #1; dimension ← *address;
  address ← address + one; groups ← *address;
  address ← address + one; n ← *address;
  address ← address + one; prime ← *address;
  area ← n * n; ab ← #5; bc ← ab + area; ac ← bc + area; base ← ac + area ]

/-- The same complete solver, with original-input argument delivery. -/
@[expose] def entryProgram : Code .standard 640 := .seq entryHeader program

/-- Fixed original-input setup, with every load, addition and multiplication charged. -/
theorem entryHeader_fixed : entryHeader.size = 14 ∧ ¬entryHeader.ReadsWidth := by decide +kernel

/-- The initialized program also has fixed code and no reads of physical width. -/
theorem entryProgram_fixed : (entryProgram.program Reg.found).length ≤ 400014 ∧
    ¬(entryProgram.program Reg.found).ReadsWidth := by
  have hno : ¬entryProgram.ReadsWidth :=
    not_or.mpr ⟨entryHeader_fixed.2, program_not_readsWidth⟩
  refine ⟨?_, Code.not_readsWidth_program hno _⟩
  have h := program_fixed.1
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton, entryProgram, Code.size, entryHeader_fixed.1] at h ⊢
  omega

private theorem entryHeader_selector_frame : ∀ j : Fin 640, j.val < 160 →
    entryHeader.Preserves j := by decide +kernel

/-- Original-input header delivery also retains the selector/parameter bank. -/
theorem entryProgram_preserves_selector (j : Fin 640) (hj : j.val < 160) :
    entryProgram.Preserves j :=
  ⟨entryHeader_selector_frame j hj, program_preserves j (Or.inl hj)⟩

/-- The real initialized setup provides actual runtime pointers and preserves every original
memory cell. Its only numerical premise concerns the original scalar/address arithmetic. -/
theorem exec_entryHeader {W n D g p : ℕ} (values : List ℤ)
    (hfit : Fits W (n + D + g + p + 5 + 3 * (n * n) + 1024)) :
    ∃ x : Data 640, ExecWithin W entryHeader
        (.init (PreparationInput.input n D g p values)) x 14 ∧
      x.mem = (Data.init (PreparationInput.input n D g p values) : Data 640).mem ∧
      x.regs Reg.n = n ∧ x.regs Reg.dimension = D ∧
      x.regs Reg.groups = g ∧ x.regs Reg.prime = p ∧ x.regs Reg.ab = 5 ∧
      x.regs Reg.bc = 5 + n * n ∧ x.regs Reg.ac = 5 + n * n + n * n ∧
      x.regs Reg.base = workspaceBase n := by
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h4 : Fits W 4 := hfit.of_le (by omega)
  have h5 : Fits W 5 := hfit.of_le (by omega)
  have ha : Fits W (n * n) := hfit.of_le (by omega)
  have hab : Fits W (5 + n * n) := hfit.of_le (by omega)
  have hac : Fits W (5 + n * n + n * n) := hfit.of_le (by omega)
  have hb : Fits W (5 + n * n + n * n + n * n) := hfit.of_le (by omega)
  generalize hstart : (Data.init (PreparationInput.input n D g p values) : Data 640) = initial
  have hDread : initial.mem 1 = D := by rw [← hstart]; simp [Data.init, PreparationInput.input]
  have hgread : initial.mem 2 = g := by rw [← hstart]; simp [Data.init, PreparationInput.input]
  have hnread : initial.mem 3 = n := by rw [← hstart]; simp [Data.init, PreparationInput.input]
  have hpread : initial.mem 4 = p := by rw [← hstart]; simp [Data.init, PreparationInput.input]
  refine ⟨?x, ?run, ?mem, ?sizeValue, ?dimensionValue, ?groupsValue, ?primeValue,
    ?ab, ?bc, ?ac, ?base⟩
  case run => ram_eval [entryHeader, hDread, hgread, hnread, hpread,
    h1, h2, h3, h4, h5, ha, hab, hac, hb, Reg.one, Reg.address,
    Reg.dimension, Reg.groups, Reg.n, Reg.prime, Reg.area, Reg.ab, Reg.bc, Reg.ac, Reg.base,
    Fin.mk.injEq]
  case mem => rfl
  case sizeValue => simp +decide
  case dimensionValue => simp +decide
  case groupsValue => simp +decide
  case primeValue => simp +decide
  case ab => simp +decide
  case bc => simp +decide
  case ac => simp +decide
  case base =>
    simpa +decide [workspaceBase] using
      (show 5 + n * n + n * n + n * n = 5 + 3 * (n * n) by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
