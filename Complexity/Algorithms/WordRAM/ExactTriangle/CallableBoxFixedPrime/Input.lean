/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime.Exec

/-!
# Actual initialized entry for the callable fixed-prime solver

The input convention is exactly `PreparationInput.input`: four raw scalar headers followed
by three canonical signed squares. Four actual loads and native pointer arithmetic deliver
the high-bank caller arguments. Workspace starts immediately after the original input;
the subsequent adapter leaves the entire original block intact.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime

open Cslib.WordRAM CallableFixedPrime

/-- The same complete solver, with original-input argument delivery. -/
@[expose] def entryProgram : Code .standard 640 := .seq entryHeader program

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

/-- Original-input header delivery also retains the selector/parameter bank. -/
theorem entryProgram_preserves_selector (j : Fin 640) (hj : j.val < 160) :
    entryProgram.Preserves j :=
  ⟨(CallableFixedPrime.entryProgram_preserves_selector j hj).1, program_preserves j (Or.inl hj)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime
