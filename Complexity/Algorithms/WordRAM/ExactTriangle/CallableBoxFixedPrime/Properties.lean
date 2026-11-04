/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime.Program

/-!
# Fixed box-caller code and preserved selector bank

The changed solver moves inside the same disjoint compiler bank. Syntactic preservation and
width independence of the unchanged actual copy/setup/return blocks are reused directly.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime

open Cslib.WordRAM CallableFixedPrime

/-- The low160 selector registers and all eight original arguments survive the actual call. -/
theorem program_preserves (i : Fin 640)
    (hi : i.val < 160 ∨ (600 ≤ i.val ∧ i.val < 608)) : program.Preserves i := by
  obtain ⟨ha, hs, -, hr⟩ := CallableFixedPrime.program_preserves i hi
  have hsolve := Code.preserves_rename_of_forall_ne
    (MemoryWindow.compile BoxFixedPrime.program) sourceBank i (by
      intro j h
      have hv := congrArg Fin.val h
      have hj := j.isLt
      change 160 + j.val = i.val at hv
      rcases hi with h | h <;> omega)
  exact ⟨ha, hs, hsolve, hr⟩

/-- The actual setup computes a virtual width; no block reads the physical width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by
  have h := CallableFixedPrime.program_not_readsWidth
  obtain ⟨ha, h⟩ := not_or.mp h
  obtain ⟨hs, h⟩ := not_or.mp h
  obtain ⟨-, hr⟩ := not_or.mp h
  have hc : ¬solve.ReadsWidth := by
    simpa only [solve, Code.readsWidth_rename, MemoryWindow.readsWidth_compile] using
      BoxFixedPrime.program_not_readsWidth
  exact not_or.mpr ⟨ha, not_or.mpr ⟨hs, not_or.mpr ⟨hc, hr⟩⟩⟩

/-- One fixed640-register standard program with at most400000 slots, including halt. -/
theorem program_fixed : (program.program Reg.found).length ≤ 400000 ∧
    ¬(program.program Reg.found).ReadsWidth := by
  refine ⟨?_, Code.not_readsWidth_program program_not_readsWidth _⟩
  have hsource := BoxFixedPrime.program_fixed.1
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hsource ⊢
  have hcompile := MemoryWindow.size_compile BoxFixedPrime.program
  have hadapt : adapt.size = 59 := by decide +kernel
  have hsetup : setup.size = 446 := by
    simp only [setup, Code.size, Code.size_rename, MemoryWindow.size_normalizeRegisters]
    decide +kernel
  have hreceive : receive.size = 5 := by decide +kernel
  simp only [program, Code.size, hadapt, hsetup, solve, Code.size_rename]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableBoxFixedPrime
