/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Program
public import Complexity.Computability.WordRAM.MemoryWindow.Normalization

/-!
# Fixed code and selector-register frame

The complete translated solver moves as one bank. Register framing uses its embedding,
without expanding the product or verifier instruction graph. The selector bank and the eight
original caller arguments survive every actual call.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

open Cslib.WordRAM

/-- The entire source bank is embedded injectively, including all compiler temporaries. -/
theorem sourceBank_injective : Function.Injective sourceBank := by
  intro i j h
  have hv := congrArg Fin.val h
  exact Fin.ext (by simpa only [sourceBank] using Nat.add_left_cancel hv)

private theorem small_preserves : ∀ i : Fin 640,
    i.val < 160 ∨ (600 ≤ i.val ∧ i.val < 608) →
    header.Preserves i ∧ firstCopy.Preserves i ∧
    (nextCopy Reg.bc).Preserves i ∧ (nextCopy Reg.ac).Preserves i ∧
    sizeArgument.Preserves i ∧
    powerArguments.Preserves i ∧ windowArguments.Preserves i ∧
    receive.Preserves i ∧ (.op (.copy Reg.total (copyBank 7)) : Code .standard 640).Preserves i :=
  by decide +kernel

/-- Both the selector's low 160 registers and the actual original call arguments are preserved
syntactically, for all executions and every physical word width. -/
theorem program_preserves (i : Fin 640)
    (hi : i.val < 160 ∨ (600 ≤ i.val ∧ i.val < 608)) : program.Preserves i := by
  have src_out : i.val < 160 ∨ 160 + 419 ≤ i.val := by omega
  have aux_out : i.val < 620 := by omega
  obtain ⟨hh, hf, hb, ha, hs, hp, hm, hr, ht⟩ := small_preserves i hi
  have hc := Code.preserves_rename_of_offset ArrayCopySum.program copyBank
    (fun _ => rfl) i (Or.inl aux_out)
  have hl := Code.preserves_rename_of_offset NatClog.program clogBank
    (fun _ => rfl) i (Or.inl aux_out)
  have hpow := Code.preserves_rename_of_offset Power.program powerBank
    (fun _ => rfl) i (Or.inl aux_out)
  have hn := Code.preserves_rename_of_offset (MemoryWindow.normalizeRegisters 416)
    sourceBank (fun _ => rfl) i src_out
  have hsolve := Code.preserves_rename_of_offset (MemoryWindow.compile StreamingFixedPrime.program)
    sourceBank (fun _ => rfl) i src_out
  have hadapt : adapt.Preserves i := ⟨hh, hf, hc, hb, hc, ha, hc, ht⟩
  have hsetup : setup.Preserves i := ⟨hs, hl, hp, hpow, hm, hn⟩
  exact ⟨hadapt, hsetup, hsolve, hr⟩

private theorem adapt_size : adapt.size = 59 := by decide +kernel

private theorem setup_size : setup.size = 446 := by
  simp only [setup, Code.size, Code.size_rename, MemoryWindow.size_normalizeRegisters]
  decide +kernel

/-- Runtime modulus computation, translation and input adaptation never read physical width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by
  have hc : ¬solve.ReadsWidth := by
    simpa only [solve, Code.readsWidth_rename, MemoryWindow.readsWidth_compile] using
      StreamingFixedPrime.program_not_readsWidth
  have ha : ¬adapt.ReadsWidth := by decide +kernel
  have hs : ¬setup.ReadsWidth := by
    simp only [setup, Code.ReadsWidth, Code.readsWidth_rename,
      MemoryWindow.normalizeRegisters_not_readsWidth, or_false]
    decide +kernel
  have hr : ¬receive.ReadsWidth := by decide +kernel
  exact not_or.mpr ⟨ha, not_or.mpr ⟨hs, not_or.mpr ⟨hc, hr⟩⟩⟩

/-- One fixed standard program with 640 registers, at most 400000 slots including halt,
and no reads of the physical width. -/
theorem program_fixed : (program.program Reg.found).length ≤ 400000 ∧
    ¬(program.program Reg.found).ReadsWidth := by
  refine ⟨?_, Code.not_readsWidth_program program_not_readsWidth _⟩
  have hsource := StreamingFixedPrime.program_fixed.1
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hsource ⊢
  have hcompile := MemoryWindow.size_compile StreamingFixedPrime.program
  simp only [program, Code.size, adapt_size, setup_size, solve, Code.size_rename]
  have hreceive : receive.size = 5 := by decide +kernel
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
