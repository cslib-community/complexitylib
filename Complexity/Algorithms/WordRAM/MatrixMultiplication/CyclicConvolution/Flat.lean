/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Exec

/-!
# Fixed native cyclic-convolution code and charged flat runs

The caller supplies only the two canonical signed arrays, ordinary runtime pointers/length,
and numerical admission bounds. The actual returned pointer, prefix run, charged halt and
coefficient memory all refer to the same final state. This is a cyclic ring coefficient
kernel, not a triangle-counting or Strassen endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.CyclicIntRing

/-- The complete kernel is fixed standard code, independent of length and physical width. -/
theorem program_fixed : (program.program Reg.output).length ≤ 256 ∧
    ¬(program.program Reg.output).ReadsWidth := by
  constructor
  · decide +kernel
  · apply Code.not_readsWidth_program
    decide +kernel

/-- Actual flat execution from a caller state, with all original magnitude, address and
separation premises. There is no supplied execution, convolution answer or time certificate. -/
theorem runs {w p A B : ℕ} (x : Data 32) (u v : ℕ → ℤ)
    (hlen : x.regs Reg.length = p)
    (hbound : GenericRAM.Signed.Fits w (magnitudeBound p A B : ℤ))
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B)
    (hA : ∀ i < p, x.mem (x.regs Reg.inputA + i) = encode (u i))
    (hB : ∀ i < p, x.mem (x.regs Reg.inputB + i) = encode (v i))
    (h2p : Fits (w + 2) (2 * p))
    (ha : Fits (w + 2) (x.regs Reg.inputA + p))
    (hb : Fits (w + 2) (x.regs Reg.inputB + p))
    (hout : Fits (w + 2) (x.regs Reg.output + p))
    (hdisjA : x.regs Reg.inputA + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputA)
    (hdisjB : x.regs Reg.inputB + p ≤ x.regs Reg.output ∨
      x.regs Reg.output + p ≤ x.regs Reg.inputB) :
    ∃ y t, t + 1 ≤ 42 * p * p + 9 * p + 5 ∧
      Runs (w + 2) (program.program Reg.output) ⟨0, x⟩ ⟨program.size, y⟩ t ∧
      Executes (w + 2) (program.program Reg.output) ⟨0, x⟩ (x.regs Reg.output) (t + 1) ∧
      (∀ r < p, y.mem (x.regs Reg.output + r) = encode (convolution p u v r)) ∧
      (∀ a, a < x.regs Reg.output ∨ x.regs Reg.output + p ≤ a → y.mem a = x.mem a) ∧
      ∀ i, (9 ≤ i.val ∧ i.val ≤ 12) ∨ 19 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨y, he, values, frame, regs⟩ :=
    exec x u v hlen hbound hu hv hA hB h2p ha hb hout hdisjA hdisjB
  obtain ⟨t, ht, he⟩ := he
  refine ⟨y, t, by omega, ?_, ?_, values, frame, regs⟩
  · simpa only [Nat.zero_add] using he.runs (pc := 0)
      (p := program.program Reg.output) (Program.Contains.self _).append_left
  · simpa only [regs Reg.output (by decide)] using he.executes Reg.output

end Cslib.Algorithms.WordRAM.CyclicConvolution
