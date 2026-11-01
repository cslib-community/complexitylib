/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Input
public import Complexity.Computability.WordRAM.Compile

/-!
# Initialized prime-selector code and actual header delivery

The existing counter's nine-instruction header reads raw `(n,D)` and computes the three
original array pointers and workspace start. It only reads/copies the second scalar; no
counter is run with `D` as a modulus. Six copies preserve these actual arguments in the
selector's high bank before its loop computes and tests candidate primes.

The input is the existing `CountPrime.inputWords n D values` format, interpreting the second
unsigned header as the window parameter rather than a supplied prime. The complete entry
program contains the actual cyclic-Strassen counter and no runtime solver argument.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

/-- Reuse the actual native matrix header and move its six arguments into selector metadata. -/
@[expose] def header : Code .standard 160 :=
  .seq (CountPrime.input.rename counterRegisters)
    (ram[ Reg.side ← Reg.countSide; Reg.window ← Reg.countPrime;
      Reg.inputAB ← Reg.countAB; Reg.inputBC ← Reg.countBC;
      Reg.inputAC ← Reg.countAC; Reg.scratch ← Reg.countScratch ])

/-- One fixed initialized native program, including the actual modular counter. -/
@[expose] def entryProgram : Code .standard 160 := .seq header (program CountPrime.program)

/-- The initialized selector adds 56 slots to the complete initialized counter's flat code. -/
theorem program_fixed : (entryProgram.program Reg.best).length ≤ 32824 ∧
    ¬(entryProgram.program Reg.best).ReadsWidth := by
  have hs : entryProgram.size = CountPrime.entryProgram.size + 56 := by
    simp only [entryProgram, header, Code.size, Code.size_rename, program_size,
      CountPrime.entryProgram, CountPrime.input]
    omega
  constructor
  · have hbound := CountPrime.program_fixed.1
    simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_cons, List.length_nil] at hbound ⊢
    rw [hs]
    omega
  · apply Code.not_readsWidth_program
    have hh : ¬header.ReadsWidth := by decide +kernel
    have hc : ¬CountPrime.program.ReadsWidth := by decide +kernel
    simpa only [entryProgram, Code.ReadsWidth, not_or] using
      And.intro hh (not_readsWidth hc)

/-- Read both original scalar words, compute all source/workspace pointers and deliver the
real selector metadata in fifteen charged instructions, preserving every memory cell. -/
theorem exec_header {W n D : ℕ} (x : Data 160) (hn : x.mem 1 = n) (hD : x.mem 2 = D)
    (hw : Fits W (3 + 3 * (n * n) + 8)) :
    ∃ y, ExecWithin W header x y 15 ∧ y.mem = x.mem ∧
      y.regs Reg.side = n ∧ y.regs Reg.window = D ∧
      y.regs Reg.inputAB = 3 ∧ y.regs Reg.inputBC = 3 + n * n ∧
      y.regs Reg.inputAC = 3 + 2 * (n * n) ∧ y.regs Reg.scratch = 3 + 3 * (n * n) := by
  have hinj : Function.Injective counterRegisters := by
    intro i j h
    exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)
  obtain ⟨s, he, hm, hs, hd, ha, hb, hc, hf⟩ :=
    CountPrime.exec_header (x.comap counterRegisters) hn hD hw
  let q := s.extend counterRegisters x
  have low (i : Fin 128) : q.regs (counterRegisters i) = s.regs i :=
    hinj.extend_apply _ _ _
  have qs : q.regs Reg.countSide = n := (low CountPrime.Reg.side).trans hs
  have qd : q.regs Reg.countPrime = D := (low CountPrime.Reg.modulus).trans hd
  have qa : q.regs Reg.countAB = 3 := (low CountPrime.Reg.inputAB).trans ha
  have qb : q.regs Reg.countBC = 3 + n * n := (low CountPrime.Reg.inputBC).trans hb
  have qc : q.regs Reg.countAC = 3 + 2 * (n * n) := (low CountPrime.Reg.inputAC).trans hc
  have qf : q.regs Reg.countScratch = 3 + 3 * (n * n) := (low CountPrime.Reg.scratch).trans hf
  let y := (((((q.set Reg.side n).set Reg.window D).set Reg.inputAB 3).set
    Reg.inputBC (3 + n * n)).set Reg.inputAC (3 + 2 * (n * n))).set
    Reg.scratch (3 + 3 * (n * n))
  have copy : ExecWithin (B := .standard) W
      (ram[ Reg.side ← Reg.countSide; Reg.window ← Reg.countPrime;
        Reg.inputAB ← Reg.countAB; Reg.inputBC ← Reg.countBC;
        Reg.inputAC ← Reg.countAC; Reg.scratch ← Reg.countScratch ]) q y 6 := by
    ram_eval [y, qs, qd, qa, qb, qc, qf, Reg.side, Reg.window, Reg.inputAB, Reg.inputBC,
      Reg.inputAC, Reg.scratch, Reg.countSide, Reg.countPrime, Reg.countAB, Reg.countBC,
      Reg.countAC, Reg.countScratch, Fin.mk.injEq]
  refine ⟨y, (he.rename hinj).seq copy, hm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
