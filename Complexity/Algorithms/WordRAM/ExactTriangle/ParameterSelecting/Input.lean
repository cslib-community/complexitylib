/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.InputProgram
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Exec

/-!
# Real original-input header execution and input admission

The raw input is n,F followed by canonical-signed AB/BC/AC in row-major order. The existing
counter input representation is reused only as this two-scalar encoding; F is not interpreted
as a supplied prime. All pointers and the workspace boundary are computed by actual code.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

/-- Read original n,F, compute all original pointers and deliver the host protocol in15 steps. -/
theorem exec_entryHeader {W n F : ℕ} (x : Data 640) (hn : x.mem 1 = n) (hF : x.mem 2 = F)
    (hfit : Fits W (3 + 3 * (n * n) + 8)) :
    ∃ y, ExecWithin W entryHeader x y 15 ∧ y.mem = x.mem ∧
      y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = 3 ∧
      y.regs Reg.bc = 3 + n * n ∧ y.regs Reg.ac = 3 + 2 * (n * n) ∧
      y.regs Reg.free = 3 + 3 * (n * n) := by
  let bank := selectorBank ∘ PrimeSelection.counterRegisters
  have inj : Function.Injective bank := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 640 => k.val) h)
  obtain ⟨s, hs, sm, sn, sF, sa, sb, sc, sf⟩ :=
    CountPrime.exec_header (x.comap bank) hn hF hfit
  let a := s.extend bank x
  have ha : ExecWithin W (CountPrime.input.rename bank) x a 9 := hs.rename inj
  have reg (i : Fin 128) : a.regs (bank i) = s.regs i := inj.extend_apply _ _ _
  have an := (reg CountPrime.Reg.side).trans sn
  have aF := (reg CountPrime.Reg.modulus).trans sF
  have aa := (reg CountPrime.Reg.inputAB).trans sa
  have ab := (reg CountPrime.Reg.inputBC).trans sb
  have ac := (reg CountPrime.Reg.inputAC).trans sc
  have af := (reg CountPrime.Reg.scratch).trans sf
  let y := a.set Reg.side n |>.set Reg.bound F |>.set Reg.ab 3
    |>.set Reg.bc (3 + n * n) |>.set Reg.ac (3 + 2 * (n * n))
    |>.set Reg.free (3 + 3 * (n * n))
  let side := bank CountPrime.Reg.side
  let bound := bank CountPrime.Reg.modulus
  let regAB := bank CountPrime.Reg.inputAB
  let regBC := bank CountPrime.Reg.inputBC
  let regAC := bank CountPrime.Reg.inputAC
  let free := bank CountPrime.Reg.scratch
  have hcopies : ExecWithin (B := .standard) W
      (ram[ Reg.side ← side; Reg.bound ← bound; Reg.ab ← regAB; Reg.bc ← regBC;
        Reg.ac ← regAC; Reg.free ← free ]) a y 6 := by
    refine ⟨6, le_rfl, ?_⟩
    ram_eval [y, an, aF, aa, ab, ac, af, side, bound, regAB, regBC, regAC, free,
      Reg.side, Reg.bound, Reg.ab, Reg.bc, Reg.ac, Reg.free, CountPrime.Reg.side,
      CountPrime.Reg.modulus, CountPrime.Reg.inputAB, CountPrime.Reg.inputBC,
      CountPrime.Reg.inputAC, CountPrime.Reg.scratch, Fin.mk.injEq]
  refine ⟨y, ha.seq hcopies, sm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp +decide [y, Reg.side, Reg.bound, Reg.ab, Reg.bc, Reg.ac, Reg.free]

/-- Original scalar words and all original signed matrix words fit before the first instruction. -/
theorem input_fits {W n F : ℕ} (values : List ℤ) (hlen : values.length = 3 * (n * n))
    (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hW : executionWidth n F (3 + 3 * (n * n)) 3 (3 + n * n) (3 + 2 * (n * n)) values ≤ W) :
    InputFits W (CountPrime.inputWords n F values) := by
  have fit := envelope_fits values hW
  have hn := Nat.le_mul_self n
  refine ⟨?_, ?_⟩
  · simpa only [CountPrime.inputWords, List.length_append, List.length_cons, List.length_nil,
      List.length_map, hlen, Nat.reduceAdd] using fit.of_le (by dsimp only [envelope]; omega)
  · intro v hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · exact fit.of_le (by dsimp only [envelope]; omega)
      · exact fit.of_le (by dsimp only [envelope]; omega)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hm
      have hb := hv z hz
      apply fit.of_le
      have henc : Signed.encode z ≤ 2 * F + 1 := by unfold Signed.encode; split_ifs <;> omega
      exact henc.trans (by dsimp only [envelope]; omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
