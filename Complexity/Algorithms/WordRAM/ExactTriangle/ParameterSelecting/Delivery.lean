/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program

/-!
# Charged selector and exhaustive-solver argument delivery

These internal interfaces describe the actual eight-copy selector delivery and six-copy slow
protocol. They neither compute an uncharged layout nor assume that a callee accepts relocated
registers: the entire actual callee bank is transported by the existing execution semantics.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

private theorem selectArguments_preserves : ∀ j : Fin 640,
    143 ≤ j.val → j ≠ CallableFixedPrime.Reg.dimension → j ≠ CallableFixedPrime.Reg.groups →
      selectArguments.Preserves j := by decide +kernel

private theorem slowArguments_preserves : ∀ j : Fin 640,
    6 ≤ j.val → slowArguments.Preserves j := by decide +kernel

/-- Deliver computed D,g and the original source pointers to the actual selector in eight copies. -/
theorem exec_selectArguments {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W selectArguments x y 8 ∧ y.mem = x.mem ∧
      y.regs CallableFixedPrime.Reg.dimension =
        x.regs (parameterBank DyadicParameters.Reg.window) ∧
      y.regs CallableFixedPrime.Reg.groups = x.regs (parameterBank DyadicParameters.Reg.groups) ∧
      y.regs (selectorBank PrimeSelection.Reg.side) = x.regs CallableFixedPrime.Reg.n ∧
      y.regs (selectorBank PrimeSelection.Reg.window) =
        x.regs (parameterBank DyadicParameters.Reg.window) ∧
      y.regs (selectorBank PrimeSelection.Reg.inputAB) = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs (selectorBank PrimeSelection.Reg.inputBC) = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs (selectorBank PrimeSelection.Reg.inputAC) = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs (selectorBank PrimeSelection.Reg.scratch) = x.regs CallableFixedPrime.Reg.base ∧
      ∀ j : Fin 640, 143 ≤ j.val → j ≠ CallableFixedPrime.Reg.dimension →
        j ≠ CallableFixedPrime.Reg.groups → y.regs j = x.regs j := by
  let d := x.regs (parameterBank DyadicParameters.Reg.window)
  let g := x.regs (parameterBank DyadicParameters.Reg.groups)
  let y := x.set CallableFixedPrime.Reg.dimension d |>.set CallableFixedPrime.Reg.groups g
    |>.set (selectorBank PrimeSelection.Reg.side) (x.regs CallableFixedPrime.Reg.n)
    |>.set (selectorBank PrimeSelection.Reg.window) d
    |>.set (selectorBank PrimeSelection.Reg.inputAB) (x.regs CallableFixedPrime.Reg.ab)
    |>.set (selectorBank PrimeSelection.Reg.inputBC) (x.regs CallableFixedPrime.Reg.bc)
    |>.set (selectorBank PrimeSelection.Reg.inputAC) (x.regs CallableFixedPrime.Reg.ac)
    |>.set (selectorBank PrimeSelection.Reg.scratch) (x.regs CallableFixedPrime.Reg.base)
  have he : ExecWithin W selectArguments x y 8 := by
    ram_eval [selectArguments, y, d, g, parameterBank, selectorBank,
      DyadicParameters.Reg.window, DyadicParameters.Reg.groups,
      CallableFixedPrime.Reg.dimension, CallableFixedPrime.Reg.groups, CallableFixedPrime.Reg.n,
      CallableFixedPrime.Reg.ab, CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac,
      CallableFixedPrime.Reg.base, PrimeSelection.Reg.side, PrimeSelection.Reg.window,
      PrimeSelection.Reg.inputAB, PrimeSelection.Reg.inputBC, PrimeSelection.Reg.inputAC,
      PrimeSelection.Reg.scratch, Fin.mk.injEq]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun j hj hd hg => he.regs_eq (selectArguments_preserves j hj hd hg)⟩
  all_goals simp +decide [y, d, g, parameterBank, selectorBank,
    DyadicParameters.Reg.window, DyadicParameters.Reg.groups,
    CallableFixedPrime.Reg.dimension, CallableFixedPrime.Reg.groups, CallableFixedPrime.Reg.n,
    CallableFixedPrime.Reg.ab, CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac,
    CallableFixedPrime.Reg.base, PrimeSelection.Reg.side, PrimeSelection.Reg.window,
    PrimeSelection.Reg.inputAB, PrimeSelection.Reg.inputBC, PrimeSelection.Reg.inputAC,
    PrimeSelection.Reg.scratch]

/-- Deliver the unchanged original six-word host protocol before the real exhaustive call. -/
theorem exec_slowArguments {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W slowArguments x y 6 ∧ y.mem = x.mem ∧
      y.regs Reg.side = x.regs CallableFixedPrime.Reg.n ∧
      y.regs Reg.bound = x.regs Reg.savedBound ∧
      y.regs Reg.ab = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs Reg.bc = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs Reg.ac = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs Reg.free = x.regs CallableFixedPrime.Reg.base ∧
      ∀ j : Fin 640, 6 ≤ j.val → y.regs j = x.regs j := by
  let y := x.set Reg.side (x.regs CallableFixedPrime.Reg.n) |>.set Reg.bound
    (x.regs Reg.savedBound) |>.set Reg.ab (x.regs CallableFixedPrime.Reg.ab)
    |>.set Reg.bc (x.regs CallableFixedPrime.Reg.bc) |>.set Reg.ac
    (x.regs CallableFixedPrime.Reg.ac) |>.set Reg.free (x.regs CallableFixedPrime.Reg.base)
  have he : ExecWithin W slowArguments x y 6 := by
    ram_eval [slowArguments, y, Reg.side, Reg.bound, Reg.savedBound, Reg.ab, Reg.bc,
      Reg.ac, Reg.free, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
      CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base,
      Fin.mk.injEq]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    fun j hj => he.regs_eq (slowArguments_preserves j hj)⟩
  all_goals simp +decide [y, Reg.savedBound, Reg.bound, Reg.side, Reg.ab, Reg.bc, Reg.ac,
    Reg.free, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
    CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base]

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
