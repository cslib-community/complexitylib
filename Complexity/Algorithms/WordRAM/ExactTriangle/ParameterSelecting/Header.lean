/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program

/-!
# Native saving and restoration of original ExactTriangle arguments

These internal execution rules charge every copy and keep the original memory unchanged.
Old registers are arbitrary; the parameter and solver stages receive their arguments from
real copies, not from a precomputed layout or an assumed caller-state relation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

private theorem save_preserves_low : ∀ j : Fin 640, j.val < 143 → save.Preserves j := by
  decide +kernel

private theorem restore_preserves_high : ∀ j : Fin 640, 7 ≤ j.val → restore.Preserves j := by
  decide +kernel

/-- Eight actual instructions save the original protocol and seed the real parameter input. -/
theorem exec_save {W : ℕ} (x : Data 640) (h0 : Fits W 0) :
    ∃ y, ExecWithin W save x y 8 ∧ y.mem = x.mem ∧
      y.regs Reg.savedBound = x.regs Reg.bound ∧
      y.regs CallableFixedPrime.Reg.n = x.regs Reg.side ∧
      y.regs CallableFixedPrime.Reg.ab = x.regs Reg.ab ∧
      y.regs CallableFixedPrime.Reg.bc = x.regs Reg.bc ∧
      y.regs CallableFixedPrime.Reg.ac = x.regs Reg.ac ∧
      y.regs CallableFixedPrime.Reg.base = x.regs Reg.free ∧
      y.regs (parameterBank DyadicParameters.Reg.side) = x.regs Reg.side ∧
      y.regs CallableFixedPrime.Reg.prime = 0 ∧
      ∀ j : Fin 640, j.val < 143 → y.regs j = x.regs j := by
  let y := x.set Reg.savedBound (x.regs Reg.bound) |>.set CallableFixedPrime.Reg.n
    (x.regs Reg.side) |>.set CallableFixedPrime.Reg.ab (x.regs Reg.ab)
    |>.set CallableFixedPrime.Reg.bc (x.regs Reg.bc) |>.set CallableFixedPrime.Reg.ac
    (x.regs Reg.ac) |>.set CallableFixedPrime.Reg.base (x.regs Reg.free)
    |>.set (parameterBank DyadicParameters.Reg.side) (x.regs Reg.side)
    |>.set CallableFixedPrime.Reg.prime 0
  have he : ExecWithin W save x y 8 := by
    ram_eval [save, y, h0, Reg.savedBound, Reg.bound, Reg.side, Reg.ab, Reg.bc,
      Reg.ac, Reg.free, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
      CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base,
      CallableFixedPrime.Reg.prime, parameterBank, DyadicParameters.Reg.side, Fin.mk.injEq]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun j hj => he.regs_eq (save_preserves_low j hj)⟩
  all_goals simp +decide [y, Reg.savedBound, Reg.bound, Reg.side, Reg.ab, Reg.bc, Reg.ac,
    Reg.free, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
    CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base,
    CallableFixedPrime.Reg.prime, parameterBank, DyadicParameters.Reg.side]

/-- Seven actual copies return the raw verdict and restore the six original host arguments. -/
theorem exec_restore {W : ℕ} (x : Data 640) :
    ∃ y, ExecWithin W restore x y 7 ∧ y.mem = x.mem ∧
      y.regs Reg.side = x.regs CallableFixedPrime.Reg.n ∧
      y.regs Reg.bound = x.regs Reg.savedBound ∧
      y.regs Reg.ab = x.regs CallableFixedPrime.Reg.ab ∧
      y.regs Reg.bc = x.regs CallableFixedPrime.Reg.bc ∧
      y.regs Reg.ac = x.regs CallableFixedPrime.Reg.ac ∧
      y.regs Reg.free = x.regs CallableFixedPrime.Reg.base ∧
      y.regs Reg.result = x.regs CallableFixedPrime.Reg.found ∧
      ∀ j : Fin 640, 7 ≤ j.val → y.regs j = x.regs j := by
  let y := x.set Reg.side (x.regs CallableFixedPrime.Reg.n) |>.set Reg.bound
    (x.regs Reg.savedBound) |>.set Reg.ab (x.regs CallableFixedPrime.Reg.ab)
    |>.set Reg.bc (x.regs CallableFixedPrime.Reg.bc) |>.set Reg.ac
    (x.regs CallableFixedPrime.Reg.ac) |>.set Reg.free (x.regs CallableFixedPrime.Reg.base)
    |>.set Reg.result (x.regs CallableFixedPrime.Reg.found)
  have he : ExecWithin W restore x y 7 := by
    ram_eval [restore, y, Reg.side, Reg.bound, Reg.savedBound, Reg.ab, Reg.bc,
      Reg.ac, Reg.free, Reg.result, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
      CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base,
      CallableFixedPrime.Reg.found, Fin.mk.injEq]
  refine ⟨y, he, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun j hj => he.regs_eq (restore_preserves_high j hj)⟩
  all_goals simp +decide [y, Reg.savedBound, Reg.bound, Reg.side, Reg.ab, Reg.bc, Reg.ac,
    Reg.free, Reg.result, CallableFixedPrime.Reg.n, CallableFixedPrime.Reg.ab,
    CallableFixedPrime.Reg.bc, CallableFixedPrime.Reg.ac, CallableFixedPrime.Reg.base,
    CallableFixedPrime.Reg.found]

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
