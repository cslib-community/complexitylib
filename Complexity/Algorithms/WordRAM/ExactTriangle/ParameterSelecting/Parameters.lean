/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Properties
public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Exec

/-!
# Actual parameter computation in the assembled solver bank

The existing logarithm/two-power program moves as one bank. Its real executed values supply
all later deliveries and the small/fast dispatch. The original dimension is the only parameter
input; neither geometry nor a precomputed exponent/flag is supplied to this execution rule.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Execute all actual parameter instructions above the selector, preserving original arguments. -/
theorem exec_parameters {W n : ℕ} (x : Data 640)
    (hn : x.regs (parameterBank DyadicParameters.Reg.side) = n)
    (hfit : Fits W (DyadicParameters.wordBudget n)) :
    ∃ y, ExecWithin W parameters x y (DyadicParameters.timeBound n) ∧
      y.regs (parameterBank DyadicParameters.Reg.side) = n ∧
      y.regs (parameterBank DyadicParameters.Reg.blocks) = ParameterChoice.blocks n ∧
      y.regs (parameterBank DyadicParameters.Reg.level) = ParameterChoice.level n ∧
      y.regs (parameterBank DyadicParameters.Reg.window) = ParameterChoice.window n ∧
      y.regs (parameterBank DyadicParameters.Reg.groups) = ParameterChoice.groups n ∧
      y.regs (parameterBank DyadicParameters.Reg.tensorDepth) = ParameterChoice.tensorDepth n ∧
      y.regs (parameterBank DyadicParameters.Reg.fast) =
        (if 0 < ParameterChoice.blocks n then 1 else 0) ∧
      y.mem = x.mem ∧
      ∀ j : Fin 640, j.val < 144 ∨ 160 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨z, hz, zn, zb, zl, zd, zg, zL, zf, zm⟩ :=
    DyadicParameters.exec (x.comap parameterBank) hn hfit
  let y := z.extend parameterBank x
  have hy : ExecWithin W parameters x y (DyadicParameters.timeBound n) :=
    hz.rename parameterBank_injective
  have reg (i : Fin 16) : y.regs (parameterBank i) = z.regs i :=
    parameterBank_injective.extend_apply _ _ _
  exact ⟨y, hy, (reg _).trans zn, (reg _).trans zb, (reg _).trans zl, (reg _).trans zd,
    (reg _).trans zg, (reg _).trans zL, (reg _).trans zf, zm,
    fun j hj => hy.regs_eq (parameters_preserves j hj)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
