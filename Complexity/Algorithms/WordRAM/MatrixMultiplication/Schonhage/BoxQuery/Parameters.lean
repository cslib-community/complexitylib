/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Program

/-!
# Persistent actual query parameters

The native controller reads these ordinary scalar contents. The predicate has no
execution, timing, intermediate-fit, geometry or solver field. The body preserves
the real original arguments while changing its stack and signed accumulator.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- Ordinary readonly arguments and explicitly initialized constants of a query. -/
structure Parameters (L t Q AA BB D V K F : ℕ) (x : Data registers) : Prop where
  /-- Original depth. -/
  levels : x.regs BoxTable.Reg.levels = L
  /-- Original threshold. -/
  threshold : x.regs BoxTable.Reg.threshold = t
  /-- Actual encoding-array length. -/
  span : x.regs BoxTable.Reg.span = 10 ^ L
  /-- Original output code. -/
  query : x.regs Reg.query = Q
  /-- Actual left array base. -/
  arrayA : x.regs BoxTable.Reg.arrayA = AA
  /-- Actual right array base. -/
  arrayB : x.regs BoxTable.Reg.arrayB = BB
  /-- Computed shared directory base. -/
  directory : x.regs BoxTable.Reg.directory = D
  /-- Actual compact value-table base. -/
  values : x.regs BoxTable.Reg.values = V
  /-- Computed compact box count. -/
  count : x.regs BoxTable.Reg.count = K
  /-- Actual computed stack base. -/
  stack : x.regs Reg.stack = F
  /-- Native task width. -/
  five : x.regs Reg.five = 5
  /-- Constant one. -/
  one : x.regs BoxTable.Reg.one = 1
  /-- Constant radix. -/
  ten : x.regs BoxTable.Reg.ten = 10
  /-- Native P0/inner digit. -/
  nine : x.regs BoxTable.Reg.nine = 9
  /-- Scalar zero outside signed arithmetic. -/
  nil : x.regs BoxTable.Reg.nil = 0

private def parameterRegisters : Finset (Fin registers) :=
  {BoxTable.Reg.levels, BoxTable.Reg.threshold, BoxTable.Reg.span, Reg.query,
    BoxTable.Reg.arrayA, BoxTable.Reg.arrayB, BoxTable.Reg.directory, BoxTable.Reg.values,
    BoxTable.Reg.count, Reg.stack, Reg.five, BoxTable.Reg.one, BoxTable.Reg.ten,
    BoxTable.Reg.nine, BoxTable.Reg.nil}

/-- Transport readonly parameter contents across the actual scalar register frame. -/
private theorem Parameters.of_frame {L t Q AA BB D V K F : ℕ} {x y : Data registers}
    (hx : Parameters L t Q AA BB D V K F x)
    (hf : ∀ i ∈ parameterRegisters, y.regs i = x.regs i) :
    Parameters L t Q AA BB D V K F y := by
  exact ⟨(hf _ (by decide)).trans hx.levels, (hf _ (by decide)).trans hx.threshold,
    (hf _ (by decide)).trans hx.span, (hf _ (by decide)).trans hx.query,
    (hf _ (by decide)).trans hx.arrayA, (hf _ (by decide)).trans hx.arrayB,
    (hf _ (by decide)).trans hx.directory, (hf _ (by decide)).trans hx.values,
    (hf _ (by decide)).trans hx.count, (hf _ (by decide)).trans hx.stack,
    (hf _ (by decide)).trans hx.five, (hf _ (by decide)).trans hx.one,
    (hf _ (by decide)).trans hx.ten, (hf _ (by decide)).trans hx.nine,
    (hf _ (by decide)).trans hx.nil⟩

/-- One actual controller step preserves the complete original argument bank. -/
theorem Parameters.after_body {w T L t Q AA BB D V K F : ℕ} {x y : Data registers}
    (hx : Parameters L t Q AA BB D V K F x) (he : ExecWithin w body x y T) :
    Parameters L t Q AA BB D V K F y := by
  apply hx.of_frame
  intro i hi
  exact he.regs_eq (by decide +revert)

/-- Popping a task changes only its active fields and leaves the original query arguments. -/
theorem Parameters.after_pop {w T L t Q AA BB D V K F : ℕ} {x y : Data registers}
    (hx : Parameters L t Q AA BB D V K F x) (he : ExecWithin w pop x y T) :
    Parameters L t Q AA BB D V K F y := by
  apply hx.of_frame
  intro i hi
  exact he.regs_eq (by decide +revert)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
