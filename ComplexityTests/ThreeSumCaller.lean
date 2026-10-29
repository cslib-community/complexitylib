/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Host.ExecuteAt
import Complexity.Algorithms.WordRAM.ThreeSum.Host.Slow
import Mathlib.Tactic.IntervalCases

/-! Actual finite callee runs and caller-owned source/workspace regressions. -/

namespace ComplexityTests.ThreeSumCaller

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.ThreeSum

private def slowInput (a b c : ℤ) : Data 24 where
  regs i := if i = 0 then 1 else if i = 1 then 1 else if i = 2 then 10
    else if i = 3 then 11 else if i = 4 then 12 else if i = 5 then 13 else 99
  mem p := if p = 10 then encode a else if p = 11 then encode b
    else if p = 12 then encode c else 77

-- Scratch starts nonzero. The finite solver computes the signed sum and keeps every memory cell.
/-- info: true -/
#guard_msgs in
#eval decide ((Host.Slow.program.eval 40 3 (slowInput 1 (-1) 0)).map
  (fun (y, _) => (y.regs 6, y.mem 0, y.mem 13)) = some (1, 77, 77))

/-- info: true -/
#guard_msgs in
#eval decide ((Host.Slow.program.eval 40 3 (slowInput 1 1 1)).map
  (fun (y, _) => y.regs 6) = some 0)

/-- info: true -/
#guard_msgs in
#eval decide ((Host.Slow.program.eval 40 3 (slowInput (-1) (-1) (-1))).map
  (fun (y, _) => y.regs 6) = some 0)

-- Every premise of the uniform concrete callee contract is discharged for a live signed input.
example : ∃ y, ExecWithin 40 Host.Slow.callee.code (slowInput 1 (-1) 0) y 56 ∧
    y.regs 6 = 1 ∧ ∀ p < 10, y.mem p = (slowInput 1 (-1) 0).mem p := by
  obtain ⟨y, he, _, hans, hm⟩ := Host.Slow.callee.exec 40 1 1 10 11 12 13
    (slowInput 1 (-1) 0) (fun _ _ => 1) (fun _ _ => -1) (fun _ _ => 0)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro i j; fin_cases i; fin_cases j; rfl)
    (by intro i j; fin_cases i; fin_cases j; rfl)
    (by intro i j; fin_cases i; fin_cases j; rfl)
    (by intro _ _; decide) (by intro _ _; decide) (by intro _ _; decide)
  exact ⟨y, he, hans.mpr ⟨0, 0, 0, by decide⟩, hm⟩

private def callerInput : Data 88 where
  regs i := if i = Host.hostRegisters (r := 24) Host.len then 1
    else if i = Host.hostRegisters (r := 24) Host.upper then 1
    else if i = Host.hostRegisters (r := 24) Host.base then 20
    else if i = Host.hostRegisters (r := 24) Host.matAB then 100 else 77
  mem p := if p = 0 then 999 else if p = 20 then encode 0 else if p = 40 then 123 else 777

-- Header zero deliberately disagrees with the actual source length. A future catalogue cell at
-- 40 remains protected while all four Convolution instances use matrices beginning at 100.
/-- info: true -/
#guard_msgs in
#eval decide (((Host.bodyAt Host.Slow.callee.code).eval 64 16 callerInput).map
  (fun (y, _) => (y.regs (Host.hostRegisters (r := 24) Host.found), y.mem 0, y.mem 20, y.mem 40)) =
  some (1, 999, 0, 123))

-- The same real caller program faults when its address arithmetic cannot fit.
/-- info: true -/
#guard_msgs in
#eval decide (((Host.bodyAt Host.Slow.callee.code).eval 4 16 callerInput).isNone)

example : ∃ y, ExecWithin 64 (Host.bodyAt Host.Slow.callee.code) callerInput y
      (Host.callerTime 1 (Host.Slow.callee.time 2 3)) ∧
    y.regs (Host.hostRegisters (r := 24) Host.found) = 1 ∧
    y.mem 0 = 999 ∧ y.mem 20 = 0 ∧ y.mem 40 = 123 := by
  obtain ⟨y, he, _, hans, hm⟩ := Host.exec_at (w := 62) (N := 1) (U := 1)
    (src := 20) (workspace := 100) Host.Slow.callee (fun _ => 0) callerInput
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro _ _; decide) (by
      intro i hi
      have hi0 : i = 0 := by omega
      subst i
      rfl)
    (by intro s hs; norm_num [Host.sideLength] at hs; interval_cases s <;> decide)
    (by decide) (by decide)
    (by intro _ _; decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨y, he, hans.mpr ⟨0, 0, by decide, by decide⟩,
    (hm 0 (by decide)).trans rfl, (hm 20 (by decide)).trans rfl,
    (hm 40 (by decide)).trans rfl⟩

end ComplexityTests.ThreeSumCaller
