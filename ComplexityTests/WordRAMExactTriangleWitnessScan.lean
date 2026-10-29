/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Exec
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Signed original-weight verifier executions

These test the interval verifier on small original arrays; they do not assert the much larger
thin-product geometry. The complete producer/product/recovery client is a separate test.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleWitnessScan

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle

private def weights (last : ℤ) : List ℤ := [2, 5, 7, 8, -1, 3, 0, 0, 4, last, 0, 0]

private def args (first length : ℕ) : WitnessScan.Args := ⟨1, 5, 9, 2, 0, 0, first, length⟩

private def fixture (last : ℤ) (first length : ℕ) : Data 32 :=
  ((Data.init ((weights last).map Signed.encode)).write 20 99)
    |>.set WitnessScan.Reg.ab 1 |>.set WitnessScan.Reg.bc 5 |>.set WitnessScan.Reg.ac 9
    |>.set WitnessScan.Reg.size 2 |>.set WitnessScan.Reg.a 0 |>.set WitnessScan.Reg.b 0
    |>.set WitnessScan.Reg.first first |>.set WitnessScan.Reg.length length

private def observe (last : ℤ) (first length : ℕ) : Option (ℕ × ℕ × ℕ × Bool) :=
  (WitnessScan.program.eval 10 8 (fixture last first length)).map fun (y, t) =>
    (y.regs WitnessScan.Reg.found, y.regs WitnessScan.Reg.witness, y.mem 20,
      decide (t ≤ 42 * length + 17))

-- c=0 fails (2-1+4=5), then the original signed weights at c=1 give 2+3-5=0.
#guard observe (-5) 0 2 == some (1, 1, 99, true)

-- A nonzero product candidate cannot turn 2+3+1 into an original zero sum.
#guard observe 1 0 2 == some (0, 0, 99, true)

-- An empty interval performs no candidate-vertex read and cannot report a witness.
#guard observe (-5) 2 0 == some (0, 2, 99, true)

-- Restricting the scan to c=0 excludes the later true witness.
#guard observe (-5) 0 1 == some (0, 0, 99, true)

private def AB (i j : ℕ) : ℤ := (weights (-5)).getD (i * 2 + j) 0
private def BC (i j : ℕ) : ℤ := (weights (-5)).getD (4 + (i * 2 + j)) 0
private def AC (i j : ℕ) : ℤ := (weights (-5)).getD (8 + (i * 2 + j)) 0

/-- Closed kernel client: every runtime, address, signed-fit and input-array premise is
discharged. The actual successful execution observes the unique original witness c=1. -/
example : ∃ y, ExecWithin 10 WitnessScan.program (fixture (-5) 0 2) y 101 ∧
    y.regs WitnessScan.Reg.found = 1 ∧ y.regs WitnessScan.Reg.witness = 1 ∧
    y.mem = (fixture (-5) 0 2).mem := by
  have hm : ∀ i < 2, ∀ j < 2,
      (fixture (-5) 0 2).mem (1 + (i * 2 + j)) = Signed.encode (AB i j) ∧
      (fixture (-5) 0 2).mem (5 + (i * 2 + j)) = Signed.encode (BC i j) ∧
      (fixture (-5) 0 2).mem (9 + (i * 2 + j)) = Signed.encode (AC i j) := by
    intro i hi j hj
    interval_cases i <;> interval_cases j <;> decide
  have hb : ∀ i < 2, ∀ j < 2,
      (AB i j).natAbs ≤ 8 ∧ (BC i j).natAbs ≤ 8 ∧ (AC i j).natAbs ≤ 8 := by
    intro i hi j hj
    interval_cases i <;> interval_cases j <;> decide
  obtain ⟨y, he, hy, hmem, hflag, hiff, hwit⟩ := WitnessScan.exec
    (w := 8) (U := 8) (args 0 2) AB BC AC (fixture (-5) 0 2)
    (by unfold WitnessScan.Args.InRegisters; decide)
    (by decide) (by decide) (by decide) hm hb (by decide) (by decide)
  have hf : y.regs WitnessScan.Reg.found = 1 := hiff.mpr ⟨1, by decide, by decide, by decide⟩
  obtain ⟨hlo, hhi, hz⟩ := hwit hf
  have hc : y.regs WitnessScan.Reg.witness = 1 := by
    change 0 ≤ y.regs WitnessScan.Reg.witness at hlo
    change y.regs WitnessScan.Reg.witness < 2 at hhi
    have hzero : y.regs WitnessScan.Reg.witness ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num [AB, BC, AC, weights, args] at hz
    omega
  exact ⟨y, he, hf, hc, hmem⟩

end ComplexityTests.WordRAMExactTriangleWitnessScan
