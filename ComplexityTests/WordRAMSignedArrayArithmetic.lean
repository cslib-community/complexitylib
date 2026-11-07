/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Computability.WordRAM.Signed.ArrayArithmetic.Exec
import Mathlib.Tactic.IntervalCases

/-!
# Real signed-array operations used by Strassen

The interpreter executes actual argument setup and the complete native loop. The checked
client also discharges every generic execution premise for nonzero signed inputs and an
in-place destination. These are coefficient-array operations, not a matrix/counting endpoint.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMSignedArrayArithmetic

open Cslib.WordRAM Cslib.WordRAM.Signed Cslib.WordRAM.Signed.ArrayArithmetic

private def setup (a b dst n : ℕ) : Code .standard 16 := ram[
  Reg.inputA ← #a; Reg.inputB ← #b; Reg.output ← #dst; Reg.length ← #n ]

private def complete (subtract : Bool) (a b dst n : ℕ) : Code .standard 16 :=
  .seq (setup a b dst n) (program subtract)

-- In-place addition into the first operand: [-3,2]+[5,-7]=[2,-5].
#guard match (complete false 1 3 1 2).eval 8 100 (.init [7, 4, 10, 15, 123]) with
  | some (y, t) => y.mem 1 == encode 2 && y.mem 2 == encode (-5) &&
      y.mem 3 == 10 && y.mem 4 == 15 && y.mem 5 == 123 && t ≤ 60
  | none => false

-- In-place subtraction into the second operand still reads its original future entries.
#guard match (complete true 1 3 3 2).eval 8 100 (.init [7, 4, 10, 15, 123]) with
  | some (y, t) => y.mem 3 == encode (-8) && y.mem 4 == encode 9 &&
      y.mem 1 == 7 && y.mem 2 == 4 && y.mem 5 == 123 && t ≤ 60
  | none => false

-- All three bases may coincide; canonical subtraction produces zero.
#guard match (complete true 1 1 1 2).eval 8 100 (.init [7, 4, 123]) with
  | some (y, _) => y.mem 1 == 0 && y.mem 2 == 0 && y.mem 3 == 123
  | none => false

-- A non-identical partial overlap is rejected by the contract.
example : ¬((1 : ℕ) + 2 ≤ 2 ∨ 2 + 2 ≤ 1 ∨ 1 = 2) := by decide

private def input : List ℕ := [7, 4, 10, 15, 123]
private def u (i : ℕ) : ℤ := if i = 0 then -3 else 2
private def v (i : ℕ) : ℤ := if i = 0 then 5 else -7

example : InputFits 8 input ∧ ∃ y t, t + 1 ≤ 61 ∧
    Runs 8 ((complete false 1 3 1 2).program Reg.output) (State.init input)
      ⟨(complete false 1 3 1 2).size, y⟩ t ∧
    Executes 8 ((complete false 1 3 1 2).program Reg.output) (State.init input) 1 (t + 1) ∧
    y.mem 1 = encode 2 ∧ y.mem 2 = encode (-5) ∧ y.mem 5 = 123 := by
  have hi : InputFits 8 input := by decide
  let x : Data 16 := ((((Data.init input).set Reg.inputA 1).set Reg.inputB 3).set
    Reg.output 1).set Reg.length 2
  have hsetup : ExecWithin 8 (setup 1 3 1 2) (.init input) x 4 := by
    ram_eval [setup, x, Reg.inputA, Reg.inputB, Reg.output, Reg.length]
  obtain ⟨y, hy, values, frame, regs⟩ := exec (w := 6) (n := 2) (A := 3) (B := 7)
    false x u v (by simp [x]) (by decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by decide) (by decide) (by decide) (Or.inr (Or.inr (by decide))) (Or.inr (Or.inl (by decide)))
  have he : ExecWithin 8 (complete false 1 3 1 2) (.init input) y 60 := hsetup.seq hy
  have hxout : x.regs Reg.output = 1 := by decide
  have hyout : y.regs Reg.output = 1 := (regs Reg.output (by decide)).trans hxout
  have h0 : y.mem 1 = encode 2 := by
    simpa only [hxout, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte,
      show u 0 + v 0 = 2 from by decide] using values 0 (by decide)
  have h1 : y.mem 2 = encode (-5) := by
    simpa only [hxout, Nat.reduceAdd, Bool.false_eq_true, ↓reduceIte,
      show u 1 + v 1 = -5 from by decide] using values 1 (by decide)
  have hs : y.mem 5 = 123 := (frame 5 (Or.inr (by decide))).trans (by decide)
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, y, t, by omega, ?_, ?_, h0, h1, hs⟩
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := (complete false 1 3 1 2).program Reg.output) (Program.Contains.self _).append_left
  · simpa only [State.init, hyout] using hex.executes Reg.output

end ComplexityTests.WordRAMSignedArrayArithmetic
