/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Flat

/-!
# Complete native cyclic coefficient kernel examples

These execute the real nested-loop kernel, including its signed multiplication/addition and
all cyclic index work. They test the prerequisite ring operation only; no complete native
Strassen or modular triangle counter is claimed.
-/

-- These regression commands intentionally run the actual native interpreter.
set_option linter.hashCommand false

namespace ComplexityTests.WordRAMCyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.CyclicConvolution

private def setup (a b out p : ℕ) : Code .standard 32 := ram[
  Reg.inputA ← #a; Reg.inputB ← #b; Reg.output ← #out; Reg.length ← #p ]

private def complete (a b out p : ℕ) : Code .standard 32 :=
  .seq (setup a b out p) program

-- (1 - 2X + 3X²)(-4 + 5X + 2X²) modulo X³ - 1 has coefficients 7, 19, -20.
-- The destination starts dirty, and a sentinel immediately after it must survive.
#guard match (complete 1 4 7 3).eval 10 1000
    (.init [2, 5, 6, 9, 10, 4, 99, 999, 42, 123]) with
  | some (y, t) => y.mem 7 == encode 7 && y.mem 8 == encode 19 &&
      y.mem 9 == encode (-20) && y.mem 1 == 2 && y.mem 6 == 4 &&
      y.mem 10 == 123 && t ≤ 413
  | none => false

-- Equal-length input blocks may be placed after the output, in the opposite address order.
#guard match (complete 4 7 1 3).eval 10 1000
    (.init [99, 999, 42, 2, 5, 6, 9, 10, 4, 123]) with
  | some (y, t) => y.mem 1 == encode 7 && y.mem 2 == encode 19 &&
      y.mem 3 == encode (-20) && y.mem 4 == 2 && y.mem 9 == 4 &&
      y.mem 10 == 123 && t ≤ 413
  | none => false

-- Nonzero signed inputs can cancel in every cyclic coefficient; zero is canonical.
#guard match (complete 1 3 5 2).eval 8 500 (.init [2, 3, 2, 2, 99, 77, 123]) with
  | some (y, _) => y.mem 5 == 0 && y.mem 6 == 0 && y.mem 7 == 123
  | none => false

-- Both input pointers may alias: (1 - X)^2 modulo X² - 1 is 2 - 2X.
#guard match (complete 1 1 3 2).eval 8 500 (.init [2, 3, 99, 88, 123]) with
  | some (y, _) => y.mem 3 == encode 2 && y.mem 4 == encode (-2) &&
      y.mem 1 == 2 && y.mem 2 == 3 && y.mem 5 == 123
  | none => false

-- A scalar cyclic product and the empty native loop exercise both recursion-leaf boundaries.
#guard match (complete 1 2 3 1).eval 8 100 (.init [7, 4, 99, 123]) with
  | some (y, _) => y.mem 3 == encode (-6) && y.mem 4 == 123
  | none => false

#guard match (complete 1 2 3 0).eval 8 20 (.init [7, 4, 99, 123]) with
  | some (y, _) => y.mem 3 == 99 && y.mem 4 == 123
  | none => false

example : Cslib.CyclicIntRing.convolution 3
    (fun i => if i = 0 then 1 else if i = 1 then -2 else 3)
    (fun i => if i = 0 then -4 else if i = 1 then 5 else 2) 2 = -20 := by decide

private def input : List ℕ := [2, 5, 6, 9, 10, 4, 99, 999, 42, 123]
private def u (i : ℕ) : ℤ := if i = 0 then 1 else if i = 1 then -2 else 3
private def v (i : ℕ) : ℤ := if i = 0 then -4 else if i = 1 then 5 else 2

-- The complete execution witness includes the real setup from State.init, the same prefix
-- and halted memory, all three coefficients, and the original input/sentinel frame.
example : InputFits 10 input ∧ ∃ y t, t + 1 ≤ 414 ∧
    Runs 10 ((complete 1 4 7 3).program Reg.output) (State.init input)
      ⟨(complete 1 4 7 3).size, y⟩ t ∧
    Executes 10 ((complete 1 4 7 3).program Reg.output) (State.init input) 7 (t + 1) ∧
    y.Bounded 10 ∧ y.mem 7 = encode 7 ∧ y.mem 8 = encode 19 ∧
    y.mem 9 = encode (-20) ∧ y.mem 10 = 123 := by
  have hi : InputFits 10 input := by decide
  let x : Data 32 := ((((Data.init input).set Reg.inputA 1).set Reg.inputB 4).set
    Reg.output 7).set Reg.length 3
  have hsetup : ExecWithin 10 (setup 1 4 7 3) (.init input) x 4 := by
    ram_eval [setup, x, Reg.inputA, Reg.inputB, Reg.output, Reg.length]
  obtain ⟨y, hy, hvalues, hframe, hregs⟩ := exec (w := 8) (p := 3) (A := 3) (B := 5)
    x u v (by simp [x]) (by decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by intro i hip; interval_cases i <;> decide)
    (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide))
  have he : ExecWithin 10 (complete 1 4 7 3) (.init input) y 413 := hsetup.seq hy
  have hyb : y.Bounded 10 := he.bounded (Data.Bounded.init hi)
  have hxout : x.regs Reg.output = 7 := by decide
  have hptr : y.regs Reg.output = 7 := by
    exact (hregs Reg.output (by decide)).trans hxout
  have h0 : y.mem 7 = encode 7 := by
    simpa only [hxout, Nat.reduceAdd,
      show Cslib.CyclicIntRing.convolution 3 u v 0 = 7 from by decide]
      using hvalues 0 (by decide)
  have h1 : y.mem 8 = encode 19 := by
    simpa only [hxout, Nat.reduceAdd,
      show Cslib.CyclicIntRing.convolution 3 u v 1 = 19 from by decide]
      using hvalues 1 (by decide)
  have h2 : y.mem 9 = encode (-20) := by
    simpa only [hxout, Nat.reduceAdd,
      show Cslib.CyclicIntRing.convolution 3 u v 2 = -20 from by decide]
      using hvalues 2 (by decide)
  have hs : y.mem 10 = 123 := (hframe 10 (Or.inr (by decide))).trans (by decide)
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, y, t, by omega, ?_, ?_, hyb, h0, h1, h2, hs⟩
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := (complete 1 4 7 3).program Reg.output) (Program.Contains.self _).append_left
  · simpa only [State.init, hptr] using hex.executes Reg.output

end ComplexityTests.WordRAMCyclicConvolution
