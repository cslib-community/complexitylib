/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Input

/-!
# Actual caller adaptation regressions

These small interpreter runs test the copies, accumulated raw-word sum, scalar headers and
the protected low register bank. Their small dimensions do not satisfy the full thin solver's
geometry, and no complete solver execution at those dimensions is claimed.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMCallableFixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle

private def copyInput : Data 8 :=
  ⟨![1, 10, 3, 99, 99, 99, 99, 5], fun q =>
    if q = 1 then 5 else if q = 2 then 2 else if q = 3 then 8 else 99⟩

-- Signed encodings of -2, 1, 4 are copied unchanged and added to the old accumulator five.
example : ∃ y, ExecWithin 8 ArrayCopySum.program copyInput y 28 ∧
    y.regs ArrayCopySum.Reg.total = 20 ∧ y.mem 10 = 5 ∧ y.mem 11 = 2 ∧ y.mem 12 = 8 ∧
    y.mem 1 = 5 ∧ y.mem 9 = 99 ∧ y.mem 13 = 99 := by
  refine ⟨?y, ?run, ?values⟩
  case run =>
    apply ExecWithin.of_eval (fuel := 3) (n := 28)
    · rfl
    · decide
  case values => decide +kernel

example : Fits 5 20 ∧ ¬Fits 4 20 := by decide +kernel

private def caller : Data 640 :=
  { regs := fun j =>
      if j.val = 600 then 1 else if j.val = 601 then 16 else if j.val = 602 then 1
      else if j.val = 603 then 3 else if j.val = 604 then 1 else if j.val = 605 then 2
      else if j.val = 606 then 3 else if j.val = 607 then 16 else 777
    mem := copyInput.mem }

private def adapted : Option (List ℕ × ℕ) :=
  (CallableFixedPrime.adapt.eval 16 4 caller).map fun (y, t) =>
    ([y.mem 16, y.mem 17, y.mem 18, y.mem 19, y.mem 20, y.mem 21, y.mem 22, y.mem 23,
      y.regs CallableFixedPrime.Reg.total, y.regs 0, y.regs 159, y.regs 600,
      y.mem 1, y.mem 15, y.mem 24], t)

#guard adapted == some ([7, 16, 1, 1, 3, 5, 2, 8, 15, 777, 777, 1, 5, 99, 99], 62)

private def returned (flag : ℕ) : Option (List ℕ × ℕ) :=
  let x : Data 640 :=
    { regs := fun j =>
        if j = CallableFixedPrime.sourceReg FixedPrime.Reg.found then flag
        else if j = CallableFixedPrime.sourceReg FixedPrime.Reg.scans then 3
        else 717
      mem := fun _ => 99 }
  (CallableFixedPrime.receive.eval 16 1 x).map fun (y, t) =>
    ([y.regs CallableFixedPrime.Reg.found, y.regs CallableFixedPrime.Reg.scans,
      y.regs CallableFixedPrime.Reg.witnessA, y.regs CallableFixedPrime.Reg.witnessB,
      y.regs CallableFixedPrime.Reg.witnessC, y.regs 0, y.regs 159, y.mem 77], t)

#guard returned 1 == some ([1, 3, 717, 717, 717, 717, 717, 99], 5)
#guard returned 0 == some ([0, 3, 717, 717, 717, 717, 717, 99], 5)

private def initialized : Option (List ℕ × ℕ) :=
  let x : Data 640 := .init (PreparationInput.input 1 16 1 3 [-2, 1, 4])
  (CallableFixedPrime.entryHeader.eval 16 1 x).map fun (y, t) =>
    ([y.regs 600, y.regs 601, y.regs 602, y.regs 603, y.regs 604, y.regs 605,
      y.regs 606, y.regs 607, y.regs 0, y.regs 159, y.mem 6, y.mem 7, y.mem 8], t)

#guard initialized == some ([1, 16, 1, 3, 5, 6, 7, 8, 0, 0, 2, 8, 0], 14)

end ComplexityTests.WordRAMCallableFixedPrime
