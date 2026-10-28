/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.PrimeTable

/-! # Native trial division and prime bitmap regressions -/

namespace ComplexityTests.WordRAMPrimeTable

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM

private def trialInput (n : ℕ) : Data 6 := (Data.init []).set PrimeTrial.arg n

/-- The smallest candidate is prime; the first composite and a larger prime are distinguished. -/
example : (Code.eval 8 8 PrimeTrial.program (trialInput 2)).map
      (fun yn => yn.1.regs PrimeTrial.flag) = some 1 ∧
    (Code.eval 8 8 PrimeTrial.program (trialInput 4)).map
      (fun yn => yn.1.regs PrimeTrial.flag) = some 0 ∧
    (Code.eval 8 8 PrimeTrial.program (trialInput 7)).map
      (fun yn => yn.1.regs PrimeTrial.flag) = some 1 := by decide

/-- The generic trial-division theorem is admissible on a composite candidate. -/
example : ∃ y, ExecWithin 8 PrimeTrial.program (trialInput 4) y 20 ∧
    y.regs PrimeTrial.flag = 0 ∧ y.regs PrimeTrial.arg = 4 ∧ y.mem 0 = 0 := by
  obtain ⟨y, hy, hf, ha, hm⟩ := PrimeTrial.exec (w := 8) (trialInput 4)
    (by decide) (by decide)
  exact ⟨y, hy, hf.trans (by decide), ha, by rw [hm]; rfl⟩

private def tableInput (n : ℕ) : Data 15 :=
  ⟨fun i => if i = PrimeTable.limit then n else if i = PrimeTable.base then 20 else 0,
    fun _ => 79⟩

private def observe (n : ℕ) : Option (List ℕ × ℕ) :=
  (Code.eval 8 (n + 1) PrimeTable.program (tableInput n)).map fun yn =>
    ((List.range (n + 1)).map (fun i => yn.1.mem (20 + i)), yn.1.regs PrimeTable.count)

/-- Zero and one are not prime; the length-two boundary adds the first prime bit. -/
example : observe 0 = some ([0], 0) ∧ observe 1 = some ([0, 0], 0) ∧
    observe 2 = some ([0, 0, 1], 1) := by decide

-- This concrete interpreter traverses all trial divisions up to ten and their register maps.
set_option maxRecDepth 4096 in
/-- The complete bitmap overwrites nonzero memory and counts all four primes up to ten. -/
example : observe 10 = some ([0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 0], 4) := by decide

/-- The quantitative complete-table contract has a satisfiable frame and fit instance. -/
example : ∃ y, ExecWithin 8 PrimeTable.program (tableInput 10) y 943 ∧
    y.regs PrimeTable.count = 4 ∧ y.mem 22 = 1 ∧ y.mem 24 = 0 ∧
    y.mem 19 = 79 ∧ y.mem 31 = 79 := by
  obtain ⟨y, hy, hm, hc, _⟩ := PrimeTable.exec (w := 8) (tableInput 10)
    (by decide) (by decide)
  refine ⟨y, hy, hc.trans (by decide), ?_, ?_, ?_, ?_⟩ <;> rw [hm] <;> decide

/-- A fitting base can still have a nonfitting bitmap endpoint, and then execution faults. -/
example : (Code.eval 8 6 PrimeTable.program
    ((tableInput 5).set PrimeTable.base 253)).map (fun yn => yn.1.regs PrimeTable.count) =
      none := by decide

end ComplexityTests.WordRAMPrimeTable
