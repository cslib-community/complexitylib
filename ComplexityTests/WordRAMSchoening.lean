/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.Schoening.Amplify

/-! Schöning's algorithm on the randomized word RAM: the encoding of a small 3-CNF, concrete runs
of the deterministic scan and of the multiword counter, the trial count, and the hypotheses of the
trial and amplification theorems at small word sizes. -/

namespace ComplexityTests.WordRAMSchoening

open Cslib.WordRAM Cslib.Logic.PL Cslib.Complexity.Schoening Cslib.Algorithms.WordRAM.Schoening

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁ ∨ x₂)`: satisfiable, with clauses of at most three literals. -/
def φ : CNF (Fin 3) := [[(0, true), (1, true)], [(0, false), (1, true), (2, true)]]

theorem φ_satisfiable : φ.Satisfiable := ⟨fun _ => true, by decide⟩

theorem φ_three : ∀ c ∈ φ, c.length ≤ 3 := by decide

-- The input: `n = 3`, then each clause as its length followed by the literal codes `2 v + b`.
example : encode φ = [3, 2, 1, 3, 3, 0, 3, 5] := rfl

/-- Registers and memory as after the setup of a trial on `encode φ`, with the assignment
`x₀ = x₁ = false`, `x₂ = true` stored at address `9`: the first clause is falsified. -/
def scanInput : Data 24 where
  regs i := if i = Reg.one then 1 else if i = Reg.cBeg then 2 else if i = Reg.aBase then 9
    else if i = Reg.nReg then 3 else 0
  mem a := if a = 0 then 8 else if a = 11 then 1 else (encode φ).getD (a - 1) 0

-- The scan finds the first clause, stored at address `2`, in `38` instructions (the bound of
-- `scan_spec` is `12 · 7 + 4 = 88`).
example : (scan.eval 16 4 scanInput).map (fun z => (z.1.regs Reg.found, z.1.regs Reg.cPtr, z.2)) =
    some (1, 2, 38) := by
  decide

-- With `x₁ = true` both clauses are satisfied and the scan reports none.
example : (scan.eval 16 4
      { scanInput with mem := fun a => if a = 10 then 1 else scanInput.mem a }).map
    (fun z => z.1.regs Reg.found) = some 0 := by
  decide

-- `scan_spec` agrees: the first falsified clause under `x₀ = x₁ = false` is `x₀ ∨ x₁`.
example : firstUnsat φ ![false, false, true] = some [(0, true), (1, true)] := by decide

-- The hypotheses of `trialProgram_spec` hold at word size `16`, so a trial halts within
-- `trialTime 3 8 = 1177` instructions and leaves an assignment with the law of `trial φ`.
example : (evalRand 16 trialProgram (trialTime 3 (encode φ).length) (.init (encode φ))).map
    (cfgAssignment ((encode φ).length + 1) 3) = trial φ :=
  (trialProgram_spec φ (w := 16) (by decide)).2.2.2

example : trialTime 3 (encode φ).length = 1177 := by decide

-- Zero trials never succeed.
example : repeatTrial φ 0 = PMF.pure false := rfl

/-! The multiword counter on concrete digits. -/

/-- A counter of value `5`, digits `[1, 0, 1]` at address `10`, with multiplier `3`, carry `1`
and divisor `3`. -/
def counter5 : Data 24 where
  regs i := if i = Reg.one then 1 else if i = Reg.bBase then 10 else if i = Reg.bLen then 3
    else if i = Reg.mulr then 3 else if i = Reg.carry then 1 else if i = Reg.dvs then 3 else 0
  mem a := if a = 10 then 1 else if a = 12 then 1 else 0

-- `5 · 3 + 1 = 16`: two digits are appended (the bound of `mulAdd_spec` is `10 · 5 + 5 = 55`).
example : (mulAdd.eval 16 8 counter5).map
    (fun z => (z.1.regs Reg.bLen, (List.range 5).map fun i => z.1.mem (10 + i), z.2)) =
    some (5, [0, 0, 0, 0, 1], 49) := by
  decide

example : mulAddDigits 3 1 [1, 0, 1] = [0, 0, 0, 0, 1] := by decide

/-- A counter of value `16`, digits `[0, 0, 0, 0, 1]`. -/
def counter16 : Data 24 :=
  { counter5 with
    regs := fun i => if i = Reg.bLen then 5 else counter5.regs i
    mem := fun a => if a = 14 then 1 else 0 }

-- `⌊16 / 3⌋ = 5` with remainder `1`, in exactly the `10 · 5 + 4` instructions of
-- `divFloor_spec`.
example : (divFloor.eval 16 8 counter16).map
    (fun z => ((List.range 5).map fun i => z.1.mem (10 + i), z.1.regs Reg.rmd, z.2)) =
    some ([1, 0, 1, 0, 0], 1, 54) := by
  decide

-- `16 - 1 = 15`: the decrement reads all five digits and reports a nonzero counter.
example : (decCounter.eval 16 8 counter16).map
    (fun z => ((List.range 5).map fun i => z.1.mem (10 + i), z.1.regs Reg.found)) =
    some ([1, 1, 1, 1, 0], 1) := by
  decide

-- A zero counter is reported as zero.
example : (decCounter.eval 16 8 { counter16 with mem := fun _ => 0 }).map
    (fun z => z.1.regs Reg.found) = some 0 := by
  decide

/-! The trial count and the amplified algorithm. -/

/-- The program computes `⌈10 (4 / 3) ^ 3⌉ = 24` trials for confidence `1` on three
variables. -/
theorem counterDigits_three : Nat.ofDigits 2 (counterDigits 3 3 1) = 24 := by decide

example : schoeningTrials 3 3 1 = 24 := by
  rw [← ofDigits_counterDigits le_rfl, counterDigits_three]

example : counterLen 3 3 1 = 49 := by decide

-- On the satisfiable `φ`, the program with `k = 3` and `c = 1` fails with probability at most
-- `e⁻¹`, already at word size `8`.
example : ((evalRand 8 ampProgram (ampTime 3 3 1 (3 :: 1 :: encode φ).length)
      (.init (3 :: 1 :: encode φ))).map cfgSuccess false).toReal ≤ Real.exp (-1) := by
  have hw : Fits 8
      ((3 :: 1 :: encode φ).length + 6 * 3 + 4 * 3 + 2 * 1 + counterLen 3 3 1 + 2) := by
    decide
  have h := ampProgram_failure_le_exp (k := 3) (c := 1) le_rfl φ_satisfiable φ_three hw
  rwa [Nat.cast_one] at h

end ComplexityTests.WordRAMSchoening
