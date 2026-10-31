/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.Schoening.Amplify

/-! Schöning's algorithm on the randomized word RAM: the encoding of a small 3-CNF, a concrete
run of the deterministic scan, and the hypotheses of the trial and amplification theorems at word
size `16`. -/

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

/-- `⌈10 (4 / 3) ^ 3⌉ = 24` trials for confidence `1` on three variables. -/
theorem schoeningTrials_three : schoeningTrials 3 3 1 ≤ 30 := by
  rw [schoeningTrials, mul_one, Nat.ceil_le]
  norm_num

-- On the satisfiable `φ`, `schoeningTrials 3 3 1` trials fail with probability at most `e⁻¹`.
example : ((evalRand 16 ampProgram (ampTime (schoeningTrials 3 3 1) 3
        (schoeningTrials 3 3 1 :: encode φ).length)
      (.init (schoeningTrials 3 3 1 :: encode φ))).map cfgSuccess false).toReal ≤
      Real.exp (-1) := by
  have hR : Fits 16 (schoeningTrials 3 3 1) :=
    (show Fits 16 30 by decide).of_le schoeningTrials_three
  simpa using ampProgram_failure_le_exp (k := 3) (c := 1) le_rfl φ_satisfiable φ_three
    (w := 16) (by simp only [List.length_cons]; decide) hR

end ComplexityTests.WordRAMSchoening
