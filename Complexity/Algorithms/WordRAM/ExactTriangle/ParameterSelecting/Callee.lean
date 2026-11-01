/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.MatrixInput
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.DyadicCost
public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Callee

/-!
# Concrete parameter-selecting ExactTriangle callee

The original host calling convention is discharged by the actual complete program. Its
natural time function depends only on n and F: the fast bound uses the proved selected-prime
allowance, and the small bound charges the actual exhaustive branch. No execution, selection,
layout or time contract is an input. Unused old caller words remain unrestricted; the separate
prefix-resource theorems require their explicit original bound P.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- Content-, layout- and physical-width-independent allowance for the real native program.
Both branches conservatively include the initialized header and halt, even for host calls. -/
@[expose] noncomputable def callerTime (n F : ℕ) : ℕ :=
  if 0 < ParameterChoice.blocks n then CallableFixedPrime.dyadicTime n F
  else DyadicParameters.timeBound n + 39 * (n * (n * n)) + 49

/-- The actual selected-prime ledger is bounded by the original-scalar natural allowance.
The prime condition is a postcondition of real selection, not an algorithm argument. -/
theorem timeBound_le_callerTime {n F p : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hp : 0 < ParameterChoice.blocks n → IsSelectedPrime
      (fun i j : Fin n => values.getD (pairIndex (i, j)) 0)
      (fun i j => values.getD (n * n + pairIndex (i, j)) 0)
      (fun i j => values.getD (2 * (n * n) + pairIndex (i, j)) 0)
      (ParameterChoice.window n) p) (mem : ℕ → ℕ) :
    timeBound n p values mem + 16 ≤ callerTime n F := by
  by_cases hf : 0 < ParameterChoice.blocks n
  · rw [timeBound_fast values mem hf, callerTime, ite_eq_left hf]
    simpa only [Nat.add_assoc] using
      CallableFixedPrime.timeBound_le_dyadicTime hf values hlen hv (hp hf) mem
  · rw [timeBound_slow values mem hf, callerTime, ite_eq_right hf]

/-- Actual original-ABI solver, with 633 scratch registers beyond the seven host protocol
registers. It restores arguments0–5 and returns raw Boolean6. The host receives the proved
code/time/width/frame contract, not an assumed solver implementation. -/
noncomputable def callee : ThreeSum.Host.Callee 633 where
  code := program
  time := callerTime
  widthCoefficient := 123357
  coefficient_pos := by decide
  not_readsWidth := program_not_readsWidth
  exec := by
    intro W n F ap bp cp b x A B C hn hF hab hbc hac hW xn xF xa xb xc xf vab vbc vac hA hB hC
    obtain ⟨values, p, mem, y, hlen, hv, readA, readB, readC, he, hf, hiff, hp, hz,
      frame, rest⟩ := exec_matrices x A B C xn xF xa xb xc xf (by omega) (by omega) hac
        vab vbc vac hA hB hC hW
    have matrixA : (fun i j : Fin n => values.getD (pairIndex (i, j)) 0) = A :=
      funext fun i => funext fun j => readA i j
    have matrixB : (fun i j : Fin n => values.getD (n * n + pairIndex (i, j)) 0) = B :=
      funext fun i => funext fun j => readB i j
    have matrixC : (fun i j : Fin n => values.getD (2 * (n * n) + pairIndex (i, j)) 0) = C :=
      funext fun i => funext fun j => readC i j
    have selected : 0 < ParameterChoice.blocks n → IsSelectedPrime
        (fun i j : Fin n => values.getD (pairIndex (i, j)) 0)
        (fun i j => values.getD (n * n + pairIndex (i, j)) 0)
        (fun i j => values.getD (2 * (n * n) + pairIndex (i, j)) 0)
        (ParameterChoice.window n) p := by
      simpa only [matrixA, matrixB, matrixC] using hp
    have budget := timeBound_le_callerTime values hlen hv selected mem
    refine ⟨y, he.mono (by omega), ?_, hiff, fun q hq => frame q (Or.inl (by omega))⟩
    change y.regs Reg.result ≤ 1
    rcases hf with h | h <;> omega

/-- Every admitted initialized run has the same original-scalar time allowance as the host
callee. Prefix, verdict, restored arguments and charged halt refer to the same final state. -/
theorem runs_input_uniform {W n F : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ F)
    (hW : inputWidth n F values ≤ W) :
    let V := fun q => values.getD q 0
    let A := fun i j : Fin n => V (pairIndex (i, j))
    let B := fun i j : Fin n => V (n * n + pairIndex (i, j))
    let C := fun i j : Fin n => V (2 * (n * n) + pairIndex (i, j))
    InputFits W (CountPrime.inputWords n F values) ∧
      ∃ (p : ℕ) (y : Data 640) (t : ℕ), t + 1 ≤ callerTime n F ∧
        Runs W (entryProgram.program Reg.result) (State.init (CountPrime.inputWords n F values))
          ⟨entryProgram.size, y⟩ t ∧
        Executes W (entryProgram.program Reg.result)
          (State.init (CountPrime.inputWords n F values)) (y.regs Reg.result) (t + 1) ∧
        y.Bounded W ∧ (y.regs Reg.result = 0 ∨ y.regs Reg.result = 1) ∧
        (y.regs Reg.result = 1 ↔ HasZeroTriangle A B C) ∧
        (0 < ParameterChoice.blocks n → IsSelectedPrime A B C (ParameterChoice.window n) p) ∧
        (¬0 < ParameterChoice.blocks n → p = 0) ∧
        (∀ q, q < 3 + 3 * (n * n) ∨ workspaceEnd n (3 + 3 * (n * n)) values ≤ q →
          y.mem q = (Data.init (CountPrime.inputWords n F values) : Data 640).mem q) ∧
        y.regs Reg.side = n ∧ y.regs Reg.bound = F ∧ y.regs Reg.ab = 3 ∧
        y.regs Reg.bc = 3 + n * n ∧ y.regs Reg.ac = 3 + 2 * (n * n) ∧
        y.regs Reg.free = 3 + 3 * (n * n) := by
  obtain ⟨hi, p, mem, y, t, ht, hr, he, hb, hf, hiff, hp, rest⟩ :=
    runs_input values hlen hv hW
  exact ⟨hi, p, y, t, ht.trans (timeBound_le_callerTime values hlen hv hp mem),
    hr, he, hb, hf, hiff, hp, rest⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
