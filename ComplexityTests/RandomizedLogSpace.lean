/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Computability.Complexity.Classes.LogSpace.Randomized
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON

/-!
# Tests for randomized logarithmic space
-/

namespace ComplexityTests.RandomizedLogSpace

open Cslib.Complexity

-- Undirected connectivity, in `L` by Reingold, is in `RL` and in `BPL`.
example : USTCON ∈ RL encUSTCON := L_subset_RL USTCON_mem_L

example : USTCON ∈ BPL encUSTCON := L_subset_BPL USTCON_mem_L

-- Going through `RL` recovers `USTCON ∈ NL`.
example : USTCON ∈ NL encUSTCON := RL_subset_NL (L_subset_RL USTCON_mem_L)

section HaltingTime

open Cslib.Turing Turing

/-- The single action of `haltAtOnce`: halt without moving or writing. -/
private def haltAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

/-- A machine without work tapes that halts at its first step. -/
private def haltAtOnce : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ action := action = haltAction

/-- Every computation path of `haltAtOnce` with at least one step ends halted. -/
private theorem haltAtOnce_runsInTime (input : List Bool) : haltAtOnce.RunsInTime input 1 := by
  intro p hp
  have hlen : 1 ≤ p.toRunPath.length := by
    simpa [MultiTapeNTM.ComputationPath.time, MultiTapeNTM.RunPath.time] using hp
  have hstep := p.toRunPath.step ⟨0, hlen⟩
  have hhead : p.toRunPath ⟨0, by omega⟩ = haltAtOnce.initCfg input := p.head_eq
  simp only [Fin.castSucc_mk, Fin.succ_mk, Nat.zero_add] at hstep
  change haltAtOnce.Step _ _ at hstep
  rw [hhead] at hstep
  obtain ⟨action, rfl, h1⟩ := hstep
  have hhalt : (p.toRunPath ⟨1, by omega⟩).Halted := by rw [h1]; rfl
  rw [MultiTapeNTM.RunPath.last_eq_of_halted _ _ hhalt]
  exact hhalt

-- The derived clock on a concrete machine: zero work tapes use no space, so the view bound
-- with `s = 0` is a halting time.
example (input : List Bool) :
    haltAtOnce.RunsInTime input
      (2 ^ (2 * MultiTapeNTM.coreLengthBound 0 Unit input.length 0 + 1)) :=
  MultiTapeNTM.runsInTime_of_runsInSpace (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    (haltAtOnce_runsInTime input)

-- The polynomial clock applies with a single exponent for all inputs.
example : ∃ d, ∀ input : List Bool,
    haltAtOnce.RunsInTime input (2 * (2 * (input.length + 1)) ^ d) := by
  obtain ⟨d, hd⟩ := MultiTapeNTM.exists_runsInTime_polynomial_of_runsInSpace_log haltAtOnce 0
  exact ⟨d, fun input => hd (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)
    (haltAtOnce_runsInTime input)⟩

end HaltingTime

end ComplexityTests.RandomizedLogSpace
