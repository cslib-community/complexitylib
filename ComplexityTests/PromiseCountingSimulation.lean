/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Complexity.Classes.CountingSimulation.Promise
import ComplexityTests.PromisePP

/-! A fixed-clock native counting simulation on a genuinely partial promise.

The native machine answers the promised singleton words without error and uses a fair coin on the
empty word. The deterministic completion retains the caller's explicit quadratic clock.
-/

namespace ComplexityTests.PromiseCountingSimulation

open Cslib Cslib.Complexity Cslib.Complexity.CountingSimulation Turing Turing.MultiTapeTM
  ComplexityTests.PromiseProbabilistic

/-- Read the first input symbol, or a fair coin when there is no symbol, and halt. -/
private def partialMachine : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ coin := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some (symbol.getD coin), state := none }
    Empty.elim Empty.elim

private theorem partialMachine_halts (input : List Bool) :
    ∀ final ∈ (ProbComp.eval
      (partialMachine.runClosedConfigFrom 1 (partialMachine.initialConfig input))).support,
      final.tapes.state = none := by
  intro final hfinal
  rw [MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins, PMF.mem_support_map_iff] at hfinal
  obtain ⟨coins, hcoins, rfl⟩ := hfinal
  obtain ⟨coin, rfl⟩ := List.length_eq_one_iff.mp
    (BitString.mem_support_uniformList_iff.mp hcoins)
  cases input <;> cases coin <;> rfl

private theorem partialMachine_singleton (b : Bool) :
    ProbComp.eval (partialMachine.runClosed 1 [b]) [b] = 1 := by
  rw [MultiTapePTM.eval_runClosed_eq_map_coins, BitString.uniformList_map_apply]
  have hcard : (Finset.univ.filter fun r : Fin 1 → Bool =>
      partialMachine.runClosedCoins (List.ofFn r) [b] = [b]).card = 2 := by
    cases b <;> decide
  rw [hcard]
  norm_num [ENNReal.div_self]

/-- Unlike a padded polynomial chosen by the simulation, this clock is fixed by the client. -/
private def clock (n : ℕ) : ℕ := (n + 1) ^ 2 + 1

private theorem clock_pos (n : ℕ) : 1 ≤ clock n := by
  unfold clock
  omega

private theorem partialMachine_halts_clock (input : List Bool) :
    ∀ final ∈ (ProbComp.eval
      (partialMachine.runClosedConfigFrom (clock input.length)
        (partialMachine.initialConfig input))).support, final.tapes.state = none := by
  rw [MultiTapePTM.eval_runClosedConfigFrom_eq_of_halted partialMachine _
    (clock_pos input.length) (partialMachine_halts input)]
  exact partialMachine_halts input

/-- Both sides of the promise have native witnesses with this same explicit clock. -/
private theorem partialSingletonBit_mem_PromiseBPTIME :
    partialSingletonBit ∈ PromiseBPTIME encBits clock := by
  refine ⟨1, 0, 0, Unit, inferInstance, partialMachine, fun input => ?_⟩
  simp only [Nat.one_mul, Nat.add_zero]
  refine ⟨partialMachine_halts_clock input, ?_, ?_⟩
  · intro hyes
    obtain rfl : input = [true] := hyes
    simp only [encBits_apply]
    rw [MultiTapePTM.eval_runClosed_eq_of_halted partialMachine _
      (clock_pos _) (partialMachine_halts _), partialMachine_singleton]
    exact ENNReal.div_le_of_le_mul (by norm_num)
  · intro hno
    obtain rfl : input = [false] := hno
    simp only [encBits_apply]
    rw [MultiTapePTM.eval_runClosed_eq_of_halted partialMachine _
      (clock_pos _) (partialMachine_halts _), partialMachine_singleton]
    exact ENNReal.div_le_of_le_mul (by norm_num)

/-- The native machine's unpromised empty input is an exact tie at the declared clock. -/
example : ([] : List Bool) ∉ partialSingletonBit.promise ∧
    ProbComp.eval (partialMachine.runClosed (clock 0) []) [true] = 1 / 2 := by
  constructor
  · simp [partialSingletonBit, PromiseProblem.promise]
  · rw [MultiTapePTM.eval_runClosed_eq_of_halted partialMachine _
      (clock_pos _) (partialMachine_halts _),
      MultiTapePTM.eval_runClosed_apply_eq_acceptCount,
      show partialMachine.acceptCount [] 1 = 1 by decide]
    norm_num

/-- A concrete partial promise gets one total deterministic machine at the client's fixed clock,
with both resource bounds and no assumed contraction algorithm. -/
example : ∃ (L : Set (List Bool)) (C d : ℕ), [true] ∈ L ∧ [false] ∉ L ∧
    DecidableInTimeAndSpace L encBits
      (fun a => 2 ^ (C * ((a.length + 1) ^ 2 + 1) /
        Nat.sqrt (Nat.log 2 ((a.length + 1) ^ 2 + 1))))
      (fun a => ((a.length + 1) ^ 2 + 1) ^ d) := by
  have hT : TimeConstructible clock := timeConstructible_succ_sq.succ
  have hbound (n : ℕ) : max n 2 ≤ clock n := by
    have h := Nat.le_self_pow (by omega : 2 ≠ 0) (n + 1)
    have hpos : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    unfold clock
    omega
  obtain ⟨L, C, d, hyes, hno, h⟩ :=
    exists_completion_of_mem_PromiseBPTIME hT hbound partialSingletonBit_mem_PromiseBPTIME
  refine ⟨L, C, d, hyes rfl, ?_, h⟩
  exact Set.disjoint_right.mp hno rfl

end ComplexityTests.PromiseCountingSimulation
