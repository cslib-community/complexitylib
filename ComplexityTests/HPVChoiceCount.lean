/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Time.AcceptCount

/-! Accepting choice strings of concrete fair-coin and nondeterministic machines. -/

namespace ComplexityTests.HPVChoiceCount

open Cslib Turing
open scoped ENNReal

/-- Emit the first coin and halt. -/
private def emitCoin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

-- No step is taken without a choice bit: nothing is accepted.
example : emitCoin.acceptCount [] 0 = 0 := by decide

-- After the first step the machine has halted, and the remaining bits are ignored.
example : emitCoin.acceptCount [] 1 = 1 := by decide
example : emitCoin.acceptCount [true, false] 3 = 4 := by decide

-- The accepted fraction is the probability of output `[true]`.
example : ProbComp.eval (emitCoin.runClosed 3 [true, false]) [true] = 4 / 8 := by
  rw [MultiTapePTM.eval_runClosed_apply_eq_acceptCount,
    show emitCoin.acceptCount [true, false] 3 = 4 by decide]
  norm_num

-- Exactly half accept: this is not a strict majority.
example : ¬ 2⁻¹ < ProbComp.eval (emitCoin.runClosed 3 []) [true] := by
  rw [MultiTapePTM.half_lt_eval_runClosed_apply_iff,
    show emitCoin.acceptCount [] 3 = 4 by decide]
  decide

/-- Run two steps, each ignoring its coin, then emit `true` exactly when the input is
nonempty. -/
private def readInput : MultiTapePTM 0 Bool (Fin 2) where
  initial := 0
  tr state symbol _ _ _ := .step
    (if state = 0 then { inputTape := 0, workTapes := Fin.elim0, output := none, state := some 1 }
    else { inputTape := 0, workTapes := Fin.elim0, output := some symbol.isSome, state := none })
    Empty.elim Empty.elim

-- Ignored bits still count: every string accepts, or none does.
example : readInput.acceptCount [false] 3 = 8 := by decide
example : readInput.acceptCount [] 3 = 0 := by decide
-- Before the decision step, no string accepts.
example : readInput.acceptCount [false] 1 = 0 := by decide

/-! ### A bounded-error decider and the strict-majority criterion -/

/-- Emit `true` exactly when the first input symbol is `true`, ignoring the coin. -/
private def echo : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ symbol _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some (symbol == some true), state := none }
    Empty.elim Empty.elim

/-- `echo` decides `{true}` (encoded as one-symbol words) with no error within one step. -/
private theorem echo_decides :
    echo.DecidesWithBoundedErrorInTime MultiTapeTM.encBool {b | b = true} fun _ => 1 := by
  intro a
  refine ⟨fun final hfinal => ?_, ?_⟩
  · rw [MultiTapePTM.eval_runClosedConfigFrom_eq_map_coins, PMF.mem_support_map_iff] at hfinal
    obtain ⟨coins, hcoins, rfl⟩ := hfinal
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp
      (BitString.mem_support_uniformList_iff.mp hcoins)
    cases a <;> cases c <;> rfl
  · rw [MultiTapePTM.eval_runClosed_eq_map_coins, BitString.uniformList_map_apply]
    cases a
    · rw [show MultiTapeTM.indicator {b : Bool | b = true} false = false by
        simp [MultiTapeTM.indicator]]
      rw [show (Finset.univ.filter fun r : Fin 1 → Bool =>
          echo.runClosedCoins (List.ofFn r) (MultiTapeTM.encBool false) = [false]).card = 2 by
        decide]
      norm_num [ENNReal.div_self]
      exact ENNReal.div_le_of_le_mul (by norm_num)
    · rw [show MultiTapeTM.indicator {b : Bool | b = true} true = true by
        simp [MultiTapeTM.indicator]]
      rw [show (Finset.univ.filter fun r : Fin 1 → Bool =>
          echo.runClosedCoins (List.ofFn r) (MultiTapeTM.encBool true) = [true]).card = 2 by
        decide]
      norm_num [ENNReal.div_self]
      exact ENNReal.div_le_of_le_mul (by norm_num)

-- With more bits than the clock, a member is accepted by all `2 ^ 4` strings.
example : true ∈ {b : Bool | b = true} ↔ 2 ^ 4 < 2 * echo.acceptCount [true] 4 :=
  echo_decides.mem_iff_two_pow_lt_two_mul_acceptCount (a := true) (by norm_num)
example : echo.acceptCount [true] 4 = 16 ∧ echo.acceptCount [false] 4 = 0 := by decide

/-! ### Nondeterministic deciders through their choice tables -/

/-- Halt with output `[b]`. -/
private def emit (b : Bool) : Action 0 Bool Bool :=
  { inputTape := 0, workTapes := Fin.elim0, output := some b, state := none }

/-- From its only running state, either accept or reject. -/
private def guess : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr q _ _ action := q = false ∧ (action = emit true ∨ action = emit false)

private theorem guess_decides :
    guess.DecidesInTime (Function.Embedding.refl (List Bool)) Set.univ fun _ => 1 := by
  intro a
  refine ⟨MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun c hc => ?_, ?_⟩
  · simp only [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init] at hc
    obtain ⟨action, ⟨-, rfl | rfl⟩, rfl⟩ := hc <;> rfl
  · have hstep : guess.Step (guess.initCfg a) ((emit true).apply (guess.initCfg a)) :=
      ⟨emit true, ⟨rfl, .inl rfl⟩, rfl⟩
    exact iff_of_true trivial
      ⟨⟨(RelSeries.singleton _ _).cons (guess.initCfg a) hstep, rfl⟩, rfl, rfl⟩

-- The accepting branch is encoded by some padded choice string, of every sufficient length.
example (x : List Bool) (τ : ℕ) (hτ : Nat.card (Action 0 Bool Bool) ≤ τ) :
    0 < guess.choiceTable.acceptCount x τ :=
  (guess_decides.mem_iff_acceptCount_choiceTable_pos (a := x) (by simpa using hτ)).mp trivial

/-- A machine permitting no action: its initial configuration is stuck. -/
private def stuck : MultiTapeNTM 0 Bool Bool where
  q₀ := false
  Tr _ _ _ _ := False

private theorem stuck_decides :
    stuck.DecidesInTime (Function.Embedding.refl (List Bool)) ∅ fun _ => 1 := by
  intro a
  have hrun : stuck.RunsInTime a 1 :=
    MultiTapeNTM.runsInTime_one_of_forall_step_initCfg fun _ hc => by
      simp [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init, stuck] at hc
  refine ⟨hrun, iff_of_false id fun hacc => ?_⟩
  obtain ⟨p, hp, -⟩ := (MultiTapeNTM.accepts_iff_exists_time_eq hrun).mp hacc
  have h0 := p.toRunPath.step ⟨0, by
    unfold MultiTapeNTM.ComputationPath.time MultiTapeNTM.RunPath.time at hp; omega⟩
  change stuck.Step (p.toRunPath 0) _ at h0
  rw [show p.toRunPath 0 = stuck.initCfg a from p.head_eq] at h0
  simp [MultiTapeNTM.Step, MultiTapeNTM.initCfg, Cfg.init, stuck] at h0

-- The choice table rejects at the stuck configuration: no choice string accepts.
example (x : List Bool) (τ : ℕ) (hτ : Nat.card (Action 0 Bool Bool) ≤ τ) :
    stuck.choiceTable.acceptCount x τ = 0 :=
  Nat.eq_zero_of_not_pos fun h =>
    (stuck_decides.mem_iff_acceptCount_choiceTable_pos (a := x) (by simpa using hτ)).mpr h

/-! ### Class-level normal forms -/

example : {b : Bool | b = true} ∈ Complexity.BPTIME MultiTapeTM.encBool fun _ => 1 :=
  ⟨1, 0, 0, Unit, inferInstance, echo, by simpa using echo_decides⟩

example (h : {b : Bool | b = true} ∈ Complexity.BPTIME MultiTapeTM.encBool fun _ => 1) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapePTM k Bool State)
      (c₁ c₂ : ℕ), ∀ a τ, c₁ * 1 + c₂ ≤ τ →
        (a ∈ {b : Bool | b = true} ↔ 2 ^ τ < 2 * machine.acceptCount (MultiTapeTM.encBool a) τ) :=
  Complexity.exists_acceptCount_of_mem_BPTIME h

end ComplexityTests.HPVChoiceCount
