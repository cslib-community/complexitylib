/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Clock
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Equivalence
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Run
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Exact signals from a prepared unary budget

The existing clock controller continues to consume its budget after the source has halted.
Specializing its source to the one-step `nop` gives one distinguished signal state per budget
cell. This is the countdown component of the binary-input step counter; it does not prepare
its own budget and alone does not establish Goldreich's Exercise 4.5.

## Main definitions

* `Turing.MultiTapeTM.StepCounter.countdown`: the native specialization of `withClock`.
* `Turing.MultiTapeTM.StepCounter.signalState`: the unique signal phase after source halting.

## Main results

* `Turing.MultiTapeTM.StepCounter.countdown_halted`: exact-budget halting in `2*n+1` steps.
* `Turing.MultiTapeTM.StepCounter.countdown_signal_iff`: the exact native signal-time profile.
* `Turing.MultiTapeTM.StepCounter.countdown_leaves_signal`: each signal is left immediately.
-/

public section

namespace Turing.MultiTapeTM.StepCounter

open MultiTapeMachine

/-- Consume an exact prepared budget using the existing clock controller. The source performs
one no-op step and halts; the controller continues producing signals until the budget ends. -/
noncomputable def countdown : MultiTapeTM 1 Bool (Clock.Control Unit) :=
  (nop 0 Bool).toMachine.withClock.toTM

/-- The source has halted and the controller is about to advance the budget head. -/
@[expose] def signalState : Clock.Control Unit := (true, none)

/-- The countdown begins before its first signal. -/
theorem countdown_q₀ : countdown.q₀ = (false, some ()) := by
  change (false, some (nop 0 Bool).q₀) = (false, some ())
  exact congrArg (fun q : Unit => (false, some q)) (Subsingleton.elim _ _)

/-- The deterministic transition table of the existing controller in this specialization. -/
theorem countdown_tr (q : Clock.Control Unit) (symbol : Option Bool)
    (work : Fin 1 → Option Bool) :
    countdown.tr q symbol work =
      if q.1 then AuxiliaryTape.move (some (false, q.2)) 1
      else if work 0 = some true then AuxiliaryTape.move (some signalState) 0
      else AuxiliaryTape.move none 0 := by
  rcases q with ⟨phase, state⟩
  cases phase <;> cases state <;> by_cases hwork : work 0 = some true
  all_goals
    simp only [countdown, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr,
      MultiTapeMachine.withClock, toMachine, nop,
      Bool.false_eq_true, Fin.last_zero, hwork, ↓reduceIte,
      MultiTapeMachine.Action.emptyOracleEquiv,
      Clock.tick, Clock.idle, AuxiliaryTape.move, signalState]
    rfl

private def sourceCfg (input : List Bool) : Config 0 Bool Unit Empty input where
  tapes := {
    state := none
    inputPos := 1
    workTapes := Fin.elim0
    workTapePos := Fin.elim0
    output := [] }
  channels := Empty.elim

private def clockCfg (input : List Bool) (n : ℕ) (p : ℤ) (q : Option (Clock.Control Unit)) :
    Cfg 1 Bool (Clock.Control Unit) input :=
  ((AuxiliaryTape.config (sourceCfg input) (tapeOfList (List.replicate n true))
    p false).tapes).withState q

private theorem step_read (input : List Bool) (n p : ℕ) (hp : p < n)
    (q : Option Unit) :
    countdown.step (clockCfg input n p (some (false, q))) =
      clockCfg input n p (some signalState) := by
  rw [countdown.step_of_state rfl, countdown_tr]
  have hread : (clockCfg input n p (some (false, q))).workTapeSymbols 0 = some true := by
    dsimp only [clockCfg, Cfg.workTapeSymbols, Cfg.withState, AuxiliaryTape.config, sourceCfg]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.lastCases_last, Fin.lastCases_last]
    simp [hp]
  simp only [Bool.false_eq_true, ↓reduceIte, hread]
  change ((AuxiliaryTape.config (sourceCfg input) (tapeOfList (List.replicate n true))
    p false).step (Clock.idle (some (true, none))) Empty.elim Empty.elim).tapes = _
  exact congrArg Config.tapes (Clock.step_pause (sourceCfg input) _ p)

private theorem step_signal (input : List Bool) (n : ℕ) (p : ℤ) :
    countdown.step (clockCfg input n p (some signalState)) =
      clockCfg input n (p + 1) (some (false, none)) := by
  rw [countdown.step_of_state rfl, countdown_tr]
  simp only [signalState, ↓reduceIte]
  change ((AuxiliaryTape.config (sourceCfg input) (tapeOfList (List.replicate n true))
    p true).step (Clock.tick none) Empty.elim Empty.elim).tapes = _
  exact congrArg Config.tapes (Clock.step_tick (sourceCfg input) _ p)

private theorem step_stop (input : List Bool) (n : ℕ) (q : Option Unit) :
    countdown.step (clockCfg input n n (some (false, q))) = clockCfg input n n none := by
  rw [countdown.step_of_state rfl, countdown_tr]
  have hread : (clockCfg input n n (some (false, q))).workTapeSymbols 0 = none := by
    dsimp only [clockCfg, Cfg.workTapeSymbols, Cfg.withState, AuxiliaryTape.config, sourceCfg]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.lastCases_last, Fin.lastCases_last]
    simp
  simp only [Bool.false_eq_true, ↓reduceIte, hread, reduceCtorEq]
  change ((AuxiliaryTape.config (sourceCfg input) (tapeOfList (List.replicate n true))
    n false).step (AuxiliaryTape.move none 0) Empty.elim Empty.elim).tapes = _
  exact congrArg Config.tapes (AuxiliaryTape.step_stop (sourceCfg input) _ n false)

private theorem clockCfg_zero (input : List Bool) (n : ℕ)
    (q : Option (Clock.Control Unit)) :
    clockCfg input n 0 q = wordsCfg input q (fun _ => List.replicate n true) [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    subst i
    simp only [clockCfg, Cfg.withState, AuxiliaryTape.config, sourceCfg, wordsCfg,
      Fin.lastCases_last]
  · funext i
    have hi : i = Fin.last 0 := Subsingleton.elim _ _
    subst i
    simp only [clockCfg, Cfg.withState, AuxiliaryTape.config, sourceCfg, wordsCfg,
      Fin.lastCases_last]

private abbrev startCfg (input : List Bool) (n : ℕ) :=
  clockCfg input n 0 (some (false, some ()))

private theorem run_even (input : List Bool) (n i : ℕ) (hi : i ≤ n) :
    countdown.runFrom (startCfg input n) (2 * i) =
      clockCfg input n i (some (false, if i = 0 then some () else none)) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, runFrom_add, ih (by omega),
      runFrom_succ, runFrom_succ]
    change countdown.step (countdown.step (clockCfg input n i
      (some (false, if i = 0 then some () else none)))) = _
    rw [step_read input n i (by omega), step_signal]
    simp

private theorem run_odd (input : List Bool) (n i : ℕ) (hi : i < n) :
    countdown.runFrom (startCfg input n) (2 * i + 1) =
      clockCfg input n i (some signalState) := by
  rw [runFrom_succ, run_even input n i hi.le, step_read input n i hi]

private theorem run_stop (input : List Bool) (n : ℕ) :
    countdown.runFrom (startCfg input n) (2 * n + 1) = clockCfg input n n none := by
  rw [runFrom_succ, run_even input n n le_rfl, step_stop]

/-- An exact prepared budget halts after `2*n+1` native steps, including zero budget. -/
theorem countdown_halted (input : List Bool) (n : ℕ) :
    (countdown.runFrom
      (wordsCfg input (some countdown.q₀) (fun _ => List.replicate n true) [])
      (2 * n + 1)).Halted := by
  rw [countdown_q₀, ← clockCfg_zero, run_stop]
  rfl

/-- The one designated signal state occurs exactly once per budget cell, at the odd times
before budget exhaustion. This statement includes all times after halting. -/
theorem countdown_signal_iff (input : List Bool) (n t : ℕ) :
    (countdown.runFrom
      (wordsCfg input (some countdown.q₀) (fun _ => List.replicate n true) []) t).state =
        some signalState ↔ ∃ i < n, t = 2 * i + 1 := by
  rw [countdown_q₀, ← clockCfg_zero]
  by_cases ht : t ≤ 2 * n
  · by_cases heven : t % 2 = 0
    · have heq : t = 2 * (t / 2) := by omega
      rw [heq, run_even input n (t / 2) (by omega)]
      simp only [clockCfg, Cfg.withState, signalState, Option.some.injEq, Prod.mk.injEq,
        Bool.false_eq_true, false_and, false_iff]
      omega
    · have heq : t = 2 * (t / 2) + 1 := by omega
      rw [heq, run_odd input n (t / 2) (by omega)]
      constructor
      · intro _
        exact ⟨t / 2, by omega, rfl⟩
      · intro _
        rfl
  · have hhalt : (countdown.runFrom (startCfg input n) (2 * n + 1)).Halted := by
      rw [run_stop]
      rfl
    rw [runFrom_eq_of_halt countdown _ (by omega) hhalt, run_stop]
    simp only [clockCfg, Cfg.withState, reduceCtorEq, false_iff]
    omega

/-- Every signal state is left on the next transition, so its visits are distinct signals. -/
theorem countdown_leaves_signal (input : List Bool) (n t : ℕ)
    (h : (countdown.runFrom
      (wordsCfg input (some countdown.q₀) (fun _ => List.replicate n true) []) t).state =
        some signalState) :
    (countdown.runFrom
      (wordsCfg input (some countdown.q₀) (fun _ => List.replicate n true) []) (t + 1)).state ≠
        some signalState := by
  intro hnext
  obtain ⟨i, hi, ht⟩ := (countdown_signal_iff input n t).mp h
  obtain ⟨j, hj, ht'⟩ := (countdown_signal_iff input n (t + 1)).mp hnext
  omega

end Turing.MultiTapeTM.StepCounter
