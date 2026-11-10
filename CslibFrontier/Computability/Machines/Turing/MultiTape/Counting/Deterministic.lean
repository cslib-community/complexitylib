/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Execution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Singleton deterministic counting machines

Embed a native deterministic machine into the shared List-choice core by putting its instruction
in a singleton list. A deterministic transition has exactly one occurrence. A halt has one
terminal trace, independently of the extra clock allowed after its first halting time.

## Main definitions

* `Turing.MultiTapeCTM.ofDeterministic`: the singleton occurrence lift.

## Main results

* `Turing.MultiTapeCTM.runList_ofDeterministic`: the interpreted run is a singleton native run.
* `Turing.MultiTapeCTM.haltsWithin_ofDeterministic_iff`: native and counting halting clocks agree.
* `Turing.MultiTapeCTM.branchCount_ofDeterministic`: a halted run contributes exactly zero or one.

## References

The native deterministic machine and tape plumbing are by Christian Reitwiessner and Samuel
Schlesinger; see `MultiTape.Deterministic` and the upstream files it imports. This singleton
embedding follows the shared machine core and does not use the two-coin probabilistic lift.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Each deterministic instruction becomes one List occurrence in the common machine core. -/
noncomputable def ofDeterministic (machine : MultiTapeTM k Symbol State) :
    MultiTapeCTM k Symbol State where
  initial := machine.q₀
  tr state symbol work _ := [.step (machine.tr state symbol work) Empty.elim Empty.elim]

/-- The live transition list has exactly the original deterministic action. -/
theorem actions_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (state : State) (h : cfg.state = some state) :
    (ofDeterministic machine).actions cfg =
      [machine.tr state cfg.inputSymbol cfg.workTapeSymbols] := by
  simp [actions, ofDeterministic, h, MultiTapeMachine.Action.emptyOracleEquiv]

/-- Interpreting the singleton lift gives one occurrence of the exact native configuration. -/
theorem runList_ofDeterministic (machine : MultiTapeTM k Symbol State) (fuel : ℕ)
    (cfg : Cfg k Symbol State input) :
    (ofDeterministic machine).runList fuel cfg = [machine.runFrom cfg fuel] := by
  induction fuel generalizing cfg with
  | zero => rfl
  | succ fuel ih =>
    cases hs : cfg.state with
    | none =>
      have hhalt : machine.runFrom cfg (fuel + 1) = cfg :=
        Function.iterate_fixed (MultiTapeTM.step_of_halt hs) _
      simp [runList_halted _ hs, hhalt]
    | some state =>
      rw [runList_succ _ cfg fuel state hs, actions_ofDeterministic machine cfg state hs]
      simp only [List.flatMap_singleton, ih, MultiTapeTM.runFrom, Function.iterate_succ_apply]
      rw [MultiTapeTM.step_of_state hs]

/-- Every local view in the singleton lift has exactly one occurrence. -/
theorem nonblocking_ofDeterministic (machine : MultiTapeTM k Symbol State) :
    (ofDeterministic machine).Nonblocking := by
  intro state symbol work
  simp [ofDeterministic]

/-- Halting clocks agree exactly, without inserting a choice or delay after early halting. -/
theorem haltsWithin_ofDeterministic_iff (machine : MultiTapeTM k Symbol State) (fuel : ℕ)
    (cfg : Cfg k Symbol State input) :
    (ofDeterministic machine).HaltsWithin fuel cfg ↔ (machine.runFrom cfg fuel).Halted := by
  constructor
  · intro h
    apply h.halted_of_mem_runList
    simp [runList_ofDeterministic]
  · intro h
    apply haltsWithin_of_halted _ (nonblocking_ofDeterministic machine).actions_ne_nil fuel cfg
    simpa [runList_ofDeterministic] using h

/-- A halted deterministic computation contributes one branch exactly when its output passes. -/
theorem branchCount_ofDeterministic (machine : MultiTapeTM k Symbol State)
    (verdict : List Symbol → Bool)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) (h : (machine.runFrom cfg fuel).Halted) :
    (ofDeterministic machine).branchCount verdict fuel cfg =
      if verdict (machine.runFrom cfg fuel).output then 1 else 0 := by
  rw [← countP_runList, runList_ofDeterministic]
  simp [h]

end Turing.MultiTapeCTM
