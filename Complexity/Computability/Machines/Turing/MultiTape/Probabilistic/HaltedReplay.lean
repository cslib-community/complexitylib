/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.AcceptCount

/-!
# Replays after halting

A halted configuration of a fair-coin table ignores its coin
(`Turing.MultiTapePTM.step_withCoin_of_halted`) and every further coin
(`Turing.MultiTapePTM.stepCoins_of_halted`). So a table that halts at its first step decides
every coin string at once: the table `Turing.MultiTapePTM.acceptAll`, which emits `true` and
halts, accepts all `2 ^ τ` coin strings of every positive length `τ`
(`Turing.MultiTapePTM.acceptCount_acceptAll`).

## Main definitions

* `Turing.MultiTapePTM.acceptAll`: the fair-coin table that emits `true` and halts.

## Main results

* `Turing.MultiTapePTM.step_withCoin_of_halted`, `Turing.MultiTapePTM.stepCoins_of_halted`: a
  halted configuration ignores its coins.
* `Turing.MultiTapePTM.acceptCount_acceptAll`: `acceptAll` accepts every coin string of positive
  length.
-/

public section

namespace Turing.MultiTapePTM

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- A halted configuration ignores its coin. -/
theorem step_withCoin_of_halted (machine : MultiTapePTM k Symbol State)
    {c : Cfg k Symbol State input} (h : c.Halted) (bit : Bool) :
    (machine.withCoin bit).toTM.step c = c :=
  MultiTapeTM.step_of_halt h

/-- A halted configuration ignores any further coins. -/
theorem stepCoins_of_halted (machine : MultiTapePTM k Symbol State)
    {c : Cfg k Symbol State input} (h : c.Halted) (coins : List Bool) :
    machine.stepCoins coins c = c := by
  induction coins with
  | nil => rfl
  | cons bit coins ih => rw [stepCoins_cons, step_withCoin_of_halted machine h, ih]

/-- The fair-coin table that emits `true` and halts at its first step, whatever the coin. -/
@[expose] def acceptAll : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ _ := .step ⟨0, Fin.elim0, some true, none⟩ Empty.elim Empty.elim

/-- Every coin string of positive length makes `acceptAll` accept. -/
theorem acceptCount_acceptAll (input : List Bool) (n : ℕ) :
    acceptAll.acceptCount input (n + 1) = 2 ^ (n + 1) := by
  rw [acceptCount, Cslib.Complexity.acceptCount, Finset.filter_true_of_mem]
  · simp
  · intro w _
    have hstep : (acceptAll.withCoin (w 0)).toTM.step (Cfg.init acceptAll.initial input) =
        ⟨none, 1, fun _ _ => none, fun _ => 0, [true]⟩ := by
      rw [MultiTapeTM.step_of_state rfl, MultiTapeMachine.toTM, MultiTapeTM.tr_ofTr]
      exact Cfg.ext rfl (by simp [acceptAll, MultiTapeMachine.Action.emptyOracleEquiv,
        withCoin]) (funext fun i => i.elim0) (funext fun i => i.elim0) rfl
    rw [List.ofFn_succ, runClosedCoins_eq_output_stepCoins, stepCoins_cons, hstep,
      stepCoins_of_halted _ rfl]
    simp

end Turing.MultiTapePTM
