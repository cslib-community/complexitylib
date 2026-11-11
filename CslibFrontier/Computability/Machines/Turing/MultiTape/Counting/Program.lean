/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Program
import Mathlib.Data.List.OfFn

/-!
# Counting-machine runs as shared programs

The choice program queries an occurrence index in `Fin choices.length`. Interpreting such
queries by the list of all indices preserves repeated occurrences, and a singleton instruction
has one outcome. An empty choice list interprets to no outcomes.

## Main definitions

* `Turing.MultiTapeCTM.occurrenceSpec`: a finite occurrence-index query.
* `Turing.MultiTapeCTM.chooseOccurrence`: select an entry without identifying equal entries.
* `Turing.MultiTapeCTM.runProgram`: the existing shared `runConfigFrom` with this choice handler.

## Main results

* `Turing.MultiTapeCTM.interpret_chooseOccurrence`: List interpretation recovers the exact list.
* `Turing.MultiTapeCTM.chooseOccurrence_map`: mapping preserves the occurrence query program.
* `Turing.MultiTapeCTM.interpret_runProgram_succ`: one actual transition unfolds by list bind.

These are programs in the existing `PFunctor.FreeM` calculus, not a second branch semantics or
an efficiency claim about an interpreter. The machine and program infrastructure credits its
authors in `MultiTape.Machine` and `MultiTape.Machine.Program`; the oracle interface and generic
interpretation credit Devon Tuma, Quang Dao and VCVio in `Languages.Probabilistic.Basic`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib

/-- Query the index of one of `n` transition occurrences; `n = 0` permits no response. -/
abbrev occurrenceSpec : OracleSpec ℕ := Fin

/-- Select a list entry by its occurrence index, preserving equal entries at distinct positions. -/
def chooseOccurrence {α : Type} (choices : List α) : OracleComp occurrenceSpec α :=
  (fun index => choices[index]) <$> OracleComp.query choices.length

/-- Mapping changes each response value without adding or identifying occurrence queries. -/
theorem chooseOccurrence_map {α β : Type} (f : α → β) (choices : List α) :
    chooseOccurrence (f <$> choices) = f <$> chooseOccurrence choices := by
  change PFunctor.FreeM.liftBind (P := ⟨ℕ, Fin⟩) (choices.map f).length
      (fun index => pure ((choices.map f)[index])) =
    PFunctor.FreeM.liftBind (P := ⟨ℕ, Fin⟩) choices.length
      (fun index => pure (f choices[index]))
  congr 1
  · simp
  · apply Function.hfunext
    · simp
    · intro left right h
      have hval : left.val = right.val := Fin.val_eq_val_of_heq h
      simp [hval]

/-- Enumerating responses recovers the original list, including its order and multiplicities. -/
theorem interpret_chooseOccurrence {α : Type} (choices : List α) :
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (chooseOccurrence choices) = choices := by
  simp [chooseOccurrence, List.map_ofFn]

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- The shared clocked machine program, with finite-index choice and no oracle channels. -/
def runProgram (machine : MultiTapeCTM k Symbol State) (fuel : ℕ)
    (cfg : Cfg k Symbol State input) : OracleComp occurrenceSpec (Cfg k Symbol State input) :=
  MultiTapeMachine.Config.tapes <$> machine.runConfigFrom chooseOccurrence
    (fun oracle => oracle.elim) fuel (MultiTapeMachine.Config.emptyOracleEquiv.symm cfg)

@[simp] theorem runProgram_zero (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) : machine.runProgram 0 cfg = pure cfg := by
  simp [runProgram, MultiTapeMachine.Config.emptyOracleEquiv]

theorem runProgram_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (fuel : ℕ) :
    machine.runProgram fuel cfg = pure cfg := by
  unfold runProgram
  rw [MultiTapeMachine.runConfigFrom_halted machine chooseOccurrence
    (fun oracle => oracle.elim) fuel (MultiTapeMachine.Config.emptyOracleEquiv.symm cfg) h]
  simp [MultiTapeMachine.Config.emptyOracleEquiv]

private theorem step_emptyOracle (cfg : Cfg k Symbol State input)
    (action : Turing.Action k Symbol State) (symbol : Empty → Option Symbol)
    (move : Empty → SignType) :
    (MultiTapeMachine.Config.emptyOracleEquiv.symm cfg).step action symbol move =
      MultiTapeMachine.Config.emptyOracleEquiv.symm (action.apply cfg) :=
  MultiTapeMachine.Config.ext rfl (funext fun oracle => oracle.elim)

/-- List interpretation executes each live occurrence once and then continues the same program. -/
theorem interpret_runProgram_succ (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) (state : State) (h : cfg.state = some state) :
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
      (machine.runProgram (fuel + 1) cfg) =
      (machine.actions cfg).flatMap fun action =>
        OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
          (machine.runProgram fuel (action.apply cfg)) := by
  have ht : (MultiTapeMachine.Config.emptyOracleEquiv.symm cfg).tapes = cfg := rfl
  have ha : (MultiTapeMachine.Config.emptyOracleEquiv.symm cfg).answerSymbols = Empty.elim :=
    funext fun oracle => oracle.elim
  simp only [runProgram, MultiTapeMachine.runConfigFrom, ht, h, ha, OracleComp.interpret_map,
    OracleComp.interpret_bind, interpret_chooseOccurrence, actions, List.flatMap_map, map_bind]
  change List.flatMap _ _ = List.flatMap _ _
  congr 1
  funext action
  cases action with
  | step action symbol move =>
    dsimp only
    rw [step_emptyOracle]
    rfl
  | query oracle _ => exact oracle.elim

end Turing.MultiTapeCTM
