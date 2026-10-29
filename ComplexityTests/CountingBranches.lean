/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Counting.Certificate
import Mathlib.Tactic.FinCases

/-! Adversarial clients for occurrence multiplicity, early halting and certificate validity. -/

namespace ComplexityTests.CountingBranches

open Turing MultiTapeCTM

private def haltAction (bit : Bool) : MultiTapeMachine.Action 0 Bool Unit Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def duplicate : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [haltAction true, haltAction true]

private def initial : Cfg 0 Bool Unit [] := Cfg.init () []

private theorem duplicate_halts : duplicate.HaltsWithin 1 initial := by
  apply HaltsWithin.step (by decide)
  intro index
  apply HaltsWithin.halt
  fin_cases index <;> rfl

-- Equal actions are distinct occurrences, with distinct traces and certificates, and a
-- deterministic singleton halt has one branch.
private def singleton : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [haltAction true]

example (fuel : ℕ) (h : 1 ≤ fuel) :
    duplicate.branches 1 initial = {[0], [1]} ∧
      duplicate.acceptCount 1 initial = 2 ∧
      duplicate.rejectCount 1 initial = 0 ∧
      duplicate.certificateCount (· == [true]) 3 initial = 2 ∧
      duplicate.acceptCount fuel initial = 2 ∧
      singleton.branches 1 initial = {[0]} ∧
      singleton.acceptCount 3 initial = 1 :=
  ⟨by decide, by decide, by decide, by decide,
    (duplicate_halts.branchCount_eq h _).trans (by decide),
    by decide, by decide⟩

-- Different actions may also have the same successor: leftward movement at the left boundary
-- agrees with staying put, but the two transition occurrences still contribute separately.
private def boundaryAction (move : SignType) : Turing.Action 0 Bool Unit :=
  { inputTape := move, workTapes := Fin.elim0, output := some true, state := none }

private def sameSuccessor : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := [MultiTapeMachine.Action.emptyOracleEquiv.symm (boundaryAction (-1)),
    MultiTapeMachine.Action.emptyOracleEquiv.symm (boundaryAction 0)]

private def leftBoundary : Cfg 0 Bool Unit [] := { initial with inputPos := 0 }

example :
    boundaryAction (-1) ≠ boundaryAction 0 ∧
      (boundaryAction (-1)).apply leftBoundary = (boundaryAction 0).apply leftBoundary ∧
      sameSuccessor.acceptCount 1 leftBoundary = 2 := by
  refine ⟨fun h => ?_, ?_, by decide⟩
  · have := congrArg Turing.Action.inputTape h
    contradiction
  · apply Cfg.ext_zero_tapes <;> simp [Turing.Action.apply, boundaryAction, leftBoundary]

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def advance : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    Empty.elim Empty.elim

private def mixed : MultiTapeCTM 0 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [stop false, stop true, stop true] else [stop true, advance]

private def mixedInitial : Cfg 0 Bool Bool [] := Cfg.init false []

private theorem mixed_halts : mixed.HaltsWithin 2 mixedInitial := by
  apply HaltsWithin.step (by decide)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  · apply HaltsWithin.step (by decide)
    intro index
    fin_cases index <;> exact HaltsWithin.halt rfl

-- Binary and ternary branching coexist. Early halting does not multiply the short branch,
-- and truncation, invalid occurrences, and nonzero post-halt padding fail both classifiers.
example (fuel : ℕ) (h : 2 ≤ fuel) :
    mixed.branches 2 mixedInitial = {[0], [1, 0], [1, 1], [1, 2]} ∧
      mixed.certificates 2 mixedInitial = {[0, 0], [1, 0], [1, 1], [1, 2]} ∧
      mixed.acceptCount 2 mixedInitial = 3 ∧
      mixed.rejectCount 2 mixedInitial = 1 ∧
      mixed.certificateCount (fun out => !(out == [true])) 4 mixedInitial = 1 ∧
      mixed.branches fuel mixedInitial = mixed.branches 2 mixedInitial ∧
      mixed.decodeCertificate mixedInitial [1] = none ∧
      mixed.decodeCertificate mixedInitial [2, 0] = none ∧
      mixed.decodeCertificate mixedInitial [0, 1] = none ∧
      mixed.certificateAccepts (· == [true]) mixedInitial [0, 1] = false ∧
      mixed.certificateAccepts (fun out => !(out == [true])) mixedInitial [0, 1] = false :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    mixed_halts.branches_eq h, rfl, rfl, by decide, by decide, by decide⟩

-- The single padding label does not turn an already halted branch into many longer branches,
-- and a machine with no transitions has no branches and never halts.
private def halted : Cfg 0 Bool Unit [] := { initial with state := none, output := [true] }

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

example (fuel : ℕ) :
    duplicate.branches 0 halted = {[]} ∧
      duplicate.branches 4 halted = {[]} ∧
      duplicate.certificateCount (· == [true]) 0 halted = 1 ∧
      duplicate.certificateCount (· == [true]) 4 halted = 1 ∧
      duplicate.decodeCertificate halted [1] = none ∧
      duplicate.branches 0 initial = ∅ ∧
      stuck.branches 3 initial = ∅ ∧
      stuck.rejectCount 3 initial = 0 ∧
      ¬stuck.HaltsWithin fuel initial ∧
      (∃ bound, ∀ input (cfg : Cfg 0 Bool Bool input), (mixed.actions cfg).length ≤ bound) ∧
      (mixed.branches 2 mixedInitial).Nonempty := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, mixed.exists_branchBound, mixed_halts.branches_nonempty⟩
  intro h
  cases h with
  | halt h => cases h
  | step h _ => exact h rfl

end ComplexityTests.CountingBranches
