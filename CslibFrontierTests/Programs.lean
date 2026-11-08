/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.Simulation

/-! Adaptive programs using the common typed-oracle interface. The state examples exercise shared
private state, including state retained across substituted calls and a change of representation.
The basic examples are adapted from cslib PR #1129. -/

namespace ComplexityTests.Programs

open Cslib

private def adaptive (input : ℕ) : OracleComp (fun _ : ℕ => ℕ) ℕ := do
  let answer ← OracleComp.query input
  OracleComp.query answer

example (f : ℕ → ℕ) (input : ℕ) :
    OracleComp.interpret (fun query => PMF.pure (f query)) (adaptive input) =
      PMF.pure (f (f input)) := by simp [adaptive]

private noncomputable def counter (_ : Unit) : StateT ℕ PMF ℕ :=
  modifyGet fun state => (state, state + 1)

private def twice : OracleComp (fun _ : Unit => ℕ) (ℕ × ℕ) := do
  let first ← OracleComp.query ()
  let second ← OracleComp.query ()
  return (first, second)

example : (OracleComp.interpret counter twice).run 10 = PMF.pure ((10, 11), 12) := by
  simp [twice, counter]

private def doubleQuery (query : Unit) : OracleComp (fun _ : Unit => ℕ) ℕ := do
  let _ ← OracleComp.query query
  OracleComp.query query

-- Discarding a reply still changes state, including inside a substituted handler.
example :
    (OracleComp.interpret counter (OracleComp.interpret doubleQuery twice)).run 10 =
      PMF.pure ((11, 13), 14) := by simp [twice, doubleQuery, counter]

private noncomputable def shiftedCounter (offset : ℕ) (_ : Unit) : StateT ℕ PMF ℕ :=
  modifyGet fun state => (state - offset, state + 1)

-- The simulation theorem applies to arbitrary adaptive programs, retaining their final state.
example {α : Type} (program : OracleComp (fun _ : Unit => ℕ) α) (initial offset : ℕ) :
    ((OracleComp.interpret counter program).run initial).map
        (fun (result, state) => (result, state + offset)) =
      (OracleComp.interpret (shiftedCounter offset) program).run (initial + offset) := by
  apply OracleComp.run_interpret_map_state_of_invariant counter (shiftedCounter offset)
    (fun state => state + offset) (fun _ => True)
  · simp
  · intro query state _
    change (PMF.pure (state, state + 1)).map _ =
      PMF.pure (state + offset - offset, state + offset + 1)
    simp [Nat.add_right_comm]
  · trivial

-- A preserved invariant need only hold on supported transitions.
example {α : Type} (program : OracleComp (fun _ : Unit => ℕ) α)
    (initial lower : ℕ) (hinitial : lower ≤ initial) (result : α) (final : ℕ)
    (h : (result, final) ∈ ((OracleComp.interpret counter program).run initial).support) :
    lower ≤ final := by
  apply OracleComp.run_interpret_invariant counter (lower ≤ ·) ?_ program initial hinitial
    result final h
  intro query state hs answer next hnext
  change (answer, next) ∈ (PMF.pure (state, state + 1)).support at hnext
  have heq : (answer, next) = (state, state + 1) := by simpa using hnext
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  lia

-- Uniform finite sampling uses the same program interface and its probability interpreter.
example : ProbComp.eval (ProbComp.uniform Bool) = Probability.PMF.uniformOfFintype Bool := by
  simp

end ComplexityTests.Programs
