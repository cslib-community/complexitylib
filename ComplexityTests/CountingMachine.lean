/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.SharpP.Machine
import Mathlib.Tactic.FinCases

/-! Actual binary-checker clients: variable branching, equal-action multiplicity, first halting,
invalid-code exclusion for both verdicts, and the forward #P/GapP endpoints. -/

namespace ComplexityTests.CountingMachine

open Cslib Turing MultiTapeCTM MultiTapeTM

private def stop (bit : Bool) : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def advance : MultiTapeMachine.Action 0 Bool Bool Empty :=
  .step { inputTape := 0, workTapes := Fin.elim0, output := none, state := some true }
    Empty.elim Empty.elim

private def mixed : MultiTapeCTM 0 Bool Bool where
  initial := false
  tr state _ _ _ := if state then [stop false, stop true, stop true] else [stop true, advance]

private theorem mixed_bound (input : List Bool) (cfg : Cfg 0 Bool Bool input) :
    (mixed.actions cfg).length ≤ 2 ^ 2 := by
  cases hs : cfg.state with
  | none => simp [MultiTapeCTM.actions, hs]
  | some state => cases state <;> simp [MultiTapeCTM.actions, hs, mixed]

private theorem mixed_halts (input : List Bool) :
    mixed.HaltsWithin 2 (Cfg.init mixed.initial input) := by
  apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
  intro index
  fin_cases index
  · exact HaltsWithin.halt rfl
  · apply HaltsWithin.step (by exact List.cons_ne_nil _ _)
    intro index
    fin_cases index <;> exact HaltsWithin.halt rfl

private def stuck : MultiTapeCTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ := []

-- One early accepting branch, two equal-action accepting occurrences, one rejecting branch,
-- clock padding stability, canonical vs. invalid binary certificates, and stuck machine checks.
example (count : ℕ) (hcount : 2 ≤ count) (verdict : Bool) :
    Complexity.acceptCount (Checker.checkBinary mixed 2 true) [] 4 = 3 ∧
    Complexity.acceptCount (Checker.checkBinary mixed 2 false) [] 4 = 1 ∧
    Complexity.acceptCount (Checker.checkBinary mixed 2 true) [] (count * 2) = 3 ∧
    Complexity.acceptCount (Checker.checkBinary mixed 2 false) [] (count * 2) = 1 ∧
    Checker.checkBinary mixed 2 true ([], [false, false, false, false]) = true ∧
    (Checker.checkBinary mixed 2 verdict ([], [false, false, false, true]) = false ∧
      Checker.checkBinary mixed 2 verdict ([], [true, false, false, false]) = false ∧
      Checker.checkBinary mixed 2 verdict ([], [false, true, true, true]) = false ∧
      Checker.checkBinary mixed 2 verdict ([], [false, true]) = false ∧
      Checker.checkBinary mixed 2 verdict ([], [false, false, false]) = false ∧
      Checker.checkBinary mixed 2 verdict ([], []) = false ∧
      Checker.checkBinary stuck 1 verdict ([], [false]) = false) ∧
    (binaryCertificate 2 ([] : List ℕ) = [] ∧
      binaryCertificate 2 [0, 1, 2] = [false, false, false, true, true, false] ∧
      binaryIndices 3 2 [false, false, false, true, true, false] = [0, 1, 2]) ∧
    Complexity.acceptCount (Checker.checkBinary stuck 1 false) [] 1 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_, by decide, ?_, ⟨rfl, by decide, by decide⟩, by decide⟩
  · rw [Checker.acceptCount_checkBinary mixed (by decide) [] (mixed_bound []) count true,
      (mixed_halts []).branchCount_eq hcount]
    decide
  · rw [Checker.acceptCount_checkBinary mixed (by decide) [] (mixed_bound []) count false,
      (mixed_halts []).branchCount_eq hcount]
    decide
  · cases verdict <;> decide

example :
    (fun input : List Bool => mixed.acceptCount 2 (Cfg.init mixed.initial input)) ∈
      Complexity.SharpP encBits ∧
    (fun input : List Bool => mixed.rejectCount 2 (Cfg.init mixed.initial input)) ∈
      Complexity.SharpP encBits ∧
    (fun input : List Bool => (mixed.acceptCount 2 (Cfg.init mixed.initial input) : ℤ) -
      mixed.rejectCount 2 (Cfg.init mixed.initial input)) ∈ Complexity.GapP encBits :=
  ⟨by simpa only [Polynomial.eval_C, encBits_apply] using
     mixed.acceptCount_mem_SharpP encBits (Polynomial.C 2),
   by simpa only [Polynomial.eval_C, encBits_apply] using
     mixed.rejectCount_mem_SharpP encBits (Polynomial.C 2),
   by simpa only [Polynomial.eval_C, encBits_apply] using
     mixed.gapCount_mem_GapP encBits (Polynomial.C 2)⟩

end ComplexityTests.CountingMachine
