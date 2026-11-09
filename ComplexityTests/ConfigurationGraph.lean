/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph

/-! Compact graph checks: native acceptance with zero tapes on every input, empty-input
boundaries, ternary blank gaps and erasure, absorbing rejecting output, and native routines. -/

namespace ComplexityTests.ConfigurationGraph

open Cslib.Turing Turing Turing.MultiTapeTM
open Turing.MultiTapeNTM.ConfigurationGraph

private def acceptAction : Action 0 Bool Unit :=
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

private def acceptMachine : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ _ _ a := a = acceptAction

private theorem accepts_acceptMachine (w : List Bool) : acceptMachine.Accepts w := by
  have hstep : acceptMachine.Step (acceptMachine.initCfg w)
      (acceptAction.apply (acceptMachine.initCfg w)) := ⟨acceptAction, rfl, rfl⟩
  refine ⟨⟨(RelSeries.singleton _ _).cons (acceptMachine.initCfg w) hstep, rfl⟩, ?_, ?_⟩ <;>
    simp [acceptAction]

/-- A concrete machine satisfies all hypotheses of the exact graph bridge, including at `[]`. -/
example (w : List Bool) : ∃ u,
    Relation.ReflTransGen (Edge acceptMachine (radix (radixExponent Unit 0) w.length) w)
      (startID acceptMachine (radix (radixExponent Unit 0) w.length)) u ∧
      bad (k := 0) (State := Unit) (radix (radixExponent Unit 0) w.length) w.length u = true :=
  (accepts_iff_reachable_bad_of_runsInSpace 0
    (MultiTapeNTM.runsInSpace_zero_tapes _ _ _)).mp (accepts_acceptMachine w)

/-- An out-of-range source ID cannot create an edge, even with an arbitrary supplied bit. -/
example (B n v : ℕ) (b : Option Bool) :
    edgeWithSymbol acceptMachine B n (vertexBound (k := 0) B) v b = false := by
  cases h : edgeWithSymbol acceptMachine B n (vertexBound (k := 0) B) v b with
  | false => rfl
  | true => have := (lt_vertexBound_of_edgeWithSymbol h).1; omega

example : inputSymbol 0 1 (some true) = none := by decide
example : inputSymbol 3 0 (some true) = none := by decide
example : inputSymbol 3 4 (some false) = none := by decide
example : inputSymbol 3 2 (some false) = some false := by decide

example : stackCode (StackTape.cons none (StackTape.cons (some false) StackTape.nil)) = 3 :=
  by decide
example : stackCode (StackTape.cons none (StackTape.nil : StackTape Bool)) = 0 := by decide
example : tapeStep (some none, .zero) (2, 17, 23) = (0, 17, 23) := by decide
example : tapeStep (none, .pos) (2, 1, 3) = (0, 5, 1) := by decide

example : outputStep 0 (some true) = 1 := by decide
example : outputStep 0 (some false) = 2 := by decide
example (b : Bool) : outputStep 1 (some b) = 2 := by cases b <;> decide
example (b : Option Bool) : outputStep 2 b = 2 := by rcases b with _ | _ | _ <;> decide

/-- Encoded radix, length, source, target, and the one supplied input symbol. -/
private abbrev encEdge : ℕ × ℕ × ℕ × ℕ × Option Bool ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat (encOption encBool))))

open ComputableInSpace in
/-- The edge routine on its exact encoded arguments, in linear workspace. -/
example : ComputableInSpace
    (fun a : ℕ × ℕ × ℕ × ℕ × Option Bool =>
      edgeWithSymbol acceptMachine a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    encEdge encBool (fun a => (encEdge a).length) := by
  have hr₁ := snd encNat (encPair encNat (encPair encNat (encPair encNat (encOption encBool))))
  have hr₂ := budget_comp_linear (snd _ _) hr₁
  have hr₃ := budget_comp_linear (snd _ _) hr₂
  exact edgeWithSymbol_budget acceptMachine (fst _ _) (budget_comp_linear (fst _ _) hr₁)
    (budget_comp_linear (fst _ _) hr₂) (budget_comp_linear (fst _ _) hr₃)
    (budget_comp_linear (snd _ _) hr₃) (.refl _)

end ComplexityTests.ConfigurationGraph
