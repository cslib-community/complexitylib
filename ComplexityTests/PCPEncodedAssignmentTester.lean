/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/


import Complexity.Computability.PCP.Encoded.AssignmentTester
import Complexity.Computability.PCP.Encoded.AssignmentTester.Enumeration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime
import Mathlib.Tactic.FinCases

/-! Tests for executable assignment testing and its uniform finite-table certificates. -/

namespace ComplexityTests.PCPEncodedTester

open Cslib.PCP Cslib.PCP.HadamardTester Turing.MultiTapeTM

attribute [local instance] HadamardTester.instFinEnumBool Rand.finEnum

private def same : Bool → Bool → Bool := fun a b => a == b

private def coins : Rand Bool :=
  ((0, 0), (0, 0), (0, 0, 0, 0, 0),
    (fun e => decide (e = .inl ((0, false), (1, true))), 0), (0, id, 0))

example : Encoded.HadamardTester.compatible same (0, false) (1, false) = true := by decide
example : Encoded.HadamardTester.compatible same (0, false) (1, true) = false := by decide
example : Encoded.HadamardTester.compatible same (0, false) (0, true) = false := by decide
example : Encoded.HadamardTester.compatible (fun _ _ : Bool => false)
    (0, false) (0, false) = false := by decide

example : Encoded.HadamardTester.equationCoeff same (.inl ((0, false), (1, true)))
    ((0, false), (1, true)) = true := by decide
example : Encoded.HadamardTester.equationCoeff same (.inl ((0, false), (1, false)))
    ((0, false), (1, false)) = false := by decide
example : Encoded.HadamardTester.equationCoeff same (.inr 0)
    ((0, true), (0, true)) = true := by decide
example : Encoded.HadamardTester.equationCoeff same (.inr 0)
    ((0, true), (1, true)) = false := by decide

-- The equation check queries the coefficient of the selected incompatible variable pair.
example : Encoded.HadamardTester.query same coins (.inr (.inr (.inr (.inl 1)))) =
    .inr (.inr (Pi.single ((0, false), (1, true)) true)) := by
  apply congrArg Sum.inr
  apply congrArg Sum.inr
  funext p
  rcases p with ⟨⟨b, a⟩, ⟨b', a'⟩⟩
  fin_cases b <;> fin_cases b' <;> cases a <;> cases a' <;> decide

-- The input check reads the selected end's long-code position and the embedded linear position.
example : Encoded.HadamardTester.query same coins (.inr (.inr (.inr (.inr 0)))) =
    .inl (0, id) := by decide
example : Encoded.HadamardTester.query same coins (.inr (.inr (.inr (.inr 2)))) =
    .inr (.inl (endEmbed 0 id)) := by
  apply congrArg Sum.inr
  apply congrArg Sum.inl
  funext p
  rcases p with ⟨b, a⟩
  fin_cases b <;> cases a <;> decide

example : Encoded.HadamardTester.accepts same coins (fun _ => false) = true := by decide
example : Encoded.HadamardTester.accepts same coins
    (fun i => decide (i = .inr (.inr (.inr (.inr 0))))) = false := by decide

-- Selecting an odd-parity endpoint equation rejects the all-zero answers.
example : Encoded.HadamardTester.accepts same
    ((0, 0), (0, 0), (0, 0, 0, 0, 0), (fun e => decide (e = .inr 0), 0), (0, id, 0))
    (fun _ => false) = false := by decide

example : Encoded.HadamardTester.accepts same coins
    (fun i => honestProof (fun _ => false) (Encoded.HadamardTester.query same coins i)) =
      true := by decide

-- Existing soundness/completeness statements apply through exact tester equality.
example {α : Type} [Fintype α] [DecidableEq α] (constraint : α → α → Bool)
    (σ : Fin 2 → α) (h : constraint (σ 0) (σ 1) = true) (ω : Rand α) :
    Encoded.HadamardTester.accepts constraint ω
      (fun i => honestProof σ (Encoded.HadamardTester.query constraint ω i)) = true := by
  rw [Encoded.HadamardTester.accepts_eq_true]
  simpa only [Encoded.HadamardTester.query_eq, LocalTest.Passes] using passes_honestProof h ω

example : ComputableInPolyTime
    (fun p : (Bool → Bool → Bool) × Rand Bool × Query =>
      Encoded.HadamardTester.query p.1 p.2.1 p.2.2)
    (encPair (encPi (encPi encBool)) (encPair (encFinEnum (Rand Bool)) (encFinEnum Query)))
    (encFinEnum (Pos Bool)) := by fun_prop

example : ComputableInPolyTime
    (fun p : (Bool → Bool → Bool) × Rand Bool × (Query → Bool) =>
      Encoded.HadamardTester.accepts p.1 p.2.1 p.2.2)
    (encPair (encPi (encPi encBool)) (encPair (encFinEnum (Rand Bool)) (encPi encBool)))
    encBool := by polytime

-- The constraint is computed from an unbounded word, not fixed with the alphabet.
example : ComputableInPolyTime
    (fun p : List Bool × Rand Bool × Query => Encoded.HadamardTester.query
      (fun a b => p.1.getD (a.toNat + 2 * b.toNat) false) p.2.1 p.2.2)
    (encPair encBits (encPair (encFinEnum (Rand Bool)) (encFinEnum Query)))
    (encFinEnum (Pos Bool)) := by polytime

end ComplexityTests.PCPEncodedTester
