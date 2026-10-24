/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Encoded.SelectedAssignmentTester
import Complexity.Computability.PCP.SelectedComposition
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-! Semantic regressions and client certificates for the selected assignment tester. -/

namespace ComplexityTests.PCPSelectedAssignmentTester

open Cslib.PCP Cslib.PCP.HadamardTester Turing.MultiTapeTM

private def same : Bool → Bool → Bool := fun a b => a == b

private def coins : Rand Bool :=
  ((0, 0), (0, 0), (0, 0, 0, 0, 0),
    (fun e => decide (e = .inl ((0, false), (1, true))), 0), (0, id, 0))

private def selected (branch : Fin 5) := (branch, coins)
private def zeros : Fin 6 → Bool := fun _ => false
private def set (i : Fin 6) : Fin 6 → Bool := fun j => if j = i then true else false

-- Branches 0 and 1 are the two BLR checks; branch 2 is the tensor check.
example : Encoded.SelectedHadamardTester.accepts same (selected 0) zeros = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 0) (set 2) = false := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 1) zeros = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 1) (set 2) = false := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 2) zeros = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 2) (set 0) = false := by decide

-- Branches 3 and 4 are equation and input checks; their unused padded slots are ignored.
example : Encoded.SelectedHadamardTester.accepts same (selected 3) zeros = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 3) (set 1) = false := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 3)
    (fun i => if i < 2 then false else true) = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 4) zeros = true := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 4) (set 0) = false := by decide
example : Encoded.SelectedHadamardTester.accepts same (selected 4)
    (fun i => if i < 3 then false else true) = true := by decide

-- Padding is ignored for the first BLR branch as well.
example : Encoded.SelectedHadamardTester.accepts same (selected 0)
    (fun i => if i < 3 then false else true) = true := by decide

-- Selected equation and input positions match the old five-check query layout.
example : Encoded.SelectedHadamardTester.query same (selected 3) 1 =
    Encoded.HadamardTester.query same coins (.inr (.inr (.inr (.inl 1)))) := by
  rfl

example : Encoded.SelectedHadamardTester.query same (selected 4) 0 =
    Encoded.HadamardTester.query same coins (.inr (.inr (.inr (.inr 0)))) := by
  rfl

-- Exact interpretation transfers perfect completeness for every satisfied Boolean constraint.
example (constraint : Bool → Bool → Bool) (σ : Fin 2 → Bool)
    (hσ : constraint (σ 0) (σ 1) = true) (ω : Fin 5 × Rand Bool) :
    Encoded.SelectedHadamardTester.accepts constraint ω
      (fun i => honestProof σ (Encoded.SelectedHadamardTester.query constraint ω i)) = true := by
  rw [Encoded.SelectedHadamardTester.accepts_eq_true]
  simpa only [LocalTest.Passes, Encoded.SelectedHadamardTester.query_eq] using
    passes_selected_honestProof (C := fun a b => constraint a b = true) hσ ω

attribute [local fun_prop] ComputableInPolySpace.tidy in
attribute [local fun_prop] ComputableInPolyTime.tidy in
example : ComputableTidilyInPolyTime
    (fun p : (Bool → Bool → Bool) × (Fin 5 × Rand Bool) × Fin 6 =>
      Encoded.SelectedHadamardTester.query p.1 p.2.1 p.2.2)
    (encPair (encPi (encPi encBool))
      (encPair (encFinite (Fin 5 × Rand Bool)) (encFinEnum (Fin 6))))
    (encFinEnum (Pos Bool)) := by fun_prop

example : ComputableTidilyInPolyTime
    (fun p : (Bool → Bool → Bool) × (Fin 5 × Rand Bool) × (Fin 6 → Bool) =>
      Encoded.SelectedHadamardTester.accepts p.1 p.2.1 p.2.2)
    (encPair (encPi (encPi encBool))
      (encPair (encFinite (Fin 5 × Rand Bool)) (encPi encBool))) encBool := by polytime

example {V E : Type} [Fintype E] (G : ConstraintGraph V E Bool) :
    G.unsatVal / 840 ≤ G.composeSelected.unsatVal := G.le_unsatVal_composeSelected

example : Fintype.card (Bool × (Fin 6 → Bool)) = 128 :=
  ConstraintGraph.card_alphabet_composeSelected

end ComplexityTests.PCPSelectedAssignmentTester
