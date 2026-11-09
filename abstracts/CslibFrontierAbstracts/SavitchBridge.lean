/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.TQBFBridge
import CslibFrontier.Computability.Complexity.Classes.Space.Savitch

/-! # Transfer of Savitch's polynomial-space equality to plain machine definitions -/

namespace CslibFrontierTests.Abstracts.SavitchBridge

/-- A Boolean is encoded by a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- PSPACE is total deterministic decision with polynomially bounded work space.
There is no time-rate restriction. Read-only input and write-only output are not charged. -/
def PSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (f : α → Bool) (t : α → ℕ) (s : ℕ → ℕ),
    Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpace f enc encBool t (fun a => s (enc a).length) ∧
    ∀ a, a ∈ A ↔ f a = true}

/-- A nondeterministic machine accepts if an actual computation path ends halted with output 1. -/
def Accepts {k : ℕ} {State : Type} (M : Turing.MultiTapeNTM k Bool State)
    (input : List Bool) : Prop :=
  ∃ p : M.ComputationPath input, p.last.Halted ∧ p.last.output = [true]

/-- Every computation prefix respects the workspace bound, membership is accepting-path
existence, and on each input some finite time bounds all paths. A stuck branch rejects. -/
def DecidesInSpace {α : Type} {k : ℕ} {State : Type}
    (M : Turing.MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α) (s : α → ℕ) : Prop :=
  (∀ a, M.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ Accepts M (enc a))) ∧
    ∀ a, ∃ t, M.RunsInTime (enc a) t

/-- Nondeterministic polynomial space, with one fixed finite-state machine and all branches
halting; the space bound holds along every computation prefix, including rejecting branches. -/
def NPSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (s : α → ℕ), (∃ b : ℕ → ℕ, Cslib.PolynomiallyBounded b ∧ ∀ a, s a ≤ b (enc a).length) ∧
    DecidesInSpace M enc A s}

theorem savitch {α : Type} (enc : α ↪ List Bool) : NPSPACE enc = PSPACE enc := by
  have hp : PSPACE enc = Cslib.Complexity.PSPACE enc :=
    Set.ext fun _ => TQBFBridge.mem_PSPACE_iff
  have hn : NPSPACE enc = Cslib.Complexity.NPSPACE enc := rfl
  rw [hn, hp]
  exact Cslib.Complexity.NPSPACE_eq_PSPACE

end CslibFrontierTests.Abstracts.SavitchBridge
