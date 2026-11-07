/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.SavitchBridge

/-! # Savitch's theorem for polynomial space

A nondeterministic computation can choose among exponentially many paths while using little
memory. Savitch's theorem says that a deterministic machine can decide whether an accepting path
exists without leaving polynomial space. The key is to test reachability between configurations
by trying possible midpoints and checking the two halves in turn, reusing storage between recursive
calls. The deterministic computation may take far longer, but its memory remains polynomial.

The statement concerns binary multi-tape machines on encoded inputs. Every nondeterministic
branch terminates (a stuck branch rejects), and every computation prefix obeys its space bound.
Read-only input and write-only output are not charged. We state equality of the polynomial-space
classes, rather than the fully
parameterized quadratic-space simulation bound.

Lean checks the transfer through the bridge, and `#check_abstract` audits the public dependencies.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Corollary 8.6][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

namespace ComplexityTests.Abstracts.SavitchAbstract

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
terminating; the space bound holds along every computation prefix, including rejecting branches. -/
def NPSPACE {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (s : α → ℕ), (∃ b : ℕ → ℕ, Cslib.PolynomiallyBounded b ∧ ∀ a, s a ≤ b (enc a).length) ∧
    DecidesInSpace M enc A s}

/-- Savitch's equality of polynomial-space classes. Every nondeterministic computation
prefix obeys its space bound, and every branch terminates (a stuck branch rejects). This does not
assert the fully parameterized `NSPACE(s) ⊆ DSPACE(s²)` theorem. -/
theorem savitch {α : Type} (enc : α ↪ List Bool) : NPSPACE enc = PSPACE enc :=
  SavitchBridge.savitch enc

/--
info: abstract audit passed for `ComplexityTests.Abstracts.SavitchAbstract`:
7 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.SavitchAbstract

end ComplexityTests.Abstracts.SavitchAbstract
