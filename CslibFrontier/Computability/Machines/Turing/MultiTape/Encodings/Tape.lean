/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
import Mathlib.Tactic.Linarith

/-!
# Encodings of finite tape storage

The existing stack and bidirectional tapes use the standard list, option and pair encodings.
The symbol encoding is a parameter: the operations do not require a finite or inhabited alphabet.
If symbol encodings have a uniform length bound, the complete tape encoding is linear in its
stored extent, including blank gaps.

## Main definitions

* `Turing.MultiTapeTM.encStackTape`: encode a stack's stored list of optional cells.
* `Turing.MultiTapeTM.encBiTape`: encode the head and both sides of a bidirectional tape.

## Main results

* `Turing.MultiTapeTM.length_encStackTape_le`, `Turing.MultiTapeTM.length_encBiTape_le`:
  explicit bounds from a fixed symbol-length bound.

## References

Adapts the encodings in Computability/Probabilistic/Tape.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using Christian Reitwiessner's standard encodings
and Bolton Bailey's tape representations.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Turing

variable {Symbol : Type}

/-- Encode the finite stored list, retaining interior blank cells. -/
def encStackTape (enc : Symbol ↪ List Bool) : StackTape Symbol ↪ List Bool where
  toFun tape := encList (encOption enc) tape.toList
  inj' := fun _ _ h => StackTape.ext ((encList _).injective h)

@[simp] theorem encStackTape_apply (enc : Symbol ↪ List Bool) (tape : StackTape Symbol) :
    encStackTape enc tape = encList (encOption enc) tape.toList := rfl

/-- Encode the current cell, left side and right side with their standard framing. -/
def encBiTape (enc : Symbol ↪ List Bool) : BiTape Symbol ↪ List Bool where
  toFun tape := encPair (encOption enc) (encPair (encStackTape enc) (encStackTape enc))
    (tape.head, tape.left, tape.right)
  inj' := fun _ _ h =>
    let heq := (encPair _ _).injective h
    BiTape.ext (congrArg Prod.fst heq) (congrArg (Prod.fst ∘ Prod.snd) heq)
      (congrArg (Prod.snd ∘ Prod.snd) heq)

@[simp] theorem encBiTape_apply (enc : Symbol ↪ List Bool) (tape : BiTape Symbol) :
    encBiTape enc tape = encPair (encOption enc) (encPair (encStackTape enc) (encStackTape enc))
      (tape.head, tape.left, tape.right) := rfl

/-- Bounded symbol encodings give a linear bound for the stored stack. -/
theorem length_encStackTape_le (enc : Symbol ↪ List Bool) (tape : StackTape Symbol)
    {bound : ℕ} (hbound : ∀ symbol, (enc symbol).length ≤ bound) :
    (encStackTape enc tape).length ≤ tape.length * (2 * bound + 3) := by
  have hoption (symbol : Option Symbol) : (encOption enc symbol).length ≤ bound + 1 := by
    cases symbol with
    | none => simp
    | some symbol =>
      simpa only [encOption_some, List.length_cons] using Nat.add_le_add_right (hbound symbol) 1
  exact length_encList_le (encOption enc) tape.toList (fun symbol _ => hoption symbol)

/-- The encoding charges all stored cells, including blanks between nonblank cells. -/
theorem length_encBiTape_le (enc : Symbol ↪ List Bool) (tape : BiTape Symbol)
    {bound : ℕ} (hbound : ∀ symbol, (enc symbol).length ≤ bound) :
    (encBiTape enc tape).length ≤ 4 * (bound + 2) * tape.spaceUsed := by
  have hhead : (encOption enc tape.head).length ≤ bound + 1 := by
    cases tape.head with
    | none => simp
    | some symbol =>
      simpa only [encOption_some, List.length_cons] using Nat.add_le_add_right (hbound symbol) 1
  have hleft := length_encStackTape_le enc tape.left hbound
  have hright := length_encStackTape_le enc tape.right hbound
  simp only [encBiTape_apply, length_encPair, BiTape.spaceUsed]
  nlinarith

end Turing.MultiTapeTM
