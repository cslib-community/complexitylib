/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BiTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Mathlib.Tactic.Linarith

/-!
# Ternary registers for binary work tapes

A normalized `StackTape Bool` is a base-three natural number, with the cell nearest the head
as its least significant digit. Blank is zero, false is one, and true is two. Normalization
of the stored tail is essential: appending a blank at the far end does not change the code.
The arithmetic push, pop and observation operations below agree with `StackTape` operations.

## Main definitions

* `Turing.MultiTapeNTM.ConfigurationGraph.symbolCode`: ternary code for a cell.
* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode`: ternary code for a normalized stack.

## Main results

* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode_cons`: push is multiplication by three.
* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode_head`: observation is remainder by three.
* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode_tail`: pop is division by three.
* `Turing.MultiTapeNTM.ConfigurationGraph.stackCode_lt`: the code fits exponentially in length.

## References

Uses Bolton Bailey's normalized `StackTape` and `BiTape` APIs.
-/

@[expose] public section

open Cslib.Turing

namespace Turing.MultiTapeNTM.ConfigurationGraph

/-- Blank, false and true are the ternary digits zero, one and two. -/
def symbolCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

theorem symbolCode_lt (b : Option Bool) : symbolCode b < 3 := by
  rcases b with _ | _ | _ <;> decide

theorem symbolCode_injective : Function.Injective symbolCode := by
  intro a b h
  rcases a with _ | _ | _ <;> rcases b with _ | _ | _ <;> simp_all [symbolCode]

/-- Little-endian base-three evaluation of a finite cell list. -/
def cellsCode : List (Option Bool) → ℕ
  | [] => 0
  | b :: bs => symbolCode b + 3 * cellsCode bs

/-- The ternary code of a normalized stack. -/
def stackCode (t : StackTape Bool) : ℕ := cellsCode t.toList

@[simp] theorem stackCode_nil : stackCode (StackTape.nil : StackTape Bool) = 0 := rfl

/-- The normalizing push still has the usual base-three arithmetic meaning. -/
theorem stackCode_cons (b : Option Bool) (t : StackTape Bool) :
    stackCode (StackTape.cons b t) = symbolCode b + 3 * stackCode t := by
  rcases t with ⟨l, h⟩
  cases b <;> cases l <;> rfl

/-- The digit under the stack head is its least significant ternary digit. -/
theorem stackCode_head (t : StackTape Bool) :
    symbolCode t.head = stackCode t % 3 := by
  have h := congrArg (fun n => n % 3) (stackCode_cons t.head t.tail)
  rw [StackTape.cons_head_tail] at h
  simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (symbolCode_lt _)] using h.symm

/-- Removing the head divides the stack register by three. -/
theorem stackCode_tail (t : StackTape Bool) : stackCode t.tail = stackCode t / 3 := by
  have h := congrArg (fun n => n / 3) (stackCode_cons t.head t.tail)
  rw [StackTape.cons_head_tail] at h
  simpa only [Nat.add_mul_div_left _ _ (by decide : 0 < 3),
    Nat.div_eq_of_lt (symbolCode_lt _), Nat.zero_add] using h.symm

/-- A stack with `l` stored cells has a ternary code smaller than `3^l`. -/
theorem cellsCode_lt (l : List (Option Bool)) : cellsCode l < 3 ^ l.length := by
  induction l with
  | nil => decide
  | cons b bs ih =>
    simp only [cellsCode, List.length_cons, pow_succ]
    have := symbolCode_lt b
    omega

theorem stackCode_lt (t : StackTape Bool) : stackCode t < 3 ^ t.length :=
  cellsCode_lt t.toList

/-- The registers of a bidirectional tape, in head/left/right order. -/
def tapeCode (t : BiTape Bool) : ℕ × ℕ × ℕ :=
  (symbolCode t.head, stackCode t.left, stackCode t.right)

/-- Execute an optional write and a signed move on the three tape registers. -/
def tapeStep (a : Option (Option Bool) × SignType) (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let h := a.1.elim t.1 symbolCode
  match a.2 with
  | .neg => (t.2.1 % 3, t.2.1 / 3, h + 3 * t.2.2)
  | .zero => (h, t.2.1, t.2.2)
  | .pos => (t.2.2 % 3, h + 3 * t.2.1, t.2.2 / 3)

/-- Arithmetic tape instructions agree with the native finite tape action. -/
theorem tapeCode_step (t : BiTape Bool) (a : Option (Option Bool) × SignType) :
    tapeCode (t.step a) = tapeStep a (tapeCode t) := by
  rcases a with ⟨w, d⟩
  cases w <;> cases d <;>
    simp [BiTape.step, BiTape.moveLeft, BiTape.moveRight, BiTape.write, tapeCode, tapeStep,
      stackCode_head, stackCode_tail, stackCode_cons]

end Turing.MultiTapeNTM.ConfigurationGraph
