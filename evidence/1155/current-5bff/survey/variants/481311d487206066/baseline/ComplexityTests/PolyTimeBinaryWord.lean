/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Tactic.PolyTime

/-! Ordinary providers preserve unary division defaults and captured padded-row inputs. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encUnary encUnary) encUnary := by fun_prop

example (n : ℕ) : n / 0 = 0 ∧ n % 0 = n := by simp

example : ComputableInPolyTime (fun word : List Bool => word) (encList encBool) encBits := by
  fun_prop

example {α : Type} {input : α ↪ List Bool} {width row : α → ℕ} {word : α → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hrow : ComputableInPolyTime row input encUnary)
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.listRow (width a) (row a) (word a))
      input encBits := by
  fail_if_success (clear hword; fun_prop)
  fun_prop

example : Cslib.BitString.listRow 0 7 [true] = [] := by decide
example : Cslib.BitString.listRow 3 0 [true] = [true, false, false] := by decide

-- The complete framed source is reused by both a raw-word operation and its unary count.
example : ComputableInPolyTime
    (fun votes : List Bool => Cslib.BitString.listNonpositiveMargin votes
      (Cslib.BitString.listStrictMajority votes)) (encList encBool) encBool := by
  fun_prop

example {α : Type} {input : α ↪ List Bool} {votes : α → List Bool}
    (hvotes : ComputableInPolyTime votes input encBits) :
    ComputableInPolyTime (fun a => (votes a).count true) input encUnary := by
  fun_prop

-- A fixed Boolean operation needs no separate computational assumption.
example (op : Bool → Bool → Bool) :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1.zipWith op p.2)
      (encPair encBits encBits) encBits := by
  fun_prop

-- The computed cap is essential to binary-to-unary conversion.
example {α : Type} {input : α ↪ List Bool} {value bound : α → ℕ}
    (hvalue : ComputableInPolyTime value input encNat)
    (hbound : ComputableInPolyTime bound input encUnary) (hle : ∀ a, value a ≤ bound a) :
    ComputableInPolyTime value input encUnary :=
  ComputableInPolyTime.binary_to_unary_bounded hvalue hbound hle
