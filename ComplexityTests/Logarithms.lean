/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime
import Complexity.Foundations.Combinatorics.Expander.TowerFamily

/-!
# Logarithmic construction schedules

The actual tower depth and selected size automate for an unbounded vertex count. The certificates
charge unary counters and outputs; a binary input cannot silently provide the same output budget.
An arbitrary fixed growth factor also supports the size schedules of amplification rounds.
-/

namespace ComplexityTests.Logarithms

open Turing.MultiTapeTM

example (base : ℕ) : ComputableInPolyTime
    (fun n : ℕ => (Nat.clog base n - 1, base ^ Nat.clog base n))
    encUnary (encPair encUnary encUnary) := by fun_prop

example (base : ℕ) : ComputableInPolyTime
    (fun n : ℕ => let rounds := Nat.clog base n; (rounds - 1, base ^ rounds))
    encUnary (encPair encUnary encUnary) := .of_tidy (by polytime)

-- Explicit let reduction also lets `fun_prop` retain the relation between size and exponent.
example (base : ℕ) : ComputableInPolyTime
    (fun n : ℕ => let rounds := Nat.clog base n; (rounds - 1, base ^ rounds))
    encUnary (encPair encUnary encUnary) := by dsimp only; fun_prop

-- A caller may use any encoding with a certified unary size function.
example {α : Type} {input : α ↪ List Bool} {size : α → ℕ}
    (hsize : ComputableInPolyTime size input encUnary) (base factor : ℕ) :
    ComputableInPolyTime (fun x => (Nat.clog base (size x), factor ^ Nat.clog base (size x)))
      input (encPair encUnary encUnary) :=
  have := hsize.tidy
  .of_tidy (by fun_prop)

-- Raw and framed words provide different input encodings of the same size-based program.
example : ComputableInPolyTime
    (fun w : List Bool => 3 ^ Nat.clog 2 w.length) encBits encUnary :=
  .of_tidy (by fun_prop)

example : ComputableInPolyTime
    (fun w : List Bool => 3 ^ Nat.clog 2 w.length) (encList encBool) encUnary :=
  .of_tidy (by fun_prop)

-- The arithmetic family's depth selection is uniform in the requested vertex count.
example : ComputableInPolyTime (fun n : ℕ => Nat.clog (257 ^ 8) n - 1)
    encUnary encUnary := by fun_prop

example (base n : ℕ) (hb : 1 < base) (hn : 2 ≤ n) :
    base ^ (Nat.clog base n - 1 + 1) = base ^ Nat.clog base n := by
  rw [Nat.sub_add_cancel (Nat.clog_pos hb hn)]

example :
    10 ≤ 3 ^ (Nat.clog 3 10 - 1 + 1) ∧
      3 ^ (Nat.clog 3 10 - 1 + 1) ≤ 3 * 10 :=
  Cslib.RotationMap.zigzagTower_size_bounds (by decide) (by decide)

-- Boundaries at powers, degenerate bases, and the initial accumulator for a zero factor.
example : (List.range 11).map (Nat.log 3) = [0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2] := by decide
example : (List.range 11).map (Nat.clog 3) = [0, 0, 1, 1, 2, 2, 2, 2, 2, 2, 3] := by decide
example : (List.range 5).map (fun n => 0 ^ Nat.clog 2 n) = [1, 1, 0, 0, 0] := by decide

example : ComputableInPolyTime (Nat.log 0) encUnary encUnary := by fun_prop
example : ComputableInPolyTime (Nat.clog 1) encUnary encUnary := by fun_prop
example : ComputableInPolyTime (fun n : ℕ => 0 ^ Nat.clog 2 n)
    encUnary encUnary := .of_tidy (by fun_prop)

example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => 2 ^ Nat.clog 2 n)
        encNat encUnary := by fun_prop
  trivial

end ComplexityTests.Logarithms
