/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import Complexity.Tactic.PolyTime

/-! Bounded search with captured predicates, inclusive bounds and exact default-zero behavior. -/

namespace ComplexityTests.PolyTimeSearch

open Turing.MultiTapeTM

-- The bound and the joint predicate certificate are independently necessary.
example {α : Type} (input : α ↪ List Bool) (bound : α → ℕ)
    (predicate : α → ℕ → Prop) [∀ a, DecidablePred (predicate a)]
    (hbound : ComputableInPolyTime bound input encUnary)
    (hpredicate : ComputableInPolyTime (fun p : α × ℕ => decide (predicate p.1 p.2))
      (encPair input encUnary) encBool) :
    ComputableInPolyTime (fun a => Nat.findGreatest (predicate a) (bound a))
      input encUnary ∧
    ComputableInPolyTime (fun a => Nat.findGreatest (predicate a) (bound a))
      input encUnary := by
  constructor
  · fail_if_success (clear hbound; fun_prop)
    fail_if_success (clear hpredicate; fun_prop)
    fun_prop
  · fail_if_success (clear hbound; polytime)
    fail_if_success (clear hpredicate; polytime)
    polytime

-- Framed and raw bit lists and arithmetic predicates with a computed unary bound are certified
-- automatically.
example :
    ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        Nat.findGreatest (fun i => (p.1[i]?).getD false = true) (p.2 + p.1.length))
      (encPair encBits encUnary) encUnary ∧
    ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        Nat.findGreatest (fun i => (p.1[i]?).getD false = true) (p.2 + p.1.length))
      (encPair (encList encBool) encUnary) encUnary ∧
    ComputableInPolyTime
      (fun n : ℕ => Nat.findGreatest (fun i => i * i ≤ n) (n + 1))
      encUnary encUnary :=
  ⟨by fun_prop, by polytime, by polytime⟩

-- The default value is exact even when zero itself is not a solution, the bound is inclusive, and
-- descending search selects the greatest matching index.
example :
    Nat.findGreatest (fun _ => False) 0 = 0 ∧
    Nat.findGreatest (fun _ => True) 0 = 0 ∧
    Nat.findGreatest (fun _ => False) 8 = 0 ∧
    Nat.findGreatest (fun i => i = 0) 8 = 0 ∧
    Nat.findGreatest (fun i => i = 9) 8 = 0 ∧
    Nat.findGreatest (fun i => i = 8) 8 = 8 ∧
    Nat.findGreatest (fun i => i = 2 ∨ i = 5 ∨ i = 9) 8 = 5 ∧
    Nat.findGreatest (fun i => ([false, true, false, true][i]?).getD false = true) 6 = 3 ∧
    Nat.findGreatest (fun i => i * i ≤ 24) 25 = 4 := by decide

end ComplexityTests.PolyTimeSearch
