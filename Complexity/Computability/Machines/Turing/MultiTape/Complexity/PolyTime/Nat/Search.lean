/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Find
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time bounded search

`Nat.findGreatest` searches the inclusive interval from zero to a computed unary bound. It
returns the greatest matching index, or zero when no index matches. The predicate may capture
the original input; its certificate is joint in that input and the candidate unary index.

The implementation enumerates the interval, reverses it, and searches the resulting list. Its
certificate charges the full candidate list, reversal, copying, every predicate call, and output.
The ordinary Mathlib specification of `Nat.findGreatest` remains available to clients.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.findGreatest`: exact total bounded search with
  uniform polynomial time in the caller's input encoding.

## References

Adapted from Cslib/Computability/Probabilistic/Search.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the plain deterministic calculus.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem findGreatest_eq_findD (predicate : ℕ → Prop) [DecidablePred predicate]
    (bound : ℕ) : Nat.findGreatest predicate bound =
      (((List.range (bound + 1)).reverse).find? (fun i => decide (predicate i))).getD 0 := by
  induction bound with
  | zero => by_cases h : predicate 0 <;> simp [h]
  | succ bound ih =>
    rw [Nat.findGreatest_succ, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.find?_cons]
    split_ifs <;> simp_all

/-- Search every index up to the supplied unary bound, returning the greatest match or zero.
Both the bound and the predicate are certified uniformly in the original input. -/
@[fun_prop]
theorem findGreatest {α : Type} {input : α ↪ List Bool} {bound : α → ℕ}
    {predicate : α → ℕ → Prop} [∀ a, DecidablePred (predicate a)]
    (hbound : ComputableInPolyTime bound input encUnary)
    (hpredicate : ComputableInPolyTime (fun p : α × ℕ => decide (predicate p.1 p.2))
      (encPair input encUnary) encBool) :
    ComputableInPolyTime (fun a => Nat.findGreatest (predicate a) (bound a))
      input encUnary := by
  simp only [findGreatest_eq_findD]
  have hlist := listReverseWithInput (range.comp (unary_add.comp (hbound.prod (const 1))))
  exact (findWithInput hlist hpredicate).optionGetDWithInput (const 0)

end Turing.MultiTapeTM.ComputableInPolyTime
