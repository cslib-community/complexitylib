/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Find

/-!
# Materializing finite functions

`tabulate` eagerly evaluates a function at every element of a finite ordered type
and returns a lookup function over the resulting table. Its clients can share the
table rather than repeatedly evaluating a nested expression. Lookup is a linear
scan of the table; this API makes no constant-time random-access claim.

## Main definitions

* `tabulate`: eager evaluation followed by finite linear lookup.

## Main results

* `tabulate_eq`: materialization preserves the function.

-/

public section

namespace Cslib.Function

/-- Eager finite lookup table for a function, with linear lookup and no recomputation. -/
@[expose] def tabulate {α β : Type*} [Fintype α] [LinearOrder α] [Inhabited β]
    (f : α → β) : α → β :=
  let entries := (Finset.univ.sort (· ≤ ·)).map fun a => (a, f a)
  fun a => ((entries.find? fun entry => entry.1 == a).map Prod.snd).getD default

/-- Finite materialization preserves the function pointwise. -/
theorem tabulate_eq {α β : Type*} [Fintype α] [LinearOrder α] [Inhabited β]
    (f : α → β) : tabulate f = f := by
  funext a
  unfold tabulate
  cases hf : ((Finset.univ.sort (· ≤ ·)).map fun a => (a, f a)).find?
      (fun entry => entry.1 == a) with
  | none =>
    have hn := List.find?_eq_none.mp hf (a, f a) (by simp)
    simp at hn
  | some entry =>
    have hm := List.mem_of_find?_eq_some hf
    obtain ⟨b, _, he⟩ := List.mem_map.mp hm
    subst entry
    have hb : b = a := by simpa using List.find?_some hf
    subst b
    rfl

end Cslib.Function
