/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Products of indicators over a list

In a monoid with zero, the product over a list of the indicators `if p a then 1 else 0` is the
indicator that `p` holds at every element of the list (`List.prod_map_boole`). This is the list
form of `Finset.prod_boole`.

## Main results

* `List.prod_map_boole`: a product of indicators is the indicator of the conjunction.
-/

public section

namespace List

/-- **A product of indicators is the indicator of the conjunction.** -/
theorem prod_map_boole {M₀ α : Type*} [MonoidWithZero M₀] (l : List α) (p : α → Prop)
    [DecidablePred p] :
    (l.map fun a => if p a then (1 : M₀) else 0).prod = if ∀ a ∈ l, p a then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases ha : p a <;> simp [ha]

end List
