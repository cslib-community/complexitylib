/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition

/-!
# Bounding the total charge of a history

`Cslib.DataStructure.StateTransitionSpec.totalCost` sums state-dependent charges along a history.
When each operation's charge is bounded by a weight that does not depend on the state, the total
is bounded by the sum of the weights, which no longer needs the intermediate states. A client's
cost then follows from counting its operations by kind.

## Main results

* `Cslib.DataStructure.StateTransitionSpec.totalCost_le_sum_map`: the total charge is at most the
  sum of state-independent bounds on the charges of the operations.
-/

@[expose] public section

namespace Cslib.DataStructure.StateTransitionSpec

universe u v w

variable {D : StateTransitionSpec.{u, v, w}}
  {f : (s : D.State) → (o : D.Op) → D.State × D.Result o} [D.HasStepFn f]

/-- Charges bounded by state-independent weights on the operations of a history total at most
the sum of the weights. -/
theorem totalCost_le_sum_map (charge : D.State → D.Op → ℕ) (w : D.Op → ℕ) {s : D.State}
    {os : List D.Op} (h : ∀ s, ∀ o ∈ os, charge s o ≤ w o) :
    D.totalCost charge s os ≤ (os.map w).sum := by
  induction os generalizing s with
  | nil => simp
  | cons o os ih =>
    have hstep := h s o List.mem_cons_self
    have hrest := ih (s := (D.stepFn s o).1) fun s o ho => h s o (List.mem_cons_of_mem _ ho)
    simp only [totalCost_cons, List.map_cons, List.sum_cons]
    omega

end Cslib.DataStructure.StateTransitionSpec
