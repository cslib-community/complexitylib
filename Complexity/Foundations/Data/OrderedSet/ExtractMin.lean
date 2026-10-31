/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.OrderedSet.Spec

/-!
# Minimum extraction through the shared ordered-set interface

The client `extractMin` queries the minimum and, when one exists, deletes that observed key.
Its semantics and chosen operation history are independent of a representation. Execution and
resource guarantees come from the realization used by the caller; pure client computation has
no machine-time claim here.

## Main definitions

* `extractMin`: an adaptive minimum-and-deletion client.

## Main results

* `extractMin_run`: the complete result, final set and answer-dependent operation history.
* `extractMin_spec`, `extractMin_state_of_some`: the returned minimum and its removal.
* `extractMin_card`: extraction reduces cardinality by one, with natural subtraction at zero.
-/

public section

namespace Cslib.OrderedSet

open Cslib.Stateful

variable {α : Type} [LinearOrder α]

/-- Return and remove the least key, or return `none` without deletion when the set is empty. -/
@[expose] def extractMin : (spec α).Client (Option α) := do
  let result ← PFunctor.FreeM.lift (P := (spec α).signature) .minimum
  match result with
  | none => pure none
  | some x =>
    let _ ← PFunctor.FreeM.lift (P := (spec α).signature) (.erase x)
    pure (some x)

/-- The deletion argument and operation history depend on the observed minimum. -/
theorem extractMin_run (s : Finset α) :
    (spec α).runClient s extractMin =
      match least s with
      | none => (none, s, [.minimum])
      | some x => (some x, s.erase x, [.minimum, .erase x]) := by
  simp only [extractMin, Spec.runClient_lift_bind', spec]
  cases least s <;> rfl

/-- Extraction returns the minimum of the original set. -/
@[simp] theorem extractMin_result (s : Finset α) :
    ((spec α).runClient s extractMin).1 = least s := by
  rw [extractMin_run]
  cases least s <;> rfl

/-- The result has the complete optional-minimum contract, including empty-set detection. -/
theorem extractMin_spec (s : Finset α) :
    LeastResult s ((spec α).runClient s extractMin).1 := by
  rw [extractMin_result]
  exact least_spec s

/-- When extraction returns a key, its final state removes exactly that key. -/
theorem extractMin_state_of_some {s : Finset α} {x : α}
    (h : ((spec α).runClient s extractMin).1 = some x) :
    ((spec α).runClient s extractMin).2.1 = s.erase x := by
  rw [extractMin_result] at h
  rw [extractMin_run, h]

/-- Exactly one element is removed from a nonempty set; an empty set stays empty. -/
theorem extractMin_card (s : Finset α) :
    ((spec α).runClient s extractMin).2.1.card = s.card - 1 := by
  rw [extractMin_run]
  have hs := least_spec s
  cases he : least s with
  | none =>
    simp only [he, LeastResult] at hs
    simp [hs]
  | some x =>
    simp only [he, LeastResult] at hs
    exact Finset.card_erase_of_mem hs.1

end Cslib.OrderedSet
