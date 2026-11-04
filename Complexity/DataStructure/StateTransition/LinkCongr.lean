/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Module

/-!
# Linking methods with identical complete runs

Changing a method's source syntax preserves a linked adaptive client when every method keeps
its complete deterministic run: result, final state and lower-operation history. Equality of
answers alone would not preserve the reached memories or the subsequent client behavior.

## Main results

* `StateTransitionSpec.runClient_link_congr`: equality of complete method runs lifts to every
  adaptive client, retaining the entire lower-operation history and final state.

This is a semantic transport result. It assigns no native cost to calling or argument staging;
equal histories can be used with the existing `totalCost` function at any chosen charge.
-/

@[expose] public section

namespace Cslib.DataStructure.StateTransitionSpec

universe u v w

variable {D E : StateTransitionSpec.{u, v, w}}
  {f : (s : E.State) → (o : E.Op) → E.State × E.Result o} [E.HasStepFn f]
  {α : Type w}

/-- Methods with identical complete deterministic runs can replace one another under linking.
The equality retains the lower history, including operations of every reached continuation. -/
theorem runClient_link_congr (methods methods' : Methods D E)
    (hmethods : ∀ s o, E.runClient s (methods o) = E.runClient s (methods' o))
    (p : D.Client α) (s : E.State) :
    E.runClient s (link methods p) = E.runClient s (link methods' p) := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih =>
    change E.runClient s ((methods o).bind fun a => link methods (k a)) =
      E.runClient s ((methods' o).bind fun a => link methods' (k a))
    rw [E.runClient_bind, E.runClient_bind, hmethods s o]
    exact congrArg (fun r : α × E.State × List E.Op =>
      (r.1, r.2.1, (E.runClient s (methods' o)).2.2 ++ r.2.2))
      (ih (E.runClient s (methods' o)).1 (E.runClient s (methods' o)).2.1)

end Cslib.DataStructure.StateTransitionSpec
