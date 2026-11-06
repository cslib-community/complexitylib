/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition

/-!
# Weakest preconditions with cost

`D.wp charge p Q s` is the weakest precondition of the client `p` of a deterministic
specification `D`, under a postcondition `Q` that sees the answer, the final state and the total
charge of the run. It holds when every operation of the run from `s` is admissible and `Q` holds
of the outcome (`StateTransitionSpec.wp_iff`). It is computed operation by operation
(`wp_pure`, `wp_lift_bind`), so a program's effect and cost follow by `simp`, and it composes
(`wp_bind`, `wp_mono`).

A postcondition that bounds the charge expresses an amortized inequality directly: `Q a s' t`
may say `t + potential s' ≤ budget + potential s`. A `CostHoare` triple, whose budget is a
function of the initial state, does not.

With the charge `fun _ _ => 1` the cost is the number of operations (`wp_one_iff`). Over
`Memory.spec w` with `Memory.charge` it is the memory cost.

## Main definitions

* `StateTransitionSpec.wp`: the weakest precondition with cost.

## Main results

* `StateTransitionSpec.wp_pure`, `StateTransitionSpec.wp_lift_bind`,
  `StateTransitionSpec.wp_lift`: evaluation, operation by operation.
* `StateTransitionSpec.wp_bind`, `StateTransitionSpec.wp_mono`: sequencing and consequence.
* `StateTransitionSpec.wp_iff`, `StateTransitionSpec.wp_one_iff`: the weakest precondition holds
  exactly when the run is admissible and the postcondition holds of its answer, final state and
  total charge, or number of operations.
-/

@[expose] public section

namespace Cslib.DataStructure.StateTransitionSpec

universe u v w y

variable {D : StateTransitionSpec.{u, v, w}} {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
  [D.HasStepFn f]

/-- The weakest precondition of the client `p` under `Q`, with charges `charge`: every operation
of the run from `s` is admissible, and `Q` holds of the answer, the final state and the total
charge. -/
def wp (D : StateTransitionSpec.{u, v, w}) {f : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    [D.HasStepFn f] (charge : D.State → D.Op → ℕ) {α : Type y} :
    D.Client α → (α → D.State → ℕ → Prop) → D.State → Prop
  | .pure a, Q, s => Q a s 0
  | .liftBind o k, Q, s =>
    D.valid s o ∧ D.wp charge (k (D.stepFn s o).2) (fun a s' t => Q a s' (t + charge s o))
      (D.stepFn s o).1

variable {charge : D.State → D.Op → ℕ}

/-- A pure client is admissible and costs nothing. -/
@[simp] theorem wp_pure {α : Type y} (a : α) (Q : α → D.State → ℕ → Prop) (s : D.State) :
    D.wp charge (@Pure.pure (no_index D.Client) _ α a) Q s ↔ Q a s 0 := Iff.rfl

/-- An operation followed by a continuation: the operation is admissible, and the continuation
runs from the next state with the operation's charge added. -/
@[simp] theorem wp_lift_bind {α : Type w} (o : D.Op) (k : D.Result o → D.Client α)
    (Q : α → D.State → ℕ → Prop) (s : D.State) :
    D.wp charge (@Bind.bind (no_index D.Client) _ (no_index (D.Result o)) α
        (@PFunctor.FreeM.lift (no_index D.signature) o) k) Q s ↔
      D.valid s o ∧
        D.wp charge (k (D.stepFn s o).2) (fun a s' t => Q a s' (t + charge s o))
          (D.stepFn s o).1 := Iff.rfl

/-- A single operation. -/
@[simp] theorem wp_lift (o : D.Op) (Q : D.Result o → D.State → ℕ → Prop) (s : D.State) :
    @wp D f _ charge (no_index (D.Result o)) (@PFunctor.FreeM.lift (no_index D.signature) o) Q
        s ↔
      D.valid s o ∧ Q (D.stepFn s o).2 (D.stepFn s o).1 (charge s o) := by
  change D.valid s o ∧ Q _ _ (0 + charge s o) ↔ _
  rw [Nat.zero_add]

/-- **Consequence**: a weaker postcondition. -/
theorem wp_mono {α : Type y} {p : D.Client α} {Q Q' : α → D.State → ℕ → Prop}
    (h : ∀ a s t, Q a s t → Q' a s t) {s : D.State} (hp : D.wp charge p Q s) :
    D.wp charge p Q' s := by
  induction p generalizing Q Q' s with
  | pure a => exact h _ _ _ hp
  | liftBind o k ih => exact ⟨hp.1, ih _ (fun a s' t => h a s' (t + charge s o)) hp.2⟩

/-- **Sequencing**: the charge of `p >>= k` is the charge of `p` plus the charge of `k`. -/
theorem wp_bind {α β : Type y} (p : D.Client α) (k : α → D.Client β)
    (Q : β → D.State → ℕ → Prop) (s : D.State) :
    D.wp charge (p >>= k) Q s ↔
      D.wp charge p (fun a s' t => D.wp charge (k a) (fun b s'' t' => Q b s'' (t + t')) s') s := by
  induction p generalizing Q s with
  | pure a =>
    change D.wp charge (k a) Q s ↔ D.wp charge (k a) (fun b s'' t' => Q b s'' (0 + t')) s
    simp only [Nat.zero_add]
  | liftBind o g ih =>
    change D.valid s o ∧ D.wp charge (g (D.stepFn s o).2 >>= k) _ _ ↔
      D.valid s o ∧ D.wp charge _ _ _
    rw [ih]
    refine and_congr_right fun _ => Iff.of_eq ?_
    congr
    funext a s' t
    congr
    funext b s'' t'
    rw [Nat.add_right_comm]

/-- **The weakest precondition holds exactly when** the run is admissible and `Q` holds of its
answer, final state and total charge. -/
theorem wp_iff {α : Type y} (p : D.Client α) (Q : α → D.State → ℕ → Prop) (s : D.State) :
    D.wp charge p Q s ↔
      D.ValidHistory s (D.clientHistory s p) ∧
        Q (D.clientResult s p) (D.clientState s p)
          (D.totalCost charge s (D.clientHistory s p)) := by
  induction p generalizing Q s with
  | pure a => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | liftBind o k ih =>
    simp only [wp, ih, clientHistory, clientResult, clientState, runClient_liftBind,
      validHistory_cons, totalCost_cons, and_assoc, Nat.add_comm]

/-- With a unit charge, the weakest precondition counts operations. -/
theorem wp_one_iff {α : Type y} (p : D.Client α) (Q : α → D.State → ℕ → Prop) (s : D.State) :
    D.wp (fun _ _ => 1) p Q s ↔
      D.ValidHistory s (D.clientHistory s p) ∧
        Q (D.clientResult s p) (D.clientState s p) (D.clientHistory s p).length := by
  rw [wp_iff, totalCost_one]

end Cslib.DataStructure.StateTransitionSpec
