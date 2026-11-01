/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Queue.Spec
public import Complexity.DataStructure.StateTransition.Refinement
public import Complexity.Foundations.Analysis.Asymptotics.CostBound

/-!
# Amortized refinements with a nonzero potential

A bag supports adding an element and clearing. It is implemented over the stack interface:
`add` pushes, and `clear` asks for the size and pops that many times. A clear can cost
arbitrarily many stack calls, but each element pays for its own pop when it is added, so with
the potential "one credit per stacked element" every bag operation costs at most two stack calls.
The tests check this per-operation certificate, telescope it along a concrete client, stack it
over the identity refinement, and export the linear bound as `CostIsBigO`.
-/

@[expose] public section

namespace ComplexityTests.StateTransitionRefinement

open Cslib Cslib.DataStructure Cslib.DataStructure.Queue

/-- Bag operations. -/
inductive BagOp where
  | add (n : ℕ)
  | clear
  deriving DecidableEq

/-- A bag with `clear`, recording its elements newest first. -/
abbrev bag : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := List ℕ) (Op := BagOp) (Result := fun _ => Unit)
    fun s o => match o with
      | .add n => (n :: s, ())
      | .clear => ([], ())

/-- Pop `n` times. -/
def popAll : ℕ → (stack ℕ).Client Unit
  | 0 => pure ()
  | n + 1 => .liftBind .pop fun _ => popAll n

/-- Bag operations as stack programs. -/
def methods : Methods bag (stack ℕ)
  | .add n => .liftBind (.push n) fun _ => .pure ()
  | .clear => .liftBind .size fun n => popAll n

/-- Popping as many times as the stack is long empties it, one call per element. -/
theorem runClient_popAll (s : List ℕ) :
    (stack ℕ).runClient s (popAll s.length) = ((), [], List.replicate s.length .pop) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    change (stack ℕ).runClient (a :: s) (.liftBind StackOp.pop fun _ => popAll s.length) = _
    rw [StateTransitionSpec.runClient_liftBind]
    change (let (v, s', os) := (stack ℕ).runClient s (popAll s.length)
      (v, s', StackOp.pop :: os)) = _
    rw [ih]
    rfl

/-- The stack holds the bag itself; there is no invariant. -/
def refinement : Refinement bag (stack ℕ) :=
  Refinement.ofFn methods (fun _ => True) id
    (fun _ _ _ => (stack ℕ).validHistory_of_forall_valid (fun _ _ => trivial) _ _)
    (by
      intro s o _ _
      cases o with
      | add n => exact ⟨rfl, trivial⟩
      | clear =>
        refine ⟨?_, trivial⟩
        simp [methods, StateTransitionSpec.clientState, runClient_popAll])

/-- Two calls per `add`, one per `clear`. -/
def bagCharge (_ : List ℕ) : BagOp → ℕ
  | .add _ => 2
  | .clear => 1

/-- One credit per stacked element pays for its eventual pop. -/
theorem amortized : refinement.Amortized (fun _ _ => 1) bagCharge List.length := by
  apply Refinement.Amortized.ofFn
  intro s o _ _
  cases o with
  | add n =>
    simp [refinement, methods, bagCharge, StateTransitionSpec.clientState,
      StateTransitionSpec.clientHistory]
    omega
  | clear =>
    simp [refinement, methods, bagCharge, StateTransitionSpec.clientState,
      StateTransitionSpec.clientHistory, runClient_popAll, StateTransitionSpec.totalCost_const]

/-- A client with one expensive clear. -/
def client : bag.Client Unit := do
  bag.call (.add 1)
  bag.call (.add 2)
  bag.call (.add 3)
  bag.call .clear
  bag.call (.add 4)

/-- The clear costs four stack calls, yet the five bag operations stay within their nine
amortized units, with one credit left for the remaining element. -/
example : (stack ℕ).totalCost (fun _ _ => 1) []
      ((stack ℕ).clientHistory [] (link refinement.methods client)) = 8 ∧
    bag.totalCost bagCharge [] (bag.clientHistory [] client) = 9 ∧
    ((stack ℕ).clientState [] (link refinement.methods client)).length = 1 := by
  decide

/-- The general telescoped bound from an empty stack. -/
theorem client_bound (p : bag.Client Unit) :
    (stack ℕ).totalCost (fun _ _ => 1) [] ((stack ℕ).clientHistory [] (link refinement.methods p)) +
        ((stack ℕ).clientState [] (link refinement.methods p)).length ≤
      bag.totalCost bagCharge [] (bag.clientHistory [] p) := by
  have h := amortized.client p (e := []) trivial
    (bag.validHistory_of_forall_valid (fun _ _ => trivial) _ _)
  exact h

/-- Stacking over the identity refinement adds a zero potential. -/
example : (refinement.comp (Refinement.id (stack ℕ))).Amortized (fun _ _ => 1) bagCharge
    (fun s => s.length + 0) :=
  amortized.comp (Refinement.Amortized.id _)

/-- The exported form: the stack calls of a bag client from an empty stack are `O(m)` in the
number `m` of bag operations, with the constant `2`. -/
example : CostIsBigO Filter.atTop (fun m : ℕ => (m : ℝ))
    (fun p : bag.Client Unit => (bag.clientHistory [] p).length)
    (fun p => (stack ℕ).totalCost (fun _ _ => 1) []
      ((stack ℕ).clientHistory [] (link refinement.methods p))) := by
  refine CostIsBigO.of_le_nat (F := fun m => 2 * m) (fun _ _ h => Nat.mul_le_mul_left 2 h)
    ?_ fun p => ?_
  · simpa using (Asymptotics.isBigO_refl (fun m : ℕ => (m : ℝ)) _).const_mul_left 2
  · have h := client_bound p
    have hc : bag.totalCost bagCharge [] (bag.clientHistory [] p) ≤
        (bag.clientHistory [] p).length * 2 :=
      bag.totalCost_le_length_mul bagCharge 2 (fun _ o _ => by cases o <;> simp [bagCharge])
        (bag.validHistory_of_forall_valid (fun _ _ => trivial) _ _)
    omega

end ComplexityTests.StateTransitionRefinement
