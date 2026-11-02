/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.StateTransition.Resource

/-!
# A modular queue implemented with two stacks

The behavior proof mentions no concrete stack representation or resource model. The front stack
stores the next elements to dequeue; the reversed rear stack stores newly enqueued elements.
When the front is empty, the implementation queries the rear size and transfers those elements.
This standard construction follows [Cormen et al., Exercise 10.1-6][CLRS2009]; the potential
method is described in Chapter 17.

## Main definitions

* `StackOp`, `stack`, `stackPair`, `QueueOp`, and `queue`: total specifications with
  operation-dependent result types.
* `transfer`, `transferTrace`, `methods`, and `implementation`: semantic queue implementation
  over the stack-pair interface.

## Main results

* `transfer_run`: stack operations reverse the rear contents into the front stack.
* `runClient_dequeue_nil`, `stepFn_methods`: the methods realize the FIFO step on the represented
  list.
* `potential_step`: at most three amortized stack calls, including the size query.
* `realized_client`: every adaptive client has a correct backend execution with its bound.
* `realized_client_bound`: every supplied linked execution satisfies correctness and the bound.

For a primitive weight bound `K`, a client performing `m` queue operations satisfies
`weight + 2 K rearFinal.length ≤ 3 K m + 2 K rearInitial.length`. This is a conditional bound on
backend traces, not a machine instruction-count theorem. Pure client computation is uncharged;
backend implementations must justify their primitive weights and state independence separately.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Queue

open Cslib.DataStructure

variable {α : Type}

-- Abstract stack states remain hidden from method bodies.

/-- Stack operations with typed answers. -/
inductive StackOp (α : Type) where
  | push (value : α)
  | pop
  | size
  deriving DecidableEq

/-- A total stack specification; popping an empty stack returns `none`. -/
abbrev stack (α : Type) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := List α) (Op := StackOp α) (Result := fun
    | .push _ => Unit
    | .pop => Option α
    | .size => Nat)
    fun s o => match o with
      | .push n => (n :: s, ())
      | .pop => (s.tail, s.head?)
      | .size => (s, s.length)

/-- Two independently addressable stacks. -/
abbrev stackPair (α : Type) : StateTransitionSpec := product (stack α) (stack α)

/-- FIFO queue operations with typed answers. -/
inductive QueueOp (α : Type) where
  | enqueue (value : α)
  | dequeue
  deriving DecidableEq

/-- A total FIFO queue specification. -/
abbrev queue (α : Type) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := List α) (Op := QueueOp α) (Result := fun
    | .enqueue _ => Unit
    | .dequeue => Option α)
    fun s o => match o with
      | .enqueue n => (s ++ [n], ())
      | .dequeue => (s.tail, s.head?)

/-- Move at most `n` items from the rear stack to the front stack.
The fuel is obtained through an explicit `size` call, rather than inspecting hidden state. -/
def transfer : Nat → (stackPair α).Client Unit
  | 0 => .pure ()
  | n + 1 => .liftBind (.inr .pop) fun
      | none => .pure ()
      | some a => .liftBind (.inl (.push a)) fun _ => transfer n

/-- The same queue methods work for every realization of the stack interface. -/
def methods : Methods (queue α) (stackPair α)
  | .enqueue n => .liftBind (.inr (.push n)) fun _ => .pure ()
  | .dequeue => .liftBind (.inl .pop) fun
      | some a => .pure (some a)
      | none => .liftBind (.inr .size) fun n => do
          let _ ← transfer n
          .liftBind (.inl .pop) fun a => .pure a

/-- Primitive-operation trace of transferring the rear contents to the front. -/
def transferTrace : List α → List (stackPair α).Op
  | [] => []
  | a :: rest => .inr .pop :: .inl (.push a) :: transferTrace rest

/-- The queue's sole traversal argument: abstract stack calls reverse the rear contents. -/
theorem transfer_run (front back : List α) :
    (stackPair α).runClient (front, back) (transfer back.length) =
      ((), (back.reverse ++ front, []), transferTrace back) := by
  induction back generalizing front with
  | nil => rfl
  | cons a back ih =>
    change (let (v, s, os) := (stackPair α).runClient (a :: front, back) (transfer back.length)
      (v, s, (Sum.inr StackOp.pop : (stackPair α).Op) :: Sum.inl (StackOp.push a) :: os)) = _
    rw [ih]
    simp [transferTrace, List.reverse_cons, List.append_assoc]

/-- A dequeue from an empty front stack asks for the rear size, transfers the rear, and pops the
front again. -/
theorem runClient_dequeue_nil (back : List α) :
    (stackPair α).runClient ([], back) (methods .dequeue) =
      (back.reverse.head?, (back.reverse.tail, []),
        .inl .pop :: .inr .size :: (transferTrace back ++ [.inl .pop])) := by
  simp only [methods, bind, StateTransitionSpec.runClient_liftBind, stackPair, stack,
    List.tail_nil, List.head?_nil]
  rw [StateTransitionSpec.runClient_bind, transfer_run, List.append_nil]
  rfl

/-- Each method returns the FIFO answer, and the stacks then represent the FIFO successor of the
represented list. -/
theorem stepFn_methods (front back : List α) (o : QueueOp α) :
    (queue α).stepFn (front ++ back.reverse) o =
      (((stackPair α).clientState (front, back) (methods o)).1 ++
          ((stackPair α).clientState (front, back) (methods o)).2.reverse,
        (stackPair α).clientResult (front, back) (methods o)) := by
  cases o with
  | enqueue n =>
    change ((front ++ back.reverse) ++ [n], ()) = (front ++ (n :: back).reverse, ())
    simp [List.reverse_cons, List.append_assoc]
  | dequeue =>
    cases front with
    | cons a front => rfl
    | nil =>
      simp only [StateTransitionSpec.clientState, StateTransitionSpec.clientResult]
      rw [runClient_dequeue_nil]
      simp

/-- Representation and behavior are proved once, before selecting a backend or cost model. -/
def implementation : Module (queue α) (stackPair α) :=
  Module.ofFn
    (methods := methods)
    (rep := fun q s => q = s.1 ++ s.2.reverse)
    (valid := fun _ _ _ =>
      (stackPair α).validHistory_of_forall_valid (by intro s o; cases o <;> trivial) _ _)
    (correct := by
      intro q s o hr _
      subst q
      obtain ⟨front, back⟩ := s
      have h := stepFn_methods front back o
      exact ⟨(congrArg Prod.snd h).symm, congrArg Prod.fst h⟩)

/-- Each transferred element incurs one pop and one push. -/
theorem transferTrace_length (back : List α) : (transferTrace back).length = 2 * back.length := by
  induction back with
  | nil => rfl
  | cons a back ih => simp only [transferTrace, List.length_cons, ih]; omega

/-- The queue has a three-call amortized bound; rear-stack credit remains private to the module.
This counts stack calls, not execution of pure continuations or machine instructions. -/
theorem potential_step (s : (stackPair α).State) (o : QueueOp α) :
    ((stackPair α).runClient s (methods o)).2.2.length +
        2 * ((stackPair α).runClient s (methods o)).2.1.2.length ≤ 3 + 2 * s.2.length := by
  obtain ⟨front, back⟩ := s
  cases o with
  | enqueue n =>
    change 1 + 2 * (n :: back).length ≤ 3 + 2 * back.length
    simp only [List.length_cons]
    omega
  | dequeue =>
    cases front with
    | cons a front =>
      change 1 + 2 * back.length ≤ 3 + 2 * back.length
      omega
    | nil =>
      rw [runClient_dequeue_nil]
      simp only [List.length_cons, List.length_append, List.length_nil]
      rw [transferTrace_length]
      omega

private theorem weighted_potential_step (K : Nat) {q : (queue α).State} {s : (stackPair α).State}
    (o : QueueOp α) (_ : implementation.rep q s) (_ : (queue α).valid q o) :
    (stackPair α).totalCost (fun _ _ => K) s ((stackPair α).runClient s (methods o)).2.2 +
        K * (2 * ((stackPair α).runClient s (methods o)).2.1.2.length) ≤
      3 * K + K * (2 * s.2.length) := by
  rw [StateTransitionSpec.totalCost_const]
  simpa only [Nat.mul_add, Nat.add_mul, Nat.mul_comm K] using
    Nat.mul_le_mul_left K (potential_step s o)

/-- Uniform primitive bounds can be chosen after proving queue correctness. The same theorem
applies to any additive measure on any backend's native traces. It also retains leftover credit. -/
theorem realized_client {C Trace β : Type} {exec : Execution (stackPair α) C Trace}
    (R : StateTransitionImpl (stackPair α) exec) (weight : Trace → Nat) (K : Nat)
    (B : Bound R weight (fun _ _ => K)) (p : (queue α).Client β)
    {q : List α} {s : (stackPair α).State} {c : C}
    (hrep : implementation.rep q s) (hbackend : R.rep s c) :
    ∃ c' traces s',
      Executes exec (link methods p) c ((queue α).runClient q p).1 c' traces ∧
      implementation.rep ((queue α).runClient q p).2.1 s' ∧ R.rep s' c' ∧
      total weight traces + K * (2 * s'.2.length) ≤
        ((queue α).runClient q p).2.2.length * (3 * K) + K * (2 * s.2.length) := by
  have hv := (queue α).validHistory_of_forall_valid (fun _ _ => trivial)
    q ((queue α).runClient q p).2.2
  obtain ⟨c', chunks, he, _⟩ := (implementation.realize R).exists_executes p ⟨s, hrep, hbackend⟩ hv
  obtain ⟨s', hrep', hr', ht⟩ := implementation.amortized_client R B
    (fun _ s => K * (2 * s.2.length)) (fun _ _ => 3 * K)
    (weighted_potential_step K) hrep hbackend hv he
  refine ⟨c', chunks.flatten, s', link_exec methods exec he, hrep', hr', ?_⟩
  simpa only [total_flatten, StateTransitionSpec.totalCost_const] using ht

/-- Correctness and the same resource bound hold for every supplied flattened execution. -/
theorem realized_client_bound {C Trace β : Type} {exec : Execution (stackPair α) C Trace}
    (R : StateTransitionImpl (stackPair α) exec) (weight : Trace → Nat) (K : Nat)
    (B : Bound R weight (fun _ _ => K)) (p : (queue α).Client β)
    {q : List α} {s : (stackPair α).State} {c c' : C} {a : β} {traces : List Trace}
    (hrep : implementation.rep q s) (hbackend : R.rep s c)
    (he : Executes exec (link methods p) c a c' traces) :
    a = ((queue α).runClient q p).1 ∧ ∃ s',
      implementation.rep ((queue α).runClient q p).2.1 s' ∧ R.rep s' c' ∧
      total weight traces + K * (2 * s'.2.length) ≤
        ((queue α).runClient q p).2.2.length * (3 * K) + K * (2 * s.2.length) := by
  obtain ⟨chunks, hc, ht⟩ := link_exec_decompose methods exec he
  have hv := (queue α).validHistory_of_forall_valid (fun _ _ => trivial)
    q ((queue α).runClient q p).2.2
  have ha := ((implementation.realize R).correct_client ⟨s, hrep, hbackend⟩ hv hc).1
  obtain ⟨s', hrep', hr', hb⟩ := implementation.amortized_client R B
    (fun _ s => K * (2 * s.2.length)) (fun _ _ => 3 * K)
    (weighted_potential_step K) hrep hbackend hv hc
  refine ⟨ha, s', hrep', hr', ?_⟩
  simpa only [ht, total_flatten, StateTransitionSpec.totalCost_const] using hb

end Cslib.DataStructure.Queue
