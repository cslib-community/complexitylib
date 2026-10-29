/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Queue

/-!
# Queue substitution and resource contract tests

The direct backend stores the top first. The reversed backend stores the top last and implements
push by appending and pop by `dropLast`/`getLast?`. Their native evidence has different types.
Both instantiate the same queue module without changing its implementation or invariant proof.

These are executable Lean state transformations with relational semantics, not Word-RAM programs.
Recorded events describe operations and sizes; they are not measurements of running time.
-/

@[expose] public section

namespace ComplexityTests.DataStructureQueue

open Cslib.Stateful Cslib.Algorithms.Lean.Queue

/-- Direct lists record the operation that was performed. -/
def directExec : Execution (stackPair Nat) (List Nat × List Nat) (stackPair Nat).Op :=
  fun c o a c' event => (c', a) = (stackPair Nat).step c o ∧ event = o

/-- Both stack components are updated by the product specification; the other is preserved. -/
def direct : Realization (stackPair Nat) directExec where
  rep := Eq
  total o hr _ := by
    subst hr
    exact ⟨((stackPair Nat).step _ o).2, ((stackPair Nat).step _ o).1, o, rfl, rfl⟩
  correct hr _ he := by
    subst hr
    exact ⟨congrArg Prod.snd he.1, (congrArg Prod.fst he.1).symm⟩

/-- A genuinely different concrete representation: each top is at the end of its list. -/
structure ReverseStacks where
  front : List Nat
  rear : List Nat
  deriving DecidableEq

/-- Decode the hidden stack contents. Method bodies do not call this function. -/
def decode (c : ReverseStacks) : (stackPair Nat).State := (c.front.reverse, c.rear.reverse)

/-- Actual bottom-first stack operations, independently written from the abstract transition. -/
def reverseStackStep (s : List Nat) : (o : StackOp Nat) → List Nat × (stack Nat).Result o
  | .push n => (s ++ [n], ())
  | .pop => (s.dropLast, s.getLast?)
  | .size => (s, s.length)

/-- Operate on precisely one of the two stored stacks. -/
def reverseStep (c : ReverseStacks) :
    (o : (stackPair Nat).Op) → ReverseStacks × (stackPair Nat).Result o
  | .inl o =>
    let r := reverseStackStep c.front o
    (⟨r.1, c.rear⟩, r.2)
  | .inr o =>
    let r := reverseStackStep c.rear o
    (⟨c.front, r.1⟩, r.2)

/-- Reversed storage records the operation and total element counts before and after it. -/
abbrev ReverseEvent := (stackPair Nat).Op × Nat × Nat

/-- Native evidence is attached to the actual reversed-storage step. -/
def reverseExec : Execution (stackPair Nat) ReverseStacks ReverseEvent :=
  fun c o a c' event => (c', a) = reverseStep c o ∧
    event = (o, c.front.length + c.rear.length, c'.front.length + c'.rear.length)

/-- The representation-specific proof needed when replacing the backend. -/
theorem reverseStep_correct (c : ReverseStacks) (o : (stackPair Nat).Op) :
    (reverseStep c o).2 = ((stackPair Nat).step (decode c) o).2 ∧
      decode (reverseStep c o).1 = ((stackPair Nat).step (decode c) o).1 := by
  rcases o with o | o <;> cases o <;>
    simp [reverseStep, reverseStackStep, decode, stackPair, stack]

/-- Reversed stacks realize precisely the same interface, with their own evidence type. -/
def reversed : Realization (stackPair Nat) reverseExec where
  rep s c := decode c = s
  total o _ _ :=
    ⟨(reverseStep _ o).2, (reverseStep _ o).1,
      (o, _, _), rfl, rfl⟩
  correct {s c o a c' trace} hr _ he := by
    subst hr
    have h := reverseStep_correct c o
    rw [← he.1] at h
    exact h

/-- Queue correctness transports to direct lists without any new queue proof. -/
def directQueue := implementation.realize direct

/-- The identical queue correctness proof transports to reversed lists. -/
def reversedQueue := implementation.realize reversed

/-- Each direct event is one backend call; this interpretation makes no instruction-cost claim. -/
theorem direct_calls : Bound direct (fun _ => 1) (fun _ _ => 1) := by
  intro s c o a c' event hr hv he
  exact Nat.le_refl 1

/-- The same call-count interpretation can be applied to a different native evidence type. -/
theorem reversed_calls : Bound reversed (fun _ => 1) (fun _ _ => 1) := by
  intro s c o a c' event hr hv he
  exact Nat.le_refl 1

/-- Later enqueue data depends on the observed dequeue answer. -/
def adaptiveClient : (queue Nat).Client (Option Nat) :=
  .liftBind (.enqueue 5) fun _ => .liftBind .dequeue fun
    | none => .pure none
    | some a => .liftBind (.enqueue (a + 1)) fun _ => .liftBind .dequeue fun b => .pure b

/-- The client starting from a nonempty queue returns its second element. -/
theorem adaptiveClient_eval :
    eval (queue Nat) adaptiveClient [7, 11] = (some 11, [5, 8]) := rfl

/-- One client theorem applies unchanged to every stack-pair realization, including different
concrete state and native trace types. Its conclusion contains the flattened backend execution. -/
theorem adaptiveClient_backend {C Trace : Type} {exec : Execution (stackPair Nat) C Trace}
    (R : Realization (stackPair Nat) exec) {c : C}
    (hr : (implementation.realize R).rep [7, 11] c) :
    ∃ c' traces, Executes exec (link methods adaptiveClient) c (some 11) c' traces ∧
      (implementation.realize R).rep [5, 8] c' := by
  obtain ⟨c', chunks, he, hr'⟩ := (implementation.realize R).exists_executes adaptiveClient hr
    ((queue Nat).validHistory_of_forall_valid (by intro s o; trivial) _ _)
  exact ⟨c', chunks.flatten, link_exec methods exec he, hr'⟩

/-- Initially all contents are in the rear stack, so this run exercises transfer. -/
theorem adaptiveClient_direct :
    ∃ c' traces, Executes directExec (link methods adaptiveClient) ([], [11, 7])
      (some 11) c' traces ∧ directQueue.rep [5, 8] c' :=
  adaptiveClient_backend direct ⟨([], [11, 7]), rfl, rfl⟩

/-- The same client and theorem execute from a different physical representation. -/
theorem adaptiveClient_reversed :
    ∃ c' traces, Executes reverseExec (link methods adaptiveClient) ⟨[], [7, 11]⟩
      (some 11) c' traces ∧ reversedQueue.rep [5, 8] c' :=
  adaptiveClient_backend reversed ⟨([], [11, 7]), rfl, rfl⟩

/-- The backend substitutions genuinely change storage order, every adaptive client starting from
empty direct or reversed stacks satisfies the universal amortized call bound, and a nonnumeric
payload exercises the polymorphic interface. -/
example {α : Type} (p : (queue Nat).Client α)
    {a₁ a₂ : α} {c₁'} {traces₁} {c₂'} {traces₂}
    (he₁ : Executes directExec (link methods p) ([], []) a₁ c₁' traces₁)
    (he₂ : Executes reverseExec (link methods p) ⟨[], []⟩ a₂ c₂' traces₂) :
    (reverseStep ⟨[3, 7], []⟩ (.inl (.push 9))).1 = ⟨[3, 7, 9], []⟩ ∧
    (reverseStep ⟨[3, 7], []⟩ (.inl .pop)).2 = some 7 ∧
    (∃ c' traces, Executes directExec (link methods p) ([], [])
        ((queue Nat).runClient [] p).1 c' traces ∧
      directQueue.rep ((queue Nat).runClient [] p).2.1 c' ∧
      traces.length ≤ ((queue Nat).runClient [] p).2.2.length * 3) ∧
    (∃ c' traces, Executes reverseExec (link methods p) ⟨[], []⟩
        ((queue Nat).runClient [] p).1 c' traces ∧
      reversedQueue.rep ((queue Nat).runClient [] p).2.1 c' ∧
      traces.length ≤ ((queue Nat).runClient [] p).2.2.length * 3) ∧
    (a₁ = ((queue Nat).runClient [] p).1 ∧
      traces₁.length ≤ ((queue Nat).runClient [] p).2.2.length * 3) ∧
    (a₂ = ((queue Nat).runClient [] p).1 ∧
      traces₂.length ≤ ((queue Nat).runClient [] p).2.2.length * 3) ∧
    ((queue String).runClient []
      (.liftBind (.enqueue "first") fun _ => .liftBind .dequeue fun answer => .pure answer)).1 =
        some "first" := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl⟩
  · obtain ⟨c', traces, s', he, hr, hb, ht⟩ :=
      realized_client direct (fun _ => 1) 1 direct_calls p
        (q := []) (s := ([], [])) (c := ([], [])) rfl rfl
    refine ⟨c', traces, he, ⟨s', hr, hb⟩, ?_⟩
    simp [total_eq_sum_map] at ht
    omega
  · obtain ⟨c', traces, s', he, hr, hb, ht⟩ :=
      realized_client reversed (fun _ => 1) 1 reversed_calls p
        (q := []) (s := ([], [])) (c := ⟨[], []⟩) rfl rfl
    refine ⟨c', traces, he, ⟨s', hr, hb⟩, ?_⟩
    simp [total_eq_sum_map] at ht
    omega
  · obtain ⟨ha, s', hr, hb, ht⟩ := realized_client_bound direct (fun _ => 1) 1 direct_calls p
      (q := []) (s := ([], [])) (c := ⟨[], []⟩) rfl rfl he₁
    refine ⟨ha, ?_⟩
    simp [total_eq_sum_map] at ht
    omega
  · obtain ⟨ha, s', hr, hb, ht⟩ := realized_client_bound reversed (fun _ => 1) 1 reversed_calls p
      (q := []) (s := ([], [])) (c := ⟨[], []⟩) rfl rfl he₂
    refine ⟨ha, ?_⟩
    simp [total_eq_sum_map] at ht
    omega

/--
info: 'ComplexityTests.DataStructureQueue.reverseStep_correct' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureQueue.reverseStep_correct
/--
info: 'ComplexityTests.DataStructureQueue.adaptiveClient_backend' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureQueue.adaptiveClient_backend
/--
info: 'ComplexityTests.DataStructureQueue.adaptiveClient_direct' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureQueue.adaptiveClient_direct
/--
info: 'ComplexityTests.DataStructureQueue.adaptiveClient_reversed' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ComplexityTests.DataStructureQueue.adaptiveClient_reversed
/--
info: 'Cslib.Stateful.Realization.exists_executes' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Realization.exists_executes
/--
info: 'Cslib.Stateful.Realization.correct_client' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Realization.correct_client
/--
info: 'Cslib.Stateful.Module.realize' does not depend on any axioms
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Module.realize
/--
info: 'Cslib.Stateful.Module.amortized_client' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.Module.amortized_client
/--
info: 'Cslib.Stateful.link_exec' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.link_exec
/--
info: 'Cslib.Stateful.link_exec_decompose' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Stateful.link_exec_decompose
/--
info: 'Cslib.Algorithms.Lean.Queue.implementation' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Queue.implementation
/--
info: 'Cslib.Algorithms.Lean.Queue.potential_step' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Queue.potential_step
/--
info: 'Cslib.Algorithms.Lean.Queue.realized_client' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Queue.realized_client
/--
info: 'Cslib.Algorithms.Lean.Queue.realized_client_bound' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Algorithms.Lean.Queue.realized_client_bound

end ComplexityTests.DataStructureQueue
