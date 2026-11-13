/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.SearchTree.Erase
public import CslibFrontier.DataStructure.OrderedSet.Spec
public import CslibFrontier.DataStructure.StateTransition.Resource
public import CslibFrontier.DataStructure.StateTransition.StepFunction

/-!
# A stateful ordered set realized by a binary search tree

Clients see finite-set semantics and operation-dependent result types. The representation relation
hides the tree's shape. Correctness transfers to every adaptive client through the common stateful
calculus; node-visit costs are supplied afterwards as a separate resource certificate. Deletion
uses the existing successor-splicing operation, including unsuccessful and repeated deletions.

## Main definitions

* `Cslib.DataStructure.OrderedSet.spec`: the shared representation-independent finite-set
  specification.
* `step`, `Exec`, `run`: concrete tree operations and client interpreter with their exact
  node-visit charge, built with `Cslib.DataStructure.Execution.ofStep`.
* `Rep`, `impl`: the search tree representation relation and its realization of the
  finite-set interface.

## Main results

* `exec_visits_le_height`: every native operation visits at most the initial tree height.
* `nodeVisitBound`: a representation-independent bound by the current set cardinality.
* `realized_client`: adaptive clients have correct executions with additive node-visit bounds.

The cardinality bound is deliberately worst-case: these trees have no balancing invariant. The
cost model excludes allocation, pure continuations and comparison implementation, and makes no
RAM or Turing-machine time claim.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 12][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.SearchTree

open Cslib.DataStructure Cslib.DataStructure.OrderedSet

variable {α : Type} [LinearOrder α]

/-- Concrete operation and exact charge in the internal-node-visit model. -/
def step (t : BinaryTree α) (o : Op α) : StepResult (BinaryTree α) Nat ((spec α).Result o) :=
  match o with
  | .contains x => ⟨t, contains x t, searchVisits x t⟩
  | .insert x => ⟨insert x t, (), searchVisits x t⟩
  | .delete x => ⟨erase x t, (), eraseVisits x t⟩
  | .minimum => ⟨t, minimum t, minimumVisits t⟩
  | .successor x => ⟨t, successor x t, successorVisits x t⟩

/-- A native execution records an actual tree operation and its exact node-visit charge. -/
abbrev Exec : Execution (spec α) (BinaryTree α) Nat := Execution.ofStep step

/-- Representation includes both set semantics and strict subtree ordering. -/
def Rep (s : Finset α) (t : BinaryTree α) : Prop := Ordered t ∧ elements t = s

/-- Empty trees represent empty sets without an initialization assumption. -/
theorem rep_empty : Rep (∅ : Finset α) .nil := ⟨trivial, rfl⟩

/-- Semantic correctness is independent of the later resource certificate. -/
def impl : StateTransitionImpl (spec α) Exec :=
  StateTransitionImpl.ofStep (D := spec α) Rep step fun {_ t} o hr _ => by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      refine ⟨?_, ht, rfl⟩
      have h := contains_eq_true ht x
      by_cases hx : x ∈ elements t <;> simp_all [step]
    | insert x => exact ⟨rfl, ordered_insert ht x, elements_insert x t⟩
    | delete x => exact ⟨rfl, ordered_erase ht x, elements_erase ht x⟩
    | minimum => exact ⟨(minimum_spec ht).eq_least, ht, rfl⟩
    | successor x => exact ⟨(successor_spec ht x).eq_least, ht, rfl⟩

/-- Costs depend on the actual initial tree height, even for an unsuccessful query. -/
theorem exec_visits_le_height {t t' : BinaryTree α} {o : Op α}
    {a : (spec α).Result o} {n : Nat} (he : Exec t o a t' n) : n ≤ t.height := by
  cases o with
  | contains x => cases he; exact searchVisits_le_height x t
  | insert x => cases he; exact searchVisits_le_height x t
  | delete x => cases he; exact eraseVisits_le_height x t
  | minimum => cases he; exact minimumVisits_le_height t
  | successor x => cases he; exact successorVisits_le_height x t

/-- Forgetting shape gives a safe linear bound, not a logarithmic claim. -/
theorem nodeVisitBound : Bound (impl (α := α)) id (fun s _ => s.card) := by
  intro s t o a t' n hr _ he
  have h := (exec_visits_le_height he).trans t.height_le_numNodes
  rw [← card_elements hr.1, hr.2] at h
  exact h

/-- Every adaptive client has the specified result and final set, together with a bound summing
current-set cardinalities along the selected history. Pure continuation evaluation is uncharged. -/
theorem realized_client {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : BinaryTree α} (hr : Rep s t) :
    let (value, finalState, history) := (spec α).runClient s p
    ∃ t' ns, Executes Exec p t value t' ns ∧ Rep finalState t' ∧
      total id ns ≤ (spec α).totalCost (fun s _ => s.card) s history :=
  nodeVisitBound.exists_executes p hr
    ((spec α).validHistory_of_forall_valid (fun _ _ => trivial) s _)

/-- Execute a client concretely, retaining one exact node-visit count per operation. -/
abbrev run {β : Type} (t : BinaryTree α) (p : (spec α).Client β) :
    RunResult (BinaryTree α) Nat β :=
  Execution.run step t p

/-- Running the concrete interpreter agrees with finite-set semantics and retains its cost bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : BinaryTree α} (hr : Rep s t) :
    let (value, finalState, history) := (spec α).runClient s p
    (run t p).value = value ∧ Rep finalState (run t p).state ∧
      total id (run t p).traces ≤ (spec α).totalCost (fun s _ => s.card) s history := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial) s
    ((spec α).clientHistory s p)
  have hexec := Execution.executes_run step p t
  have h := impl.correct_client hr hv hexec
  exact ⟨h.1, h.2, nodeVisitBound.client hr hv hexec⟩

end Cslib.DataStructure.SearchTree
