/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.SearchTree.Cost
public import Complexity.Foundations.Data.OrderedSet.Spec
public import Complexity.Foundations.Semantics.Stateful.Resource

/-!
# A stateful ordered set realized by a binary search tree

Clients see finite-set semantics and operation-dependent result types. The representation relation
hides the tree's shape. Correctness transfers to every adaptive client through the common stateful
calculus; node-visit costs are supplied afterwards as a separate resource certificate.

## Main definitions

* `Cslib.OrderedSet.spec`: the shared representation-independent finite-set specification.
* `step`, `Exec`, `run`: concrete tree operations and client interpreter with their exact
  node-visit charge.
* `Rep`, `realization`: the search tree representation relation and its realization of the
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

namespace Cslib.Algorithms.Lean.SearchTree

open Cslib.Stateful Cslib.OrderedSet

variable {α : Type} [LinearOrder α]

/-- Concrete operation and exact charge in the internal-node-visit model. -/
def step (t : BinaryTree α) (o : Op α) : BinaryTree α × (spec α).Result o × Nat :=
  match o with
  | .contains x => (t, contains x t, searchVisits x t)
  | .insert x => (insert x t, (), searchVisits x t)
  | .minimum => (t, minimum t, minimumVisits t)
  | .successor x => (t, successor x t, successorVisits x t)

/-- A native execution records an actual tree operation and its exact node-visit charge. -/
def Exec : Execution (spec α) (BinaryTree α) Nat :=
  fun t o a t' n => step t o = (t', a, n)

/-- Representation includes both set semantics and strict subtree ordering. -/
def Rep (s : Finset α) (t : BinaryTree α) : Prop := Ordered t ∧ elements t = s

/-- Empty trees represent empty sets without an initialization assumption. -/
theorem rep_empty : Rep (∅ : Finset α) .nil := ⟨trivial, rfl⟩

/-- Semantic correctness is independent of the later resource certificate. -/
def realization : Realization (spec α) Exec where
  rep := Rep
  total o _ _ := ⟨(step _ o).2.1, (step _ o).1, (step _ o).2.2, rfl⟩
  correct {s t o a t' n} hr _ he := by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      cases he
      refine ⟨?_, ht, rfl⟩
      have h := contains_eq_true ht x
      by_cases hx : x ∈ elements t <;> simp_all
    | insert x =>
      cases he
      exact ⟨rfl, ordered_insert ht x, elements_insert x t⟩
    | minimum =>
      cases he
      exact ⟨(minimum_spec ht).eq_least, ht, rfl⟩
    | successor x =>
      cases he
      exact ⟨(successor_spec ht x).eq_least, ht, rfl⟩

/-- Costs depend on the actual initial tree height, even for an unsuccessful query. -/
theorem exec_visits_le_height {t t' : BinaryTree α} {o : Op α}
    {a : (spec α).Result o} {n : Nat} (he : Exec t o a t' n) : n ≤ t.height := by
  cases o with
  | contains x => cases he; exact searchVisits_le_height x t
  | insert x => cases he; exact searchVisits_le_height x t
  | minimum => cases he; exact minimumVisits_le_height t
  | successor x => cases he; exact successorVisits_le_height x t

/-- Forgetting shape gives a safe linear bound, not a logarithmic claim. -/
theorem nodeVisitBound : Bound (realization (α := α)) id (fun s _ => s.card) := by
  intro s t o a t' n hr _ he
  have h := (exec_visits_le_height he).trans t.height_le_numNodes
  rw [← card_elements hr.1, hr.2] at h
  exact h

/-- Every adaptive client has the specified result and final set, together with a bound summing
current-set cardinalities along the selected history. Pure continuation evaluation is uncharged. -/
theorem realized_client {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : BinaryTree α} (hr : Rep s t) :
    ∃ t' ns, Executes Exec p t ((spec α).runClient s p).1 t' ns ∧
      Rep ((spec α).runClient s p).2.1 t' ∧
      total id ns ≤ (spec α).totalCost (fun s _ => s.card) s
        ((spec α).runClient s p).2.2 := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  exact nodeVisitBound.exists_executes p hr hv

/-- Execute a client concretely, retaining one exact node-visit count per operation. -/
def run {β : Type} (t : BinaryTree α) : (spec α).Client β →
    β × BinaryTree α × List Nat
  | .pure a => (a, t, [])
  | .liftBind o k =>
      let next := step t o
      let rest := run next.1 (k next.2.1)
      (rest.1, rest.2.1, next.2.2 :: rest.2.2)

/-- The executable interpreter supplies native execution evidence rather than assuming it. -/
theorem run_exec {β : Type} (p : (spec α).Client β) (t : BinaryTree α) :
    Executes Exec p t (run t p).1 (run t p).2.1 (run t p).2.2 := by
  induction p generalizing t with
  | pure a => exact .pure a t
  | liftBind o k ih => exact .call rfl (ih _ _)

/-- Running the concrete interpreter agrees with finite-set semantics and retains its cost bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : BinaryTree α} (hr : Rep s t) :
    (run t p).1 = ((spec α).runClient s p).1 ∧
      Rep ((spec α).runClient s p).2.1 (run t p).2.1 ∧
      total id (run t p).2.2 ≤ (spec α).totalCost (fun s _ => s.card) s
        ((spec α).runClient s p).2.2 := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  have h := realization.correct_client hr hv (run_exec p t)
  exact ⟨h.1, h.2, nodeVisitBound.client hr hv (run_exec p t)⟩

end Cslib.Algorithms.Lean.SearchTree
