/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.AVLTree.Erase
public import CslibFrontier.DataStructure.OrderedSet.Spec
public import CslibFrontier.DataStructure.StateTransition.Resource
public import CslibFrontier.DataStructure.StateTransition.StepFunction

/-!
# Stateful ordered-set realization by height-balanced AVL trees

This module realizes the shared `Cslib.DataStructure.OrderedSet.spec α` interface (`contains`,
`insert`, `delete`, `minimum`, `successor`) using height-cached AVL trees in the same
internal-node-visit cost model as
`Cslib.DataStructure.SearchTree`, upgrading `SearchTree.nodeVisitBound`'s worst-case linear
`s.card` bound to the representation-independent logarithmic bound
`2 * Nat.log 2 (s.card + 1)`.

## Cost model and limitations

As in `Cslib.DataStructure.SearchTree`, native operation traces count internal nodes visited along
the downward search (and `splitMin`) path (`0` on an empty tree, at most `t.cachedHeight` on any
height-consistent tree), specified by `SearchTree`'s path-visit functions on `t.toBinaryTree`. At
each visited ancestor during `insert` or `erase`, `balance` performs non-recursive `O(1)` reads of
off-path sibling/nephew cached heights and at most a single or double rotation; those constant-work
rebalancing steps, `toBinaryTree` trace-specification projection, node allocations, order-comparison
implementations, and pure client continuations are not charged as separate RAM or Turing-machine
instructions.

## Main definitions

* `step`, `Exec`, `run`: concrete AVL operations, native execution relation, and executable client
  runner with exact internal-node-visit traces, built with `Cslib.DataStructure.Execution.ofStep`.
* `Rep`, `impl`: AVL representation relation (`Valid t ∧ elements t = s`) and
  `Cslib.DataStructure.StateTransitionImpl` of `Cslib.DataStructure.OrderedSet.spec α`.
* `charge`: representation-independent logarithmic node-visit budget
  `2 * Nat.log 2 (s.card + 1)`.

## Main results

* `Rep.valid`, `Rep.elements_eq`, `rep_empty`, `impl_rep`: representation invariant
  projections and empty-set initialization.
* `exec_visits_le_cachedHeight`: every native operation visits at most `t.cachedHeight` path nodes.
* `nodeVisitBound`: logarithmic `Cslib.DataStructure.Bound` certificate
  `2 * Nat.log 2 (s.card + 1)`.
* `realized_client`, `run_correct`: adaptive ordered-set clients (including `extractMin`) execute
  with finite-set correctness and additive logarithmic node-visit bounds.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 12 and Problem 13-3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.AVLTree

open Cslib.DataStructure Cslib.DataStructure.OrderedSet

variable {α : Type} [LinearOrder α]

/-- Execute a single `OrderedSet.Op α` on an AVL tree, returning the updated tree, answer, and
internal-node-visit count. -/
@[expose] def step (t : AVLTree α) (o : Op α) : StepResult (AVLTree α) ℕ ((spec α).Result o) :=
  match o with
  | .contains x => ⟨t, contains x t, searchVisits x t⟩
  | .insert x => ⟨insert x t, (), searchVisits x t⟩
  | .delete x => ⟨erase x t, (), eraseVisits x t⟩
  | .minimum => ⟨t, minimum t, minimumVisits t⟩
  | .successor x => ⟨t, successor x t, successorVisits x t⟩

/-- Native execution relation for `OrderedSet.spec α` over `AVLTree α`. -/
abbrev Exec : Execution (spec α) (AVLTree α) ℕ := Execution.ofStep step

/-- Representation relation coupling a mathematical `Finset α` with a valid AVL tree `t`. -/
@[expose] def Rep (s : Finset α) (t : AVLTree α) : Prop :=
  Valid t ∧ elements t = s

/-- Extract AVL validity from `Rep`. -/
theorem Rep.valid {s : Finset α} {t : AVLTree α} (hr : Rep s t) : Valid t := hr.1

/-- Extract the key-set equality from `Rep`. -/
theorem Rep.elements_eq {s : Finset α} {t : AVLTree α} (hr : Rep s t) : elements t = s := hr.2

/-- The empty AVL tree represents the empty `Finset α`. -/
theorem rep_empty : Rep (∅ : Finset α) .nil :=
  ⟨valid_nil, rfl⟩

/-- Semantic realization of `OrderedSet.spec α` by `AVLTree α`. -/
@[expose] def impl : StateTransitionImpl (spec α) (Exec (α := α)) :=
  StateTransitionImpl.ofStep (D := spec α) Rep step fun {_ t} o hr _ => by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      refine ⟨?_, ht, rfl⟩
      have h := contains_eq_true ht.ordered x
      by_cases hx : x ∈ elements t <;> simp_all [step]
    | insert x => exact ⟨rfl, valid_insert ht x, elements_insert x t⟩
    | delete x => exact ⟨rfl, valid_erase ht x, elements_erase ht.ordered x⟩
    | minimum => exact ⟨(minimum_spec ht.ordered).eq_least, ht, rfl⟩
    | successor x => exact ⟨(successor_spec ht.ordered x).eq_least, ht, rfl⟩

/-- `impl.rep` is definitionally `Rep`. -/
@[simp]
theorem impl_rep : (impl (α := α)).rep = Rep := rfl

/-- Every native AVL operation visits at most `t.cachedHeight` internal path nodes. -/
theorem exec_visits_le_cachedHeight {t t' : AVLTree α} {o : Op α}
    {a : (spec α).Result o} {n : ℕ} (hc : HeightConsistent t) (he : Exec t o a t' n) :
    n ≤ t.cachedHeight := by
  cases o with
  | contains x => cases he; exact searchVisits_le_cachedHeight hc x
  | insert x => cases he; exact searchVisits_le_cachedHeight hc x
  | delete x => cases he; exact eraseVisits_le_cachedHeight hc x
  | minimum => cases he; exact minimumVisits_le_cachedHeight hc
  | successor x => cases he; exact successorVisits_le_cachedHeight hc x

/-- Representation-independent logarithmic node-visit budget (`0` on `∅`, `2 * log₂(|s| + 1)` in
general). -/
@[expose] def charge (s : Finset α) (_ : Op α) : ℕ :=
  2 * Nat.log 2 (s.card + 1)

/-- Logarithmic per-operation node-visit certificate for `AVLTree.impl`. -/
theorem nodeVisitBound : Bound (impl (α := α)) id charge := by
  intro s t o a t' n hr _ he
  have hvisit := exec_visits_le_cachedHeight hr.valid.heightConsistent he
  have hlog := hr.valid.cachedHeight_le_two_mul_log
  rw [hr.elements_eq] at hlog
  exact hvisit.trans hlog

/-- Every adaptive `OrderedSet` client executes on `AVLTree` with finite-set correctness and
additive `2 * Nat.log 2 (s.card + 1)` node-visit bounds along its chosen history. -/
theorem realized_client {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : AVLTree α} (hr : Rep s t) :
    let (value, finalState, history) := (spec α).runClient s p
    ∃ t' ns, Executes Exec p t value t' ns ∧ Rep finalState t' ∧
      total id ns ≤ (spec α).totalCost charge s history :=
  nodeVisitBound.exists_executes p hr
    ((spec α).validHistory_of_forall_valid (fun _ _ => trivial) s _)

/-- Execute an `OrderedSet` client concretely on an AVL tree, recording exact node visits per
operation. -/
abbrev run {β : Type} (t : AVLTree α) (p : (spec α).Client β) :
    RunResult (AVLTree α) ℕ β :=
  Execution.run step t p

/-- Running the concrete AVL interpreter agrees with abstract `Finset α` semantics, preserves `Rep`,
and satisfies the additive logarithmic node-visit bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : AVLTree α} (hr : Rep s t) :
    let (value, finalState, history) := (spec α).runClient s p
    (run t p).value = value ∧ Rep finalState (run t p).state ∧
      total id (run t p).traces ≤ (spec α).totalCost charge s history := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial) s
    ((spec α).clientHistory s p)
  have hexec := Execution.executes_run step p t
  have hc := impl.correct_client hr hv hexec
  exact ⟨hc.1, hc.2, nodeVisitBound.client hr hv hexec⟩

end Cslib.DataStructure.AVLTree
