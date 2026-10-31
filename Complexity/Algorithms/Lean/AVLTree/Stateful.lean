/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.AVLTree.Erase
public import Complexity.Foundations.Data.OrderedSet.Spec
public import Complexity.Foundations.Semantics.Stateful.Resource

/-!
# Stateful ordered-set realization by height-balanced AVL trees

This module realizes the shared `Cslib.OrderedSet.spec α` interface (`contains`, `insert`, `erase`,
`minimum`, `successor`) using height-cached AVL trees in the same internal-node-visit cost model as
`Cslib.Algorithms.Lean.SearchTree`, upgrading `SearchTree.nodeVisitBound`'s worst-case linear
`s.card` bound to the representation-independent logarithmic bound
`2 * Nat.log 2 (s.card + 1)`.

## Cost model and limitations

As in `Cslib.Algorithms.Lean.SearchTree`, native operation traces count internal nodes visited along
the downward search (and `splitMin`) path (`0` on an empty tree, at most `t.cachedHeight` on any
height-consistent tree), specified by `SearchTree`'s path-visit functions on `t.toBinaryTree`. At
each visited ancestor during `insert` or `erase`, `balance` performs non-recursive `O(1)` reads of
off-path sibling/nephew cached heights and at most a single or double rotation; those constant-work
rebalancing steps, `toBinaryTree` trace-specification projection, node allocations, order-comparison
implementations, and pure client continuations are not charged as separate RAM or Turing-machine
instructions.

## Main definitions

* `step`, `Exec`, `run`: concrete AVL operations, native execution relation, and executable client
  runner with exact internal-node-visit traces.
* `Rep`, `realization`: AVL representation relation (`Valid t ∧ elements t = s`) and
  `Cslib.Stateful.Realization` of `Cslib.OrderedSet.spec α`.
* `charge`: representation-independent logarithmic node-visit budget
  `2 * Nat.log 2 (s.card + 1)`.

## Main results

* `Rep.valid`, `Rep.elements_eq`, `rep_empty`, `realization_rep`: representation invariant
  projections and empty-set initialization.
* `exec_visits_le_cachedHeight`: every native operation visits at most `t.cachedHeight` path nodes.
* `nodeVisitBound`: logarithmic `Cslib.Stateful.Bound` certificate `2 * Nat.log 2 (s.card + 1)`.
* `realized_client`, `run_correct`: adaptive ordered-set clients (including `extractMin`) execute
  with finite-set correctness and additive logarithmic node-visit bounds.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 12 and Problem 13-3][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.AVLTree

open Cslib.Stateful Cslib.OrderedSet

variable {α : Type} [LinearOrder α]

/-- Execute a single `OrderedSet.Op α` on an AVL tree, returning the updated tree, answer, and
internal-node-visit count. -/
@[expose] def step (t : AVLTree α) (o : Op α) : AVLTree α × (spec α).Result o × ℕ :=
  match o with
  | .contains x => (t, contains x t, searchVisits x t)
  | .insert x => (insert x t, (), searchVisits x t)
  | .erase x => (erase x t, (), eraseVisits x t)
  | .minimum => (t, minimum t, minimumVisits t)
  | .successor x => (t, successor x t, successorVisits x t)

/-- Native execution relation for `OrderedSet.spec α` over `AVLTree α`. -/
@[expose] def Exec : Execution (spec α) (AVLTree α) ℕ :=
  fun t o a t' n => step t o = (t', a, n)

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
@[expose] def realization : Realization (spec α) (Exec (α := α)) where
  rep := Rep
  total {_ t} o _ _ :=
    match h : step t o with
    | (t', a, n) => ⟨a, t', n, h⟩
  correct {s t o a t' n} hr _ he := by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      cases he
      refine ⟨?_, ht, rfl⟩
      have h := contains_eq_true ht.ordered x
      by_cases hx : x ∈ elements t <;> simp_all
    | insert x =>
      cases he
      exact ⟨rfl, valid_insert ht x, elements_insert x t⟩
    | erase x =>
      cases he
      exact ⟨rfl, valid_erase ht x, elements_erase ht.ordered x⟩
    | minimum =>
      cases he
      exact ⟨(minimum_spec ht.ordered).eq_least, ht, rfl⟩
    | successor x =>
      cases he
      exact ⟨(successor_spec ht.ordered x).eq_least, ht, rfl⟩

/-- `realization.rep` is definitionally `Rep`. -/
@[simp]
theorem realization_rep : (realization (α := α)).rep = Rep := rfl

/-- Every native AVL operation visits at most `t.cachedHeight` internal path nodes. -/
theorem exec_visits_le_cachedHeight {t t' : AVLTree α} {o : Op α}
    {a : (spec α).Result o} {n : ℕ} (hc : HeightConsistent t) (he : Exec t o a t' n) :
    n ≤ t.cachedHeight := by
  cases o with
  | contains x => cases he; exact searchVisits_le_cachedHeight hc x
  | insert x => cases he; exact searchVisits_le_cachedHeight hc x
  | erase x => cases he; exact eraseVisits_le_cachedHeight hc x
  | minimum => cases he; exact minimumVisits_le_cachedHeight hc
  | successor x => cases he; exact successorVisits_le_cachedHeight hc x

/-- Representation-independent logarithmic node-visit budget (`0` on `∅`, `2 * log₂(|s| + 1)` in
general). -/
@[expose] def charge (s : Finset α) (_ : Op α) : ℕ :=
  2 * Nat.log 2 (s.card + 1)

/-- Logarithmic per-operation node-visit certificate for `AVLTree.realization`. -/
theorem nodeVisitBound : Bound (realization (α := α)) id charge := by
  intro s t o a t' n hr _ he
  have hvisit := exec_visits_le_cachedHeight hr.valid.heightConsistent he
  have hlog := hr.valid.cachedHeight_le_two_mul_log
  rw [hr.elements_eq] at hlog
  exact hvisit.trans hlog

/-- Every adaptive `OrderedSet` client executes on `AVLTree` with finite-set correctness and
additive `2 * Nat.log 2 (s.card + 1)` node-visit bounds along its chosen history. -/
theorem realized_client {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : AVLTree α} (hr : Rep s t) :
    ∃ t' ns, Executes Exec p t ((spec α).runClient s p).1 t' ns ∧
      Rep ((spec α).runClient s p).2.1 t' ∧
      total id ns ≤ (spec α).totalCost charge s ((spec α).runClient s p).2.2 := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  exact Bound.exists_executes nodeVisitBound p hr hv

/-- Execute an `OrderedSet` client concretely on an AVL tree, recording exact node visits per
operation. -/
@[expose] def run {β : Type} (t : AVLTree α) :
    (spec α).Client β → β × AVLTree α × List ℕ
  | .pure a => (a, t, [])
  | .liftBind o k =>
      let (t', a, c) := step t o
      let (res, t'', cs) := run t' (k a)
      (res, t'', c :: cs)

/-- The concrete runner produces a valid `Executes Exec` derivation. -/
theorem run_exec {β : Type} (p : (spec α).Client β) (t : AVLTree α) :
    Executes Exec p t (run t p).1 (run t p).2.1 (run t p).2.2 := by
  induction p generalizing t with
  | pure a => exact .pure a t
  | liftBind o k ih => exact .call rfl (ih _ _)

/-- Running the concrete AVL interpreter agrees with abstract `Finset α` semantics, preserves `Rep`,
and satisfies the additive logarithmic node-visit bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : Finset α} {t : AVLTree α} (hr : Rep s t) :
    (run t p).1 = ((spec α).runClient s p).1 ∧
      Rep ((spec α).runClient s p).2.1 (run t p).2.1 ∧
      total id (run t p).2.2 ≤
        (spec α).totalCost charge s ((spec α).runClient s p).2.2 := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  have hexec := run_exec p t
  have hc := realization.correct_client hr hv hexec
  exact ⟨hc.1, hc.2, Bound.client nodeVisitBound hr hv hexec⟩

end Cslib.Algorithms.Lean.AVLTree
