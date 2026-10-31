/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.FenwickTree.Basic
public import Complexity.Foundations.Semantics.Stateful.Resource

/-!
# Stateful Dynamic Prefix-Sum Realization by Fenwick Trees

This module defines a representation-independent `Cslib.Stateful.Spec` for fixed-length dynamic
prefix-sum sequences (`add`, `prefixSum`) over any `[AddCommMonoid α]` and realizes it by
`Cslib.Algorithms.Lean.FenwickTree` with per-operation node-visit budget
`Nat.clog 2 (s.length + 1)` (`0` when `s = []`, `⌊log₂ s.length⌋ + 1` when `s ≠ []`).

Because every operation preserves `s.length`, the abstract `totalCost` along any `k`-operation
history starting from `s` simplifies to `k * Nat.clog 2 (s.length + 1)` (`totalCost_charge`).

## Cost Model and Limitations

* **Charged (`1` unit per visited Fenwick node):** each step along a downward query chain in
  `prefixSumM` or upward update chain in `addM`.
* **Uncharged (`0` units) and model boundaries:** `Exec` projects `TimeM` node-visit counts rather
  than Word-RAM instructions. Index arithmetic (including recursive `lowbit` on `ℕ`), bounds
  checks, monoid `+`, initial `zeros` or `s.length`-tick `ofListM` construction (proved separately
  in `Basic.lean`), pure client continuations, and functional `Array.modify` copying if a tree
  value is shared non-linearly rather than uniquely owned (for example, `step` binds
  `let m := addM t pos δ` on `t`) are uncharged.
* **Universe level:** `Cslib.Stateful.Realization` places the concrete state `FenwickTree α` and
  cost trace `ℕ : Type` in the same universe (`Type`), whereas `Basic.lean` is universe-polymorphic
  over `{α : Type*}`.

## Main definitions

* `Cslib.Algorithms.Lean.FenwickTree.Op`, `spec`: representation-independent dynamic prefix-sum
  operations and `List α` specification.
* `Cslib.Algorithms.Lean.FenwickTree.step`, `Exec`, `run`: concrete `TimeM`-backed execution step,
  native execution relation, and executable client interpreter.
* `Cslib.Algorithms.Lean.FenwickTree.realization`: `Cslib.Stateful.Realization` of `spec α` using
  `Valid` directly as the representation invariant (`rep s t := Valid t s`).
* `Cslib.Algorithms.Lean.FenwickTree.charge`: representation-independent logarithmic node-visit
  budget `Nat.clog 2 (s.length + 1)`.

## Main results

* `Cslib.Algorithms.Lean.FenwickTree.stepBound`: logarithmic `Cslib.Stateful.Bound` certificate.
* `Cslib.Algorithms.Lean.FenwickTree.totalCost_charge`: for any history `os`,
  `(spec α).totalCost charge s os = os.length * Nat.clog 2 (s.length + 1)`.
* `Cslib.Algorithms.Lean.FenwickTree.realized_client`, `run_correct`: adaptive dynamic prefix-sum
  clients execute with `List α` correctness and additive `Nat.clog 2 (s.length + 1)` bounds.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.Algorithms.Lean.FenwickTree

open Cslib.Stateful

/-- Dynamic prefix-sum operations over `α`, independent of storage representation. -/
inductive Op (α : Type) where
  /-- Increment the entry at `0`-based index `pos` by `delta` (no-op when out of bounds). -/
  | add (pos : ℕ) (delta : α)
  /-- Query the sum `(s.take len).sum` of the first `len` elements. -/
  | prefixSum (len : ℕ)
  deriving DecidableEq, Repr

/-- Mathematical specification of dynamic prefix sums on `List α`. All operations are admissible:
out-of-bounds `add` is a no-op and `prefixSum len` sums `s.take len`. -/
abbrev spec (α : Type) [AddCommMonoid α] : Spec where
  State := List α
  Op := Op α
  Result
    | .add _ _ => Unit
    | .prefixSum _ => α
  step s
    | .add pos δ => (addAt s pos δ, ())
    | .prefixSum len => (s, (s.take len).sum)

variable {α : Type} [AddCommMonoid α]

@[simp]
theorem length_spec_step (s : List α) (o : Op α) :
    ((spec α).step s o).1.length = s.length := by
  cases o with
  | add pos δ => exact length_addAt s pos δ
  | prefixSum len => rfl

/-- Execute a single `Op α` on `t : FenwickTree α`, returning the updated tree, observation, and
exact `TimeM` node-visit count. -/
@[expose] def step (t : FenwickTree α) (o : Op α) : FenwickTree α × (spec α).Result o × ℕ :=
  match o with
  | .add pos δ =>
      let m := addM t pos δ
      (m.ret, (), m.time)
  | .prefixSum len =>
      let m := prefixSumM t len
      (t, m.ret, m.time)

/-- Native execution relation for `spec α` over `FenwickTree α`. -/
@[expose] def Exec : Execution (spec α) (FenwickTree α) ℕ :=
  fun t o a t' c => step t o = (t', a, c)

/-- Semantic realization of `spec α` by `FenwickTree α`, using `Valid t s` directly as the
representation invariant. -/
@[expose] def realization : Realization (spec α) (Exec (α := α)) where
  rep s t := Valid t s
  total {_ t} o _ _ :=
    match h : step t o with
    | (t', a, c) => ⟨a, t', c, h⟩
  correct {s t o a t' c} hr _ he := by
    cases o with
    | add pos δ =>
      cases he
      exact ⟨rfl, valid_add hr pos δ⟩
    | prefixSum len =>
      cases he
      exact ⟨ret_prefixSumM_eq hr len, hr⟩

@[simp]
theorem realization_rep (s : List α) (t : FenwickTree α) :
    (realization (α := α)).rep s t = Valid t s := rfl

/-- Representation-independent per-operation node-visit budget `⌈log₂ (|s| + 1)⌉`
(`0` when `s = []`, `⌊log₂ |s|⌋ + 1` when `s ≠ []`). -/
@[expose] def charge (s : List α) (_ : Op α) : ℕ :=
  Nat.clog 2 (s.length + 1)

/-- Because every `Op α` preserves `s.length`, the abstract `totalCost` along any history `os`
equals `os.length * Nat.clog 2 (s.length + 1)`. -/
theorem totalCost_charge (s : List α) (os : List (Op α)) :
    (spec α).totalCost (charge (α := α)) s os = os.length * Nat.clog 2 (s.length + 1) := by
  induction os generalizing s with
  | nil => simp only [Spec.totalCost_nil, List.length_nil, Nat.zero_mul]
  | cons o os ih =>
    rw [Spec.totalCost_cons, ih ((spec α).step s o).1, length_spec_step]
    simp only [charge, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Logarithmic per-operation node-visit certificate for `FenwickTree.realization`. -/
theorem stepBound : Bound (realization (α := α)) id charge := by
  intro s t o a t' c hr _ he
  have hsz : t.size = s.length := hr.size_eq
  cases o with
  | add pos δ =>
    cases he
    simpa only [id_eq, charge, hsz] using addM_time_le_clog t pos δ
  | prefixSum len =>
    cases he
    simpa only [id_eq, charge, hsz] using prefixSumM_time_le_clog t len

/-- Every adaptive dynamic prefix-sum client executes on `FenwickTree` with `List α` correctness and
additive `Nat.clog 2 (s.length + 1)` node-visit bounds. -/
theorem realized_client {β : Type} (p : (spec α).Client β)
    {s : List α} {t : FenwickTree α} (hr : Valid t s) :
    ∃ t' cs, Executes Exec p t ((spec α).runClient s p).1 t' cs ∧
      Valid t' ((spec α).runClient s p).2.1 ∧
      total id cs ≤ (spec α).totalCost charge s ((spec α).runClient s p).2.2 := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  exact Bound.exists_executes stepBound p hr hv

/-- Execute a dynamic prefix-sum client concretely on a Fenwick tree, recording exact node visits
per operation. -/
@[expose] def run {β : Type} (t : FenwickTree α) :
    (spec α).Client β → β × FenwickTree α × List ℕ
  | .pure a => (a, t, [])
  | .liftBind o k =>
      let (t', a, c) := step t o
      let (res, t'', cs) := run t' (k a)
      (res, t'', c :: cs)

/-- The concrete runner produces a valid `Executes Exec` derivation. -/
theorem run_exec {β : Type} (p : (spec α).Client β) (t : FenwickTree α) :
    Executes Exec p t (run t p).1 (run t p).2.1 (run t p).2.2 := by
  induction p generalizing t with
  | pure a => exact .pure a t
  | liftBind o k ih => exact .call rfl (ih _ _)

/-- Running the concrete Fenwick tree interpreter agrees with abstract `List α` semantics, preserves
`Valid`, and satisfies the additive logarithmic node-visit bound. -/
theorem run_correct {β : Type} (p : (spec α).Client β)
    {s : List α} {t : FenwickTree α} (hr : Valid t s) :
    (run t p).1 = ((spec α).runClient s p).1 ∧
      Valid (run t p).2.1 ((spec α).runClient s p).2.1 ∧
      total id (run t p).2.2 ≤
        ((spec α).runClient s p).2.2.length * Nat.clog 2 (s.length + 1) := by
  have hv := (spec α).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec α).runClient s p).2.2
  have hexec := run_exec p t
  have hc := realization.correct_client hr hv hexec
  have hb := Bound.client stepBound hr hv hexec
  rw [totalCost_charge] at hb
  exact ⟨hc.1, hc.2, hb⟩

end Cslib.Algorithms.Lean.FenwickTree
