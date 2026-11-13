/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.FenwickTree.Basic
public import CslibFrontier.DataStructure.PrefixSums.Spec
public import CslibFrontier.DataStructure.StateTransition.Resource
public import CslibFrontier.DataStructure.StateTransition.StepFunction

/-!
# Stateful Dynamic Prefix-Sum Implementation by Fenwick Trees

This module realizes the representation-independent dynamic prefix-sum specification
`Cslib.DataStructure.PrefixSums.spec` (`add`, `sum`) over any `[AddCommMonoid α]` by
`Cslib.DataStructure.FenwickTree` with per-operation node-visit budget
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
* **Universe level:** `Cslib.DataStructure.StateTransitionImpl` places the concrete state
  `FenwickTree α` and
  cost trace `ℕ : Type` in the same universe (`Type`), whereas `Basic.lean` is universe-polymorphic
  over `{α : Type*}`.

## Main definitions

* `Cslib.DataStructure.FenwickTree.step`, `Exec`, `run`: concrete `TimeM`-backed execution step,
  native execution relation, and executable client interpreter, built with
  `Cslib.DataStructure.Execution.ofStep`.
* `Cslib.DataStructure.FenwickTree.impl`: `Cslib.DataStructure.StateTransitionImpl` of
  `PrefixSums.spec α` using
  `Valid` directly as the representation invariant (`rep s t := Valid t s`).
* `Cslib.DataStructure.FenwickTree.charge`: representation-independent logarithmic node-visit
  budget `Nat.clog 2 (s.length + 1)`.

## Main results

* `Cslib.DataStructure.FenwickTree.stepBound`: logarithmic `Cslib.DataStructure.Bound`
  certificate.
* `Cslib.DataStructure.FenwickTree.totalCost_charge`: for any history `os`,
  `(PrefixSums.spec α).totalCost charge s os = os.length * Nat.clog 2 (s.length + 1)`.
* `Cslib.DataStructure.FenwickTree.realized_client`, `run_correct`: adaptive dynamic prefix-sum
  clients execute with `List α` correctness and additive `Nat.clog 2 (s.length + 1)` bounds.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.DataStructure.FenwickTree

open Cslib.DataStructure

variable {α : Type} [AddCommMonoid α]

/-- Execute a single `PrefixSums.Op α` on `t : FenwickTree α`, returning the updated tree,
observation, and exact `TimeM` node-visit count. -/
@[expose] def step (t : FenwickTree α) (o : PrefixSums.Op α) :
    StepResult (FenwickTree α) ℕ ((PrefixSums.spec α).Result o) :=
  match o with
  | .add pos δ =>
      let m := addM t pos δ
      ⟨m.ret, (), m.time⟩
  | .sum len =>
      let m := prefixSumM t len
      ⟨t, m.ret, m.time⟩

/-- Native execution relation for `PrefixSums.spec α` over `FenwickTree α`. -/
abbrev Exec : Execution (PrefixSums.spec α) (FenwickTree α) ℕ := Execution.ofStep step

/-- Semantic realization of `PrefixSums.spec α` by `FenwickTree α`, using `Valid t s` directly as
the representation invariant. -/
@[expose] def impl : StateTransitionImpl (PrefixSums.spec α) (Exec (α := α)) :=
  StateTransitionImpl.ofStep (D := PrefixSums.spec α) (fun s t => Valid t s) step
    fun o hr _ => by
      cases o with
      | add pos δ => exact ⟨rfl, valid_add hr pos δ⟩
      | sum len => exact ⟨ret_prefixSumM_eq hr len, hr⟩

@[simp]
theorem impl_rep (s : List α) (t : FenwickTree α) :
    (impl (α := α)).rep s t = Valid t s := rfl

/-- Representation-independent per-operation node-visit budget `⌈log₂ (|s| + 1)⌉`
(`0` when `s = []`, `⌊log₂ |s|⌋ + 1` when `s ≠ []`). -/
@[expose] def charge (s : List α) (_ : PrefixSums.Op α) : ℕ :=
  Nat.clog 2 (s.length + 1)

/-- Because every `PrefixSums.Op α` preserves `s.length`, the abstract `totalCost` along any
history `os` equals `os.length * Nat.clog 2 (s.length + 1)`. -/
theorem totalCost_charge (s : List α) (os : List (PrefixSums.Op α)) :
    (PrefixSums.spec α).totalCost (charge (α := α)) s os =
      os.length * Nat.clog 2 (s.length + 1) := by
  induction os generalizing s with
  | nil => simp only [StateTransitionSpec.totalCost_nil, List.length_nil, Nat.zero_mul]
  | cons o os ih =>
    rw [StateTransitionSpec.totalCost_cons, ih ((PrefixSums.spec α).stepFn s o).1,
      PrefixSums.length_stepFn]
    simp only [charge, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- Logarithmic per-operation node-visit certificate for `FenwickTree.impl`. -/
theorem stepBound : Bound (impl (α := α)) id charge := by
  intro s t o a t' c hr _ he
  have hsz : t.size = s.length := hr.size_eq
  cases o with
  | add pos δ =>
    cases he
    simpa only [id_eq, charge, hsz] using addM_time_le_clog t pos δ
  | sum len =>
    cases he
    simpa only [id_eq, charge, hsz] using prefixSumM_time_le_clog t len

/-- Every adaptive dynamic prefix-sum client executes on `FenwickTree` with `List α` correctness and
additive `Nat.clog 2 (s.length + 1)` node-visit bounds. -/
theorem realized_client {β : Type} (p : (PrefixSums.spec α).Client β)
    {s : List α} {t : FenwickTree α} (hr : Valid t s) :
    let (value, finalState, history) := (PrefixSums.spec α).runClient s p
    ∃ t' cs, Executes Exec p t value t' cs ∧ Valid t' finalState ∧
      total id cs ≤ (PrefixSums.spec α).totalCost charge s history :=
  Bound.exists_executes stepBound p hr
    ((PrefixSums.spec α).validHistory_of_forall_valid (fun _ _ => trivial) s _)

/-- Execute a dynamic prefix-sum client concretely on a Fenwick tree, recording exact node visits
per operation. -/
abbrev run {β : Type} (t : FenwickTree α) (p : (PrefixSums.spec α).Client β) :
    RunResult (FenwickTree α) ℕ β :=
  Execution.run step t p

/-- Running the concrete Fenwick tree interpreter agrees with abstract `List α` semantics, preserves
`Valid`, and satisfies the additive logarithmic node-visit bound. -/
theorem run_correct {β : Type} (p : (PrefixSums.spec α).Client β)
    {s : List α} {t : FenwickTree α} (hr : Valid t s) :
    let (value, finalState, history) := (PrefixSums.spec α).runClient s p
    (run t p).value = value ∧ Valid (run t p).state finalState ∧
      total id (run t p).traces ≤ history.length * Nat.clog 2 (s.length + 1) := by
  have hv := (PrefixSums.spec α).validHistory_of_forall_valid (fun _ _ => trivial) s
    ((PrefixSums.spec α).clientHistory s p)
  have hexec := Execution.executes_run step p t
  have hc := impl.correct_client hr hv hexec
  have hb := Bound.client stepBound hr hv hexec
  rw [totalCost_charge] at hb
  exact ⟨hc.1, hc.2, hb⟩

end Cslib.DataStructure.FenwickTree
