/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.Recursion

/-!
# A bounded worklist for the exact Chan–He recursion

The worklist expands the existing `ChanHe.nodes` in its existing preorder. Empty triples and
zero fuel are popped without emitting an instance. Three children replace one set each by its
existing heavy subset, in the order used by the finite reduction.

This is the mathematical invariant for the native traversal, not a native execution contract.
In particular, expanding a worklist entry here does not discharge a native modulus or node call.
The stack bound counts pending entries, including empty and zero-fuel entries. Those entries
still require charged native pop and branch instructions.

## Main definitions

* `Task`: one pending three-set call, including its remaining fuel.
* `step`: one exact worklist transition and its optional emitted node.
* `potential`: a natural-valued bound on all remaining transitions, including skipped entries.
* `Bounded`: a stack-depth invariant giving at most `2f+1` pending entries for root fuel `f`.

## Main results

* `output_step`: one transition preserves the exact preorder output.
* `potential_step`: every transition strictly decreases the charged-transition bound.
* `bounded_step`, `Bounded.length_le`: the explicit stack has linear capacity in root fuel.

These worklist invariants are original. They reuse the finite recursion of [ChanHe2020].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

namespace Math

open Cslib.Algorithms.ThreeSum.ChanHe

/-- One pending call of the existing finite recursion. -/
structure Task where
  /-- Remaining recursion levels. -/
  fuel : ℕ
  /-- The three mathematical sets represented by the native descriptor. -/
  sets : Fin 3 → Finset ℤ

/-- The exact existing preorder associated with one pending call. -/
def Task.output (Q : Finset ℕ) (Λ : ℕ) (t : Task) : List Node :=
  nodes Q Λ t.fuel (t.sets 0) (t.sets 1) (t.sets 2)

/-- The exact existing modulus and three sets of a nonempty call. -/
def Task.node (Q : Finset ℕ) (Λ : ℕ) (t : Task) : Node :=
  ⟨t.sets 0, t.sets 1, t.sets 2, modulus Q Λ (t.sets 0) (t.sets 1) (t.sets 2)⟩

/-- Whether a call is skipped because one of its sets is empty. -/
abbrev Task.empty (t : Task) : Prop := t.sets 0 = ∅ ∨ t.sets 1 = ∅ ∨ t.sets 2 = ∅

/-- The three children, with exactly the mathematical reduction's order and heavy sets. -/
def Task.children (Q : Finset ℕ) (Λ f : ℕ) (t : Task) : List Task :=
  let M := (t.node Q Λ).M
  [⟨f, ![heavy (t.sets 0) M, t.sets 1, t.sets 2]⟩,
    ⟨f, ![t.sets 0, heavy (t.sets 1) M, t.sets 2]⟩,
    ⟨f, ![t.sets 0, t.sets 1, heavy (t.sets 2) M]⟩]

/-- The sequence still to be emitted from a top-first worklist. -/
def output (Q : Finset ℕ) (Λ : ℕ) (ts : List Task) : List Node :=
  ts.flatMap (Task.output Q Λ)

/-- One pop, followed either by a skip or by one emission and three children. -/
def step (Q : Finset ℕ) (Λ : ℕ) (t : Task) (ts : List Task) : List Task × Option Node :=
  match t.fuel with
  | 0 => (ts, none)
  | f + 1 => if t.empty then (ts, none) else (t.children Q Λ f ++ ts, some (t.node Q Λ))

/-- One worklist transition preserves the exact output list, including order and skipped calls. -/
theorem output_step (Q : Finset ℕ) (Λ : ℕ) (t : Task) (ts : List Task) :
    output Q Λ (t :: ts) =
      (step Q Λ t ts).2.toList ++ output Q Λ (step Q Λ t ts).1 := by
  cases t with
  | mk f S =>
    cases f with
    | zero => simp [output, step, Task.output, nodes]
    | succ f =>
      by_cases he : Task.empty ⟨f + 1, S⟩
      · simp only [Task.empty] at he
        simp [output, step, Task.empty, he, Task.output, nodes]
      · simp only [Task.empty] at he
        simp [output, step, Task.empty, he, Task.output, nodes, Task.children, Task.node,
          List.append_assoc]

/-- Number of transitions for the full ternary tree, counting its zero-fuel leaves. -/
def work : ℕ → ℕ
  | 0 => 1
  | f + 1 => 1 + 3 * work f

/-- Every pending entry costs at least one pop/skip transition. -/
theorem work_pos (f : ℕ) : 1 ≤ work f := by
  cases f <;> simp [work]

/-- Closed form without a truncated quotient. -/
theorem work_eq (f : ℕ) : 2 * work f + 1 = 3 ^ (f + 1) := by
  induction f with
  | zero => decide
  | succ f ih =>
    simp only [work, pow_succ] at *
    omega

/-- The sum of the transition budgets of all pending entries. -/
def potential (ts : List Task) : ℕ := (ts.map fun t => work t.fuel).sum

/-- One transition spends at least one unit, including the empty and zero-fuel cases. -/
theorem potential_step (Q : Finset ℕ) (Λ : ℕ) (t : Task) (ts : List Task) :
    potential (step Q Λ t ts).1 + 1 ≤ potential (t :: ts) := by
  cases t with
  | mk f S =>
    cases f with
    | zero => simp [step, potential, work]
    | succ f =>
      by_cases he : Task.empty ⟨f + 1, S⟩
      · simp only [step, he, ↓reduceIte, potential, List.map_cons, List.sum_cons]
        have := work_pos (f + 1)
        omega
      · simp only [step, he, ↓reduceIte, potential, Task.children, List.map_append,
          List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, work]
        omega

/-- Each entry's fuel plus the pending suffix gives a bound measured from the stack bottom. -/
def Bounded (f : ℕ) : List Task → Prop
  | [] => True
  | t :: ts => 2 * t.fuel + ts.length ≤ 2 * f ∧ Bounded f ts

/-- A single root of fuel `f` satisfies the stack invariant. -/
theorem bounded_singleton (t : Task) : Bounded t.fuel [t] := by
  simp [Bounded]

/-- The explicit stack requires at most `2f+1` entries, even with zero-fuel entries present. -/
theorem Bounded.length_le {f : ℕ} {ts : List Task} (h : Bounded f ts) :
    ts.length ≤ 2 * f + 1 := by
  cases ts with
  | nil => simp
  | cons t ts =>
    simp only [Bounded] at h
    simp only [List.length_cons]
    omega

/-- A native pop/skip or three-child push preserves the same fixed stack capacity. -/
theorem bounded_step {f : ℕ} (Q : Finset ℕ) (Λ : ℕ) (t : Task) (ts : List Task)
    (h : Bounded f (t :: ts)) : Bounded f (step Q Λ t ts).1 := by
  obtain ⟨hf, hts⟩ := h
  cases ht : t.fuel with
  | zero => simpa only [step, ht] using hts
  | succ g =>
    by_cases he : t.empty
    · simpa only [step, ht, he, ↓reduceIte] using hts
    · simp only [step, ht, he, ↓reduceIte, Task.children, List.cons_append,
        List.nil_append, Bounded, List.length_cons] at *
      exact ⟨by omega, by omega, by omega, hts⟩

end Math

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
