/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Queue
public import Complexity.Computability.WordRAM.Defs

/-!
# The FIFO meaning of a two-stack representation

The front stack lists the oldest values first; the rear stack lists the newest values first.
Thus the represented FIFO sequence is `front ++ rear.reverse`. Enqueue pushes onto the rear.
Dequeue pops the front when possible; otherwise it reverses the entire rear into the front
before popping. Reversal is only a mathematical description here: the machine implementation
executes a charged loop, moving one value at a time.

## Main definitions

* `spec`: the existing FIFO specification restricted to fitting words and a fixed capacity.
* `contents`: the FIFO sequence represented by a pair of stacks.
* `pairStep`: the corresponding transition of the two stacks.

## Main results

* `pairStep_correct`: both the returned answer and the new FIFO sequence match `spec`.
* `pairStep_length_le`: admissible calls preserve the shared capacity bound.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Exercise 10.1-6][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Queue

open Cslib.Algorithms.Lean.Queue

/-- A queue admits an enqueue exactly when it has spare capacity and the value fits a word. -/
abbrev spec (w capacity : ℕ) : DataStructure.StateTransitionSpec :=
  DataStructure.StateTransitionSpec.ofFn (queue ℕ).stepFn fun q o => match o with
    | .enqueue v => q.length < capacity ∧ Fits w v
    | .dequeue => True

/-- Front is in FIFO order; rear is in reverse FIFO order. -/
def contents (s : List ℕ × List ℕ) : List ℕ := s.1 ++ s.2.reverse

/-- Mathematical description of the machine's two-stack transition, including an empty pop. -/
def pairStep (s : List ℕ × List ℕ) (o : QueueOp ℕ) :
    (List ℕ × List ℕ) × (queue ℕ).Result o :=
  match o with
  | .enqueue v => ((s.1, v :: s.2), ())
  | .dequeue => match s.1 with
    | [] => ((s.2.reverse.tail, []), s.2.reverse.head?)
    | a :: front => ((front, s.2), some a)

/-- Projecting the concrete stack transition gives exactly the specified FIFO step. -/
theorem pairStep_correct (s : List ℕ × List ℕ) (o : QueueOp ℕ) :
    (contents (pairStep s o).1, (pairStep s o).2) = (queue ℕ).stepFn (contents s) o := by
  obtain ⟨front, rear⟩ := s
  cases o with
  | enqueue v => simp [pairStep, contents, queue, List.reverse_cons, List.append_assoc]
  | dequeue => cases front <;> simp [pairStep, contents, queue]

/-- The sum of live stack lengths is the FIFO length, not the size of the reserved regions. -/
theorem contents_length (s : List ℕ × List ℕ) :
    (contents s).length = s.1.length + s.2.length := by
  simp [contents]

/-- Enqueues require one spare slot; dequeues cannot increase the number of live values. -/
theorem pairStep_length_le {w capacity : ℕ} {s : List ℕ × List ℕ}
    (hs : (contents s).length ≤ capacity) (o : QueueOp ℕ)
    (hv : (spec w capacity).valid (contents s) o) :
    (contents (pairStep s o).1).length ≤ capacity := by
  have hc := congrArg (fun p => p.1.length) (pairStep_correct s o)
  rw [hc]
  cases o with
  | enqueue v =>
    change (contents s ++ [v]).length ≤ capacity
    simp only [List.length_append, List.length_singleton]
    exact Nat.succ_le_of_lt hv.1
  | dequeue =>
    change (contents s).tail.length ≤ capacity
    simp only [List.length_tail]
    omega

end Cslib.WordRAM.Queue
