/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Queue.WordRAM.Model
public import Complexity.DataStructure.Stack.Memory
public import Complexity.Foundations.Analysis.Asymptotics.CostBound

/-!
# A queue over two array stacks over the memory oracle

The bounded FIFO queue `Queue.WordRAM.spec w C` is implemented in two refinement steps, each
proved once:

1. `refinement`: the two-stack queue `Queue.methods` over a pair of bounded stacks. It reuses the
   queue's existing methods and their behavior (`Queue.stepFn_methods`) and potential argument
   (`Queue.potential_step`); only the capacity and word-fit admissibility of the bounded stacks is
   new. Each queue operation costs at most three stack calls, amortized, with two credits per
   rear element.
2. `Stack.Memory.pairRefinement`: two array stacks with disjoint layouts over `Memory.spec w`,
   each stack call costing at most three memory units.

`memRefinement` composes them, and `mem_amortized` stacks the potentials across the composition
(`Refinement.Amortized.comp`): every queue operation costs at most nine memory units, amortized,
with six credits per rear element. `run` allocates the two stacks and then runs a queue client;
`run_correct` and `run_cost` state its result and its exact memory cost from any well-formed memory,
and `run_cost_isBigO` exports the cost as `O(m)` in the number `m` of queue operations.

The machine-level counterpart is `Queue.WordRAM`, whose dispatcher is hand-stepped instruction by
instruction. Here the proofs mention neither registers nor instructions; executing the memory
programs on the word RAM is the separate realization step of #2205.

## Main definitions

* `boundedStacks`: the pair of bounded stacks.
* `Inv`: a FIFO list within capacity holding words.
* `refinement`: the two-stack queue over the pair of bounded stacks.
* `memRefinement`: the queue over two array stacks over memory.
* `run`: allocate the stacks, then run a queue client.

## Main results

* `amortized`: three stack calls per queue operation, with two credits per rear element.
* `mem_amortized`: nine memory units per queue operation, with six credits per rear element.
* `run_correct`, `run_cost`: the allocated queue answers like the specification and costs at
  most `6 + 9 m` memory units for `m` queue operations.
* `run_cost_isBigO`: the same cost as `O(m)`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Exercise 10.1-6 and Chapter 17][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.Memory

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Queue

/-- Two bounded stacks of capacity `C` at word size `w`. -/
abbrev boundedStacks (w C : ℕ) : StateTransitionSpec :=
  product (Stack.WordRAM.spec w C) (Stack.WordRAM.spec w C)

/-- A FIFO list within capacity `C` whose entries fit a `w`-bit word. -/
structure Inv (w C : ℕ) (q : List ℕ) : Prop where
  /-- The list is within capacity. -/
  length_le : q.length ≤ C
  /-- Every entry fits a word. -/
  fits : ∀ x ∈ q, Fits w x

namespace Inv

variable {w C : ℕ}

/-- Admissible FIFO steps keep the list within capacity and made of words. -/
theorem step {q : List ℕ} (h : Inv w C q) {o : QueueOp ℕ}
    (hv : (Queue.WordRAM.spec w C).valid q o) : Inv w C ((queue ℕ).stepFn q o).1 := by
  cases o with
  | enqueue n =>
    obtain ⟨hlen, hfit⟩ := hv
    refine ⟨by simp; omega, fun x hx => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h.fits x hx
    · exact hfit
  | dequeue =>
    exact ⟨by simp; have := h.length_le; omega, fun x hx => h.fits x (List.mem_of_mem_tail hx)⟩

end Inv

variable {w C : ℕ}

/-- The bounded stacks step exactly as the unbounded ones; only admissibility differs. -/
theorem runClient_boundedStacks {β : Type} (s : List ℕ × List ℕ) (p : (stackPair ℕ).Client β) :
    (boundedStacks w C).runClient s p = (stackPair ℕ).runClient s p := by
  induction p generalizing s with
  | pure a => rfl
  | liftBind o k ih =>
    have hstep : (boundedStacks w C).stepFn s o = (stackPair ℕ).stepFn s o := by cases o <;> rfl
    simp only [StateTransitionSpec.runClient_liftBind, hstep, ih]

/-- Moving the rear into the front is admissible for bounded stacks when both fit together and
the rear holds words. -/
theorem validHistory_transferTrace {front back : List ℕ} (hlen : front.length + back.length ≤ C)
    (hfit : ∀ x ∈ back, Fits w x) : (boundedStacks w C).ValidHistory (front, back) (transferTrace back) := by
  induction back generalizing front with
  | nil => trivial
  | cons a back ih =>
    simp only [List.length_cons] at hlen
    refine ⟨trivial, ⟨by simp only; omega, hfit a (by simp)⟩, ?_⟩
    exact ih (front := a :: front) (by simp only [List.length_cons]; omega)
      fun x hx => hfit x (by simp [hx])

/-- The two-stack queue over a pair of bounded stacks: the stacks represent `front ++ rear⁻¹`. -/
def refinement (w C : ℕ) : Refinement (Queue.WordRAM.spec w C) (boundedStacks w C) :=
  Refinement.ofFn (methods (α := ℕ)) (fun s => Inv w C (Queue.WordRAM.contents s))
    Queue.WordRAM.contents
    (by
      rintro ⟨front, back⟩ o hs hv
      have hlen := hs.length_le
      simp only [Queue.WordRAM.contents, List.length_append, List.length_reverse] at hlen
      cases o with
      | enqueue n =>
        obtain ⟨hq, hfit⟩ := hv
        simp only [Queue.WordRAM.contents, List.length_append, List.length_reverse] at hq
        exact ⟨⟨by omega, hfit⟩, trivial⟩
      | dequeue =>
        cases front with
        | cons a front => exact ⟨trivial, trivial⟩
        | nil =>
          change (boundedStacks w C).ValidHistory ([], back)
            ((boundedStacks w C).runClient ([], back) (methods .dequeue)).2.2
          rw [runClient_boundedStacks, runClient_dequeue_nil]
          refine ⟨trivial, trivial, ?_⟩
          rw [StateTransitionSpec.validHistory_append]
          refine ⟨validHistory_transferTrace (by simpa using hlen) fun x hx =>
            hs.fits x (by simp [Queue.WordRAM.contents, hx]), trivial, trivial⟩)
    (by
      rintro ⟨front, back⟩ o hs hv
      have h := stepFn_methods front back o
      refine ⟨h, ?_⟩
      have hstep := hs.step hv
      rw [show Queue.WordRAM.contents (front, back) = front ++ back.reverse from rfl, h] at hstep
      exact hstep)

/-- Each queue operation costs at most three stack calls, amortized, with two credits per rear
element. -/
theorem amortized :
    (refinement w C).Amortized (fun _ _ => 1) (fun _ _ => 3) fun s => 2 * s.2.length :=
  Refinement.Amortized.ofFn fun {s} o _ _ => by
    have h := potential_step s o
    rw [← runClient_boundedStacks (w := w) (C := C)] at h
    rw [StateTransitionSpec.totalCost_one]
    exact h

/-! ## Over memory -/

/-- The queue over two array stacks over memory. -/
def memRefinement {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) :
    Refinement (Queue.WordRAM.spec w C) (Memory.spec w) :=
  (refinement w C).comp (Stack.Memory.pairRefinement h₁ h₂ hd)

/-- **Stacked potentials.** Every queue operation costs at most nine memory units, amortized,
with six credits per element of the rear stack: the queue's potential, at three memory units per
stack call, read through the stacks' abstraction. -/
theorem mem_amortized {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C)
    (hd : Disjoint L₁.footprint L₂.footprint) :
    (memRefinement h₁ h₂ hd).Amortized charge (fun _ _ => 9)
      fun s => 6 * (Stack.Memory.abs L₂ s).length := by
  have h := (amortized.mul_left 3).comp (Stack.Memory.pair_amortized h₁ h₂ hd)
  have hΦ : (fun s : Memory.State =>
      3 * (2 * (Stack.Memory.abs L₂ s).length) + 0) =
        fun s => 6 * (Stack.Memory.abs L₂ s).length := by
    funext s
    omega
  exact hΦ ▸ h

end Cslib.DataStructure.Queue.Memory
