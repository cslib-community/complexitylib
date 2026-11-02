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
2. Two array stacks allocated one after the other, as the generic product
   `Memory.Allocator.prod` of two stack allocators, each stack call costing at most three memory
   units.

`allocator` puts the first step on top of the second (`Memory.Allocator.comp`), and
`amortized_allocator` stacks the potentials across the composition: every queue operation costs
at most nine memory units, amortized, with six credits per rear element. `run` allocates the two
stacks and then runs a queue client. From any memory with room for both stacks, `run_correct`
gives its answer and the admissibility of its memory operations, `run_cost` bounds its memory
cost by `6 + 9 m` for `m` queue operations, and `run_cost_isBigO` exports that bound as `O(m)`.
All three are instances of the generic theorems of `Memory.Allocator`, so this file has no setup
proof of its own.

The machine-level counterpart is `Queue.WordRAM`, whose dispatcher is hand-stepped instruction by
instruction. Here the proofs mention neither registers nor instructions. Executing the memory
programs on the word RAM is a separate, generic realization step, which this file does not
provide.

## Main definitions

* `boundedStacks`: the pair of bounded stacks.
* `Inv`: a FIFO list within capacity holding words.
* `refinement`: the two-stack queue over the pair of bounded stacks.
* `allocator`: the queue over two array stacks, allocated in memory.
* `run`: allocate the stacks, then run a queue client.

## Main results

* `runClient_boundedStacks`: bounded stacks run clients exactly as unbounded ones.
* `amortized`: three stack calls per queue operation, with two credits per rear element.
* `amortized_allocator`: nine memory units per queue operation, with six credits per rear
  element.
* `run_correct`, `run_cost`: the allocated queue answers like the specification and costs at
  most `6 + 9 m` memory units for `m` queue operations.
* `run_cost_glue`: with glue charged per memory operation, at most `(2 K + 1) (6 + 9 m)`.
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

/-- The final state of a client of the bounded stacks. -/
theorem clientState_boundedStacks {β : Type} (s : List ℕ × List ℕ)
    (p : (stackPair ℕ).Client β) :
    (boundedStacks w C).clientState s p = (stackPair ℕ).clientState s p := by
  simp only [StateTransitionSpec.clientState, runClient_boundedStacks]

/-- The result of a client of the bounded stacks. -/
theorem clientResult_boundedStacks {β : Type} (s : List ℕ × List ℕ)
    (p : (stackPair ℕ).Client β) :
    (boundedStacks w C).clientResult s p = (stackPair ℕ).clientResult s p := by
  simp only [StateTransitionSpec.clientResult, runClient_boundedStacks]

/-- The history of a client of the bounded stacks. -/
theorem clientHistory_boundedStacks {β : Type} (s : List ℕ × List ℕ)
    (p : (stackPair ℕ).Client β) :
    (boundedStacks w C).clientHistory s p = (stackPair ℕ).clientHistory s p := by
  simp only [StateTransitionSpec.clientHistory, runClient_boundedStacks]

/-- Moving the rear into the front is admissible for bounded stacks when both fit together and
the rear holds words. -/
theorem validHistory_transferTrace {front back : List ℕ} (hlen : front.length + back.length ≤ C)
    (hfit : ∀ x ∈ back, Fits w x) :
    (boundedStacks w C).ValidHistory (front, back) (transferTrace back) := by
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
        refine ⟨⟨?_, hfit⟩, trivial⟩
        change back.length < C
        omega
      | dequeue =>
        cases front with
        | cons a front => exact ⟨trivial, trivial⟩
        | nil =>
          rw [clientHistory_boundedStacks, StateTransitionSpec.clientHistory,
            runClient_dequeue_nil]
          refine ⟨trivial, trivial, ?_⟩
          rw [StateTransitionSpec.validHistory_append]
          refine ⟨validHistory_transferTrace (by simpa using hlen) fun x hx =>
            hs.fits x (by simp [Queue.WordRAM.contents, hx]), trivial, trivial⟩)
    (by
      rintro ⟨front, back⟩ o hs hv
      have h := stepFn_methods front back o
      rw [clientState_boundedStacks, clientResult_boundedStacks]
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
    change (boundedStacks w C).totalCost (fun _ _ => 1) s
        ((boundedStacks w C).clientHistory s (methods o)) +
        2 * ((boundedStacks w C).clientState s (methods o)).2.length ≤ 3 + 2 * s.2.length
    rw [StateTransitionSpec.totalCost_one, clientHistory_boundedStacks, clientState_boundedStacks]
    exact h

/-! ## Over memory -/

/-- The queue over two array stacks of capacity `C`: allocate the stacks one after the other,
and run the two-stack queue on their product. -/
def allocator (w C : ℕ) : Allocator (Queue.WordRAM.spec w C) w :=
  ((Stack.Memory.allocator w C).prod (Stack.Memory.allocator w C)).comp (refinement w C)
    (show Inv w C [] from ⟨Nat.zero_le C, fun _ h => absurd h List.not_mem_nil⟩)

/-- The allocated queue is empty. -/
@[simp] theorem init_allocator : (allocator w C).init = [] := rfl

/-- The two stacks take `2 (C + 1)` cells. -/
@[simp] theorem room_allocator : (allocator w C).room = 2 * (C + 1) := by
  change (C + 1) + (C + 1) = _
  omega

/-- The two stacks are allocated from scratch, so the allocation needs nothing of the memory
besides room. -/
theorem pre_allocator (s : Memory.State) : (allocator w C).Pre s :=
  ⟨trivial, trivial, Finset.disjoint_empty_left _⟩

/-- **Stacked potentials.** Every queue operation costs at most nine memory units, amortized,
with six credits per element of the rear stack: the queue's potential, at three memory units per
stack call, read through the stacks' abstraction. Allocation leaves no potential. -/
theorem amortized_allocator : (allocator w C).Amortized (fun _ _ => 9) 0 := by
  have hpair := (Stack.Memory.amortized_allocator (w := w) (C := C)).prod
    (Stack.Memory.amortized_allocator (w := w) (C := C))
  rw [productCharge_const] at hpair
  exact Allocator.Amortized.comp (amortized.mul_left 3) hpair

/-- Allocate two empty stacks of capacity `C`, then run a queue client on them. -/
def run (w C : ℕ) {β : Type} (p : (Queue.WordRAM.spec w C).Client β) : Prog β :=
  (allocator w C).run p

/-- **Correctness.** From any memory with room for both stacks, an admissible queue client run
over two freshly allocated array stacks issues only admissible memory operations and returns the
specified answer. -/
theorem run_correct {β : Type} (p : (Queue.WordRAM.spec w C).Client β) {s : Memory.State}
    (hfit : Fits w (s.frontier + 2 * (C + 1)))
    (hv : (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (run w C p)) ∧
      (Memory.spec w).clientResult s (run w C p) = (Queue.WordRAM.spec w C).clientResult [] p :=
  have ⟨hvE, hres, _⟩ := (allocator w C).run_correct p (pre_allocator s) (room_allocator ▸ hfit) hv
  ⟨hvE, hres⟩

/-- **Cost.** The same run costs at most `6 + 9 m` memory units for a client of `m` queue
operations: six for the two allocations and nine per operation, amortized. -/
theorem run_cost {β : Type} (p : (Queue.WordRAM.spec w C).Client β) {s : Memory.State}
    (hfit : Fits w (s.frontier + 2 * (C + 1)))
    (hv : (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)) :
    (Memory.spec w).totalCost charge s ((Memory.spec w).clientHistory s (run w C p)) ≤
      6 + 9 * ((Queue.WordRAM.spec w C).clientHistory [] p).length :=
  Allocator.run_cost_le amortized_allocator p (pre_allocator s) (room_allocator ▸ hfit) hv

/-- **Cost with glue.** A realization also charges the glue that runs after each memory operation.
If that glue costs at most `K` times the operation's charge plus `K`, the run costs at most
`(2 K + 1) (6 + 9 m)` in memory charges and glue together. The queue's and the stacks' methods
are straight-line code between memory operations, so their glue is of this form. -/
theorem run_cost_glue {β : Type} (p : (Queue.WordRAM.spec w C).Client β) {s : Memory.State}
    (hfit : Fits w (s.frontier + 2 * (C + 1)))
    (hv : (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p))
    {glue : Memory.State → Memory.Op → ℕ} {K : ℕ}
    (hglue : ∀ s o, glue s o ≤ K * (charge s o + 1)) :
    (Memory.spec w).totalCost (fun s o => charge s o + glue s o) s
        ((Memory.spec w).clientHistory s (run w C p)) ≤
      (2 * K + 1) * (6 + 9 * ((Queue.WordRAM.spec w C).clientHistory [] p).length) :=
  ((Memory.spec w).totalCost_glue_le one_le_charge hglue s _).trans
    (Nat.mul_le_mul_left _ (run_cost p hfit hv))

/-- **The exported form.** Over admissible clients, the memory cost of a run is `O(m)` in the
number `m` of queue operations. -/
theorem run_cost_isBigO (s : Memory.State) (hfit : Fits w (s.frontier + 2 * (C + 1))) :
    CostIsBigO Filter.atTop (fun m : ℕ => (m : ℝ))
      (fun p : {p : (Queue.WordRAM.spec w C).Client Unit //
          (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)} =>
        ((Queue.WordRAM.spec w C).clientHistory [] p.1).length)
      (fun p => (Memory.spec w).totalCost charge s
        ((Memory.spec w).clientHistory s (run w C p.1))) :=
  Allocator.run_cost_isBigO amortized_allocator (pre_allocator s) (room_allocator ▸ hfit)

end Cslib.DataStructure.Queue.Memory
