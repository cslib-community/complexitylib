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
with six credits per rear element. `run` allocates the two stacks and then runs a queue client.
From any memory with room for both stacks, `run_correct` gives its answer and the admissibility of
its memory operations, `run_cost` bounds its memory cost by `6 + 9 m` for `m` queue operations,
and `run_cost_isBigO` exports that bound as `O(m)`.

The machine-level counterpart is `Queue.WordRAM`, whose dispatcher is hand-stepped instruction by
instruction. Here the proofs mention neither registers nor instructions. Executing the memory
programs on the word RAM is a separate, generic realization step, which this file does not
provide.

## Main definitions

* `boundedStacks`: the pair of bounded stacks.
* `Inv`: a FIFO list within capacity holding words.
* `refinement`: the two-stack queue over the pair of bounded stacks.
* `memRefinement`, `memMethods`: the queue over two array stacks over memory, and its methods as
  plain memory programs.
* `run`: allocate the stacks, then run a queue client.

## Main results

* `runClient_boundedStacks`: bounded stacks run clients exactly as unbounded ones.
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

/-! ## Allocation and a whole run -/

/-- The queue methods over two array stacks, as plain memory programs. -/
def memMethods (L₁ L₂ : Stack.Memory.Layout) (w C : ℕ) :
    Methods (Queue.WordRAM.spec w C) (Memory.spec w) :=
  fun o => link (Stack.Memory.pairMethods L₁ L₂ w C) (methods o)

/-- The composite's methods are `memMethods`, whatever the proofs about the layouts. -/
theorem memRefinement_methods {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C)
    (h₂ : L₂.Valid w C) (hd : Disjoint L₁.footprint L₂.footprint) :
    (memRefinement h₁ h₂ hd).methods = memMethods L₁ L₂ w C := by
  funext o
  change link (Stack.Memory.pairRefinement h₁ h₂ hd).methods (methods o) = _
  rw [Stack.Memory.pairRefinement_methods]
  rfl

/-- Allocate two empty stacks of capacity `C`, then run a queue client on them. -/
def run (w C : ℕ) {β : Type} (p : (Queue.WordRAM.spec w C).Client β) : Prog β := do
  let L₁ ← Stack.Memory.allocLayout C
  let L₂ ← Stack.Memory.allocLayout C
  link (memMethods L₁ L₂ w C) p

/-- The first stack allocated from `s`. -/
abbrev frontLayout (s : Memory.State) (C : ℕ) : Stack.Memory.Layout :=
  ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, C⟩⟩

/-- The second stack allocated from `s`. -/
abbrev rearLayout (s : Memory.State) (C : ℕ) : Stack.Memory.Layout :=
  ⟨⟨s.frontier + 1 + C, 1⟩, ⟨s.frontier + 1 + C + 1, C⟩⟩

/-- The memory after both allocations. -/
abbrev allocated (s : Memory.State) (C : ℕ) : Memory.State :=
  ⟨clear (clear s.mem s.frontier 1) (s.frontier + 1 + C) 1, s.frontier + 1 + C + 1 + C⟩

/-- A run allocates both stacks, then runs the linked client from the allocated memory. -/
theorem runClient_run {β : Type} (p : (Queue.WordRAM.spec w C).Client β) (s : Memory.State) :
    (Memory.spec w).runClient s (run w C p) =
      let (v, s', os) := (Memory.spec w).runClient (allocated s C)
        (link (memMethods (frontLayout s C) (rearLayout s C) w C) p)
      (v, s', .alloc 1 :: .allocDirty C :: .alloc 1 :: .allocDirty C :: os) := rfl

/-- The facts that start the refinement after allocation. -/
private theorem setup (s : Memory.State) (hfit : Fits w (s.frontier + 2 * (C + 1))) :
    ∃ (h₁ : (frontLayout s C).Valid w C) (h₂ : (rearLayout s C).Valid w C)
      (hd : Disjoint (frontLayout s C).footprint (rearLayout s C).footprint),
      (memRefinement h₁ h₂ hd).inv (allocated s C) ∧
        (memRefinement h₁ h₂ hd).abs (allocated s C) = [] ∧
        Stack.Memory.abs (rearLayout s C) (allocated s C) = [] := by
  have h₁ : (frontLayout s C).Valid w C := Stack.Memory.valid_allocLayout (hfit.of_le (by omega))
  have h₂ : (rearLayout s C).Valid w C := Stack.Memory.valid_allocLayout (hfit.of_le (by omega))
  have hd : Disjoint (frontLayout s C).footprint (rearLayout s C).footprint := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Stack.Memory.Layout.footprint, Finset.mem_union, Block.mem_footprint,
      Block.Owns] at ha hb
    omega
  -- The first stack, as allocated, before the second allocation.
  obtain ⟨hi₁, ha₁⟩ := Stack.Memory.inv_allocLayout (C := C) s
  -- The second stack, allocated from the state after the first.
  obtain ⟨hi₂, ha₂⟩ := Stack.Memory.inv_allocLayout (C := C)
    ⟨clear s.mem s.frontier 1, s.frontier + 1 + C⟩
  -- The second allocation leaves the first stack's cells alone.
  have hframe : ∀ a ∈ (frontLayout s C).footprint,
      (allocated s C).mem a = clear s.mem s.frontier 1 a := by
    intro a ha
    simp only [Stack.Memory.Layout.footprint, Finset.mem_union, Block.mem_footprint,
      Block.Owns] at ha
    exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  have hi₁' := hi₁.congr h₁ hframe (by simp only; omega)
  have ha₁' := (Stack.Memory.abs_congr h₁ hi₁ hframe).trans ha₁
  refine ⟨h₁, h₂, hd, ⟨⟨hi₁', hi₂⟩, ?_⟩, ?_, ha₂⟩
  · change Inv w C (Queue.WordRAM.contents
      (Stack.Memory.abs (frontLayout s C) (allocated s C),
        Stack.Memory.abs (rearLayout s C) (allocated s C)))
    rw [ha₁', ha₂]
    exact ⟨by simp [Queue.WordRAM.contents], by simp [Queue.WordRAM.contents]⟩
  · change Queue.WordRAM.contents
      (Stack.Memory.abs (frontLayout s C) (allocated s C),
        Stack.Memory.abs (rearLayout s C) (allocated s C)) = []
    rw [ha₁', ha₂]
    rfl

/-- **Correctness.** From any memory with room for both stacks, an admissible queue client run
over two freshly allocated array stacks issues only admissible memory operations and returns the
specified answer. -/
theorem run_correct {β : Type} (p : (Queue.WordRAM.spec w C).Client β) {s : Memory.State}
    (hfit : Fits w (s.frontier + 2 * (C + 1)))
    (hv : (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (run w C p)) ∧
      (Memory.spec w).clientResult s (run w C p) = (Queue.WordRAM.spec w C).clientResult [] p := by
  obtain ⟨h₁, h₂, hd, hinv, habs, -⟩ := setup s hfit
  obtain ⟨hvE, hres, -, -⟩ :=
    (memRefinement h₁ h₂ hd).simulates_client p hinv (by rw [habs]; exact hv)
  rw [memRefinement_methods] at hvE hres
  simp only [StateTransitionSpec.clientHistory, StateTransitionSpec.clientResult,
    runClient_run] at hvE hres ⊢
  simp only [StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, step_alloc,
    step_allocDirty, valid_alloc, valid_allocDirty]
  refine ⟨⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
    hfit.of_le (by omega), hvE⟩, hres.trans (by rw [habs])⟩

/-- **Cost.** The same run costs at most `6 + 9 m` memory units for a client of `m` queue
operations: six for the two allocations and nine per operation, amortized. -/
theorem run_cost {β : Type} (p : (Queue.WordRAM.spec w C).Client β) {s : Memory.State}
    (hfit : Fits w (s.frontier + 2 * (C + 1)))
    (hv : (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)) :
    (Memory.spec w).totalCost charge s ((Memory.spec w).clientHistory s (run w C p)) ≤
      6 + 9 * ((Queue.WordRAM.spec w C).clientHistory [] p).length := by
  obtain ⟨h₁, h₂, hd, hinv, habs, hrear⟩ := setup s hfit
  have h := (mem_amortized h₁ h₂ hd).client p hinv (by rw [habs]; exact hv)
  rw [memRefinement_methods, habs, StateTransitionSpec.totalCost_const, hrear] at h
  simp only [StateTransitionSpec.clientHistory, runClient_run,
    StateTransitionSpec.totalCost_cons, charge_alloc, charge_allocDirty,
    StateTransitionSpec.stepFn, step_alloc, step_allocDirty] at h ⊢
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero, allocated] at h ⊢
  omega

/-- **The exported form.** Over admissible clients, the memory cost of a run is `O(m)` in the
number `m` of queue operations. -/
theorem run_cost_isBigO (s : Memory.State) (hfit : Fits w (s.frontier + 2 * (C + 1))) :
    CostIsBigO Filter.atTop (fun m : ℕ => (m : ℝ))
      (fun p : {p : (Queue.WordRAM.spec w C).Client Unit //
          (Queue.WordRAM.spec w C).ValidHistory [] ((Queue.WordRAM.spec w C).clientHistory [] p)} =>
        ((Queue.WordRAM.spec w C).clientHistory [] p.1).length)
      (fun p => (Memory.spec w).totalCost charge s
        ((Memory.spec w).clientHistory s (run w C p.1))) :=
  CostIsBigO.of_le_add_mul 6 9 fun p => run_cost p.1 hfit p.2

end Cslib.DataStructure.Queue.Memory
