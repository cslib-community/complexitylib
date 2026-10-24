/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Queue.Basic
public import Complexity.Foundations.Semantics.Stateful.Amortized

/-!
# Correctness and amortized instruction cost of a RAM queue

The mathematical client sees only a FIFO list. The realization hides how that list is split
between the two arrays. A dequeue can move every rear element, but each enqueue deposits eight
credits: six instructions move an element and two instructions control that loop iteration.
Consequently every admissible history costs at most fourteen instructions per operation,
plus the initial rear credit. The final unused credit is retained in the inequality.

These are actual RAM operation instructions, including each call's halt. The operation interface
still uses externally delivered argument registers; arbitrary pure computation in a client's
Lean continuation is not included in this bound. Initialization is a separate six-instruction
program. The arrays reserve twice the queue capacity, while at most one capacity's worth of
values are live. No allocator or dynamically growing capacity is assumed.

## Main definitions

* `QueueRep`: the FIFO representation hiding the split into two stacks.
* `certificate`: a semantic realization of the bounded queue interface.
* `amortized`: the separate instruction-cost certificate with rear-stack potential.

## Main results

* `run_client`: correct adaptive execution and the amortized native instruction bound.
* `frame`: every operation preserves any disjoint heap assertion.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapters 10 and 17][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Queue

open Cslib.Algorithms.Lean.Queue

/-- The two reserved blocks contain exactly twice the queue capacity in word cells. -/
theorem footprint_card (base capacity : ℕ) : (footprint base capacity).card = 2 * capacity :=
  Block.card_footprint _

/-- A client observes a FIFO list, while the machine retains a hidden split between two stacks. -/
def QueueRep (w base capacity : ℕ) (q : List ℕ) (x : Data 11) : Prop :=
  ∃ front back, q = contents (front, back) ∧ Rep w base capacity front back x

/-- The fixed dispatcher implements the bounded FIFO specification. -/
def certificate {w base capacity : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) :
    DynamicCertificate (implementation w capacity) w where
  rep := QueueRep w base capacity
  bounded h := by obtain ⟨_, _, _, hr⟩ := h; exact hr.bounded
  arguments_fit o hv i _ := arguments_fit h1 o hv i
  execute o hr hv := by
    obtain ⟨front, back, rfl, hr⟩ := hr
    obtain ⟨y, he, ha, hy, _⟩ := execute hc hr o hv
    have hs := pairStep_correct (front, back) o
    refine ⟨y, _, he, ?_, ?_⟩
    · exact ha.trans (congrArg some (congrArg Prod.snd hs))
    · exact ⟨_, _, (congrArg Prod.fst hs).symm, hy⟩

/-- The expensive transfer consumes eight credits per rear element, including loop control.
The final halt contributes the extra one in the left side. -/
private theorem bodyCost_potential (front back : List ℕ) (o : QueueOp ℕ) :
    bodyCost front back o + 1 + 8 * (pairStep (front, back) o).1.2.length ≤
      14 + 8 * back.length := by
  cases o with
  | enqueue v => simp only [bodyCost, pairStep, List.length_cons]; omega
  | dequeue => cases front <;> cases back <;>
      simp only [bodyCost, pairStep, List.cons_ne_nil, ↓reduceIte,
        List.length_nil, List.length_cons] <;> omega

/-- Every native operation has the exact charged body cost plus its final halt. -/
theorem instructions_eq {w base capacity : ℕ} (hc : Fits w (base + 2 * capacity))
    {front back : List ℕ} {x y : Data 11} {o : QueueOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : Rep w base capacity front back x)
    (hv : (spec w capacity).valid (contents (front, back)) o)
    (he : (implementation w capacity).ExecOp w x o a y trace) :
    trace.instructions = bodyCost front back o + 1 := by
  obtain ⟨z, hz, _, _, _⟩ := execute hc hr o hv
  exact (he.eq_of_exec hz).2

/-- Rear-stack credit is read from the concrete persistent length register. -/
def potential (x : Data 11) : ℕ := 8 * x.regs backLen

/-- Amortized constant instruction cost is certified separately from FIFO correctness. -/
theorem amortized {w base capacity : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) :
    Stateful.Amortized (certificate h1 hc).realization
      DynamicProgram.OperationTrace.instructions (fun _ x => potential x) (fun _ _ => 14) where
  step hr hv he := by
    obtain ⟨front, back, rfl, hr⟩ := hr
    obtain ⟨z, hz, _, hrz, _⟩ := execute hc hr _ hv
    obtain ⟨rfl, hn⟩ := he.eq_of_exec hz
    rw [hn]
    simpa only [potential, hr.backLen_eq, hrz.backLen_eq] using
      bodyCost_potential front back _

/-- Every admissible adaptive client has a correct native execution with a telescoping bound.
This sums operation calls; the externally supplied client controller is not machine code. -/
theorem run_client {w base capacity : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) {α : Type} (p : (spec w capacity).Client α)
    {q : List ℕ} {x : Data 11} (hr : QueueRep w base capacity q x)
    (hv : (spec w capacity).ValidHistory q ((spec w capacity).runClient q p).2.2) :
    ∃ y traces, Stateful.Executes ((implementation w capacity).ExecOp w) p x
        ((spec w capacity).runClient q p).1 y traces ∧
      QueueRep w base capacity ((spec w capacity).runClient q p).2.1 y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        ((spec w capacity).runClient q p).2.2.length * 14 + potential x :=
  (amortized h1 hc).exists_executes_const p hr hv

/-- Starting with arbitrary bounded data, charge the six initialization instructions before
summing the actual queue calls. Empty regions need no zeroing; controller computation and
external argument delivery retain the boundary stated in `run_client`. -/
theorem run_initialized {w base capacity : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) {α : Type} (p : (spec w capacity).Client α)
    {x : Data 11} (hx : x.Bounded w)
    (hv : (spec w capacity).ValidHistory [] ((spec w capacity).runClient [] p).2.2) :
    ∃ ready y traces, Exec w (initializeCode base capacity) x ready 6 ∧
      Stateful.Executes ((implementation w capacity).ExecOp w) p ready
        ((spec w capacity).runClient [] p).1 y traces ∧
      QueueRep w base capacity ((spec w capacity).runClient [] p).2.1 y ∧
      6 + Stateful.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        6 + ((spec w capacity).runClient [] p).2.2.length * 14 := by
  obtain ⟨ready, hi, hr, _⟩ := initialize_exec hx h1 hc
  have hp : potential ready = 0 := by simp [potential, hr.backLen_eq]
  obtain ⟨y, traces, he, hy, hb⟩ := run_client (q := []) h1 hc p ⟨[], [], rfl, hr⟩ hv
  exact ⟨ready, y, traces, hi, he, hy, by omega⟩

/-- Actual queue calls modify only the two reserved array regions. -/
theorem modifies {w base capacity : ℕ}
    (hc : Fits w (base + 2 * capacity)) {q : List ℕ} {x y : Data 11} {o : QueueOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : QueueRep w base capacity q x) (hv : (spec w capacity).valid q o)
    (he : (implementation w capacity).ExecOp w x o a y trace) :
    Modifies (footprint base capacity) x.mem y.mem := by
  obtain ⟨front, back, rfl, hr⟩ := hr
  obtain ⟨z, hz, _, _, hf⟩ := execute hc hr o hv
  exact (he.eq_of_exec hz).1 ▸ hf

/-- Disjoint heap representations survive every queue call, including a full rear transfer. -/
theorem frame {w base capacity : ℕ}
    (hc : Fits w (base + 2 * capacity)) {q : List ℕ} {x y : Data 11} {o : QueueOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : QueueRep w base capacity q x) (hv : (spec w capacity).valid q o)
    (he : (implementation w capacity).ExecOp w x o a y trace)
    {Q : HeapAssertion} (hQ : Q.holds x.mem)
    (hd : Disjoint Q.footprint (footprint base capacity)) : Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies hc hr hv he)

end Cslib.WordRAM.Queue
