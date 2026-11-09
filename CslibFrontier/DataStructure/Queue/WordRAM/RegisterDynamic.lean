/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterExecution

/-!
# Adaptive clients of the realized resident queue

The existing dynamic certificate supplies correctness and the generic resource theorem
telescopes the actual native instruction counts with the terminal rear potential. The operation
program, register file and exchange factor precede widths, layouts, dirty memory and adaptive
clients. Initialization is a literal base/capacity code family, fixed before width and entry data;
its six instructions change no physical memory cell. The client controller and external
tag/payload delivery keep the original calling boundary.

## Main results

* `amortized`, `run_client`, `run_initialized`: native adaptive execution and resource bounds.
* `modifies`, `frame`: the original two-array footprint and disjoint heap assertions.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM

open Cslib.WordRAM Cslib.WordRAM.Realization
open RegisterMetadata

/-- Both reserved arrays together contain exactly twice the capacity in cells. -/
theorem footprint_card (base capacity : ℕ) : (footprint base capacity).card = 2 * capacity :=
  Block.card_footprint _

/-- The expensive native transfer consumes the scaled rear credit. Both branches include
their control, count commits and final halt in this globally constant per-call charge. -/
theorem amortized {w base capacity : ℕ} (h1 : Fits w 1) :
    DataStructure.Amortized (certificate (base := base) (capacity := capacity) h1).impl
      DynamicProgram.OperationTrace.instructions (fun _ x => potential x)
      (fun _ _ => 4 * Backend.factor family + 6) :=
  DataStructure.Amortized.ofFn fun hr hv he => by
    obtain ⟨front, back, rfl, hr⟩ := hr
    obtain ⟨z, n, hz, _, _, _, hp⟩ := execute h1 hr _ hv
    obtain ⟨rfl, hn⟩ := he.eq_of_exec hz
    rw [hn]
    exact hp

/-- Every admissible adaptive client has a correct native execution with terminal potential
retained. This sums calls of the fixed program, without charging a host controller as RAM. -/
theorem run_client {w base capacity : ℕ} (h1 : Fits w 1) {α : Type}
    (p : (spec w capacity).Client α) {q : List ℕ} {x : Data registers}
    (hr : QueueRep w base capacity q x)
    (hv : (spec w capacity).ValidHistory q ((spec w capacity).runClient q p).2.2) :
    ∃ y traces, DataStructure.Executes ((implementation w capacity).ExecOp w) p x
        ((spec w capacity).runClient q p).1 y traces ∧
      QueueRep w base capacity ((spec w capacity).runClient q p).2.1 y ∧
      DataStructure.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        ((spec w capacity).runClient q p).2.2.length * (4 * Backend.factor family + 6) +
          potential x :=
  (amortized h1).exists_executes_const p hr hv

/-- Starting from arbitrary bounded dirty data, the actual six initializer instructions
establish zero rear credit. The physical end-fit domain is exactly the original `base+2*C`.
No clearing, installed frontier or zero-memory premise is needed. -/
theorem run_initialized {w base capacity : ℕ} (h1 : Fits w 1)
    (hc : Fits w (base + 2 * capacity)) {α : Type} (p : (spec w capacity).Client α)
    {x : Data registers} (hx : x.Bounded w)
    (hv : (spec w capacity).ValidHistory [] ((spec w capacity).runClient [] p).2.2) :
    ∃ ready y traces, Exec w (initializeCode base capacity) x ready 6 ∧
      DataStructure.Executes ((implementation w capacity).ExecOp w) p ready
        ((spec w capacity).runClient [] p).1 y traces ∧
      QueueRep w base capacity ((spec w capacity).runClient [] p).2.1 y ∧
      6 + DataStructure.total DynamicProgram.OperationTrace.instructions traces + potential y ≤
        6 + ((spec w capacity).runClient [] p).2.2.length * (4 * Backend.factor family + 6) := by
  have hr := initialized_rep hx hc
  have hp : potential (initialized base capacity x) = 0 := by
    simp only [potential, hr.backLen_eq, List.length_nil, Nat.mul_zero]
  obtain ⟨y, traces, he, hy, hb⟩ := run_client (q := []) h1 p ⟨[], [], rfl, hr⟩ hv
  exact ⟨initialized base capacity x, y, traces, (initialize_exec hx hc).1,
    he, hy, by omega⟩

/-- Actual native queue calls modify only the original two reserved array regions. -/
theorem modifies {w base capacity : ℕ} (h1 : Fits w 1)
    {q : List ℕ} {x y : Data registers} {o : Queue.QueueOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : QueueRep w base capacity q x) (hv : (spec w capacity).valid q o)
    (he : (implementation w capacity).ExecOp w x o a y trace) :
    Modifies (footprint base capacity) x.mem y.mem := by
  obtain ⟨front, back, rfl, hr⟩ := hr
  obtain ⟨z, n, hz, _, _, hf, _⟩ := execute h1 hr o hv
  exact (he.eq_of_exec hz).1 ▸ hf

/-- Disjoint heap assertions survive every call, including the native reversal. This is
the original physical-memory frame, not a claim about another structure's frontier invariant. -/
theorem frame {w base capacity : ℕ} (h1 : Fits w 1)
    {q : List ℕ} {x y : Data registers} {o : Queue.QueueOp ℕ}
    {a : (spec w capacity).Result o} {trace : DynamicProgram.OperationTrace}
    (hr : QueueRep w base capacity q x) (hv : (spec w capacity).valid q o)
    (he : (implementation w capacity).ExecOp w x o a y trace)
    {Q : HeapAssertion} (hQ : Q.holds x.mem)
    (hd : Disjoint Q.footprint (footprint base capacity)) : Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies h1 hr hv he)

end Cslib.DataStructure.Queue.WordRAM
