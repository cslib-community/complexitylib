/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorCall
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLocalEmission
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalPackedBounds

/-!
# Live worklist and Boolean fold for the Chan–He visitor

The proof state records pending native descriptors and the ordered nodes already consumed.
It does not assert a retained pointer table or packed catalogue. Pending arrays, stack,
bitmap and frontend prefix remain live below the fresh allocation frontier. The accumulator
is the disjunction of the exact mathematical inputs already supplied to the actual solver.

## Main definitions

* `Cursor`: pending entries and the ghost sequence of consumed nodes.
* `Cursor.Invariant`: live native readback, allocation budget and exact Boolean fold.
* `Cursor.credit`: remaining traversal work plus solver charges for emitted nodes only.

These are proof invariants for the existing native instructions, not runtime node encodings.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Mathematical proof state for the real native worklist; consumed nodes need no retained table. -/
structure Cursor where
  /-- Top-first native records and their exact represented lists. -/
  pending : List ChanHe.Traversal.Entry
  /-- Nodes already passed to the solver, including their order and multiplicity. -/
  consumed : List Node

/-- Remaining native transitions, including empty and zero-fuel entries. -/
@[expose] def Cursor.work (s : Cursor) : ℕ :=
  ChanHe.Traversal.Math.potential (s.pending.map ChanHe.Traversal.Entry.task)

/-- Exact ordered mathematical calls still pending. -/
@[expose] def Cursor.remaining (s : Cursor) (a : ChanHe.Traversal.Arena) : List Node :=
  ChanHe.Traversal.Math.output (Nat.primesLE a.m) a.Λ
    (s.pending.map ChanHe.Traversal.Entry.task)

/-- Charge traversal work on every entry and solver work only on actual node emissions. -/
@[expose] def Cursor.credit (s : Cursor) (a : ChanHe.Traversal.Arena) (T : ℕ) : ℕ :=
  s.work * (ChanHe.Traversal.visitTime a.n a.m a.N + 316) + (s.remaining a).length * T

/-- Live readback and the ordered Boolean fold at the actual native loop header. -/
structure Cursor.Invariant {r : ℕ} (a : ChanHe.Traversal.Arena) (w κ n : ℕ)
    (target : List Node) (s : Cursor) (x : Data (registerCount r)) : Prop where
  /-- Every actual native word fits, including arbitrary used solver scratch. -/
  bounded : x.Bounded (w + 2)
  /-- Persistent traversal parameters survive. -/
  controls : a.Controls (x.comap (preprocessingRegisters r))
  /-- The actual prime bitmap remains available. -/
  bitmap : a.Bitmap x.mem
  /-- The actual stack serializes exactly the pending records. -/
  stack : ChanHe.Traversal.WordStack.Rep (w + 2) a.stack a.capacity
    (s.pending.flatMap ChanHe.Traversal.Entry.words)
    ((x.comap (preprocessingRegisters r)).comap ChanHe.Traversal.registers)
  /-- The fixed stack capacity follows from recursion depth. -/
  depth : ChanHe.Traversal.Math.Bounded a.fuel
    (s.pending.map ChanHe.Traversal.Entry.task)
  /-- Current sets satisfy the finite reduction's existing promises. -/
  valid : ∀ e ∈ s.pending, e.Valid a.n a.U
  /-- Every pending source is read back from actual current memory. -/
  stored : ∀ e ∈ s.pending, e.Stored x.mem
  /-- Live sources avoid the reserved stack gap. -/
  around : ∀ e ∈ s.pending, e.Around a.stack (a.floor - a.stack)
  /-- All pending source cells precede the fresh allocation. -/
  ends : ∀ e ∈ s.pending, ∀ j,
    e.source j + (e.data j).length ≤ x.regs (preprocessingRegisters r ChanHe.Traversal.heap)
  /-- The allocation frontier stays above the reserved gap. -/
  floor : a.floor ≤ x.regs (preprocessingRegisters r ChanHe.Traversal.heap)
  /-- Unfinished native work reserves the remaining heavy/node allocations. -/
  heapBudget : x.regs (preprocessingRegisters r ChanHe.Traversal.heap) +
    s.work * ChanHe.Traversal.allocationSize a.n a.m a.N ≤ a.ceiling
  /-- The saved common packed length is actual runtime metadata. -/
  packedLength : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = 4 * a.N
  /-- The value envelope was computed from the original input length. -/
  envelopeValue : x.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ
  /-- Boolean accumulation uses the actual native constant one. -/
  unit : x.regs (controllerRegisters r one) = 1
  /-- The accumulator is a raw Boolean. -/
  boolean : x.regs (controllerRegisters r answer) ≤ 1
  /-- Exact disjunction of the calls already executed. -/
  verdict : x.regs (controllerRegisters r answer) = 1 ↔
    ∃ node ∈ s.consumed, Cslib.Algorithms.ThreeSum.Convolution (4 * a.N) (node.oneArray a.U)
  /-- Consumed prefix and pending recursion retain the complete original preorder. -/
  exactOutput : s.consumed ++ s.remaining a = target
  /-- Original frontend/source cells survive for every later root. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- A live native stack condition requires a nonempty semantic worklist. -/
theorem Cursor.Invariant.nonempty {r w κ n : ℕ} {a : ChanHe.Traversal.Arena}
    {target : List Node} {s : Cursor} {x : Data (registerCount r)}
    (h : s.Invariant a w κ n target x)
    (hc : (Cond.lt (preprocessingRegisters r ChanHe.Traversal.zero)
      (preprocessingRegisters r (ChanHe.Traversal.registers
        ChanHe.Traversal.WordStack.len))).Holds x) : s.pending ≠ [] := by
  intro he
  have hz := h.controls.2.2.2.2.2.2.2.2.2.1
  have hl := h.stack.length_eq
  change x.regs (preprocessingRegisters r ChanHe.Traversal.zero) = 0 at hz
  change x.regs (preprocessingRegisters r (ChanHe.Traversal.registers
    ChanHe.Traversal.WordStack.len)) = (s.pending.flatMap ChanHe.Traversal.Entry.words).length at hl
  change x.regs (preprocessingRegisters r ChanHe.Traversal.zero) <
    x.regs (preprocessingRegisters r (ChanHe.Traversal.registers
      ChanHe.Traversal.WordStack.len)) at hc
  simp only [he, List.flatMap_nil, List.length_nil] at hl
  omega

/-- Exhausting the actual stack completes the entire ordered fold. -/
theorem Cursor.Invariant.finished {r w κ n : ℕ} {a : ChanHe.Traversal.Arena}
    {target : List Node} {s : Cursor} {x : Data (registerCount r)}
    (h : s.Invariant a w κ n target x)
    (hc : ¬(Cond.lt (preprocessingRegisters r ChanHe.Traversal.zero)
      (preprocessingRegisters r (ChanHe.Traversal.registers
        ChanHe.Traversal.WordStack.len))).Holds x) :
    s.pending = [] ∧ s.consumed = target := by
  have hz := h.controls.2.2.2.2.2.2.2.2.2.1
  have hl := h.stack.length_eq
  change x.regs (preprocessingRegisters r ChanHe.Traversal.zero) = 0 at hz
  change x.regs (preprocessingRegisters r (ChanHe.Traversal.registers
    ChanHe.Traversal.WordStack.len)) = (s.pending.flatMap ChanHe.Traversal.Entry.words).length at hl
  rw [ChanHe.Traversal.length_serialized] at hl
  change ¬x.regs (preprocessingRegisters r ChanHe.Traversal.zero) <
    x.regs (preprocessingRegisters r (ChanHe.Traversal.registers
      ChanHe.Traversal.WordStack.len)) at hc
  have he : s.pending = [] := List.eq_nil_of_length_eq_zero (by omega)
  refine ⟨he, ?_⟩
  simpa only [Cursor.remaining, he, List.map_nil, ChanHe.Traversal.Math.output,
    List.flatMap_nil, List.append_nil] using h.exactOutput

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
