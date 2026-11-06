/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorLoop
import Complexity.Computability.WordRAM.RegisterFrame
import Complexity.Computability.WordRAM.Call
import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers

import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalInitialize
import Complexity.Computability.WordRAM.Sequence

/-!
# Complete native root traversal with an in-place Convolution consumer

The actual stack initializer and seven-word root push enter the certified visitor loop.
The resulting Boolean folds the exact root preorder together with the previously consumed
prefix. No pointer-table readback or catalogue publication is required. The caller supplies
a local allocation ceiling, allowing later forest roots to retain their reserved space.

## Main definitions

* `RootInput`: actual descriptor, live memory and resource obligations before stack initialization.

## Main results

* `oneRoot_preserves`: all saved frontend and forest registers survive, including the counters.
* `root_exec`: actual complete root execution and its exact Boolean-fold invariant.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- Every saved frontend/forest scalar survives the entire root, even for opaque solver code. -/
theorem oneRoot_preserves {r : ℕ} (solver : Code .standard (r + 7))
    (i : Fin 128) (hi : 109 ≤ i.val) :
    (oneRoot solver).Preserves (preprocessingRegisters r i) := by
  let z := ChanHe.Traversal.zero
  let o := ChanHe.Traversal.one
  let ptr := registers WordStack.ptr
  let len := registers WordStack.len
  let stack := stackBase
  have hinit : ∀ i : Fin 128, 109 ≤ i.val →
      (ram[ z ← #0; o ← #1; ptr ← stack; len ← #0 ] :
        Code .standard 128).Preserves i := by decide
  have hpush : ∀ i : Fin 128, 109 ≤ i.val → pushFrame.Preserves i := by decide
  have hpop : ∀ i : Fin 128, 109 ≤ i.val → popFrame.Preserves i := by decide
  have hlocal : ∀ i : Fin 128, 109 ≤ i.val → localVisit.Preserves i := by decide
  have hchildren : ∀ i : Fin 128, 109 ≤ i.val → pushChildren.Preserves i := by decide
  have lift {code : Code .standard 128} (hp : code.Preserves i) :
      (code.rename (preprocessingRegisters r)).Preserves (preprocessingRegisters r i) :=
    Code.preserves_rename (preprocessing_injective r) hp
  have hskip : (Code.op (B := Basis.standard) (.copy
      (preprocessingRegisters r (slot 0)) (preprocessingRegisters r (slot 0)))).Preserves
        (preprocessingRegisters r i) := by
    simp only [Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    intro he
    have hv := congrArg Fin.val he
    simp only [preprocessingRegisters, Fin.val_castAdd] at hv
    dsimp only [slot] at hv
    omega
  have hprepare : (prepareHost (r := r)).Preserves (preprocessingRegisters r i) := by
    simp only [prepareHost, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    exact ⟨(preprocessing_ne_host i _).symm, (preprocessing_ne_host i _).symm,
      (preprocessing_ne_host i _).symm, (preprocessing_ne_host i _).symm⟩
  have hhost := (Host.bodyAt solver).preserves_rename_of_forall_ne (hostRegisters r)
    (preprocessingRegisters r i) (fun j => (preprocessing_ne_host i j).symm)
  have hreceive : (receive (r := r)).Preserves (preprocessingRegisters r i) := by
    simp only [receive, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    exact ⟨controller_ne_preprocessing answer i, controller_ne_preprocessing answer i⟩
  have hrelease : (releasePacked (r := r)).Preserves (preprocessingRegisters r i) := by
    simp only [releasePacked, Code.Preserves, Op.dest, ne_eq, Option.some.injEq]
    intro he
    have hv := congrArg Fin.val he
    simp only [preprocessingRegisters, Fin.val_castAdd, heap] at hv
    omega
  exact ⟨lift (hinit i hi), lift (hpush i hi), lift (hpop i hi), hskip, hskip, hskip, hskip,
    lift (hlocal i hi), ⟨hprepare, hhost, hreceive⟩, hrelease, lift (hchildren i hi)⟩

/-- Caller obligations for an actual root descriptor and its already accumulated Boolean fold. -/
structure RootInput {r : ℕ} (a : Arena) (w κ n : ℕ) (e : Entry) (ns : List Node)
    (x : Data (registerCount r)) : Prop where
  /-- All actual words already fit. -/
  bounded : x.Bounded (w + 2)
  /-- Persistent traversal parameters. -/
  controls : a.Controls (x.comap (preprocessingRegisters r))
  /-- The actual root metadata is loaded in the native descriptor registers. -/
  loaded : e.Loaded (x.comap (preprocessingRegisters r))
  /-- The three actual source blocks retain exact signed readback. -/
  stored : e.Stored x.mem
  /-- The existing reduction's cardinality, magnitude and duplicate-free promises. -/
  valid : e.Valid a.n a.U
  /-- The actual prime bitmap is ready. -/
  bitmap : a.Bitmap x.mem
  /-- Root sources avoid the complete reserved stack gap. -/
  around : e.Around a.stack (a.floor - a.stack)
  /-- Every root source ends below the fresh allocation. -/
  ends : ∀ j, e.source j + (e.data j).length ≤
    x.regs (preprocessingRegisters r heap)
  /-- Root fuel matches the reserved stack depth. -/
  fuel : e.fuel = a.fuel
  /-- Allocation starts above the reserved gap. -/
  floor : a.floor ≤ x.regs (preprocessingRegisters r heap)
  /-- This root's complete work retains its local allocation reservation. -/
  heapBudget : x.regs (preprocessingRegisters r heap) +
    Math.work e.fuel * allocationSize a.n a.m a.N ≤ a.ceiling
  /-- The common packed length remains actual metadata. -/
  packedLength : x.regs (preprocessingRegisters r ChanHe.Preprocessing.packedLength) = 4 * a.N
  /-- The value envelope was computed from the original ordinary input length. -/
  envelopeValue : x.regs (controllerRegisters r envelope) = (n + 2) ^ envelopeExponent κ
  /-- The actual Boolean accumulator constant. -/
  unit : x.regs (controllerRegisters r one) = 1
  /-- Raw Boolean accumulator. -/
  boolean : x.regs (controllerRegisters r answer) ≤ 1
  /-- The accumulator is exactly the disjunction of the previous calls. -/
  verdict : x.regs (controllerRegisters r answer) = 1 ↔
    ∃ node ∈ ns, Cslib.Algorithms.ThreeSum.Convolution (4 * a.N) (node.oneArray a.U)
  /-- The original frontend prefix is available for later roots. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- Initialize the actual stack and consume every native node of this root in exact preorder. -/
theorem root_exec {r κ n w : ℕ} {a : Arena} (c : Host.Callee r)
    (e : Entry) (ns : List Node) (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient n ≤ w + 2) (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w) (h : RootInput a w κ n e ns x) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ y, ExecWithin (w + 2) (oneRoot c.code) x y
        (70 + Math.work e.fuel * (visitTime a.n a.m a.N + 316) +
          (e.task.output (Nat.primesLE a.m) a.Λ).length * T) ∧
      (Cursor.mk [] (ns ++ e.task.output (Nat.primesLE a.m) a.Λ)).Invariant a w κ n
        (ns ++ e.task.output (Nat.primesLE a.m) a.Λ) y ∧
      (∀ p < a.stack, y.mem p = x.mem p) ∧
      ∀ i : Fin 128, 109 ≤ i.val →
        y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) := by
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  have hunsigned := Signed.unsigned_fits_of_signed hready.2.2
  have hsum := envelope_ge_sum a.ceiling a.n a.m a.Λ a.U a.N
  have h2 : Fits (w + 2) 2 := hunsigned.of_le (by omega)
  have hcap : Fits (w + 2) (a.stack + a.capacity) := hunsigned.of_le (by
    have hb := h.heapBudget
    have hf := h.floor
    have ht := ha.2.1
    have hgap := ha.2.2.1
    omega)
  obtain ⟨b, hinit, ⟨hstack, bcontrols, hframe, hbr⟩, hbouter⟩ :=
    Exec.rename_post (preprocessing_injective r)
      (initializeRoot_exec (x.comap (preprocessingRegisters r)) e
        ⟨fun i => h.bounded.1 (preprocessingRegisters r i), h.bounded.2⟩
        h.controls h.loaded h2 hcap (by have := ha.2.2.2; omega))
  have breg (i : Fin 128) (hi : i.val < 96) :
      b.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) :=
    hbr i (Or.inl hi)
  have bframe (q : ℕ) (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) : b.mem q = x.mem q := by
    apply hframe
    simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
    omega
  have bm (i : Fin 16) : b.regs (controllerRegisters r i) = x.regs (controllerRegisters r i) :=
    hbouter _ (fun j => (controller_ne_preprocessing i j).symm)
  let s : Cursor := ⟨[e], ns⟩
  have work : s.work = Math.work e.fuel := by
    simp only [s, Cursor.work, List.map_cons, List.map_nil, Math.potential, List.sum_cons,
      List.sum_nil, Nat.add_zero, Entry.task]
  have remaining : s.remaining a = e.task.output (Nat.primesLE a.m) a.Λ := by
    simp only [s, Cursor.remaining, List.map_cons, List.map_nil, Math.output,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have gap : a.capacity ≤ a.floor - a.stack := by
    have ht := ha.2.1
    have hg := ha.2.2.1
    omega
  have hi : s.Invariant a w κ n (ns ++ e.task.output (Nat.primesLE a.m) a.Λ) b := by
    refine {
      bounded := hinit.bounded h.bounded
      controls := bcontrols
      bitmap := ?_
      stack := ?_
      depth := ?_
      valid := ?_
      stored := ?_
      around := ?_
      ends := ?_
      floor := ?_
      heapBudget := ?_
      packedLength := ?_
      envelopeValue := (bm _).trans h.envelopeValue
      unit := (bm _).trans h.unit
      boolean := (bm _).symm ▸ h.boolean
      verdict := ?_
      exactOutput := ?_
      protectedMemory := ?_ }
    · intro q hq
      rw [bframe _ (Or.inl (by have := ha.1; omega))]
      exact h.bitmap q hq
    · simpa only [s, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hstack
    · rw [← h.fuel]
      exact Math.bounded_singleton e.task
    · intro d hd
      have he : d = e := by simpa only [s, List.mem_singleton] using hd
      exact he ▸ h.valid
    · intro d hd
      have he : d = e := by simpa only [s, List.mem_singleton] using hd
      subst d
      exact h.stored.of_stack_frame (h.around.mono_capacity gap) hframe
    · intro d hd
      have he : d = e := by simpa only [s, List.mem_singleton] using hd
      exact he ▸ h.around
    · intro d hd j
      have he : d = e := by simpa only [s, List.mem_singleton] using hd
      subst d
      rw [breg heap (by decide)]
      exact h.ends j
    · rw [breg heap (by decide)]
      exact h.floor
    · rw [breg heap (by decide), work]
      exact h.heapBudget
    · exact (hbr _ (Or.inr (by decide))).trans h.packedLength
    · rw [bm]
      exact h.verdict
    · rw [remaining]
    · intro q hq
      exact (bframe q (Or.inl hq)).trans (h.protectedMemory q hq)
  obtain ⟨y, he, hfinal⟩ := loop_exec c hw ha hresources hready h2 hcap s b hi
  have hexec : ExecWithin (w + 2) (oneRoot c.code) x y
      (70 + Math.work e.fuel * (visitTime a.n a.m a.N + 316) +
        (e.task.output (Nat.primesLE a.m) a.Λ).length * T) := by
    have hc := ExecWithin.seq_assoc.mp (hinit.within.seq he)
    exact hc.mono (by rw [Cursor.credit, work, remaining]; dsimp only [T]; omega)
  refine ⟨y, hexec, hfinal, ?_, ?_⟩
  · intro q hq
    exact (hfinal.protectedMemory q hq).trans (h.protectedMemory q hq).symm
  · intro i hi
    exact hexec.regs_eq (oneRoot_preserves c.code i hi)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
