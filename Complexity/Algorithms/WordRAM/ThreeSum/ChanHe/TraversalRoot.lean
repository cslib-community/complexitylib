/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalLoop

/-!
# Complete native Chan–He traversal from a supplied root

The finite 128-register program initializes its actual stack and constants, pushes the supplied
seven-word root and executes the complete bounded traversal. Every emitted array is the existing
finite node's `oneArray`, in preorder. The protected frontend prefix survives for later roots.

## Main definitions

* `RootInput`: concrete native array, metadata and disjoint-memory obligations of a root call.

## Main results

* `root_exec`: complete actual native execution with exact output and a charged bound.

These native composition proofs are original. The initialized-input forest and global
logarithmic-width/subquadratic-cost composition remain separate obligations.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Concrete caller obligations before the complete native root program initializes its stack. -/
structure RootInput (a : Arena) (w : ℕ) (e : Entry) (ns : List (ℕ × Node))
    (x : Data 128) : Prop where
  /-- Initial actual words fit. -/
  bounded : x.Bounded (w + 2)
  /-- Persistent caller metadata. -/
  controls : a.Controls x
  /-- Exact root register metadata. -/
  loaded : e.Loaded x
  /-- Exact root data readback. -/
  stored : e.Stored x.mem
  /-- Duplicate-free existing three-set admissibility. -/
  valid : e.Valid a.n a.U
  /-- The actual prime bitmap is ready. -/
  bitmap : a.Bitmap x.mem
  /-- Original arrays avoid the complete reserved stack and output-table gap. -/
  around : e.Around a.stack (a.floor - a.stack)
  /-- All root arrays end below the fresh allocation. -/
  ends : ∀ j, e.source j + (e.data j).length ≤ x.regs heap
  /-- The supplied fuel agrees with the fixed stack reservation. -/
  fuel : e.fuel = a.fuel
  /-- The initial fresh allocation lies above the reserved gap. -/
  floor : a.floor ≤ x.regs heap
  /-- The full tree's transitions reserve sufficient fresh memory. -/
  heapBudget : x.regs heap + Math.work e.fuel * allocationSize a.n a.m a.N ≤ a.ceiling
  /-- Actual accumulated output count. -/
  count : x.regs outputCount = ns.length
  /-- The full tree's transitions reserve sufficient output-pointer cells. -/
  tableBudget : ns.length + Math.work e.fuel ≤ a.outputCapacity
  /-- Existing output retains its exact native readback. -/
  output : StoredNodes a.U a.N a.table ns x.mem
  /-- Existing packed arrays lie above the gap and below the fresh allocation. -/
  outputBounds : ∀ i : Fin ns.length,
    a.floor ≤ ns[i.val].1 ∧ ns[i.val].1 + 4 * a.N ≤ x.regs heap
  /-- The entire frontend prefix is available. -/
  protectedMemory : ∀ p < a.stack, x.mem p = a.retained p

/-- Execute the fixed complete native root program. There are no supplied kernel executions:
all calls are proved from the actual arrays, bitmap, finite bounds and one signed envelope.
The caller chooses `m`, `Λ` and fuel. Setting `m = mPar n U`, `Λ = labelBits U` and
`e.fuel = fuel n` makes `e.task.output (Nat.primesLE a.m) a.Λ` the existing Chan–He
`reduction n U` of the root sets; the initialized-input bridge is in `PreprocessingEntries`. -/
theorem root_exec {a : Arena} {w : ℕ} (e : Entry) (ns : List (ℕ × Node)) (x : Data 128)
    (ha : a.Separated) (hw : a.Ready w) (h : RootInput a w e ns x) :
    ∃ (out : List (ℕ × Node)) (y : Data 128),
      ExecWithin (w + 2) oneRoot x y (rootTime e.fuel a.n a.m a.N) ∧
      (Cursor.mk [] out).Invariant a w
        (ns.map Prod.snd ++ e.task.output (Nat.primesLE a.m) a.Λ) y ∧
      out.map Prod.snd = ns.map Prod.snd ++ e.task.output (Nat.primesLE a.m) a.Λ ∧
      (∀ p < a.stack, y.mem p = x.mem p) ∧
      ∀ i : Fin 128, 109 ≤ i.val → y.regs i = x.regs i := by
  have hunsigned := Signed.unsigned_fits_of_signed hw.2.2
  have hsum := envelope_ge_sum a.ceiling a.n a.m a.Λ a.U a.N
  have h2 : Fits (w + 2) 2 := hunsigned.of_le (by omega)
  have hcap : Fits (w + 2) (a.stack + a.capacity) := hunsigned.of_le (by
    have hb := h.heapBudget
    have hf := h.floor
    have ht := ha.2.1
    have hgap := ha.2.2.1
    omega)
  let p := (((x.set zero 0).set one 1).set (registers Stack.ptr) (x.regs stackBase)).set
    (registers Stack.len) 0
  let ptr := registers Stack.ptr
  let len := registers Stack.len
  have h1 : Fits (w + 2) 1 := h2.of_le (by decide)
  have hp : Exec (B := .standard) (w + 2)
      (ram[ zero ← #0; one ← #1; ptr ← stackBase; len ← #0 ]) x p 4 := by
    ram_eval [p, ptr, len, zero, one, registers, Stack.ptr, Stack.len, stackBase, h1]
  have preg (i : Fin 128) (hi : i.val < 96) :
      p.regs i = ((x.set zero 0).set one 1).regs i := by
    have hp' : i ≠ registers Stack.ptr := by
      intro he; have := congrArg Fin.val he; norm_num [registers, Stack.ptr] at this; omega
    have hl' : i ≠ registers Stack.len := by
      intro he; have := congrArg Fin.val he; norm_num [registers, Stack.len] at this; omega
    simp only [p, Data.set_regs, Function.update_of_ne hp', Function.update_of_ne hl']
  have pmeta (i : Fin 128) (hi : i.val < 96) : p.regs i = x.regs i := by
    rw [preg i hi]
    by_cases hz : i = zero
    · subst i
      simpa +decide [Data.set, zero, one] using h.controls.2.2.2.2.2.2.2.2.2.1.symm
    · by_cases ho : i = one
      · subst i
        simpa +decide [Data.set, zero, one] using h.controls.2.2.2.2.2.2.2.2.2.2.symm
      · simp only [Data.set_regs, Function.update_of_ne ho, Function.update_of_ne hz]
  have pcontrols : a.Controls p := h.controls.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact pmeta i (by omega))
  have ploaded : e.Loaded p := by
    refine ⟨(pmeta _ (by decide)).trans h.loaded.1, ?_, ?_⟩
    · intro j
      exact (pmeta _ (by dsimp [arraySource, slot]; omega)).trans (h.loaded.2.1 j)
    · intro j
      exact (pmeta _ (by dsimp [arrayLength, slot]; omega)).trans (h.loaded.2.2 j)
  have pstack : Stack.Rep (w + 2) a.stack a.capacity [] (p.comap registers) := by
    refine ⟨⟨fun i => (hp.bounded h.bounded).1 (registers i), (hp.bounded h.bounded).2⟩,
      ?_, ?_, Nat.zero_le _, fun i => Fin.elim0 i⟩
    · simpa +decide [p, Data.comap, Data.set, registers, Stack.ptr, Stack.len, zero, one]
        using h.controls.2.2.2.2.2.2.2.1
    · simp +decide [p, Data.comap, Data.set, registers, Stack.ptr, Stack.len, zero, one]
  obtain ⟨b, hb, hstack, hframe, hbr⟩ := pushFrame_exec p [] h2 hcap pstack
    (fun i => (hp.bounded h.bounded).1 (slot i)) (by
      have := ha.2.2.2
      simp only [List.length_nil]
      omega)
  have breg (i : Fin 128) (hi : i.val < 96) : b.regs i = x.regs i :=
    (hbr i (Or.inl hi)).trans (pmeta i hi)
  have bframe (q : ℕ) (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) : b.mem q = x.mem q := by
    apply hframe
    simp only [Stack.footprint, Block.mem_footprint, Block.Owns]
    omega
  let s : Cursor := ⟨[e], ns⟩
  have work : s.work = Math.work e.fuel := by
    simp only [s, Cursor.work, List.map_cons, List.map_nil, Math.potential, List.sum_cons,
      List.sum_nil, Nat.add_zero, Entry.task]
  have gap : a.capacity ≤ a.floor - a.stack := by
    have ht := ha.2.1
    have hg := ha.2.2.1
    omega
  have hi : s.Invariant a w
      (ns.map Prod.snd ++ e.task.output (Nat.primesLE a.m) a.Λ) b := by
    refine ⟨hb.bounded (hp.bounded h.bounded), h.controls.congr (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact breg i (by omega)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq
      rw [bframe _ (Or.inl (by have := ha.1; omega))]
      exact h.bitmap q hq
    · simpa only [s, List.flatMap_cons, List.flatMap_nil, Entry.loaded_words ploaded,
        List.append_nil] using hstack
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
    · exact (breg outputCount (by decide)).trans h.count
    · rw [work]
      exact h.tableBudget
    · apply h.output.congr
      · intro q hq _
        exact bframe q (Or.inr (by have := ha.2.1; omega))
      · intro i u _
        exact bframe _ (Or.inr (by
          have hp' := (h.outputBounds i).1
          have ht := ha.2.1
          have hg := ha.2.2.1
          omega))
    · intro i
      rw [breg heap (by decide)]
      exact h.outputBounds i
    · simp only [s, List.map_cons, List.map_nil, Math.output, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
    · intro q hq
      exact (bframe q (Or.inl hq)).trans (h.protectedMemory q hq)
  obtain ⟨out, y, he, hfinal, hout⟩ := loop_exec ha hw h2 hcap s b hi
  have hexec : ExecWithin (w + 2) oneRoot x y (rootTime e.fuel a.n a.m a.N) := by
    have hc := hp.within.seq (hb.within.seq he)
    exact hc.mono (by rw [work]; dsimp only [rootTime]; omega)
  refine ⟨out, y, hexec, hfinal, hout, ?_, ?_⟩
  · intro q hq
    exact (hfinal.protectedMemory q hq).trans (h.protectedMemory q hq).symm
  · intro i hi
    exact hexec.regs_eq (oneRoot_preserves i hi)

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
