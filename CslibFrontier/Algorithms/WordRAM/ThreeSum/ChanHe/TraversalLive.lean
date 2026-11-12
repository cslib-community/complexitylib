/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalAdmitted
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalEmissionFrame
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStackFrame
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.TraversalStep

/-!
# Complete live transitions of the native Chan–He worklist

One transition executes the seven pops, both complete modulus searches, all three actual
histogram/packing calls, output delivery and the three reversed child pushes. Its invariant
preserves exact existing-node output, live arrays, the actual prime bitmap, and the space
reservations paid for by the strictly decreasing work measure.

## Main results

* `live_transition`: complete actual native body execution and full invariant preservation.

These native composition and invariant proofs are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)

/-- Execute and verify the whole live native worklist transition. -/
theorem live_transition {a : Arena} {w : ℕ} {target : List Node}
    (e : Entry) (es : List Entry) (ns : List (ℕ × Node)) (x : Data 128)
    (ha : a.Separated) (hw : a.Ready w) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity))
    (h : (Cursor.mk (e :: es) ns).Invariant a w target x)
    (hf : e.fuel ≠ 0) (hn : ∀ j, (e.data j).length ≠ 0) :
    ∃ (s : Cursor) (y : Data 128),
      ExecWithin (w + 2) body x y (visitTime a.n a.m a.N + 314) ∧
      s.Invariant a w target y ∧ s.work < (Cursor.mk (e :: es) ns).work := by
  obtain ⟨p, hp, hstack, hl, hframe, hpr⟩ := pop_entry x e es h2 hcap h.stack
  obtain ⟨ph, pc, hc, frame, gap, oldStored, oldEnds, oldBitmap, hfloor⟩ :=
    Arena.preserved_of_stack_frame x p ha h.controls h.bitmap h.stored h.around h.ends h.floor
      hframe (fun i hi hi' => hpr i (Or.inl hi') (Or.inr hi))
  replace pc : p.regs outputCount = ns.length := pc.trans h.count
  have oldOutput : StoredNodes a.U a.N a.table ns p.mem :=
    h.output.of_arena_frame ha (fun i => (h.outputBounds i).1) hframe
  have oldBounds (i : Fin ns.length) :
      a.floor ≤ ns[i.val].1 ∧ ns[i.val].1 + 4 * a.N ≤ p.regs heap := by
    rw [ph]
    exact h.outputBounds i
  have hwork : 1 ≤ (Cursor.mk (e :: es) ns).work := by
    have hw := Math.work_pos e.fuel
    change 1 ≤ Math.work e.fuel + Math.potential (es.map Entry.task)
    omega
  have htable : a.table + ns.length < a.floor := by
    have hb := h.tableBudget
    change ns.length + (Cursor.mk (e :: es) ns).work ≤ a.outputCapacity at hb
    have hh := ha.2.2.1
    omega
  have hheap : p.regs heap ≤ a.ceiling := by
    rw [ph]
    have hb := h.heapBudget
    omega
  have htablep : p.regs outputs + p.regs outputCount < a.floor := by
    rw [hc.2.2.2.2.2.2.1, pc]
    exact htable
  obtain ⟨v, hv₀, ⟨em⟩⟩ := emit_admitted true p e ha hw hc hl (h.valid e (by simp))
    (oldStored e (by simp)) oldBitmap hfloor hheap (oldEnds e (by simp)) (fun _ => by omega)
  have hv : ExecWithin (w + 2) visit p v (visitTime a.n a.m a.N) := by simpa using hv₀
  let s : Cursor := ⟨em.children ++ es, ns ++ [((recordLayout p em.M).packed,
    e.task.node (Nat.primesLE a.m) a.Λ)]⟩
  have mathStep := em.math_step es hf hn
  have hdec := Math.potential_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
  rw [mathStep] at hdec
  change s.work + 1 ≤ (Cursor.mk (e :: es) ns).work at hdec
  have depth : Math.Bounded a.fuel (s.pending.map Entry.task) := by
    have hd := Math.bounded_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task) h.depth
    rw [mathStep] at hd
    exact hd
  have capacity : 21 + (es.flatMap Entry.words).length ≤ a.capacity := by
    have hd := depth.length_le
    rw [List.length_map] at hd
    change (em.children ++ es).length ≤ 2 * a.fuel + 1 at hd
    simp only [Emission.children, List.length_append, List.length_cons, List.length_nil] at hd
    rw [length_serialized]
    have hh := ha.2.2.2
    omega
  have vcontrols := em.controls hc
  have vstack := em.stack ha hc (hv.bounded (hp.bounded h.bounded))
    (es.flatMap Entry.words) hstack (by
      have hs := ha.2.1
      have hf := ha.2.2.1
      omega)
  obtain ⟨y, hy, hystack, hyframe, hyr⟩ := pushChildren_exec v (es.flatMap Entry.words)
    (hv.bounded (hp.bounded h.bounded)) vcontrols.2.2.2.2.2.2.2.2.2.2 h2 hcap vstack capacity
  have yreg (i : Fin 128) (hi : 71 ≤ i.val) (hi' : i.val < 96) :
      y.regs i = v.regs i := hyr i (Or.inl ⟨hi, hi'⟩)
  have yframe := a.stack_frame hyframe
  have hbody := body_live hp hl hc.2.2.2.2.2.2.2.2.2.1 hf hn hv hy
  have vsStored := em.stored ha hc (oldStored e (by simp)) (h.around e (by simp))
    (oldEnds e (by simp)) htablep
  have newStored : ∀ d ∈ s.pending, d.Stored v.mem := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_stored vsStored d hd
    · exact em.stored ha hc (oldStored d (List.mem_cons_of_mem e hd))
        (h.around d (List.mem_cons_of_mem e hd)) (oldEnds d (List.mem_cons_of_mem e hd)) htablep
  have newAround : ∀ d ∈ s.pending, d.Around a.stack (a.floor - a.stack) := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_around (h.around e (by simp)) (by omega) d hd
    · exact h.around d (List.mem_cons_of_mem e hd)
  have newEnds : ∀ d ∈ s.pending, ∀ j, d.source j + (d.data j).length ≤ v.regs heap := by
    intro d hd j
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_ends hl (oldEnds e (by simp)) d hd j
    · exact (oldEnds d (List.mem_cons_of_mem e hd) j).trans em.heap_mono
  have houtput := em.output hc ns oldOutput pc oldBounds htable hfloor
  have yh : y.regs heap = v.regs heap := yreg _ (by decide) (by decide)
  have heapAllocation : v.regs heap ≤ p.regs heap + allocationSize a.n a.m a.N := by
    rw [em.heap_eq]
    apply allocation_le
    · intro j
      rw [hl.2.2]
      exact (h.valid e (by simp)).length_le j
    · exact hc.2.2.2.1.le
    · simpa only [hc.1] using em.upper
  have newBounds (i : Fin s.emitted.length) :
      a.floor ≤ s.emitted[i.val].1 ∧ s.emitted[i.val].1 + 4 * a.N ≤ y.regs heap := by
    rw [yh, em.heap_eq]
    by_cases hi : i.val < ns.length
    · simp only [s, List.getElem_append_left hi]
      exact ⟨(oldBounds ⟨i.val, hi⟩).1,
        (oldBounds ⟨i.val, hi⟩).2.trans (em.heap_eq ▸ em.heap_mono)⟩
    · have hi' := i.isLt
      have he : i.val = ns.length := by
        dsimp only [s] at hi'
        simp only [List.length_append, List.length_singleton] at hi'
        omega
      have hg : (ns ++ [((recordLayout p em.M).packed,
          e.task.node (Nat.primesLE a.m) a.Λ)])[ns.length] =
          ((recordLayout p em.M).packed, e.task.node (Nat.primesLE a.m) a.Λ) := by simp
      change a.floor ≤ (ns ++ [_])[i.val].1 ∧ (ns ++ [_])[i.val].1 + 4 * a.N ≤ _
      simp only [he, hg]
      constructor
      · dsimp only [NodePacking.Layout.packed, recordLayout]
        omega
      · dsimp only [NodePacking.Layout.endpoint, NodePacking.Layout.hist,
          NodePacking.Layout.scratch, recordLayout]
        have hN := hc.2.2.2.1
        omega
  refine ⟨s, y, hbody, ?_, by omega⟩
  refine ⟨hbody.bounded h.bounded, vcontrols.of_regs_71_96 yreg, ?_, ?_, depth, ?_, ?_, newAround,
    ?_, ?_, ?_, ?_, ?_, houtput.of_arena_frame ha (fun i => (newBounds i).1) hyframe, newBounds,
    ?_, ?_⟩
  · intro q hq
    rw [yframe _ (Or.inl (by have := ha.1; omega)),
      em.prefix_preserved _ (by have := ha.1; have := ha.2.1; omega) (by
        have ht := hc.2.2.2.2.2.2.1
        have hq' := ha.1
        have hh := ha.2.1
        omega)]
    exact oldBitmap q hq
  · simpa only [s, em.children_words hl, List.flatMap_append, List.append_assoc] using hystack
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_valid (h.valid e (by simp)) d hd
    · exact h.valid d (List.mem_cons_of_mem e hd)
  · intro d hd
    exact (newStored d hd).of_arena_frame ha (newAround d hd) hyframe
  · intro d hd j
    rw [yh]
    exact newEnds d hd j
  · rw [yh]
    exact hfloor.trans em.heap_mono
  · rw [yh]
    have hb := h.heapBudget
    have hd := Nat.mul_le_mul_right (allocationSize a.n a.m a.N) hdec
    rw [Nat.add_mul, Nat.one_mul] at hd
    rw [ph] at heapAllocation
    omega
  · rw [yreg outputCount (by decide) (by decide), em.count, pc]
    simp only [s, List.length_append, List.length_singleton, Bool.toNat_true]
  · have hb := h.tableBudget
    change ns.length + (Cursor.mk (e :: es) ns).work ≤ a.outputCapacity at hb
    change (ns ++ [_]).length + s.work ≤ a.outputCapacity
    simp only [List.length_append, List.length_singleton]
    omega
  · have he := Math.output_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
    rw [mathStep] at he
    simpa only [s, List.map_append, List.map_singleton, List.map_cons, Option.toList_some,
      List.singleton_append, List.append_assoc, List.map_nil, List.nil_append, he]
      using h.exactOutput
  · intro q hq
    rw [yframe q (Or.inl hq), em.prefix_preserved q (by
      have ht := ha.2.1
      have hf' := ha.2.2.1
      omega) (by
        have ht := ha.2.1
        have hp' := hc.2.2.2.2.2.2.1
        omega), frame q (Or.inl hq)]
    exact h.protectedMemory q hq

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Traversal
