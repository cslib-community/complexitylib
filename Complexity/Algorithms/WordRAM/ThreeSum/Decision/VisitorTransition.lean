/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorLive
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorSkip
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorRelease
import Complexity.Computability.WordRAM.Call
import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Registers

/-!
# Complete live transitions of the fused Chan–He visitor

Each live transition executes actual popping, local node construction, the certified solver,
one packed-tail release and three child pushes. No pointer-table readback is assumed. Pending
arrays and the frontend
prefix survive the callee's arbitrary higher scratch writes.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- Consume exactly the next preorder node and preserve the complete actual native worklist. -/
theorem live_transition {r κ n w : ℕ} {target : List Node} {a : Arena}
    (c : Host.Callee r)
    (e : Entry) (es : List Entry) (ns : List Node) (x : Data (registerCount r))
    (hw : width κ c.widthCoefficient n ≤ w + 2)
    (ha : a.Separated)
    (hresources : a.ceiling ≤ (n + 2) ^ envelopeExponent κ ∧
      4 * a.N < (n + 2) ^ envelopeExponent κ ∧
      60 * a.U + 40 ≤ (n + 2) ^ envelopeExponent κ)
    (hready : a.Ready w)
    (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack +
      a.capacity))
    (h : (Cursor.mk (e :: es) ns).Invariant
      a w κ n target x)
    (hf : e.fuel ≠ 0) (hn : ∀ j, (e.data j).length ≠ 0) :
    let T := Host.callerTime (4 * a.N)
      (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
    ∃ (s : Cursor) (y : Data (registerCount r)),
      ExecWithin (w + 2) (body c.code) x y (visitTime a.n a.m a.N + 314 + T) ∧
      s.Invariant a w κ n target y ∧
      (Cursor.mk (e :: es) ns).remaining a = e.task.node (Nat.primesLE a.m) a.Λ ::
        s.remaining a ∧ s.work + 1 ≤ (Cursor.mk (e :: es) ns).work ∧
      y.regs (preprocessingRegisters r heap) = x.regs (preprocessingRegisters r heap) + 3 +
        ((e.data 0).length + (e.data 1).length + (e.data 2).length) := by
  let T := Host.callerTime (4 * a.N)
    (c.time (Host.sideLength (4 * a.N)) (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8
  obtain ⟨p, hp, hstack, hl, hframe, hpr, hpm⟩ := pop_entry x e es h2 hcap h.stack
  have preg (i : Fin 128) (hi : 71 ≤ i.val) (hi' : i.val < 96) :
      p.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) :=
    hpr i (Or.inl hi') (Or.inr hi)
  have ph : p.regs (preprocessingRegisters r heap) =
      x.regs (preprocessingRegisters r heap) := preg _ (by decide) (by decide)
  have hc : a.Controls (p.comap (preprocessingRegisters r)) := h.controls.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact preg i (by omega) (by omega))
  have frame (q : ℕ) (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) :
      p.mem q = x.mem q := by
    apply hframe
    simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
    omega
  have gap : a.capacity ≤ a.floor - a.stack := by
    have ht := ha.2.1
    have hh := ha.2.2.1
    omega
  have oldStored (d : Entry) (hd : d ∈ e :: es) : d.Stored p.mem :=
    (h.stored d hd).of_stack_frame ((h.around d hd).mono_capacity gap) hframe
  have oldEnds (d : Entry) (hd : d ∈ e :: es) (j : Fin 3) :
      d.source j + (d.data j).length ≤ p.regs (preprocessingRegisters r heap) := by
    rw [ph]
    exact h.ends d hd j
  have oldBitmap : a.Bitmap p.mem := by
    intro q hq
    rw [frame _ (Or.inl (by have := ha.1; omega))]
    exact h.bitmap q hq
  have hwork : 1 ≤ (Cursor.mk (e :: es) ns).work := by
    have hw := Math.work_pos e.fuel
    change 1 ≤ Math.work e.fuel + Math.potential (es.map Entry.task)
    omega
  have hfloor : a.floor ≤ p.regs (preprocessingRegisters r heap) := by
    rw [ph]
    exact h.floor
  have hbudget : p.regs (preprocessingRegisters r heap) + allocationSize a.n a.m a.N ≤
      a.ceiling := by
    have hb : x.regs (preprocessingRegisters r heap) +
        (Cursor.mk (e :: es) ns).work * allocationSize a.n a.m a.N ≤ a.ceiling := h.heapBudget
    have hm := Nat.mul_le_mul_right (allocationSize a.n a.m a.N) hwork
    rw [ph]
    omega
  obtain ⟨q, v, hq, hv, ⟨em⟩, hvb, hva, hvr, hvm, hvf⟩ :=
    construct_consume c e p hw ha hresources hready hc hl
    (h.valid e (by simp)) (oldStored e (by simp)) oldBitmap hfloor hbudget
    (oldEnds e (by simp))
    ((hpr _ (Or.inr (by decide)) (Or.inr (by decide))).trans h.packedLength)
    ((hpm _).trans h.envelopeValue) ((hpm _).trans h.unit) (by rw [hpm]; exact h.boolean)
  let s : Cursor := ⟨em.children ++ es, ns ++ [e.task.node (Nat.primesLE a.m) a.Λ]⟩
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
  have qb := hq.bounded (hp.bounded h.bounded)
  have vb := hv.bounded qb
  have vc : a.Controls (v.comap (preprocessingRegisters r)) :=
    (em.controls hc).congr (fun i _ => hvr i)
  have qstack := em.stack ha hc
    ⟨fun i => qb.1 (preprocessingRegisters r i), qb.2⟩ (es.flatMap Entry.words) hstack (by
      have hs := ha.2.1
      have hf := ha.2.2.1
      simp only [Data.comap_regs] at *; omega)
  have vstack : WordStack.Rep (w + 2) a.stack a.capacity (es.flatMap Entry.words)
      ((v.comap (preprocessingRegisters r)).comap registers) := by
    refine ⟨⟨fun i => vb.1 (preprocessingRegisters r (registers i)), vb.2⟩,
      (hvr _).trans qstack.pointer, (hvr _).trans qstack.length_eq, qstack.capacity_le, ?_⟩
    intro i
    exact (hvf _ (by
      have ht := ha.2.1
      have hf := ha.2.2.1
      have hm := em.heap_mono
      have hi := i.isLt.trans_le qstack.capacity_le
      simp only [Data.comap_regs] at *; omega)).trans (qstack.contents i)
  let u := releaseState v
  have hrelease : Exec (w + 2) releasePacked v u 1 := exec_releasePacked v
  have ub := hrelease.bounded vb
  have ubp : (u.comap (preprocessingRegisters r)).Bounded (w + 2) :=
    ⟨fun i => ub.1 (preprocessingRegisters r i), ub.2⟩
  have uc : a.Controls (u.comap (preprocessingRegisters r)) := release_controls vc
  have ur (i : Fin 128) (hi : i ≠ heap) :
      u.regs (preprocessingRegisters r i) = v.regs (preprocessingRegisters r i) :=
    releaseState_regs v _ (fun he => hi ((preprocessing_injective r) he))
  have hpush := pushChildren_exec (u.comap (preprocessingRegisters r)) (es.flatMap Entry.words)
    ubp uc.2.2.2.2.2.2.2.2.2.2 h2 hcap (release_stack vstack) capacity
  obtain ⟨y, hy, ⟨hystack, hyframe, hyr⟩, hyouter⟩ :=
    Exec.rename_post (preprocessing_injective r) hpush
  have yreg (i : Fin 128) (hi : 71 ≤ i.val) (hi' : i.val < 96) :
      y.regs (preprocessingRegisters r i) = u.regs (preprocessingRegisters r i) :=
    hyr i (Or.inl ⟨hi, hi'⟩)
  have ym (i : Fin 16) : y.regs (controllerRegisters r i) = v.regs (controllerRegisters r i) :=
    (hyouter _ (fun j => (controller_ne_preprocessing i j).symm)).trans
      (releaseState_regs v _ (controller_ne_preprocessing i heap))
  have yframe (q : ℕ) (hq : q < a.stack ∨ a.stack + a.capacity ≤ q) : y.mem q = v.mem q := by
    apply hyframe
    simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
    simp only [Data.comap_regs] at *; omega
  have hvisit : ExecWithin (w + 2) (visit c.code) p y (visitTime a.n a.m a.N + T + 207) := by
    exact (hq.seq (hv.seq (hrelease.within.seq hy.within))).mono (by
      simp only [T, Data.comap_regs] at *
      omega)
  have oldPrefix (a : ℕ) (ha : a < p.regs (preprocessingRegisters r heap)) :
      v.mem a = p.mem a :=
    (hvf a (ha.trans_le em.heap_mono)).trans (em.local_prefix a ha)
  have hbody := body_live c.code hp hl hc.2.2.2.2.2.2.2.2.2.1 hf hn hvisit
  have retainedStored (d : Entry) (hd : d ∈ e :: es) : d.Stored q.mem := by
    exact (oldStored d hd).of_prefix (oldEnds d hd) em.local_prefix
  have newStored : ∀ d ∈ s.pending, d.Stored q.mem := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_stored (retainedStored e (by simp)) d hd
    · exact retainedStored d (List.mem_cons_of_mem e hd)
  have newAround : ∀ d ∈ s.pending, d.Around a.stack (a.floor - a.stack) := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_around (h.around e (by simp)) (by
        simp only [T, Data.comap_regs] at *
        omega) d hd
    · exact h.around d (List.mem_cons_of_mem e hd)
  have newEnds : ∀ d ∈ s.pending, ∀ j,
      d.source j + (d.data j).length ≤ u.regs (preprocessingRegisters r heap) := by
    intro d hd j
    rcases List.mem_append.mp hd with hd | hd
    · exact release_children_ends em hvr hl (oldEnds e (by simp)) d hd j
    · exact (oldEnds d (List.mem_cons_of_mem e hd) j).trans (release_heap_mono em hvr)
  have yh : y.regs (preprocessingRegisters r heap) =
      u.regs (preprocessingRegisters r heap) := yreg _ (by decide) (by decide)
  have bodyFrontier : y.regs (preprocessingRegisters r heap) =
      x.regs (preprocessingRegisters r heap) + 3 +
        ((e.data 0).length + (e.data 1).length + (e.data 2).length) := by
    have hr : u.regs (preprocessingRegisters r heap) = p.regs (preprocessingRegisters r heap) + 3 +
        (p.regs (preprocessingRegisters r (slot 2)) + p.regs (preprocessingRegisters r (slot 4)) +
          p.regs (preprocessingRegisters r (slot 6))) := release_frontier em hvr
    have h₀ : p.regs (preprocessingRegisters r (slot 2)) = (e.data 0).length := hl.2.2 0
    have h₁ : p.regs (preprocessingRegisters r (slot 4)) = (e.data 1).length := hl.2.2 1
    have h₂ : p.regs (preprocessingRegisters r (slot 6)) = (e.data 2).length := hl.2.2 2
    rw [yh, hr, ph, h₀, h₁, h₂]
  have heapAllocation : u.regs (preprocessingRegisters r heap) ≤
      p.regs (preprocessingRegisters r heap) + allocationSize a.n a.m a.N := by
    apply (release_heap_le em hvr).trans
    rw [hvr]
    have heh := em.heap_eq
    simp only [Data.comap_regs] at heh
    rw [heh]
    apply allocation_le
    · intro j
      rw [hl.2.2]
      exact (h.valid e (by simp)).length_le j
    · exact hc.2.2.2.1.le
    · simpa only [hc.1] using em.upper
  have hremaining : (Cursor.mk (e :: es) ns).remaining a =
      e.task.node (Nat.primesLE a.m) a.Λ :: s.remaining a := by
    have he := Math.output_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
    rw [mathStep] at he
    simpa only [Cursor.remaining, s, List.map_cons, Option.toList_some,
      List.singleton_append] using he
  refine ⟨s, y, hbody.mono (by simp only [T, Data.comap_regs] at *; omega), ?_,
    hremaining, hdec, bodyFrontier⟩
  refine {
    bounded := hbody.bounded h.bounded
    controls := uc.congr (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      exact yreg i (by omega) (by omega))
    bitmap := ?_
    stack := ?_
    depth := depth
    valid := ?_
    stored := ?_
    around := newAround
    ends := ?_
    floor := ?_
    heapBudget := ?_
    packedLength := ?_
    envelopeValue := ?_
    unit := ?_
    boolean := ?_
    verdict := ?_
    exactOutput := ?_
    protectedMemory := ?_ }
  · intro a ha'
    rw [yframe _ (Or.inl (by have := ha.1; simp only [T, Data.comap_regs] at *; omega))]
    exact (oldPrefix _ (by
      have hs := ha.1
      have ht := ha.2.1
      simp only [Data.comap_regs] at *; omega)).trans (oldBitmap a ha')
  · have words (j : Fin 3) : childWords (v.comap (preprocessingRegisters r)) j =
        childWords (q.comap (preprocessingRegisters r)) j := by
      simp only [childWords, Data.comap_regs, hvr]
    simpa only [s, u, release_childWords, words, em.children_words hl, List.flatMap_append,
      List.append_assoc] using hystack
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact em.children_valid (h.valid e (by simp)) d hd
    · exact h.valid d (List.mem_cons_of_mem e hd)
  · intro d hd
    exact ((newStored d hd).of_prefix (fun j =>
      (newEnds d hd j).trans ((release_heap_le em hvr).trans_eq (hvr heap))) hvf).of_stack_frame
        ((newAround d hd).mono_capacity gap) hyframe
  · intro d hd j
    rw [yh]
    exact newEnds d hd j
  · rw [yh]
    exact hfloor.trans (release_heap_mono em hvr)
  · rw [yh]
    have hb : x.regs (preprocessingRegisters r heap) +
        (Cursor.mk (e :: es) ns).work * allocationSize a.n a.m a.N ≤ a.ceiling := h.heapBudget
    have hd := Nat.mul_le_mul_right (allocationSize a.n a.m a.N) hdec
    rw [Nat.add_mul, Nat.one_mul] at hd
    rw [ph] at heapAllocation
    simp only [T, Data.comap_regs] at *; omega
  · have hr := hyr ChanHe.Preprocessing.packedLength (Or.inr (by decide))
    have hv := em.registers ChanHe.Preprocessing.packedLength (by decide) (by decide)
      (by decide) (by decide) (by decide) (Or.inr (by decide))
    exact hr.trans ((ur _ (by decide)).trans ((hvr _).trans (hv.trans
      ((hpr _ (Or.inr (by decide)) (Or.inr (by decide))).trans h.packedLength))))
  · rw [ym, hvm _ (by decide), hpm]
    exact h.envelopeValue
  · rw [ym, hvm _ (by decide), hpm]
    exact h.unit
  · rw [ym]
    exact hvb
  · rw [ym, hva, hpm, h.verdict]
    simp only [s, List.mem_append, List.mem_singleton, or_and_right,
      exists_or, exists_eq_left]
  · change (ns ++ [e.task.node (Nat.primesLE a.m) a.Λ]) ++ s.remaining a = target
    rw [List.append_assoc, List.singleton_append, ← hremaining]
    exact h.exactOutput
  · intro a ha'
    rw [yframe a (Or.inl ha')]
    exact (oldPrefix a (by
      have := ha.2.1
      simp only [Data.comap_regs] at *; omega)).trans
        ((frame a (Or.inl ha')).trans (h.protectedMemory a ha'))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
