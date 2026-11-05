/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.VisitorPop

/-!
# Actual skipped transitions in the fused Chan–He visitor

Zero-fuel and empty-column entries execute the original seven pops and actual branch paths.
They perform no solver call, leave the consumed prefix unchanged and preserve every live
pending source, the bitmap and the original frontend prefix.

## Main results

* `skip_transition`: actual execution, complete cursor preservation and decreasing work.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum.ChanHe (Node)
open ChanHe.Traversal

/-- A skipped native descriptor leaves the Boolean fold unchanged and reduces traversal credit. -/
theorem skip_transition {r w κ n : ℕ} {a : Arena} {target : List Node}
    (solver : Code .standard (r + 7)) (e : Entry) (es : List Entry) (ns : List Node)
    (x : Data (registerCount r)) (ha : a.Separated) (h2 : Fits (w + 2) 2)
    (hcap : Fits (w + 2) (a.stack + a.capacity))
    (h : (Cursor.mk (e :: es) ns).Invariant a w κ n target x)
    (hskip : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
      (e.data 1).length = 0 ∨ (e.data 2).length = 0) :
    ∃ y, ExecWithin (w + 2) (body solver) x y 107 ∧
      (Cursor.mk es ns).Invariant a w κ n target y ∧
      (Cursor.mk es ns).remaining a = (Cursor.mk (e :: es) ns).remaining a ∧
      (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work ∧
      ∀ T, 109 + (Cursor.mk es ns).credit a T ≤ (Cursor.mk (e :: es) ns).credit a T := by
  obtain ⟨y, hy, hstack, hloaded, hframe, hp, hm⟩ := pop_entry x e es h2 hcap h.stack
  have hreg (i : Fin 128) (hi : 71 ≤ i.val) (hi' : i.val < 96) :
      y.regs (preprocessingRegisters r i) = x.regs (preprocessingRegisters r i) :=
    hp i (Or.inl hi') (Or.inr hi)
  have hheap : y.regs (preprocessingRegisters r ChanHe.Traversal.heap) =
      x.regs (preprocessingRegisters r ChanHe.Traversal.heap) := hreg _ (by decide) (by decide)
  have hcontrols : a.Controls (y.comap (preprocessingRegisters r)) := h.controls.congr (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    exact hreg i (by omega) (by omega))
  have hbody := body_skip solver hy hloaded hcontrols.2.2.2.2.2.2.2.2.2.1 hskip
  have hmem (p : ℕ) (hp : p < a.stack ∨ a.stack + a.capacity ≤ p) : y.mem p = x.mem p := by
    apply hframe
    simp only [WordStack.footprint, Block.mem_footprint, Block.Owns]
    omega
  have hstep : Math.step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task) =
      (es.map Entry.task, none) := by
    by_cases hf : e.fuel = 0
    · simp only [Math.step, Entry.task, hf]
    · have hempty : e.task.empty := by
        simp only [Math.Task.empty, Entry.task, List.toFinset_eq_empty_iff]
        rcases hskip with hf' | h₀ | h₁ | h₂
        · exact (hf hf').elim
        · exact Or.inl (List.eq_nil_of_length_eq_zero h₀)
        · exact Or.inr (Or.inl (List.eq_nil_of_length_eq_zero h₁))
        · exact Or.inr (Or.inr (List.eq_nil_of_length_eq_zero h₂))
      cases he : e.fuel with
      | zero => exact (hf he).elim
      | succ f => simp only [Math.step, show e.task.fuel = f + 1 from he, hempty, ↓reduceIte]
  have hdec := Math.potential_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
  rw [hstep] at hdec
  change (Cursor.mk es ns).work + 1 ≤ (Cursor.mk (e :: es) ns).work at hdec
  have hremaining : (Cursor.mk es ns).remaining a =
      (Cursor.mk (e :: es) ns).remaining a := by
    have he := Math.output_step (Nat.primesLE a.m) a.Λ e.task (es.map Entry.task)
    rw [hstep] at he
    simp only [Option.toList_none, List.nil_append] at he
    exact he.symm
  have hcredit (T : ℕ) :
      109 + (Cursor.mk es ns).credit a T ≤ (Cursor.mk (e :: es) ns).credit a T := by
    simp only [Cursor.credit, hremaining]
    have hd := Nat.mul_le_mul_right (visitTime a.n a.m a.N + 316) hdec
    rw [Nat.add_mul, Nat.one_mul] at hd
    omega
  refine ⟨y, hbody, ?_, hremaining, hdec, hcredit⟩
  refine {
    bounded := hbody.bounded h.bounded
    controls := hcontrols
    bitmap := ?_
    stack := hstack
    depth := h.depth.2
    valid := fun d hd => h.valid d (List.mem_cons_of_mem e hd)
    stored := ?_
    around := fun d hd => h.around d (List.mem_cons_of_mem e hd)
    ends := ?_
    floor := hheap.symm ▸ h.floor
    heapBudget := ?_
    packedLength := ?_
    envelopeValue := (hm _).trans h.envelopeValue
    unit := (hm _).trans h.unit
    boolean := (hm _).symm ▸ h.boolean
    verdict := ?_
    exactOutput := ?_
    protectedMemory := ?_ }
  · intro q hq
    rw [hmem _ (Or.inl (by have := ha.1; omega))]
    exact h.bitmap q hq
  · intro d hd
    exact (h.stored d (List.mem_cons_of_mem e hd)).of_stack_frame
      ((h.around d (List.mem_cons_of_mem e hd)).mono_capacity (by
        have ht := ha.2.1
        have hf := ha.2.2.1
        omega)) hframe
  · intro d hd j
    rw [hheap]
    exact h.ends d (List.mem_cons_of_mem e hd) j
  · rw [hheap]
    have hb := h.heapBudget
    have hd := Nat.mul_le_mul_right (ChanHe.Traversal.allocationSize a.n a.m a.N)
      (show (Cursor.mk es ns).work ≤ (Cursor.mk (e :: es) ns).work by omega)
    omega
  · exact (hp _ (Or.inr (by decide)) (Or.inr (by decide))).trans h.packedLength
  · rw [hm]
    exact h.verdict
  · rw [hremaining]
    exact h.exactOutput
  · intro p hp
    exact (hmem p (Or.inl hp)).trans (h.protectedMemory p hp)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
