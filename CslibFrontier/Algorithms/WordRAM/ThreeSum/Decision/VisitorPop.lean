/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.VisitorInvariant
import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Registers
import CslibFrontier.Computability.WordRAM.Call

/-!
# Native descriptor popping in the fused visitor

The original seven-pop routine executes in the preprocessing register bank with the same
exact clock. Its stack frame, actual descriptor readback and outer register frame are retained.

## Main results

* `pop_entry`: the native pop in the complete visitor register file.
* `body_skip`, `body_live`: charged native dispatch on the actual descriptor guards.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM

/-- Lift the actual seven-pop program and all its readback/frame facts into the visitor. -/
theorem pop_entry {r w base capacity : ℕ} (x : Data (registerCount r))
    (e : ChanHe.Traversal.Entry) (es : List ChanHe.Traversal.Entry)
    (h2 : Fits w 2) (hcap : Fits w (base + capacity))
    (hr : ChanHe.Traversal.WordStack.Rep w base capacity
      ((e :: es).flatMap ChanHe.Traversal.Entry.words)
      ((x.comap (preprocessingRegisters r)).comap ChanHe.Traversal.registers)) :
    ∃ y, Exec w (ChanHe.Traversal.popFrame.rename (preprocessingRegisters r)) x y 99 ∧
      ChanHe.Traversal.WordStack.Rep w base capacity
        (es.flatMap ChanHe.Traversal.Entry.words)
        ((y.comap (preprocessingRegisters r)).comap ChanHe.Traversal.registers) ∧
      e.Loaded (y.comap (preprocessingRegisters r)) ∧
      Modifies (ChanHe.Traversal.WordStack.footprint base capacity) x.mem y.mem ∧
      (∀ j, ChanHe.Traversal.Outside j → (j.val < 64 ∨ 71 ≤ j.val) →
        y.regs (preprocessingRegisters r j) = x.regs (preprocessingRegisters r j)) ∧
      ∀ j, y.regs (controllerRegisters r j) = x.regs (controllerRegisters r j) := by
  obtain ⟨p, hp, hs, hl, hm, hf⟩ :=
    ChanHe.Traversal.pop_entry (x.comap (preprocessingRegisters r)) e es h2 hcap hr
  obtain ⟨y, hy, hQ, hframe⟩ := Exec.rename_post (preprocessing_injective r)
    (Q := fun p => ChanHe.Traversal.WordStack.Rep w base capacity
      (es.flatMap ChanHe.Traversal.Entry.words) (p.comap ChanHe.Traversal.registers) ∧
      e.Loaded p ∧ Modifies (ChanHe.Traversal.WordStack.footprint base capacity) x.mem p.mem ∧
      ∀ j, ChanHe.Traversal.Outside j → (j.val < 64 ∨ 71 ≤ j.val) →
        p.regs j = x.regs (preprocessingRegisters r j))
    ⟨p, hp, hs, hl, hm, hf⟩
  exact ⟨y, hy, hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2,
    fun j => hframe _ (fun i => (controller_ne_preprocessing j i).symm)⟩

private theorem copy_self {r w : ℕ} (x : Data (registerCount r)) :
    Exec (B := .standard) w (.op (.copy
      (preprocessingRegisters r (ChanHe.Traversal.slot 0))
      (preprocessingRegisters r (ChanHe.Traversal.slot 0)))) x x 1 := by
  convert (Exec.copy (B := Basis.standard) (w := w) (x := x)
    (d := preprocessingRegisters r (ChanHe.Traversal.slot 0))
    (s := preprocessingRegisters r (ChanHe.Traversal.slot 0))) using 1
  ext i <;> simp [Data.set]

/-- The actual dispatch preserves the pop result when fuel or any source column is empty. -/
theorem body_skip {r w : ℕ} {x y : Data (registerCount r)} {e : ChanHe.Traversal.Entry}
    (solver : Code .standard (r + 7))
    (hp : Exec w (ChanHe.Traversal.popFrame.rename (preprocessingRegisters r)) x y 99)
    (hl : e.Loaded (y.comap (preprocessingRegisters r)))
    (hz : y.regs (preprocessingRegisters r ChanHe.Traversal.zero) = 0)
    (hskip : e.fuel = 0 ∨ (e.data 0).length = 0 ∨
      (e.data 1).length = 0 ∨ (e.data 2).length = 0) :
    ExecWithin w (body solver) x y 107 := by
  have hf : y.regs (preprocessingRegisters r (ChanHe.Traversal.slot 0)) = e.fuel := hl.1
  have hn₀ : y.regs (preprocessingRegisters r (ChanHe.Traversal.slot 2)) =
      (e.data 0).length := hl.2.2 0
  have hn₁ : y.regs (preprocessingRegisters r (ChanHe.Traversal.slot 4)) =
      (e.data 1).length := hl.2.2 1
  have hn₂ : y.regs (preprocessingRegisters r (ChanHe.Traversal.slot 6)) =
      (e.data 2).length := hl.2.2 2
  by_cases h₀ : e.fuel = 0
  · exact (hp.seq (Exec.branch_pos
      (by change y.regs _ = y.regs _; omega) (copy_self y))).within.mono (by omega)
  · by_cases h₁ : (e.data 0).length = 0
    · exact (hp.seq (Exec.branch_neg
        (by change ¬y.regs _ = y.regs _; omega)
        (Exec.branch_pos (by change y.regs _ = y.regs _; omega)
          (copy_self y)))).within.mono (by omega)
    · by_cases h₂ : (e.data 1).length = 0
      · exact (hp.seq (Exec.branch_neg
          (by change ¬y.regs _ = y.regs _; omega)
          (Exec.branch_neg (by change ¬y.regs _ = y.regs _; omega)
            (Exec.branch_pos (by change y.regs _ = y.regs _; omega)
              (copy_self y))))).within.mono (by omega)
      · have h₃ : (e.data 2).length = 0 := by omega
        exact (hp.seq (Exec.branch_neg
          (by change ¬y.regs _ = y.regs _; omega)
          (Exec.branch_neg (by change ¬y.regs _ = y.regs _; omega)
            (Exec.branch_neg (by change ¬y.regs _ = y.regs _; omega)
              (Exec.branch_pos (by change y.regs _ = y.regs _; omega)
                (copy_self y)))))).within.mono (by omega)

/-- A live descriptor takes all four actual negative guards before its complete visit. -/
theorem body_live {r w T : ℕ} {x a y : Data (registerCount r)}
    {e : ChanHe.Traversal.Entry} (solver : Code .standard (r + 7))
    (hp : Exec w (ChanHe.Traversal.popFrame.rename (preprocessingRegisters r)) x a 99)
    (hl : e.Loaded (a.comap (preprocessingRegisters r)))
    (hz : a.regs (preprocessingRegisters r ChanHe.Traversal.zero) = 0)
    (hf : e.fuel ≠ 0) (hn : ∀ j, (e.data j).length ≠ 0)
    (hv : ExecWithin w (visit solver) a y T) :
    ExecWithin w (body solver) x y (T + 107) := by
  obtain ⟨t, ht, he⟩ := hv
  have hg₀ : ¬(Cond.eq
      (preprocessingRegisters r (ChanHe.Traversal.slot 0))
      (preprocessingRegisters r ChanHe.Traversal.zero)).Holds a := by
    change a.regs _ ≠ a.regs _
    have hf' : a.regs (preprocessingRegisters r (ChanHe.Traversal.slot 0)) = e.fuel := hl.1
    rw [hf', hz]
    exact hf
  have hg (j : Fin 3) : ¬(Cond.eq
      (preprocessingRegisters r (ChanHe.Traversal.arrayLength j))
      (preprocessingRegisters r ChanHe.Traversal.zero)).Holds a := by
    change a.regs _ ≠ a.regs _
    have hn' : a.regs (preprocessingRegisters r (ChanHe.Traversal.arrayLength j)) =
        (e.data j).length := hl.2.2 j
    rw [hn', hz]
    exact hn j
  have hbody : Exec w (body solver) x y (99 + (t + 2 + 2 + 2 + 2)) :=
    hp.seq (Exec.branch_neg hg₀ (Exec.branch_neg (hg 0) (Exec.branch_neg (hg 1)
      (Exec.branch_neg (hg 2) he))))
  exact hbody.within.mono (by omega)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
