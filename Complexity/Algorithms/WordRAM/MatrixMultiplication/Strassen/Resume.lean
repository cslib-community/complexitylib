/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Pending
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Next
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Finish

/-!
# Real parent resumption after a native Strassen child

These internal induction steps consume the proved semantic result of the same native child
controller. They actually reload the protected parent frame, recompute child pointers,
dispatch the saved phase, update the output and prepare the next child or return. The child
result is a recursive proof postcondition, never an extra program input or assumed solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The next actual parent iteration derives the next pending child from the previous
actual child return. Every load, comparison, tag, accumulation, form and push is charged. -/
theorem exec_step_resume_next {w p k A B a b out scratch frames frame : ℕ}
    (phase : Fin 6) (parent child returned : Data 64) (u v : ℕ → ℤ)
    (hp : NodeHeader p (k + 1) a b out scratch frames frame parent)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (pending : PendingChild p k a b out scratch frames frame ⟨phase.val, by omega⟩
      u v parent child)
    (hchild : NodeResult p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u ⟨phase.val, by omega⟩)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v ⟨phase.val, by omega⟩)
      child returned)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) step returned y
        (receiveBudget ⟨phase.val, by omega⟩ (4 ^ k * p) + 52 * (4 ^ k * p) + 92) ∧
      PendingChild p k a b out scratch frames frame ⟨phase.val + 1, by omega⟩ u v parent y ∧
      (∀ d, ¬NodeWrites p (k + 1) out scratch frames frame d → y.mem d = returned.mem d) := by
  let current : Fin 7 := ⟨phase.val, by omega⟩
  let next : Fin 7 := ⟨phase.val + 1, by omega⟩
  let selected : Fin 8 := ⟨phase.val + 1, by omega⟩
  have ha := hl.left_before
  have hb := hl.right_before
  have ho := hl.output_before
  have hs := hl.scratch_before
  have hf := hl.frames_before
  have hsize : 4 ^ (k + 1) * p = 4 * (4 ^ k * p) := by rw [pow_succ]; ring
  obtain ⟨originalA, originalB, partialWords, productWords⟩ := pending.after_result hl hchild
  obtain ⟨s, load, sm, sh, sphase, _, _⟩ := exec_restore_parent current parent child returned
    _ _ hp hl hchild pending.saved haddr
  obtain ⟨r, locate, rh, rc, rm, rr⟩ := exec_locateChild_header s sh hl haddr
  let z := dispatchState selected r
  have zm : z.mem = returned.mem := (dispatchState_mem selected r).trans (rm.trans sm)
  have zh : NodeHeader p (k + 1) a b out scratch frames frame z :=
    rh.of_regs_eq (fun i _ hi => dispatchState_regs selected r i (by
      intro he; subst i; contradiction))
  have zc : ChildBuffers p k scratch z :=
    rc.of_regs_eq (fun i _ hi => dispatchState_regs selected r i (by
      intro he; subst i; contradiction))
  obtain ⟨y, stageRun, ready, leftValues, rightValues, outputs, parentPhase, memory⟩ :=
    exec_stage_next phase z u v zh zc hl hu hv
      (by simpa only [zm] using originalA) (by simpa only [zm] using originalB)
      (by simpa only [zm] using partialWords) (by simpa only [zm] using productWords) hmag haddr
  have rphase : r.regs Reg.phase = selected.val :=
    (rr Reg.phase (by decide)).trans sphase
  have dispatched := exec_dispatch selected r y rh.zero_eq rphase
    (haddr.of_le (by unfold addressBound; omega)) stageRun
  have depthTest : ¬(Cond.eq Reg.depth Reg.zero).Holds s := by
    simp only [Cond.holds_eq, sh.depth_eq, sh.zero_eq]
    omega
  have dispatch_le : dispatchBudget selected ≤ 20 := by
    unfold dispatchBudget
    split <;> omega
  have he : ExecWithin (w + 2) step returned y
      (receiveBudget current (4 ^ k * p) + 52 * (4 ^ k * p) + 92) :=
    (load.seq (ExecWithin.branch_neg depthTest (locate.seq dispatched))).mono (by
      dsimp only [current] at *
      omega)
  refine ⟨y, he, ⟨ready, leftValues, rightValues, ?_, ?_, outputs, ?_⟩, ?_⟩
  · intro j hj
    rw [memory _ ?_ (Or.inl (by omega)) (Or.inl (by omega)), zm]
    · exact originalA j hj
    · rcases hl.left_disjoint with h | h <;> omega
  · intro j hj
    rw [memory _ ?_ (Or.inl (by omega)) (Or.inl (by omega)), zm]
    · exact originalB j hj
    · rcases hl.right_disjoint with h | h <;> omega
  · intro j
    by_cases heq : j.val = 6
    · have hj : j = 6 := Fin.ext heq
      subst j
      simpa [next] using parentPhase
    · rw [ite_eq_right heq, memory _ (Or.inr (by omega))
        (Or.inr (by rw [hsize] at hs; omega)) (Or.inl (by omega)), zm,
        hchild.parent_frame hl j, pending.saved j, ite_eq_right heq]
  · intro d hd
    obtain ⟨ho', hs', hf'⟩ := hl.outside_stage hd
    simpa only [zm] using memory d ho' hs' hf'

/-- The last actual parent iteration consumes the seventh returned child and returns the
complete product. Its frame/flag and every outside word are the actual final-state ones. -/
theorem exec_step_resume_finish {w p k A B a b out scratch frames frame : ℕ}
    (parent child returned : Data 64) (u v : ℕ → ℤ)
    (hp : NodeHeader p (k + 1) a b out scratch frames frame parent)
    (hl : NodeLayout p (k + 1) a b out scratch frames frame)
    (pending : PendingChild p k a b out scratch frames frame 6 u v parent child)
    (hchild : NodeResult p k (scratch + 2 * (4 ^ k * p)) (scratch + 3 * (4 ^ k * p))
      frames (frame + 7)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.leftOperand p k u 6)
      (Cslib.Algorithms.MatrixMultiplication.Strassen.rightOperand p k v 6) child returned)
    (hu : ∀ i < 4 ^ (k + 1) * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ (k + 1) * p, (v i).natAbs ≤ B)
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B (k + 1) : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame (k + 1))) :
    ∃ y, ExecWithin (w + 2) step returned y (26 * (4 ^ k * p) + 55) ∧
      NodeResult p (k + 1) out scratch frames frame u v returned y := by
  obtain ⟨_, _, partialWords, productWords⟩ := pending.after_result hl hchild
  obtain ⟨s, load, sm, sh, sphase, _, _⟩ := exec_restore_parent 6 parent child returned
    _ _ hp hl hchild pending.saved haddr
  obtain ⟨r, locate, rh, rc, rm, rr⟩ := exec_locateChild_header s sh hl haddr
  let z := dispatchState 7 r
  have zm : z.mem = returned.mem := (dispatchState_mem 7 r).trans (rm.trans sm)
  have zh : NodeHeader p (k + 1) a b out scratch frames frame z :=
    rh.of_regs_eq (fun i _ hi => dispatchState_regs 7 r i (by
      intro he; subst i; contradiction))
  have zc : ChildBuffers p k scratch z :=
    rc.of_regs_eq (fun i _ hi => dispatchState_regs 7 r i (by
      intro he; subst i; contradiction))
  obtain ⟨y, stageRun, result⟩ := exec_stage_finish z u v zh zc hl hu hv
    (by simpa [zm] using partialWords) (by simpa only [zm] using productWords) hmag haddr
  have rphase : r.regs Reg.phase = 7 := (rr Reg.phase (by decide)).trans sphase
  have dispatched := exec_dispatch 7 r y rh.zero_eq rphase
    (haddr.of_le (by unfold addressBound; omega)) stageRun
  have depthTest : ¬(Cond.eq Reg.depth Reg.zero).Holds s := by
    simp only [Cond.holds_eq, sh.depth_eq, sh.zero_eq]
    omega
  have he : ExecWithin (w + 2) step returned y (26 * (4 ^ k * p) + 55) :=
    (load.seq (ExecWithin.branch_neg depthTest (locate.seq dispatched))).mono (by
      norm_num [dispatchBudget]
      omega)
  refine ⟨y, he, { result with outside := ?_ }⟩
  intro d hd
  simpa only [zm] using result.outside d hd

end Cslib.Algorithms.WordRAM.Strassen
