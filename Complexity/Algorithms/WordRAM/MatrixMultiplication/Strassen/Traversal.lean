/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Resume

/-!
# Native Strassen traversal induction

The explicit native controller executes all seven children, real parent resumptions and
the final pop. The proof inducts on matrix depth and the actual remaining child phases.
Every recursive execution comes from that induction; there is no assumed multiplication,
execution or time field in the final result. Root setup and initialized counter composition
must separately derive the entry invariants from original input data.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Internal remaining-work budget, including each real child and its parent return step.
The five double updates and two single updates account for exactly twelve coefficient loops. -/
@[expose] def suffixBudget (p k : ℕ) : Fin 7 → ℕ
  | 0 => 7 * traceBudget p k + 624 * (4 ^ k * p) + 731
  | 1 => 6 * traceBudget p k + 520 * (4 ^ k * p) + 617
  | 2 => 5 * traceBudget p k + 416 * (4 ^ k * p) + 503
  | 3 => 4 * traceBudget p k + 312 * (4 ^ k * p) + 389
  | 4 => 3 * traceBudget p k + 208 * (4 ^ k * p) + 275
  | 5 => 2 * traceBudget p k + 104 * (4 ^ k * p) + 161
  | 6 => traceBudget p k + 26 * (4 ^ k * p) + 57

private theorem suffixBudget_next (p k : ℕ) (phase : Fin 6) :
    traceBudget p k + (receiveBudget ⟨phase.val, by omega⟩ (4 ^ k * p) +
      52 * (4 ^ k * p) + 92) + 2 + suffixBudget p k ⟨phase.val + 1, by omega⟩ =
      suffixBudget p k ⟨phase.val, by omega⟩ := by
  fin_cases phase <;> norm_num [suffixBudget, receiveBudget] <;> omega

private abbrev Continues (w : ℕ) (x y : Data 64) (T : ℕ) : Prop :=
  ∀ z N, ExecWithin w controller y z N → ExecWithin w controller x z (T + N)

private theorem continues_trans {w U T : ℕ} {x y z : Data 64}
    (hxy : Continues w x y U) (hyz : Continues w y z T) : Continues w x z (U + T) := by
  intro s N hs
  exact (hxy s _ (hyz s N hs)).mono (by omega)

private theorem continues_step {w T : ℕ} {x y : Data 64}
    (hc : (Cond.lt Reg.zero Reg.active).Holds x) (he : ExecWithin w step x y T) :
    Continues w x y (T + 2) := by
  intro z N hz
  exact (ExecWithin.loop_iter hc he hz).mono (by omega)

/-- Complete native execution of one ready node, including every recursively executed
child, stack access, phase decision, operand loop, accumulation and return. The continuation
form charges the surrounding real loop while allowing a nonroot child to return to its parent. -/
theorem exec_ready (k : ℕ) {w p A B a b out scratch frames frame : ℕ}
    (x : Data 64) (u v : ℕ → ℤ) (hx : NodeReady p k a b out scratch frames frame x)
    (hl : NodeLayout p k a b out scratch frames frame)
    (hu : ∀ i < 4 ^ k * p, (u i).natAbs ≤ A)
    (hv : ∀ i < 4 ^ k * p, (v i).natAbs ≤ B)
    (hleft : ∀ i < 4 ^ k * p, x.mem (a + i) = encode (u i))
    (hright : ∀ i < 4 ^ k * p, x.mem (b + i) = encode (v i))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound p A B k : ℤ))
    (haddr : Fits (w + 2) (addressBound frames frame k)) :
    ∃ y, NodeResult p k out scratch frames frame u v x y ∧
      ∀ z T, ExecWithin (w + 2) controller y z T →
        ExecWithin (w + 2) controller x z (traceBudget p k + T) := by
  induction k generalizing A B a b out scratch frame x u v with
  | zero =>
    exact exec_ready_zero x u v hx hl
      (by simpa only [pow_zero, Nat.one_mul] using hu)
      (by simpa only [pow_zero, Nat.one_mul] using hv)
      (by simpa only [pow_zero, Nat.one_mul] using hleft)
      (by simpa only [pow_zero, Nat.one_mul] using hright) hmag haddr
  | succ k ih =>
    have childFits : GenericRAM.Signed.Fits w (magnitudeBound p (2 * A) (2 * B) k : ℤ) :=
      hmag.of_natAbs_le (by
        rw [Int.natAbs_natCast]
        exact child_magnitudeBound_le p A B k)
    have childAddr : Fits (w + 2) (addressBound frames (frame + 7) k) := by
      simpa only [addressBound_child] using haddr
    have childLayout := hl.child
    have remaining : ∀ remainingCount : ℕ, ∀ phase : Fin 7,
        6 - phase.val = remainingCount → ∀ child : Data 64,
        PendingChild p k a b out scratch frames frame phase u v x child →
        ∃ y, NodeResult p (k + 1) out scratch frames frame u v child y ∧
          Continues (w + 2) child y (suffixBudget p k phase) := by
      intro remainingCount
      induction remainingCount with
      | zero =>
        intro phase hphase child pending
        have hphase' : phase = 6 := Fin.ext (by omega)
        subst phase
        obtain ⟨returned, childResult, childExecution⟩ := ih child _ _ pending.ready childLayout
          (fun j hj => (Cslib.Algorithms.MatrixMultiplication.Strassen.operands_natAbs_le
            u 6 hu hj).1)
          (fun j hj => (Cslib.Algorithms.MatrixMultiplication.Strassen.operands_natAbs_le
            v 6 hv hj).2) pending.left pending.right childFits childAddr
        obtain ⟨y, stepRun, finalResult⟩ := exec_step_resume_finish x child returned u v
          hx.toNodeHeader hl pending childResult hu hv hmag haddr
        have active : (Cond.lt Reg.zero Reg.active).Holds returned := by
          have hf := hl.frames_before
          simp only [Cond.holds_lt, childResult.zero_eq, childResult.active_eq]
          rw [ite_eq_left (by omega)]
          decide
        have cont := continues_trans childExecution (continues_step active stepRun)
        refine ⟨y, { finalResult with outside := ?_ }, ?_⟩
        · intro d hd
          exact (finalResult.outside d hd).trans
            (childResult.outside d (fun h => hd (NodeWrites.child_subset hl h)))
        · simpa [suffixBudget, Nat.add_assoc] using cont
      | succ remainingCount inductionRemaining =>
        intro phase hphase child pending
        have hlt : phase.val < 6 := by omega
        let current : Fin 6 := ⟨phase.val, hlt⟩
        let next : Fin 7 := ⟨phase.val + 1, by omega⟩
        obtain ⟨returned, childResult, childExecution⟩ := ih child _ _ pending.ready childLayout
          (fun j hj => (Cslib.Algorithms.MatrixMultiplication.Strassen.operands_natAbs_le
            u phase hu hj).1)
          (fun j hj => (Cslib.Algorithms.MatrixMultiplication.Strassen.operands_natAbs_le
            v phase hv hj).2) pending.left pending.right childFits childAddr
        obtain ⟨nextChild, stepRun, nextPending, stepOutside⟩ := exec_step_resume_next current
          x child returned u v hx.toNodeHeader hl pending childResult hu hv hmag haddr
        obtain ⟨y, result, rest⟩ := inductionRemaining next (by dsimp [next]; omega)
          nextChild nextPending
        have active : (Cond.lt Reg.zero Reg.active).Holds returned := by
          have hf := hl.frames_before
          simp only [Cond.holds_lt, childResult.zero_eq, childResult.active_eq]
          rw [ite_eq_left (by omega)]
          decide
        have cont := continues_trans childExecution
          (continues_trans (continues_step active stepRun) rest)
        refine ⟨y, { result with outside := ?_ }, ?_⟩
        · intro d hd
          exact ((result.outside d hd).trans (stepOutside d hd)).trans
            (childResult.outside d (fun h => hd (NodeWrites.child_subset hl h)))
        · intro z T hz
          have hc := cont z T hz
          apply hc.mono
          have hb := suffixBudget_next p k current
          have heq : (⟨phase.val, by omega⟩ : Fin 7) = phase := Fin.ext rfl
          dsimp only [current, next] at *
          rw [heq] at hb hc
          rw [heq]
          omega
    obtain ⟨first, firstStep, firstPending, firstOutside⟩ :=
      exec_first_pending x u v hx hl hu hv hleft hright hmag haddr
    obtain ⟨y, result, rest⟩ := remaining 6 0 (by decide) first firstPending
    have active : (Cond.lt Reg.zero Reg.active).Holds x := by
      simp only [Cond.holds_lt, hx.zero_eq, hx.active_eq]
      decide
    have cont := continues_trans (continues_step active firstStep) rest
    refine ⟨y, { result with outside := ?_ }, ?_⟩
    · intro d hd
      exact (result.outside d hd).trans (firstOutside d hd)
    · intro z T hz
      exact (cont z T hz).mono (by simp only [traceBudget, suffixBudget]; omega)

end Cslib.Algorithms.WordRAM.Strassen
