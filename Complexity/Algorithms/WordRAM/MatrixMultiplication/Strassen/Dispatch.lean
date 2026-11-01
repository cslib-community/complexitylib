/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
import Mathlib.Tactic.FinCases

/-!
# Charged native Strassen phase dispatch

This internal proof follows every actual comparison and tag constant in the fixed branch
chain. The selected stage executes ordinary native code; no uncharged table dispatch is
introduced. Positive branches cost one instruction, negative branches two.
-/

public section

namespace Cslib.Algorithms.WordRAM.Strassen

open Cslib.WordRAM

/-- Comparisons and tag constants executed before the selected real stage. -/
@[expose] def dispatchBudget (phase : Fin 8) : ℕ :=
  if phase.val < 7 then 3 * phase.val + 1 else 20

/-- The tag value actually assigned by the branch chain before entering a stage. -/
@[expose] def dispatchState (phase : Fin 8) (x : Data 64) : Data 64 :=
  if phase.val = 0 then x else x.set Reg.tag (min phase.val 6)

/-- The dispatch prefix only writes the tag register. -/
theorem dispatchState_regs (phase : Fin 8) (x : Data 64) (i : Fin 64) (hi : i ≠ Reg.tag) :
    (dispatchState phase x).regs i = x.regs i := by
  unfold dispatchState
  split
  · rfl
  · exact Function.update_of_ne hi _ _

/-- Comparisons and tag constants never change memory. -/
theorem dispatchState_mem (phase : Fin 8) (x : Data 64) : (dispatchState phase x).mem = x.mem := by
  unfold dispatchState
  split <;> rfl

/-- Follow the actual phase chain, charging every failed comparison and tag assignment.
The stage premise is an internal composition step, discharged by the native stage lemmas. -/
theorem exec_dispatch {w T : ℕ} (phase : Fin 8) (x y : Data 64)
    (hzero : x.regs Reg.zero = 0) (hphase : x.regs Reg.phase = phase.val)
    (hfit : Fits w 6)
    (hstage : ExecWithin w (stage phase) (dispatchState phase x) y T) :
    ExecWithin w dispatch x y (T + dispatchBudget phase) := by
  fin_cases phase
  all_goals simp only [dispatchBudget]
  all_goals norm_num
  all_goals unfold dispatch
  all_goals change x.regs (38 : Fin 64) = _ at hphase
  all_goals change x.regs (49 : Fin 64) = 0 at hzero
  case «0» =>
    have hc : (Cond.eq Reg.phase Reg.zero).Holds x := by
      change x.regs (38 : Fin 64) = x.regs (49 : Fin 64)
      exact hphase.trans hzero.symm
    exact .branch_pos hc (by simpa [dispatchState, stage] using hstage)
  case «1» =>
    let s1 := x.set Reg.tag 1
    have hstart : ExecWithin w (stage 1) s1 y T := by
      simpa [dispatchState, stage, s1, Data.set, Function.update_idem] using hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc1 : (Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_pos hc1 hstart))).mono (by omega)
  case «2» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    have hstart : ExecWithin w (stage 2) s2 y T := by
      simpa [dispatchState, stage, s1, s2, Data.set, Function.update_idem] using hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc2 : (Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_pos hc2 hstart))))).mono
      (by omega)
  case «3» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    let s3 := s2.set Reg.tag 3
    have hstart : ExecWithin w (stage 3) s3 y T := by
      simpa [dispatchState, stage, s1, s2, s3, Data.set, Function.update_idem] using hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, s3, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, s3, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc2 : ¬(Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, s3, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    have hc3 : (Cond.eq Reg.phase Reg.tag).Holds s3 := by
      norm_num [Cond.holds_eq, s1, s2, s3, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase, hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc2
      ((ExecWithin.const (x := s2) (d := Reg.tag) (v := 3) (hfit.of_le (by decide))).seq
      (ExecWithin.branch_pos hc3 hstart))))))).mono (by omega)
  case «4» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    let s3 := s2.set Reg.tag 3
    let s4 := s3.set Reg.tag 4
    have hstart : ExecWithin w (stage 4) s4 y T := by
      simpa [dispatchState, stage, s1, s2, s3, s4, Data.set, Function.update_idem] using hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc2 : ¬(Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc3 : ¬(Cond.eq Reg.phase Reg.tag).Holds s3 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc4 : (Cond.eq Reg.phase Reg.tag).Holds s4 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc2
      ((ExecWithin.const (x := s2) (d := Reg.tag) (v := 3) (hfit.of_le (by decide))).seq
      (ExecWithin.branch_neg hc3 ((ExecWithin.const (x := s3) (d := Reg.tag) (v := 4) (hfit.of_le
      (by decide))).seq (ExecWithin.branch_pos hc4 hstart))))))))).mono (by omega)
  case «5» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    let s3 := s2.set Reg.tag 3
    let s4 := s3.set Reg.tag 4
    let s5 := s4.set Reg.tag 5
    have hstart : ExecWithin w (stage 5) s5 y T := by
      simpa [dispatchState, stage, s1, s2, s3, s4, s5, Data.set, Function.update_idem] using hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc2 : ¬(Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc3 : ¬(Cond.eq Reg.phase Reg.tag).Holds s3 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc4 : ¬(Cond.eq Reg.phase Reg.tag).Holds s4 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    have hc5 : (Cond.eq Reg.phase Reg.tag).Holds s5 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, Data.set, Reg.phase, Reg.zero, Reg.tag, hphase,
        hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc2
      ((ExecWithin.const (x := s2) (d := Reg.tag) (v := 3) (hfit.of_le (by decide))).seq
      (ExecWithin.branch_neg hc3 ((ExecWithin.const (x := s3) (d := Reg.tag) (v := 4) (hfit.of_le
      (by decide))).seq (ExecWithin.branch_neg hc4 ((ExecWithin.const (x := s4) (d := Reg.tag) (v
      := 5) (hfit.of_le (by decide))).seq (ExecWithin.branch_pos hc5 hstart))))))))))).mono (by
      omega)
  case «6» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    let s3 := s2.set Reg.tag 3
    let s4 := s3.set Reg.tag 4
    let s5 := s4.set Reg.tag 5
    let s6 := s5.set Reg.tag 6
    have hstart : ExecWithin w (stage 6) s6 y T := by
      simpa [dispatchState, stage, s1, s2, s3, s4, s5, s6, Data.set, Function.update_idem] using
        hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc2 : ¬(Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc3 : ¬(Cond.eq Reg.phase Reg.tag).Holds s3 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc4 : ¬(Cond.eq Reg.phase Reg.tag).Holds s4 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc5 : ¬(Cond.eq Reg.phase Reg.tag).Holds s5 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc6 : (Cond.eq Reg.phase Reg.tag).Holds s6 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc2
      ((ExecWithin.const (x := s2) (d := Reg.tag) (v := 3) (hfit.of_le (by decide))).seq
      (ExecWithin.branch_neg hc3 ((ExecWithin.const (x := s3) (d := Reg.tag) (v := 4) (hfit.of_le
      (by decide))).seq (ExecWithin.branch_neg hc4 ((ExecWithin.const (x := s4) (d := Reg.tag) (v
      := 5) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc5 ((ExecWithin.const (x := s5)
      (d := Reg.tag) (v := 6) (hfit.of_le (by decide))).seq (ExecWithin.branch_pos hc6
      hstart))))))))))))).mono (by omega)
  case «7» =>
    let s1 := x.set Reg.tag 1
    let s2 := s1.set Reg.tag 2
    let s3 := s2.set Reg.tag 3
    let s4 := s3.set Reg.tag 4
    let s5 := s4.set Reg.tag 5
    let s6 := s5.set Reg.tag 6
    have hstart : ExecWithin w (stage 7) s6 y T := by
      simpa [dispatchState, stage, s1, s2, s3, s4, s5, s6, Data.set, Function.update_idem] using
        hstage
    have hc0 : ¬(Cond.eq Reg.phase Reg.zero).Holds x := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc1 : ¬(Cond.eq Reg.phase Reg.tag).Holds s1 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc2 : ¬(Cond.eq Reg.phase Reg.tag).Holds s2 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc3 : ¬(Cond.eq Reg.phase Reg.tag).Holds s3 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc4 : ¬(Cond.eq Reg.phase Reg.tag).Holds s4 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc5 : ¬(Cond.eq Reg.phase Reg.tag).Holds s5 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    have hc6 : ¬(Cond.eq Reg.phase Reg.tag).Holds s6 := by
      norm_num [Cond.holds_eq, s1, s2, s3, s4, s5, s6, Data.set, Reg.phase, Reg.zero, Reg.tag,
        hphase, hzero]
    exact (ExecWithin.branch_neg hc0 ((ExecWithin.const (x := x) (d := Reg.tag) (v := 1)
      (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc1 ((ExecWithin.const (x := s1) (d :=
      Reg.tag) (v := 2) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc2
      ((ExecWithin.const (x := s2) (d := Reg.tag) (v := 3) (hfit.of_le (by decide))).seq
      (ExecWithin.branch_neg hc3 ((ExecWithin.const (x := s3) (d := Reg.tag) (v := 4) (hfit.of_le
      (by decide))).seq (ExecWithin.branch_neg hc4 ((ExecWithin.const (x := s4) (d := Reg.tag) (v
      := 5) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc5 ((ExecWithin.const (x := s5)
      (d := Reg.tag) (v := 6) (hfit.of_le (by decide))).seq (ExecWithin.branch_neg hc6
      (hstart)))))))))))))).mono (by omega)

end Cslib.Algorithms.WordRAM.Strassen
