/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Program
import Complexity.Computability.WordRAM.SymbolicExec
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
  have hfit_le (v : ℕ) (hv : v ≤ 6) : Fits w v := hfit.of_le hv
  have hidem (z : Data 64) (a b : ℕ) : (z.set Reg.tag a).set Reg.tag b = z.set Reg.tag b := by
    simp only [Data.set, Function.update_idem]
  refine WP.execWithin ?_
  unfold dispatch
  fin_cases phase <;>
    simp only [dispatchBudget, dispatchState, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, ↓reduceIte, Nat.reduceLT, Nat.reduceEqDiff, Nat.reduceMul, Nat.reduceAdd,
      Nat.min_def, Nat.reduceLeDiff] at hphase hstage ⊢ <;>
    wram_exec [hphase, hzero, hfit_le]
  all_goals refine WP.of_execWithin (y := y) (T := T) ?_ ⟨by omega, rfl⟩
  all_goals simpa only [hidem] using hstage

end Cslib.Algorithms.WordRAM.Strassen
