/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Step

/-!
# Complete charged native sparse-query loop

The loop repeatedly executes the actual proved pop/expand/consume block. A finite
measure decoded from occupied native stack words decreases at every iteration.
The initialized frontier accounts for the complete original allowed-leaf sum, and
all original arrays and retained table words remain protected throughout execution.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Complete actual query traversal, charging every real controller iteration and loop exit. -/
theorem exec_loop {w L m t AA BB D V K F A B : ℕ} (x : Data registers)
    (η : OutStr L) (hη : (innerSetO η).card = m) (a b : Leaf L → ℤ)
    (ha : ∀ τ, (a τ).natAbs ≤ A) (hb : ∀ τ, (b τ).natAbs ≤ B)
    (hx : Ready η m t AA BB D V K F a b [] [[]] x)
    (hK : K = (boxes L m t).card) (hF : F = V + K)
    (hAA : AA + 10 ^ L ≤ F) (hBB : BB + 10 ^ L ≤ F)
    (hD : D + (m - t + 1) * 10 ^ L ≤ F)
    (hfit : Fits (w + 2) (queryAddressBound L t AA BB D V K))
    (hmag : GenericRAM.Signed.Fits w (magnitudeBound L A B : ℕ)) :
    ∃ y, ExecWithin (w + 2) (.loop (.lt BoxTable.Reg.nil Reg.top) body) x y
        (258 * (L + 1) * (queryLeaves m t η).card + 2) ∧
      Parameters L t (PrunedQuery.queryIndex η).val AA BB D V K F y ∧
      y.regs Reg.top = 0 ∧ y.regs Reg.answer = Signed.encode (queryValue m t η a b) ∧
      Readback m t D V AA BB a b y.mem ∧
      (∀ q, ¬(F ≤ q ∧ q < F + 5 * stackCapacity L) → y.mem q = x.mem q) := by
  let I (y : Data registers) : Prop :=
    ∃ finished tasks, Ready η m t AA BB D V K F a b finished tasks y ∧
      ∀ q, ¬(F ≤ q ∧ q < F + 5 * stackCapacity L) → y.mem q = x.mem q
  have hi : I x := ⟨[], [[]], hx, fun _ _ => rfl⟩
  have hbody (y : Data registers) (hy : I y)
      (hc : (Cond.lt BoxTable.Reg.nil Reg.top).Holds y) :
      ∃ z, ExecWithin (w + 2) body y z 256 ∧ I z ∧
        workMeasure η t F z < workMeasure η t F y := by
    obtain ⟨finished, tasks, hready, hframe⟩ := hy
    cases tasks with
    | nil =>
      have htop : y.regs Reg.top = 0 := hready.top
      simp only [Cond.holds_lt, hready.parameters.nil, htop, lt_self_iff_false] at hc
    | cons xs tasks =>
      obtain ⟨z, finished', tasks', hz, hzready, hzwork, hzframe⟩ :=
        exec_step y η hη a b ha hb finished xs tasks hready hK hF hAA hBB hD hfit hmag
      exact ⟨z, hz, ⟨finished', tasks', hzready,
        fun q hq => (hzframe q hq).trans (hframe q hq)⟩, hzwork⟩
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I
    (workMeasure η t F) hbody hi
  obtain ⟨finished, tasks, hready, hframe⟩ := hIy
  have htop : y.regs Reg.top = 0 := by
    simp only [Cond.holds_lt, hready.parameters.nil, not_lt] at hstop
    omega
  have htasks : tasks = [] := List.length_eq_zero_iff.mp (hready.top.symm.trans htop)
  subst tasks
  have hvalue : (finished.map (leafQueryValue m t η a b)).sum = queryValue m t η a b := by
    have hv := hready.frontier.finished_value
    rw [possibleLeaves_root_eq_queryLeaves η hη] at hv
    exact hv
  refine ⟨y, ?_, hready.parameters, htop, hready.answer.trans
    (congrArg Signed.encode hvalue), hready.table, hframe⟩
  have hwork : workMeasure η t F x = (L + 1) * (queryLeaves m t η).card := by
    rw [hx.work_eq, frontierWork_root, possibleLeaves_root_eq_queryLeaves η hη]
  simpa only [hwork, Nat.reduceAdd, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hy

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
