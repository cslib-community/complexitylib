/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Driver
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearchCorrect

/-!
# Scanning and entering the increasing-guess simulation

The fixed driver's first phase measures the actual input length. Its next clock enters the
outer search, which thereafter runs on the same original input. The scan costs only the
binary counter and one phase tag.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

variable {k s : ℕ} {Q : Type}

/-- Once entered, the outer search runs step for step, including halted clocks. -/
theorem runFrom_inr (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (state : OuterSearch.State k Q) (t : ℕ) :
    (machine M e).runFrom w (.inr state) t =
      .inr ((OuterSearch.machine M e).runFrom w state t) := by
  have hstep (q : OuterSearch.State k Q) :
      (machine M e).step w (.inr q) = .inr ((OuterSearch.machine M e).step w q) := by
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inr]
    by_cases h : (OuterSearch.machine M e).halted q = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih, hstep, QueryMachine.runFrom_succ]

/-- Every scan clock reproduces the existing native length scanner. -/
theorem run_scan (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (j : ℕ) (hj : j ≤ w.length + 1) :
    (machine M e).run w j = .inl (QueryMachine.InputLength.machine.run w j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hpre := QueryMachine.InputLength.live w (show j < w.length + 1 by omega)
    rw [QueryMachine.run_succ, ih (by omega), QueryMachine.run_succ]
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inl, hpre,
      Bool.false_eq_true, ↓reduceIte]

/-- The first clock after measuring length starts the actual outer search. -/
theorem run_entry (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool) :
    (machine M e).run w (w.length + 2) = .inr (OuterSearch.initial w.length) := by
  rw [show w.length + 2 = (w.length + 1) + 1 by omega, QueryMachine.run_succ,
    run_scan M e w _ le_rfl, QueryMachine.InputLength.run_at_end]
  simp only [QueryMachine.step, machine, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte,
    QueryMachine.InputLength.machine, resume]

/-- Scan, handoff, and every subsequent outer-search clock share the original input. -/
theorem run_after_entry (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (t : ℕ) :
    (machine M e).run w (w.length + 2 + t) =
      .inr ((OuterSearch.machine M e).runFrom w (OuterSearch.initial w.length) t) := by
  change (machine M e).runFrom w (machine M e).init (w.length + 2 + t) = _
  rw [QueryMachine.runFrom_add]
  change (machine M e).runFrom w ((machine M e).run w (w.length + 2)) t = _
  rw [run_entry, runFrom_inr]

/-- The complete scan prefix has logarithmic encoded state length. -/
theorem length_run_scan_le [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (j : ℕ) (hj : j ≤ w.length + 1) :
    (encState ((machine M e).run w j)).length ≤ 2 * (Nat.log2 w.length + 1) + 3 := by
  rw [run_scan M e w j hj]
  change (QueryMachine.InputLength.encState (QueryMachine.InputLength.machine.run w j)).length
    + 1 ≤ _
  have h := QueryMachine.InputLength.length_run_le w j
  omega

/-- Uniform scan and outer-search allowance through a given source halting clock. -/
@[expose] noncomputable def space (k s : ℕ) (Q : Type) (N τ : ℕ) : ℕ :=
  2 * (Nat.log2 N + 1) + OuterSearch.space k s Q N (max (N + 1) τ) + 4

/-- A halting source yields a first halt of the fixed driver, the exact Boolean decision, and
an all-clock bound. The source time is used only in this proof and its mathematical allowance. -/
theorem exists_first_decision [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (τ : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) :
    ∃ T,
      (∀ t < T, (machine M e).halted ((machine M e).run w t) = false) ∧
      (machine M e).halted ((machine M e).run w T) = true ∧
      (machine M e).output w T =
        [decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])] ∧
      ∀ t ≤ T, (encState ((machine M e).run w t)).length ≤ space k s Q w.length τ := by
  classical
  obtain ⟨U, guess, hguess, hpre, hrun, hhalted, hspace⟩ :=
    OuterSearch.exists_first_decision M e w τ hhalt
  let T := w.length + 2 + U
  have hfinal : (machine M e).run w T = .inr
      (.inl (w.length, guess,
        some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])))) := by
    rw [run_after_entry, hrun]
  have hbefore : ∀ t < T, (machine M e).halted ((machine M e).run w t) = false := by
    intro t ht
    by_cases hscan : t ≤ w.length + 1
    · rw [run_scan M e w t hscan]
      rfl
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show w.length + 2 ≤ t by omega)
      rw [run_after_entry]
      exact hpre u (by dsimp only [T] at ht; omega)
  refine ⟨T, hbefore, ?_, ?_, ?_⟩
  · rw [hfinal]
    rfl
  · rw [QueryMachine.output_eq_of_not_halted _ _ hbefore]
    have hemit : (machine M e).emit = fun _ => [] := rfl
    simp only [hemit, List.map_const', List.flatten_replicate_nil, List.nil_append]
    rw [hfinal]
    rfl
  · intro t ht
    by_cases hscan : t ≤ w.length + 1
    · have hs := length_run_scan_le M e w t hscan
      dsimp only [space]
      omega
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show w.length + 2 ≤ t by omega)
      rw [run_after_entry]
      change (OuterSearch.encState ((OuterSearch.machine M e).runFrom w
        (OuterSearch.initial w.length) u)).length + 1 ≤ _
      have hs := hspace u (show u ≤ U by dsimp only [T] at ht; omega)
      dsimp only [space]
      omega

end Turing.MultiTapePTM.BlockComputation.Driver
