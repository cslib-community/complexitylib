/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.Driver
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearchCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Scanning and entering the increasing-guess simulation

The fixed driver's first phase measures the actual input length. Its next clock enters the
outer search, which thereafter runs on the same original input. The scan costs only the
binary counter and one phase tag.

## Main results

* `Driver.exists_first_decision`: with a correct evaluator, the driver halts with the source
  machine's Boolean decision within `Driver.space`.
* `Driver.space_le_of_le`: `Driver.space` is linear in any bound on the evaluator allowance
  and the binary block parameters through the largest guess.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM

variable {k : ℕ} {Q : Type} (E : ScheduleSearch.Evaluator) (P : OuterSearch.Parameters)

/-- Once entered, the outer search runs step for step, including halted clocks. -/
theorem runFrom_inr (w : List Bool) (state : OuterSearch.State E) (t : ℕ) :
    (machine E k P).runFrom w (.inr state) t =
      .inr ((OuterSearch.machine E k P).runFrom w state t) := by
  have hstep (q : OuterSearch.State E) :
      (machine E k P).step w (.inr q) = .inr ((OuterSearch.machine E k P).step w q) := by
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inr]
    by_cases h : (OuterSearch.machine E k P).halted q = true <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte]
  induction t with
  | zero => rfl
  | succ t ih => rw [QueryMachine.runFrom_succ, ih, hstep, QueryMachine.runFrom_succ]

/-- Every scan clock reproduces the existing native length scanner. -/
theorem run_scan (w : List Bool) (j : ℕ) (hj : j ≤ w.length + 1) :
    (machine E k P).run w j = .inl (QueryMachine.InputLength.machine.run w j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hpre := QueryMachine.InputLength.live w (show j < w.length + 1 by omega)
    rw [QueryMachine.run_succ, ih (by omega), QueryMachine.run_succ]
    simp only [QueryMachine.step, QueryMachine.read, machine, Sum.elim_inl, hpre,
      Bool.false_eq_true, ↓reduceIte]

/-- The first clock after measuring length starts the actual outer search. -/
theorem run_entry (w : List Bool) :
    (machine E k P).run w (w.length + 2) = .inr (OuterSearch.initial E w.length) := by
  rw [show w.length + 2 = (w.length + 1) + 1 by omega, QueryMachine.run_succ,
    run_scan E P w _ le_rfl, QueryMachine.InputLength.run_at_end]
  simp only [QueryMachine.step, machine, Sum.elim_inl, Bool.false_eq_true, ↓reduceIte,
    QueryMachine.InputLength.machine, resume]

/-- Scan, handoff, and every subsequent outer-search clock share the original input. -/
theorem run_after_entry (w : List Bool) (t : ℕ) :
    (machine E k P).run w (w.length + 2 + t) =
      .inr ((OuterSearch.machine E k P).runFrom w (OuterSearch.initial E w.length) t) := by
  change (machine E k P).runFrom w (machine E k P).init (w.length + 2 + t) = _
  rw [QueryMachine.runFrom_add]
  change (machine E k P).runFrom w ((machine E k P).run w (w.length + 2)) t = _
  rw [run_entry, runFrom_inr]

/-- The complete scan prefix has logarithmic encoded state length. -/
theorem length_run_scan_le (w : List Bool) (j : ℕ) (hj : j ≤ w.length + 1) :
    (encState E ((machine E k P).run w j)).length ≤ 2 * (Nat.log2 w.length + 1) + 3 := by
  rw [run_scan E P w j hj]
  change (QueryMachine.InputLength.encState (QueryMachine.InputLength.machine.run w j)).length
    + 1 ≤ _
  have h := QueryMachine.InputLength.length_run_le w j
  omega

/-- Uniform scan and outer-search allowance through a given source halting clock, for
evaluator allowance `A` and parameters `P`. -/
@[expose] noncomputable def space (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (P : OuterSearch.Parameters)
    (N τ : ℕ) : ℕ :=
  2 * (Nat.log2 N + 1) + OuterSearch.space k A P N (max (N + 1) τ) + 4

variable {E}

/-- A halting source yields a first halt of the fixed driver, the exact Boolean decision, and
an all-clock bound. The source time is used only in this proof and its mathematical allowance. -/
theorem exists_first_decision {M : MultiTapeTM k Bool Q} {A : ℕ → ℕ → ℕ → ℕ}
    (hE : E.Correct M A) (w : List Bool) (τ : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) :
    ∃ T,
      (∀ t < T, (machine E k P).halted ((machine E k P).run w t) = false) ∧
      (machine E k P).halted ((machine E k P).run w T) = true ∧
      (machine E k P).output w T =
        [decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])] ∧
      ∀ t ≤ T, (encState E ((machine E k P).run w t)).length ≤ space k A P w.length τ := by
  classical
  obtain ⟨U, guess, hguess, hpre, hrun, hhalted, hspace⟩ :=
    OuterSearch.exists_first_decision hE P w τ hhalt
  let T := w.length + 2 + U
  have hfinal : (machine E k P).run w T = .inr
      (.inl (w.length, guess,
        some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])))) := by
    rw [run_after_entry, hrun]
  have hbefore : ∀ t < T, (machine E k P).halted ((machine E k P).run w t) = false := by
    intro t ht
    by_cases hscan : t ≤ w.length + 1
    · rw [run_scan E P w t hscan]
      rfl
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show w.length + 2 ≤ t by omega)
      rw [run_after_entry]
      exact hpre u (by dsimp only [T] at ht; omega)
  refine ⟨T, hbefore, ?_, ?_, ?_⟩
  · rw [hfinal]
    rfl
  · rw [QueryMachine.output_eq_of_not_halted _ _ hbefore]
    have hemit : (machine E k P).emit = fun _ => [] := rfl
    simp only [hemit, List.map_const', List.flatten_replicate_nil, List.nil_append]
    rw [hfinal]
    rfl
  · intro t ht
    by_cases hscan : t ≤ w.length + 1
    · have hs := length_run_scan_le (k := k) E P w t hscan
      dsimp only [space]
      omega
    · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show w.length + 2 ≤ t by omega)
      rw [run_after_entry]
      change (OuterSearch.encState E ((OuterSearch.machine E k P).runFrom w
        (OuterSearch.initial E w.length) u)).length + 1 ≤ _
      have hs := hspace u (show u ≤ U by dsimp only [T] at ht; omega)
      dsimp only [space]
      omega

/-- The complete driver storage is linear in any common bound `X` on the evaluator allowance,
the binary block width and the horizon of every guess through the largest one. -/
theorem space_le_of_le (k : ℕ) (A : ℕ → ℕ → ℕ → ℕ) (P : OuterSearch.Parameters) (N τ X : ℕ)
    (hX : ∀ guess ≤ max (N + 1) τ,
      A N (P.blockWidth guess) (P.horizon guess) + (P.blockWidth guess).size +
        P.horizon guess ≤ X) :
    space k A P N τ ≤ 64 * (k + 2) * (X + N.size + (max (N + 1) τ).size + 1) := by
  have hlog := Nat.log2_le_size N
  have hcandidate : OuterSearch.candidateSpace k A P N (max (N + 1) τ) ≤
      32 * N.size + (32 * k + 48) * X + 50 := by
    apply Finset.sup_le
    intro guess hguess
    have hle := hX guess (Nat.lt_succ_iff.mp (Finset.mem_range.mp hguess))
    have hhs : (P.horizon guess).size ≤ P.horizon guess := by
      simpa only [length_encNat_eq_size] using length_encNat_le_self (P.horizon guess)
    have hmul : k * P.horizon guess ≤ k * X := Nat.mul_le_mul_left k (by omega)
    simp only [ScheduleSearch.space, ScheduleSearch.callerSpace, ScheduleSearch.encArgs,
      length_encPair, length_encNat_eq_size]
    nlinarith
  simp only [space, OuterSearch.space, OuterSearch.callerSpace, length_encNat_eq_size]
  have hk : 0 ≤ k * X := Nat.zero_le _
  nlinarith

end Turing.MultiTapePTM.BlockComputation.Driver
