/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.ObservedProcess
import CslibFrontier.Probability.PMF.Expect
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic

/-!
# Unbounded stopped discrete execution

An absorbing hidden-state process has an actual terminal subdistribution, the
increasing limit of its clocked halted masses. Completing missing mass with
`none` records nontermination rather than assuming a common terminating clock.
The complete stopped state may contain a whole finite transcript and resources.

This is a limit construction from actual transition laws, not a supplied
representation or termination certificate. Arbitrary discrete state types are
allowed; no almost-sure termination or finite expectation is required.

## Main results

* `terminal_score`: monotone convergence for every nonnegative terminal score.
* `terminal_support`: a terminal state occurs at some actual finite clock.
* `terminal_observed`: complete stopped observations have the constructed behavioral law.
-/

public section
noncomputable section
namespace Cslib.Probability.StoppedProcess
open scoped ENNReal
open ObservedProcess
variable {S H : Type}

/-- Monotone convergence of discrete nonnegative sums, on arbitrary types. -/
theorem tsum_iSup_nat {A : Type} (f : ℕ → A → ℝ≥0∞) (hm : Monotone f) :
    (∑' a, ⨆ n, f n a) = ⨆ n, ∑' a, f n a := by
  let : MeasurableSpace A := ⊤
  simpa only [MeasureTheory.lintegral_count] using
    (MeasureTheory.lintegral_iSup (μ := MeasureTheory.Measure.count)
      (fun _ => measurable_from_top) hm)

/-- Complete a discrete subprobability law with explicit divergence mass. -/
@[expose] def withDivergence (mass : S → ℝ≥0∞) (hm : ∑' x, mass x ≤ 1) : PMF (Option S) :=
  ⟨fun x => x.elim (1 - ∑' s, mass s) mass, by
    apply CompleteLattice.summable.hasSum_iff.mpr
    rw [← (Equiv.optionEquivSumPUnit.{0, 0} S).symm.tsum_eq,
      Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
    simp only [Equiv.optionEquivSumPUnit_symm_inl,
      Equiv.optionEquivSumPUnit_symm_inr, Option.elim_some, Option.elim_none,
      tsum_fintype, Fintype.sum_unique]
    exact add_tsub_cancel_of_le hm⟩

/-- A PMF on optional states is determined by all its terminating masses. -/
theorem option_ext {p q : PMF (Option S)} (h : ∀ x, p (some x) = q (some x)) : p = q := by
  have hp := p.tsum_coe
  have hq := q.tsum_coe
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} S).symm.tsum_eq,
    Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable] at hp hq
  simp only [Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr, tsum_fintype, Fintype.sum_unique, h] at hp hq
  have hs : (∑' x, q (some x)) ≠ ⊤ := ne_top_of_le_ne_top (show (1 : ℝ≥0∞) ≠ ⊤ by norm_num)
    (by rw [← hq]; exact le_self_add)
  have hn : p none = q none := (ENNReal.add_right_inj hs).mp (hp.trans hq.symm)
  ext x
  cases x with
  | none => exact hn
  | some x => exact h x

variable (step : S → PMF S) (halt : S → Prop) [DecidablePred halt]

/-- Actual mass already halted at a particular native or abstract clock. -/
@[expose] def stopped (n : ℕ) (s x : S) : ℝ≥0∞ :=
  if halt x then stateLaw step n s x else 0

/-- Terminal masses are derived from all finite actual executions. -/
@[expose] def terminalMass (s x : S) : ℝ≥0∞ := ⨆ n, stopped step halt n s x

variable (absorb : ∀ x, halt x → step x = PMF.pure x)
include absorb

/-- Previously halted mass cannot be lost at a later clock. -/
theorem stopped_mono (s : S) : Monotone (fun n => stopped step halt n s) := by
  apply monotone_nat_of_le_succ
  intro n x
  by_cases hx : halt x
  · simp only [stopped, ite_eq_left hx, stateLaw, PMF.bind_apply]
    calc
      stateLaw step n s x = stateLaw step n s x * step x x := by rw [absorb x hx]; simp
      _ ≤ ∑' y, stateLaw step n s y * step y x :=
        le_tsum (fun y => stateLaw step n s y * step y x) x
  · simp [stopped, hx]

omit absorb in
/-- Total halted mass at any clock is at most one. -/
theorem stopped_sum_le (n : ℕ) (s : S) : ∑' x, stopped step halt n s x ≤ 1 := by
  calc
    _ ≤ ∑' x, stateLaw step n s x := tsum_le_tsum fun x => by
      by_cases hx : halt x <;> simp [stopped, hx]
    _ = 1 := (stateLaw step n s).tsum_coe

omit absorb in
/-- Splitting off the first actual instruction, retaining hidden state. -/
theorem stateLaw_succ_left (n : ℕ) (s : S) :
    stateLaw step (n + 1) s = (step s).bind (stateLaw step n) := by
  induction n with
  | zero => simp [stateLaw]
  | succ n ih =>
    change ((stateLaw step (n + 1) s).bind step) = _
    rw [ih, PMF.bind_bind]
    rfl

/-- The unbounded halted-state masses satisfy the actual first-step equation.
This follows from their clock limit and does not select an arbitrary fixed point. -/
theorem terminalMass_unfold (s x : S) :
    terminalMass step halt s x = ∑' next, step s next * terminalMass step halt next x := by
  have hs : (⨆ n, stopped step halt n s x) = ⨆ n, stopped step halt (n + 1) s x := by
    apply le_antisymm
    · exact iSup_le fun n => (stopped_mono step halt absorb s (Nat.le_succ n) x).trans
        (le_iSup (fun m => stopped step halt (m + 1) s x) n)
    · exact iSup_le fun n => le_iSup (fun m => stopped step halt m s x) (n + 1)
  unfold terminalMass
  rw [hs]
  simp only [ENNReal.mul_iSup]
  rw [tsum_iSup_nat _ (by
    intro i j hij next
    change step s next * stopped step halt i next x ≤ step s next * stopped step halt j next x
    gcongr
    exact stopped_mono step halt absorb next hij x)]
  apply iSup_congr
  intro n
  by_cases hx : halt x
  · simp only [stopped, ite_eq_left hx, stateLaw_succ_left, PMF.bind_apply]
  · simp [stopped, hx]

omit [DecidablePred halt] in
/-- Actual halting is absorbing at every finite clock. -/
theorem stateLaw_halted (s : S) (h : halt s) (n : ℕ) :
    stateLaw step n s = PMF.pure s := by
  induction n with
  | zero => rfl
  | succ n ih => simp [stateLaw, ih, absorb s h]

/-- An already halted state has its actual deterministic terminal law. -/
theorem terminalMass_halted (s : S) (h : halt s) (x : S) :
    terminalMass step halt s x = PMF.pure s x := by
  classical
  simp only [terminalMass, stopped, stateLaw_halted step halt absorb s h]
  by_cases hx : halt x
  · simp [hx]
  · have hn : x ≠ s := fun he => hx (he ▸ h)
    simp [hx, PMF.pure_apply, hn]

/-- No probability mass is created by taking the unbounded stopped limit. -/
theorem terminalMass_sum_le (s : S) : ∑' x, terminalMass step halt s x ≤ 1 := by
  change (∑' x, ⨆ n, stopped step halt n s x) ≤ 1
  rw [tsum_iSup_nat _ (stopped_mono step halt absorb s)]
  exact iSup_le fun n => stopped_sum_le step halt n s

/-- Nontermination is missing stopped mass. It is not a failed, halted result. -/
@[expose] def divergence (s : S) : ℝ≥0∞ := 1 - ∑' x, terminalMass step halt s x

/-- Actual unbounded execution. `some` retains a complete halted state and
`none` denotes divergence; no common finite clock is chosen. -/
@[expose] def terminal (s : S) : PMF (Option S) :=
  withDivergence (terminalMass step halt s) (terminalMass_sum_le step halt absorb s)

/-- The unbounded law's point masses are the actual clock limit. -/
theorem terminal_some (s x : S) :
    terminal step halt absorb s (some x) = terminalMass step halt s x := rfl

/-- Nontermination remains visible as a separate event. -/
theorem terminal_none (s : S) : terminal step halt absorb s none = divergence step halt s := rfl

/-- Every supported terminal state comes from an actual finite run; null states
cannot enter through the limit or its divergence completion. -/
theorem terminal_support (s x : S) :
    some x ∈ (terminal step halt absorb s).support ↔
      halt x ∧ ∃ n, x ∈ (stateLaw step n s).support := by
  simp only [PMF.mem_support_iff, terminal_some, terminalMass, stopped]
  by_cases hx : halt x
  · simp only [hx, ite_true, true_and]
    have he : (⨆ n, stateLaw step n s x) = 0 ↔ ∀ n, stateLaw step n s x = 0 := iSup_eq_bot
    simp only [ne_eq, he, not_forall]
  · simp [hx]

/-- Monotone convergence for every nonnegative stopped score, including joint
output/resource indicators and unbounded token scores. Divergence is excluded
explicitly, not assigned a terminal bill. -/
theorem terminal_score (s : S) (score : S → ℝ≥0∞) :
    (∑' x, terminal step halt absorb s (some x) * score x) =
      ⨆ n, ∑' x, stopped step halt n s x * score x := by
  simp only [terminal_some, terminalMass, ENNReal.iSup_mul]
  apply tsum_iSup_nat
  intro i j hij x
  change stopped step halt i s x * score x ≤ stopped step halt j s x * score x
  gcongr
  exact stopped_mono step halt absorb s hij x

open Classical in
/-- A complete observed stopped-state law is derived from the actual
history-dependent behavioral process. Local silent steps are retained in that
process; only the final complete observation is read here. -/
theorem terminal_observed (s : S) (observe : S → H) (done : H → Prop)
    [DecidablePred done] (hd : ∀ x, done (observe x) ↔ halt x) (z : H) :
    (terminal step halt absorb s).map (Option.map observe) (some z) =
      ⨆ n, ∑' history, publicLaw step observe n s history *
        (if done (history.headD (observe s)) ∧ history.headD (observe s) = z then 1 else 0) := by
  classical
  have score (n : ℕ) :
      (∑' history, publicLaw step observe n s history *
        (if done (history.headD (observe s)) ∧ history.headD (observe s) = z then 1 else 0)) =
      ∑' x, stopped step halt n s x * (if observe x = z then 1 else 0) := by
    have he := congrArg (fun p : PMF H => ∑' h, p h *
      (if done h ∧ h = z then 1 else 0)) (public_current step observe n s)
    simp only [PMF.tsum_map_mul] at he
    convert he using 1
    apply tsum_congr
    intro x
    simp only [stopped, ← hd x]
    by_cases hx : done (observe x) <;> by_cases hz : observe x = z <;> simp [hx, hz]
  simp only [score]
  rw [← terminal_score step halt absorb]
  simp only [PMF.map_apply]
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} S).symm.tsum_eq,
      Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr, Option.map_some, Option.map_none,
    Option.some.injEq, reduceCtorEq, ite_false, tsum_zero, add_zero]
  apply tsum_congr
  intro x
  by_cases hx : observe x = z
  · simp [hx]
  · simp [hx, Ne.symm hx]

end Cslib.Probability.StoppedProcess
