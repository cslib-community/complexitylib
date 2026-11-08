/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF.StoppedProcess
import Complexity.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Pausing an actual discrete execution at its next boundary

`beforeBoundary` executes the original transition until the first selected
boundary, then holds that exact hidden state. Its stopped law retains missing
boundary-hit mass as divergence. `terminal_restart` proves that pausing and
resuming leaves the entire original terminal law unchanged, without assuming
almost-sure boundary reach or a common clock.

## Main results

* `terminal_restart`: actual first-boundary disintegration of the complete stopped law.
* `terminal_step`: unbounded stopped execution satisfies its actual one-step law.
-/

public section
noncomputable section
namespace Cslib.Probability.StoppedProcess
open ObservedProcess
open scoped ENNReal
variable {S : Type}

/-- Stop before crossing a selected boundary, retaining its complete hidden state. -/
@[expose] def beforeBoundary (step : S → PMF S) (boundary : S → Prop)
    [DecidablePred boundary] (s : S) : PMF S :=
  if boundary s then PMF.pure s else step s

/-- The first boundary is absorbing, rather than dispatched prematurely. -/
theorem beforeBoundary_absorbs (step : S → PMF S) (boundary : S → Prop)
    [DecidablePred boundary] (s : S) (h : boundary s) :
    beforeBoundary step boundary s = PMF.pure s := by simp [beforeBoundary, h]

private theorem stopped_succ_left (step : S → PMF S) (halt : S → Prop)
    [DecidablePred halt] (n : ℕ) (s x : S) :
    stopped step halt (n + 1) s x = ∑' next, step s next * stopped step halt n next x := by
  by_cases hx : halt x
  · simp only [stopped, ite_eq_left hx, stateLaw_succ_left, PMF.bind_apply]
  · simp [stopped, hx]

/-- The clock-limit stopped mass is the least nonnegative superharmonic majorant
of its actual zero-clock stopped mass. -/
theorem terminalMass_le (step : S → PMF S) (halt : S → Prop) [DecidablePred halt]
    (x : S) (f : S → ℝ≥0∞) (hzero : ∀ s, stopped step halt 0 s x ≤ f s)
    (hstep : ∀ s, (∑' next, step s next * f next) ≤ f s) (s : S) :
    terminalMass step halt s x ≤ f s := by
  apply iSup_le
  intro n
  induction n generalizing s with
  | zero => exact hzero s
  | succ n ih =>
    rw [stopped_succ_left]
    exact (tsum_le_tsum fun next => mul_le_mul_right (ih next) _).trans (hstep s)

private theorem stateLaw_score_le (step : S → PMF S) (f : S → ℝ≥0∞)
    (hstep : ∀ s, (∑' next, step s next * f next) ≤ f s) (n : ℕ) (s : S) :
    (∑' next, stateLaw step n s next * f next) ≤ f s := by
  induction n generalizing s with
  | zero => simp [stateLaw, PMF.pure_apply, ite_mul]
  | succ n ih =>
    rw [stateLaw_succ_left, PMF.tsum_bind_mul]
    exact (tsum_le_tsum fun next => mul_le_mul_right (ih next) _).trans (hstep s)

variable (step : S → PMF S) (halt boundary : S → Prop)
variable [DecidablePred halt] [DecidablePred boundary]
variable (absorb : ∀ s, halt s → step s = PMF.pure s)
variable (contains : ∀ s, halt s → boundary s)

include absorb contains in
/-- Every actual terminal mass factors through the actual next boundary. Silent
divergence contributes no terminal mass, rather than requiring a reach assumption. -/
theorem terminalMass_restart (s x : S) :
    terminalMass step halt s x = ∑' b,
      terminalMass (beforeBoundary step boundary) boundary s b * terminalMass step halt b x := by
  let f (s : S) := terminalMass step halt s x
  let g (s : S) := ∑' b, terminalMass (beforeBoundary step boundary) boundary s b * f b
  have hf (s : S) : f s = ∑' next, step s next * f next :=
    terminalMass_unfold step halt absorb s x
  have hgB (s : S) (hs : boundary s) : g s = f s := by
    simp only [g, terminalMass_halted _ _ (beforeBoundary_absorbs step boundary) s hs]
    simp [PMF.pure_apply, ite_mul]
  have hgStep (s : S) : g s = ∑' next, beforeBoundary step boundary s next * g next := by
    calc
      g s = ∑' b, (∑' next, beforeBoundary step boundary s next *
          terminalMass (beforeBoundary step boundary) boundary next b) * f b := by
        apply tsum_congr
        intro b
        rw [terminalMass_unfold _ _ (beforeBoundary_absorbs step boundary)]
      _ = _ := by
        simp only [← ENNReal.tsum_mul_right, mul_assoc]
        rw [tsum_comm]
        simp only [g, ENNReal.tsum_mul_left]
  have hg_le (s : S) : g s ≤ f s := by
    have hsuper (s : S) : (∑' next, beforeBoundary step boundary s next * f next) ≤ f s := by
      by_cases hs : boundary s
      · simp [beforeBoundary, hs, PMF.pure_apply, ite_mul]
      · simpa only [beforeBoundary, ite_eq_right hs] using (hf s).ge
    have hm := stopped_mono (beforeBoundary step boundary) boundary
      (beforeBoundary_absorbs step boundary) s
    change (∑' b, (⨆ n, stopped (beforeBoundary step boundary) boundary n s b) * f b) ≤ f s
    simp only [ENNReal.iSup_mul]
    rw [tsum_iSup_nat _ (by
      intro i j hij b
      change stopped (beforeBoundary step boundary) boundary i s b * f b ≤
        stopped (beforeBoundary step boundary) boundary j s b * f b
      gcongr
      exact hm hij b)]
    apply iSup_le
    intro n
    calc
      _ ≤ ∑' b, stateLaw (beforeBoundary step boundary) n s b * f b := by
        apply tsum_le_tsum
        intro b
        by_cases hb : boundary b <;> simp [stopped, hb]
      _ ≤ f s := stateLaw_score_le _ f hsuper n s
  apply le_antisymm
  · apply terminalMass_le step halt x g
    · intro y
      by_cases hy : boundary y
      · rw [hgB y hy]
        exact le_iSup (fun n => stopped step halt n y x) 0
      · have hn : ¬ halt y := fun h => hy (contains y h)
        by_cases hx : halt x
        · have hxy : y ≠ x := fun he => hn (he ▸ hx)
          simp [stopped, stateLaw, hx, PMF.pure_apply, Ne.symm hxy]
        · simp [stopped, hx]
    · intro y
      by_cases hy : boundary y
      · rw [hgB y hy]
        exact (tsum_le_tsum fun next => mul_le_mul_right (hg_le next) _).trans (hf y).ge
      · rw [hgStep y]
        simp only [beforeBoundary, ite_eq_right hy]
        exact le_rfl
  · exact hg_le s

/-- The unbounded actual stopped law satisfies its one-step execution equation. -/
theorem terminal_step (s : S) :
    terminal step halt absorb s = (step s).bind (terminal step halt absorb) := by
  apply option_ext
  intro x
  simp only [PMF.bind_apply, terminal_some]
  exact terminalMass_unfold step halt absorb s x

/-- An already halted state is a terminating result, not divergence. -/
theorem terminal_halted (s : S) (h : halt s) :
    terminal step halt absorb s = PMF.pure (some s) := by
  classical
  apply option_ext
  intro x
  simp [terminal_some, terminalMass_halted step halt absorb s h, PMF.pure_apply]

include contains in
/-- Pause at the actual first boundary, then resume the original process.
The complete optional terminal law, including all divergent mass, is unchanged. -/
theorem terminal_restart (s : S) :
    terminal step halt absorb s =
      (terminal (beforeBoundary step boundary) boundary
        (beforeBoundary_absorbs step boundary) s).bind
        (fun hit => hit.elim (PMF.pure none) (terminal step halt absorb)) := by
  classical
  apply option_ext
  intro x
  rw [PMF.bind_apply, ← (Equiv.optionEquivSumPUnit.{0, 0} S).symm.tsum_eq,
    Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
  simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr,
    Option.elim_some, Option.elim_none, terminal_some, PMF.pure_apply, reduceCtorEq, ite_false,
    mul_zero, tsum_zero, add_zero]
  exact terminalMass_restart step halt boundary absorb contains s x

end Cslib.Probability.StoppedProcess
