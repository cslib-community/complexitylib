/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.StoppedProcess
import Mathlib.Tactic

/-!
# Mapping actual unbounded stopped processes

An exact one-step simulation preserving the halting predicate preserves the entire
terminal law, including divergent mass. The map need not be injective; hidden
states may be forgotten. No common clock or termination hypothesis is required.

## Main results

* `terminal_map`: exact transport of actual stopped laws.
-/

public section
noncomputable section
namespace Cslib.Probability.StoppedProcess
open ObservedProcess
open scoped ENNReal
variable {S T : Type}

/-- Exact one-step simulation transports the whole clock-limit terminal law,
including divergence, without assuming the desired terminal correspondence. -/
theorem terminal_map (stepS : S → PMF S) (haltS : S → Prop) [DecidablePred haltS]
    (absorbS : ∀ s, haltS s → stepS s = PMF.pure s)
    (stepT : T → PMF T) (haltT : T → Prop) [DecidablePred haltT]
    (absorbT : ∀ t, haltT t → stepT t = PMF.pure t)
    (f : S → T) (hstep : ∀ s, (stepS s).map f = stepT (f s))
    (hhalt : ∀ s, haltT (f s) ↔ haltS s) (s : S) :
    (terminal stepS haltS absorbS s).map (Option.map f) =
      terminal stepT haltT absorbT (f s) := by
  classical
  have hclock (n : ℕ) : (stateLaw stepS n s).map f = stateLaw stepT n (f s) := by
    induction n with
    | zero => simp [stateLaw]
    | succ n ih =>
      rw [stateLaw, PMF.map_bind, stateLaw, ← ih, PMF.bind_map]
      simp only [hstep]
      rfl
  apply option_ext
  intro t
  have hm : (terminal stepS haltS absorbS s).map (Option.map f) (some t) =
      ∑' x, terminal stepS haltS absorbS s (some x) * (if f x = t then 1 else 0) := by
    rw [PMF.map_apply, ← (Equiv.optionEquivSumPUnit.{0, 0} S).symm.tsum_eq,
      Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
    simp only [Equiv.optionEquivSumPUnit_symm_inl, Equiv.optionEquivSumPUnit_symm_inr,
      Option.map_some, Option.map_none, Option.some.injEq, reduceCtorEq, ite_false,
      tsum_fintype, Fintype.sum_unique, add_zero, mul_ite, mul_one, mul_zero, eq_comm]
  rw [hm, terminal_score, terminal_some, terminalMass]
  apply iSup_congr
  intro n
  unfold stopped
  rw [← hclock, PMF.map_apply]
  by_cases ht : haltT t
  · simp only [ht, ite_true]
    apply tsum_congr
    intro x
    by_cases he : f x = t
    · have hx : haltS x := (hhalt x).mp (he.symm ▸ ht)
      simp [he, hx]
    · simp [he, Ne.symm he]
  · simp only [ht, ite_false]
    apply tsum_eq_zero_iff.mpr
    intro x
    by_cases he : f x = t
    · have hx : ¬haltS x := fun h => ht (he ▸ (hhalt x).mpr h)
      simp [he, hx]
    · simp [he]

end Cslib.Probability.StoppedProcess
