/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (test driver)

import Complexity.Algorithms.Lean.Scheduling.Brent
import Complexity.Algorithms.Lean.Scheduling.LPT
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Scheduling Bounds

Checked instances for list scheduling on identical machines (Graham's bound and its tight family),
the LPT rule, and greedy scheduling with precedence constraints (Graham's critical chain, work and
span laws, Brent's theorem).
-/

-- Regression `#guard` checks run the compiled `listSchedule` and `lptSchedule`.
set_option linter.hashCommand false

namespace ComplexityTests.Scheduling

open Cslib.Algorithms.Lean.Scheduling

/-! ## 1. Graham's bound is tight on three machines -/

-- `grahamTight ℚ 3`: six unit jobs, then one job of length three.
#guard makespan (grahamTight ℚ 3) (listSchedule (m := 3) (grahamTight ℚ 3)) = 5
-- `grahamTight ℚ 5`: twenty unit jobs, then one job of length five; `2 · 5 - 1 = 9`.
#guard makespan (grahamTight ℚ 5) (listSchedule (m := 5) (grahamTight ℚ 5)) = 9

example : optMakespan 3 (grahamTight ℚ 3) = 3 := optMakespan_grahamTight ℚ 3

/-- On `grahamTight ℚ 3` the computed list schedule attains `(2 - 1/3) · OPT = 5`. -/
example : makespan (grahamTight ℚ 3) (listSchedule (m := 3) (grahamTight ℚ 3)) = 5 := by
  rw [(isListSchedule_listSchedule _).makespan_grahamTight, optMakespan_grahamTight]
  norm_num

/-! ## 2. LPT on the standard two-machine tight instance `3, 3, 2, 2, 2` -/

private def lptJobs : Fin 5 → ℚ := ![3, 3, 2, 2, 2]

-- LPT puts `3, 2, 2` on one machine: makespan `7 = (4/3 - 1/6) · 6`.
#guard makespan lptJobs (lptSchedule (m := 2) lptJobs) = 7

/-- The optimum is `6` (`3 + 3` and `2 + 2 + 2`), so LPT's ratio `7/6 = 4/3 - 1/(3 · 2)` is
attained on two machines. -/
example : optMakespan 2 lptJobs = 6 := by
  refine le_antisymm ?_ ?_
  · refine (optMakespan_le lptJobs ![0, 0, 1, 1, 1]).trans ?_
    rw [makespan_le_iff]
    intro i
    fin_cases i <;> norm_num [load_def, Finset.sum_filter, Fin.sum_univ_five, lptJobs]
  · have h := sum_le_card_nsmul_optMakespan (m := 2) lptJobs
    simp only [Fin.sum_univ_five, lptJobs, nsmul_eq_mul] at h ⊢
    norm_num at h
    linarith

example : makespan lptJobs (lptSchedule (m := 2) lptJobs) ≤
    (4 / 3 - 1 / (3 * 2)) * optMakespan 2 lptJobs := by
  refine makespan_lptSchedule_le (m := 2) lptJobs fun j => ?_
  fin_cases j <;> norm_num [lptJobs]

/-! ## 3. LPT on the standard three-machine tight instance `5, 5, 4, 4, 3, 3, 3` -/

private def lptJobs3 : Fin 7 → ℚ := ![5, 5, 4, 4, 3, 3, 3]

-- LPT puts `5, 3, 3` on one machine: makespan `11 = (4/3 - 1/9) · 9`.
#guard makespan lptJobs3 (lptSchedule (m := 3) lptJobs3) = 11

/-- The optimum is `9` (`5 + 4`, `5 + 4`, `3 + 3 + 3`), so LPT's ratio `11/9 = 4/3 - 1/(3 · 3)` is
attained on three machines. -/
example : optMakespan 3 lptJobs3 = 9 := by
  refine le_antisymm ?_ ?_
  · refine (optMakespan_le lptJobs3 ![0, 1, 0, 1, 2, 2, 2]).trans ?_
    rw [makespan_le_iff]
    intro i
    fin_cases i <;> norm_num [load_def, Finset.sum_filter, Fin.sum_univ_seven, lptJobs3]
  · have h := sum_le_card_nsmul_optMakespan (m := 3) lptJobs3
    simp only [Fin.sum_univ_seven, lptJobs3, nsmul_eq_mul] at h ⊢
    norm_num at h
    linarith

/-- The entries of the tight instance are available to clients. -/
example : grahamTight ℚ 3 0 = 1 ∧ grahamTight ℚ 3 (Fin.last 6) = 3 :=
  ⟨grahamTight_of_lt (by decide), grahamTight_last⟩

/-! ## 4. Greedy schedules with precedence constraints -/

namespace Precedence

open Cslib.Algorithms.Lean.Scheduling.Precedence

/-- Two independent unit jobs started together on two machines form a greedy schedule. -/
example : IsGreedy 2 (fun _ _ : Fin 2 => False) (fun _ => 1) (fun _ => 0) where
  prec_le := fun _ _ h => h.elim
  card_running_le := fun _ => (Finset.card_le_univ _).trans (by simp)
  ready_started := fun _ _ _ h => absurd h (Nat.not_lt_zero _)

/-- Running the two jobs one after the other is feasible but not greedy: a machine idles at time
`0` while job `1` is ready. -/
example : IsFeasible 2 (fun _ _ : Fin 2 => False) (fun _ => 1) ![0, 1] ∧
    ¬ IsGreedy 2 (fun _ _ : Fin 2 => False) (fun _ => 1) ![0, 1] := by
  have h0 : running (fun _ => 1) ![0, 1] 0 = {0} := by
    ext j
    fin_cases j <;> simp [mem_running]
  refine ⟨⟨fun _ _ h => h.elim, fun _ => (Finset.card_le_univ _).trans (by simp)⟩, fun hg => ?_⟩
  obtain ⟨i, hi, -⟩ := hg.ready_started 0 1 (by rw [h0]; decide) (by decide)
  exact hi

/-- Well-foundedness of `prec` is needed in `IsGreedy.exists_chain`: a zero-length job that is its
own predecessor is never ready, so a greedy schedule may start it arbitrarily late, and no chain
gives `m · T ≤ ∑ p + (m - 1) · (chain length)`. -/
example : IsGreedy 1 (fun _ _ : Fin 1 => True) (fun _ => 0) (fun _ => 5) ∧
    ¬ ∃ c : List (Fin 1), c.IsChain (fun _ _ : Fin 1 => True) ∧
      1 * makespan (fun _ : Fin 1 => 0) (fun _ => 5) ≤
        ∑ j, (fun _ : Fin 1 => 0) j + (1 - 1) * (c.map fun _ => 0).sum := by
  refine ⟨⟨⟨fun _ _ _ => le_rfl, fun _ => (Finset.card_le_univ _).trans (by simp)⟩,
    fun _ _ _ ht => ⟨0, trivial, ht⟩⟩, ?_⟩
  rintro ⟨c, -, h⟩
  have h5 := le_makespan (J := Fin 1) (fun _ => 0) (fun _ => 5) 0
  simp only [Finset.sum_const_zero, Nat.sub_self, zero_mul, add_zero, one_mul] at h h5
  omega

/-- A chain of three unit jobs. -/
private def chain3 (i j : Fin 3) : Prop := j.val = i.val + 1

private theorem wf_chain3 : WellFounded chain3 :=
  Subrelation.wf (fun {i j} (h : chain3 i j) => (show i.val < j.val by
    unfold chain3 at h; omega)) (InvImage.wf Fin.val wellFounded_lt)

/-- `makespan_le_iff` bounds a concrete schedule directly: three unit jobs at times `0, 1, 2`. -/
example : makespan (fun _ : Fin 3 => 1) (fun j => j.val) ≤ 3 :=
  Precedence.makespan_le_iff.mpr fun j => j.isLt

/-- The span of the three-job chain is `3`. -/
theorem span_chain3 : span chain3 (fun _ => 1) = 3 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨c, hc, h⟩ := exists_chain_sum_eq_span wf_chain3 (fun _ => 1)
    rw [← h]
    simpa using sum_chain_le_sum wf_chain3 (fun _ => 1) hc
  · have hc : [(0 : Fin 3), 1, 2].IsChain chain3 := by
      simp [List.isChain_cons_cons, chain3]
    simpa using sum_chain_le_span wf_chain3 (fun _ => 1) hc

/-- Greedy schedules exist (`exists_isGreedy`), and Brent's bound `2 · T ≤ W + (2 - 1) · D`
gives `T ≤ 3` for the chain on two machines; the span law gives `T ≥ 3`. -/
example : ∃ s, IsGreedy 2 chain3 (fun _ => 1) s ∧ makespan (fun _ => 1) s = 3 := by
  obtain ⟨s, hs⟩ := exists_isGreedy 2 (by norm_num) chain3 wf_chain3 (fun _ => 1) fun _ => one_pos
  refine ⟨s, hs, le_antisymm ?_ ?_⟩
  · have h := hs.mul_makespan_le_card_add_span wf_chain3
    rw [span_chain3, Fintype.card_fin] at h
    omega
  · have h := hs.span_le_makespan
    rwa [span_chain3] at h

end Precedence

end ComplexityTests.Scheduling
