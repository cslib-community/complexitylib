/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.FiniteTable
import Mathlib.Tactic

/-!
# Stateful finite-table execution with a poisoned null history

The first true response disables all later true responses. The impossible
history containing two true responses is deliberately assigned a certain true
response, violating an all-history upper envelope. Exact expectation and support
bridges let the finite client use the supported sequential comparison directly.
-/

noncomputable section
namespace CslibFrontierTests.StochasticOracleFiniteTable
open Cslib.Probability Cslib.Probability.StochasticOracle
open Cslib.Optimization.OneConstraint AdaptiveSelection MeasureTheory

private def half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
private def law (h : List Bool) : Distribution Bool ℝ :=
  if h = [true, true] then Distribution.pure true
  else if true ∈ h then Distribution.pure false
  else pair true false (1 / 2) (by norm_num) (by norm_num)
private def score (h : List Bool) : ℝ :=
  if h = [false, true] then 7 else if h = [true, false] then 3 else 0

-- The actual stateful response law assigns mass one-half to the score-seven path
-- and one-quarter to the score-three path.
example :
    ∑ h : Fin 2 → Bool,
      (PMF.seqProcess (responseStep (fun h => (law h).toPMF)) 2 h).toReal *
        score (PMF.seqHistory h) = 17 / 4 := by
  rw [← historyExpectation_eq_sum_seqProcess]
  norm_num [historyExpectation, law, score, pair_mean, Distribution.mean_pure]

private theorem bad_unreachable : ¬Reachable law [true, true] := by
  intro h
  cases h with
  | cons _ hx => norm_num [law, Distribution.pure] at hx

example :
    (fun _ : Fin 2 => true) ∉
      (PMF.seqProcess (responseStep (fun h => (law h).toPMF)) 2).support := by
  intro hh
  apply bad_unreachable
  have hr := (reachable_seqHistory_iff_mem_support law 2 (fun _ => true)).mpr hh
  simpa [PMF.seqHistory, List.ofFn_succ] using hr

example : ¬((law [true, true]).mean (fun x => if x then (1 : ℝ) else 0) ≤ (half : ℝ)) := by
  norm_num [law, Distribution.mean_pure, half]

example : historyExpectation law
    (fun h => if 1 ≤ count (fun _ x => x) h then (1 : ℝ) else 0) 3 [] ≤
      (ProbabilityTheory.binomial 3 half).real (Set.Ici 1) := by
  apply count_tail_le_binomial
  intro h hh
  have hn : h ≠ [true, true] := by
    intro he
    subst h
    exact bad_unreachable hh
  by_cases ht : true ∈ h <;>
    norm_num [law, hn, ht, Distribution.mean_pure, pair_mean, half]

end CslibFrontierTests.StochasticOracleFiniteTable
