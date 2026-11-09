/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.MonotoneDisjunctions

/-! Checked instances for WINNOW1 and monotone disjunctions: concrete runs with a promotion step
and with an elimination step, Littlestone's Theorem 7 on the first run, the lower bound for
two-literal disjunctions of eight variables with the matching WINNOW1 upper bound, and the empty
class when `k > n`. -/

namespace CslibFrontierTests.Winnow

open Cslib.MachineLearning Cslib.MachineLearning.OnlineLearning.MistakeBound
open PACLearning (vcDim)

/-- The all-ones instance on one variable. -/
def x₁ : Fin 1 → Bool := fun _ => true

/-- WINNOW1 with `α = 2`, `θ = 1` and ties predicted `false` on one variable. The first score is
`1 = θ`, so it predicts `false` and errs; the promotion step doubles the weight, the second score
is `2 > θ`, and the second prediction is correct. -/
example : mistakes (winnow (n := 1) 2 1 false) [(x₁, true), (x₁, true)] = 1 := by
  have hs0 : winnowScore (fun _ : Fin 1 => (1 : ℝ)) x₁ = 1 := by simp [winnowScore_def, x₁]
  have hp0 : winnowPredict 1 false (fun _ : Fin 1 => (1 : ℝ)) x₁ = false :=
    winnowPredict_of_eq false hs0
  have hw1 : winnowWeight 2 1 false [(x₁, true)] = winnowPromote 2 (fun _ => 1) x₁ := by
    have h := winnowWeight_append_singleton (2 : ℝ) 1 false [] (x₁, true)
    rw [List.nil_append, winnowWeight_nil, winnowStep_promote hp0] at h
    exact h
  have hs1 : winnowScore (winnowPromote 2 (fun _ : Fin 1 => (1 : ℝ)) x₁) x₁ = 2 := by
    simp [winnowScore_def, winnowPromote_apply, x₁]
  have hp1 : winnowPredict 1 false (winnowPromote 2 (fun _ : Fin 1 => (1 : ℝ)) x₁) x₁ = true :=
    winnowPredict_of_gt false (by rw [hs1]; norm_num)
  simp [mistakes, mistakesFrom_cons, winnow_apply, hp0, hw1, hp1]

/-- An elimination step: WINNOW1 with `α = 2`, `θ = 1` and ties predicted `true` on one variable.
The first score is `1 = θ`, so it predicts `true` on a negative example and errs; the elimination
step sets the active weight to `0`, the second score is `0 < θ`, and the second prediction is
correct. -/
example : mistakes (winnow (n := 1) 2 1 true) [(x₁, false), (x₁, false)] = 1 := by
  have hs0 : winnowScore (fun _ : Fin 1 => (1 : ℝ)) x₁ = 1 := by simp [winnowScore_def, x₁]
  have hp0 : winnowPredict 1 true (fun _ : Fin 1 => (1 : ℝ)) x₁ = true :=
    winnowPredict_of_eq true hs0
  have hw1 : winnowWeight 2 1 true [(x₁, false)] = winnowEliminate (fun _ => 1) x₁ := by
    have h := winnowWeight_append_singleton (2 : ℝ) 1 true [] (x₁, false)
    rw [List.nil_append, winnowWeight_nil, winnowStep_eliminate hp0] at h
    exact h
  have hs1 : winnowScore (winnowEliminate (fun _ : Fin 1 => (1 : ℝ)) x₁) x₁ = 0 := by
    simp [winnowScore_def, winnowEliminate_apply, x₁]
  have hp1 : winnowPredict 1 true (winnowEliminate (fun _ : Fin 1 => (1 : ℝ)) x₁) x₁ = false :=
    winnowPredict_of_lt true (by rw [hs1]; norm_num)
  simp [mistakes, mistakesFrom_cons, winnow_apply, hp0, hw1, hp1]

/-- Theorem 7 on the same run, labelled by the disjunction `x₀`: at most
`2 · 1 · (log₂ 1 + 1) + 1 / 1 = 3` mistakes. -/
example : (mistakes (winnow (n := 1) 2 1 false) [(x₁, true), (x₁, true)] : ℝ) ≤ 3 := by
  have h := mistakes_winnow_le (n := 1) (α := 2) (θ := 1) one_lt_two (by norm_num) false {0}
    [(x₁, true), (x₁, true)] (by simp [monotoneDisjunction_eq_true, x₁])
  norm_num at h
  exact_mod_cast h

/-- The class of two-literal disjunctions of eight variables is nonempty. -/
example : (monotoneDisjunctions 8 2).Nonempty := monotoneDisjunctions_nonempty_iff.mpr (by norm_num)

/-- Littlestone's lower bound for two-literal disjunctions of eight variables:
`2 ⌊log₂ (8 / 2)⌋ = 4`, both for the VC dimension and for the optimal mistake bound. -/
example : 4 ≤ vcDim (monotoneDisjunctions 8 2) ∧
    (4 : ℕ∞) ≤ optimalMistakeBound (monotoneDisjunctions 8 2) := by
  have hlog : 2 * Nat.log 2 (8 / 2) = 4 := by decide
  have h1 := le_vcDim_monotoneDisjunctions 8 2
  have h2 := le_optimalMistakeBound_monotoneDisjunctions 8 2
  rw [hlog] at h1 h2
  exact ⟨h1, by exact_mod_cast h2⟩

/-- The matching upper bound: WINNOW1 with `α = 2` and `θ = 8 / 2` makes at most
`2 · 2 · log₂ 4 + 3 · 2 = 14` mistakes on every sequence labelled by a two-literal disjunction of
eight variables. -/
example : mistakeBound (winnow 2 (((8 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) false)
    (monotoneDisjunctions 8 2) ≤ 14 := by
  have h := mistakeBound_winnow_two_div_le (n := 8) (k := 2) (by norm_num) false
  have hlog : Real.logb 2 (((8 : ℕ) : ℝ) / ((2 : ℕ) : ℝ)) = 2 := by
    rw [show ((8 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two]
    norm_num
  rw [hlog] at h
  refine h.trans ?_
  norm_num

/-- With more literals than variables the class is empty, and its optimal mistake bound is `0`. -/
example : optimalMistakeBound (monotoneDisjunctions 2 3) = 0 := by
  have h : monotoneDisjunctions 2 3 = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp (by rw [monotoneDisjunctions_nonempty_iff]; omega)
  rw [h, optimalMistakeBound_empty]

end CslibFrontierTests.Winnow
