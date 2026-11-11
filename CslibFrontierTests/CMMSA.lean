/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CMMSA

/-! Nonvacuity of `GapCMMSA`: a small yes-instance, a small no-instance at `σ = 1`, and a
no-instance at a proportion `σ < 1`. -/

namespace CslibFrontierTests.CMMSA

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-- Two variables of weight `1`; the formulas `x₀ ∨ x₁` and `x₀`, at threshold `1`. -/
def small : CMMSAInstance :=
  ⟨[1, 1], 1, [[[(0, true)], [(1, true)]], [[(0, true)]]]⟩

theorem wellFormed_small : small.WellFormed 2 where
  weight_pos := by decide
  threshold_pos := by decide
  formula_ne_nil := by decide
  term_ne_nil := by decide
  monotone := by decide
  var_lt := by decide
  length_flatten_le := by decide

/-- Setting `x₀` alone satisfies both formulas at weight `1`. -/
example : small ∈ (GapCMMSA 2 5 (1 / 2)).yes :=
  mem_yes_GapCMMSA.2 ⟨wellFormed_small, {0}, by decide, by decide, by decide⟩

/-- One variable of weight `2` and the formula `x₀`, at threshold `1`: the only satisfying
assignment is too heavy for the gap `3 / 2`. -/
def heavy : CMMSAInstance :=
  ⟨[2], 1, [[[(0, true)]]]⟩

theorem wellFormed_heavy : heavy.WellFormed 1 where
  weight_pos := by decide
  threshold_pos := by decide
  formula_ne_nil := by decide
  term_ne_nil := by decide
  monotone := by decide
  var_lt := by decide
  length_flatten_le := by decide

/-- Every assignment of weight at most `3 / 2` falsifies `x₀`. -/
example : heavy ∈ (GapCMMSA 1 (3 / 2) 1).no := by
  refine mem_no_GapCMMSA_one.2 ⟨wellFormed_heavy, by norm_num, fun S hS hw => ?_⟩
  refine ⟨[[(0, true)]], List.mem_singleton_self _, ?_⟩
  by_cases h0 : 0 ∈ S
  · have hle : heavy.weight {0} ≤ heavy.weight S :=
      Finset.sum_le_sum_of_subset (Finset.singleton_subset_iff.2 h0)
    have h2 : heavy.weight {0} = 2 := by decide
    have hth : heavy.threshold = 1 := rfl
    rw [h2] at hle
    rw [hth] at hw
    have : (2 : ℝ) ≤ heavy.weight S := by exact_mod_cast hle
    norm_num at hw
    linarith
  · simp [DNF.eval, Term.eval, Literal.eval, h0]

/-- The weights matter: with weight `1` the same formula is a yes-instance. -/
example : (⟨[1], 1, [[[(0, true)]]]⟩ : CMMSAInstance) ∈ (GapCMMSA 1 (3 / 2) 1).yes :=
  mem_yes_GapCMMSA.2 ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩, {0}, by decide, by decide, by decide⟩

/-- Two formulas `x₀` and `x₁` of weight `1` each, at threshold `1`: an assignment of weight at
most `3 / 2` sets at most one variable, so it satisfies fewer than `3 / 4` of the formulas. -/
def pair : CMMSAInstance :=
  ⟨[1, 1], 1, [[[(0, true)]], [[(1, true)]]]⟩

example : pair ∈ (GapCMMSA 1 (3 / 2) (3 / 4)).no := by
  refine mem_no_GapCMMSA.2 ⟨⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩, by norm_num, by norm_num, fun S hS hw => ?_⟩
  have hpair : pair.formulas.length = 2 := rfl
  rw [hpair]
  have hth : pair.threshold = 1 := rfl
  rw [hth] at hw
  -- `S` is a subset of `{0, 1}` of weight at most `1`, so it misses `0` or `1`.
  have hmiss : 0 ∉ S ∨ 1 ∉ S := by
    by_contra h
    simp only [not_or, not_not] at h
    have hle : pair.weight {0, 1} ≤ pair.weight S :=
      Finset.sum_le_sum_of_subset (Finset.insert_subset_iff.2 ⟨h.1,
        Finset.singleton_subset_iff.2 h.2⟩)
    have h2 : pair.weight {0, 1} = 2 := by decide
    have : (2 : ℝ) ≤ pair.weight S := by exact_mod_cast h2 ▸ hle
    norm_num at hw
    linarith
  have hcount : pair.satCount S ≤ 1 := by
    rcases hmiss with h | h <;>
      simp only [CMMSAInstance.satCount, DNF.eval, pair, List.any_cons, Term.eval, List.all_cons,
        Literal.eval, h, decide_false, beq_true, List.all_nil, Bool.and_true, List.any_nil,
        Bool.or_self, Bool.false_eq_true, not_false_eq_true, List.countP_cons_of_neg,
        List.countP_cons, List.countP_nil, Bool.or_false, decide_eq_true_eq, zero_add] <;>
        split <;> simp
  have : (pair.satCount S : ℝ) ≤ 1 := by exact_mod_cast hcount
  linarith

end CslibFrontierTests.CMMSA
