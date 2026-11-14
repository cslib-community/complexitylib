/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Logics.Propositional.CNF.LocalLemma
import CslibFrontier.Logics.Propositional.CNF.Moser.LocalLemma

/-! Tests for constructive `k`-SAT Moser–Tardos and Section 6 conflict-graph lopsided LLL. -/

set_option linter.privateModule false

namespace CslibFrontierTests.MoserLocalLemma

open Cslib.Logic.PL Cslib.Logic.PL.Moser Cslib.Probability.MoserTardos
open scoped ENNReal

private theorem exp_one_le_eleven_quarters : Real.exp 1 ≤ 11 / 4 := by
  have h := Real.exp_bound (x := (1 : ℝ)) (by norm_num) (n := 2) (by decide)
  simp [Finset.sum_range_succ, Nat.factorial] at h
  linarith [(abs_le.mp h).2]

/-! ### Standard constructive `k`-SAT (`e (d + 1) ≤ 2 ^ k`) beyond Moser's `r < 2 ^ (k - 3)` -/

/-- Exact `4`-CNF on `16` variables: `5` clauses all sharing variable `0`, giving `degree = 4`.
Moser's `degree < 2 ^ (4 - 3) = 2` fails, while constructive `e * (4 + 1) ≤ 16` holds. -/
private abbrev star4CNF : CNF (Fin 16) :=
  [ [(0, true), (1, true), (2, true), (3, true)],
    [(0, false), (4, true), (5, true), (6, true)],
    [(0, true), (7, true), (8, true), (9, true)],
    [(0, false), (10, true), (11, true), (12, true)],
    [(0, true), (13, true), (14, true), (15, true)] ]

private theorem star4_exact : star4CNF.IsExactDistinct 4 := by decide

private theorem star4_degree : ∀ i : Fin star4CNF.length, degree star4CNF i = 4 := by decide

example : ¬(∀ i : Fin star4CNF.length, degree star4CNF i < 2 ^ (4 - 3)) := by
  intro h
  have h0 := h 0
  have hd : degree star4CNF 0 = 4 := star4_degree 0
  omega

example {sel : (∀ p : Fin 16 × ℕ, (fun _ : Fin 16 => Bool) p.1) →
      List (Fin star4CNF.length) → Option (Fin star4CNF.length)}
    (hsel : ∀ T w i, sel T w = some i →
      current (clauseVbl star4CNF) T w ∈ violated star4CNF i)
    (i : Fin star4CNF.length) :
    ∫⁻ T, resamplings (α := fun _ : Fin 16 => Bool) sel i T ∂table fairCoin ≤
        ENNReal.ofReal (1 / 4) ∧
      ∫⁻ T, ∑ j : Fin star4CNF.length,
          resamplings (α := fun _ : Fin 16 => Bool) sel j T ∂table fairCoin ≤
        ENNReal.ofReal (5 / 4) := by
  have hlll : Real.exp 1 * ((4 : ℕ) + 1 : ℝ) ≤ 2 ^ 4 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  refine ⟨?_, ?_⟩
  · refine (lintegral_resamplings_le_of_exp_mul_le star4_exact (d := 4) (by decide)
      (fun j => (star4_degree j).le) hlll hsel i).trans_eq ?_
    norm_num
  · refine (lintegral_sum_resamplings_le_of_exp_mul_le star4_exact (d := 4) (by decide)
      (fun j => (star4_degree j).le) hlll hsel).trans_eq ?_
    norm_num [star4CNF]

example :
    (∀ᵐ T ∂table (fairCoin (n := 16)), ∃ N,
      CNF.eval (current (clauseVbl star4CNF) T
        (run (α := fun _ : Fin 16 => Bool) (firstViolatedRule star4CNF) T N))
        star4CNF = true) ∧
      star4CNF.Satisfiable := by
  have hlll : Real.exp 1 * ((4 : ℕ) + 1 : ℝ) ≤ 2 ^ 4 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  exact ⟨ae_exists_eval_run_firstViolated_of_exp_mul_le star4_exact
      (fun j => (star4_degree j).le) hlll,
    star4_exact.satisfiable_of_exp_mul_le (fun j => (star4_degree j).le) hlll⟩

/-! ### Deterministic `firstViolatedRule` execution and `d = 0` isolated exact `3`-CNF -/

private abbrev single3CNF : CNF (Fin 3) := [[(0, true), (1, true), (2, true)]]

private def stepTrueTable (p : Fin 3 × ℕ) : (fun _ : Fin 3 => Bool) p.1 :=
  decide (1 ≤ p.2)

example :
    firstViolatedRule single3CNF stepTrueTable [] = some 0 ∧
      run (α := fun _ : Fin 3 => Bool) (firstViolatedRule single3CNF) stepTrueTable 1 = [0] ∧
      firstViolatedRule single3CNF stepTrueTable
        (run (α := fun _ : Fin 3 => Bool) (firstViolatedRule single3CNF) stepTrueTable 1) =
          none ∧
      CNF.eval (current (clauseVbl single3CNF) stepTrueTable
        (run (α := fun _ : Fin 3 => Bool) (firstViolatedRule single3CNF) stepTrueTable 1))
        single3CNF = true := by
  decide

example :
    (∀ᵐ T ∂table (fairCoin (n := 3)), ∃ N,
      CNF.eval (current (clauseVbl single3CNF) T
        (run (α := fun _ : Fin 3 => Bool) (firstViolatedRule single3CNF) T N))
        single3CNF = true) ∧
      single3CNF.Satisfiable := by
  have hex : single3CNF.IsExactDistinct 3 := by decide
  have hdeg : ∀ i : Fin single3CNF.length, degree single3CNF i ≤ 0 := by decide
  have hlll : Real.exp 1 * ((0 : ℕ) + 1 : ℝ) ≤ 2 ^ 3 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  exact ⟨ae_exists_eval_run_firstViolated_of_exp_mul_le hex hdeg hlll,
    hex.satisfiable_of_exp_mul_le hdeg hlll⟩

/-! ### Conflict-graph lopsided `k`-SAT (`d' = 0` and `d' = 1`, `degree = 3` fails) -/

/-- Monotone exact `3`-CNF of `4` clauses sharing `x₀`: `degree = 3` fails `e (d + 1) ≤ 8`,
while `conflictDegree = 0` succeeds via lopsided Moser–Tardos (`e (0 + 1) ≤ 8`). -/
private abbrev posStar3CNF : CNF (Fin 9) :=
  [ [(0, true), (1, true), (2, true)],
    [(0, true), (3, true), (4, true)],
    [(0, true), (5, true), (6, true)],
    [(0, true), (7, true), (8, true)] ]

private theorem posStar3_exact : posStar3CNF.IsExactDistinct 3 := by decide

private theorem posStar3_degree : ∀ i : Fin posStar3CNF.length, degree posStar3CNF i = 3 := by
  decide

private theorem posStar3_conflictDegree :
    ∀ i : Fin posStar3CNF.length, conflictDegree posStar3CNF i = 0 := by
  decide

example :
    ¬(Real.exp 1 * ((3 : ℕ) + 1 : ℝ) ≤ 2 ^ 3) ∧
      ¬Lopsidependent (clauseVbl posStar3CNF) (violated posStar3CNF) (0 : Fin 4) 1 ∧
      (∀ᵐ T ∂table (fairCoin (n := 9)), ∃ N,
        CNF.eval (current (clauseVbl posStar3CNF) T
          (run (α := fun _ : Fin 9 => Bool) (firstViolatedRule posStar3CNF) T N))
          posStar3CNF = true) ∧
      posStar3CNF.Satisfiable := by
  have hlll : Real.exp 1 * ((0 : ℕ) + 1 : ℝ) ≤ 2 ^ 3 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 := Real.add_one_lt_exp (one_ne_zero : (1 : ℝ) ≠ 0)
    norm_num
    linarith
  · exact not_lopsidependent_of_not_conflicts posStar3CNF (i := 0) (j := 1) (by decide)
  · exact ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le posStar3_exact
      (fun i => (posStar3_conflictDegree i).le) hlll
  · exact posStar3_exact.satisfiable_of_conflict_exp_mul_le
      (fun i => (posStar3_conflictDegree i).le) hlll

/-- Exact `3`-CNF of `4` clauses sharing `x₀` (`degree = 3` fails `e * 4 ≤ 8`), where only
clauses `0` and `1` conflict (opposing on `x₁`): `conflictDegree ≤ 1`, so `e * (1 + 1) ≤ 8`
holds constructively and yields expected resamplings `≤ 1` per clause and `≤ 4` total. -/
private abbrev oneConflict3CNF : CNF (Fin 8) :=
  [ [(0, true), (1, true), (2, true)],
    [(0, true), (1, false), (3, true)],
    [(0, true), (4, true), (5, true)],
    [(0, true), (6, true), (7, true)] ]

private theorem oneConflict3_exact : oneConflict3CNF.IsExactDistinct 3 := by decide

private theorem oneConflict3_degree :
    ∀ i : Fin oneConflict3CNF.length, degree oneConflict3CNF i = 3 := by
  decide

private theorem oneConflict3_conflictDegree :
    conflictDegree oneConflict3CNF 0 = 1 ∧
      ∀ i : Fin oneConflict3CNF.length, conflictDegree oneConflict3CNF i ≤ 1 := by
  decide

example {sel : (∀ p : Fin 8 × ℕ, (fun _ : Fin 8 => Bool) p.1) →
      List (Fin oneConflict3CNF.length) → Option (Fin oneConflict3CNF.length)}
    (hsel : ∀ T w i, sel T w = some i →
      current (clauseVbl oneConflict3CNF) T w ∈ violated oneConflict3CNF i)
    (i : Fin oneConflict3CNF.length) :
    ∫⁻ T, resamplings (α := fun _ : Fin 8 => Bool) sel i T ∂table fairCoin ≤ 1 ∧
      ∫⁻ T, ∑ j : Fin oneConflict3CNF.length,
          resamplings (α := fun _ : Fin 8 => Bool) sel j T ∂table fairCoin ≤ 4 ∧
      (∀ᵐ T ∂table (fairCoin (n := 8)), ∃ N,
        CNF.eval (current (clauseVbl oneConflict3CNF) T
          (run (α := fun _ : Fin 8 => Bool) (firstViolatedRule oneConflict3CNF) T N))
          oneConflict3CNF = true) ∧
      oneConflict3CNF.Satisfiable := by
  have hlll : Real.exp 1 * ((1 : ℕ) + 1 : ℝ) ≤ 2 ^ 3 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  have hcd := oneConflict3_conflictDegree.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (lintegral_resamplings_le_of_conflict_exp_mul_le oneConflict3_exact (d' := 1)
      (by decide) hcd hlll hsel i).trans_eq ?_
    norm_num
  · refine (lintegral_sum_resamplings_le_of_conflict_exp_mul_le oneConflict3_exact (d' := 1)
      (by decide) hcd hlll hsel).trans_eq ?_
    norm_num [oneConflict3CNF]
  · exact ae_exists_eval_run_firstViolated_of_conflict_exp_mul_le oneConflict3_exact hcd hlll
  · exact oneConflict3_exact.satisfiable_of_conflict_exp_mul_le hcd hlll

/-! ### Parallel `k`-SAT (`greedyParallelCNF` and expected parallel rounds) -/

example {psel : (∀ p : Fin 16 × ℕ, (fun _ : Fin 16 => Bool) p.1) →
      List (Fin star4CNF.length) → List (Fin star4CNF.length)}
    (hrule : IsValidParallelRule (clauseVbl star4CNF) (violated star4CNF) psel) :
    ∫⁻ T, parallelRounds (α := fun _ : Fin 16 => Bool) psel T ∂table (fairCoin (n := 16)) ≤
        ENNReal.ofReal ((max 0 (Real.log ((5 : ℝ) / 4)) + 1) / (1 / 8 : ℝ)) ∧
      (∀ᵐ T ∂table (fairCoin (n := 16)), ∃ N,
        CNF.eval (current (clauseVbl star4CNF) T
          (parallelRun (α := fun _ : Fin 16 => Bool) (greedyParallelCNF star4CNF) T N))
          star4CNF = true) := by
  have hlll : Real.exp 1 * ((4 : ℕ) + 1 : ℝ) ≤ (1 - (1 / 8 : ℝ)) * 2 ^ 4 := by
    have := exp_one_le_eleven_quarters
    norm_num
    linarith
  refine ⟨?_, ?_⟩
  · simpa [star4CNF] using
      lintegral_parallelRounds_le_of_exp_mul_le_of_pos star4_exact (d := 4) (ε := 1 / 8)
        (by decide) (fun j => (star4_degree j).le) ⟨by norm_num, by norm_num⟩ hlll hrule
  · exact ae_exists_eval_parallelRun_greedy_of_exp_mul_le star4_exact (d := 4) (ε := 1 / 8)
      (fun j => (star4_degree j).le) ⟨by norm_num, by norm_num⟩ hlll

-- Two disjoint exact `3`-clauses: `greedyParallelCNF` resamples both in round 0 simultaneously.
private abbrev disj3CNF : CNF (Fin 6) :=
  [ [(0, true), (1, true), (2, true)],
    [(3, true), (4, true), (5, true)] ]

private def stepTrue6Table (p : Fin 6 × ℕ) : (fun _ : Fin 6 => Bool) p.1 :=
  decide (1 ≤ p.2)

example :
    greedyParallelCNF disj3CNF stepTrue6Table [] = [0, 1] ∧
      parallelRun (α := fun _ : Fin 6 => Bool) (greedyParallelCNF disj3CNF) stepTrue6Table 1 =
        [0, 1] ∧
      greedyParallelCNF disj3CNF stepTrue6Table
          (parallelRun (α := fun _ : Fin 6 => Bool)
            (greedyParallelCNF disj3CNF) stepTrue6Table 1) = [] ∧
      CNF.eval (current (clauseVbl disj3CNF) stepTrue6Table
        (parallelRun (α := fun _ : Fin 6 => Bool)
          (greedyParallelCNF disj3CNF) stepTrue6Table 1)) disj3CNF = true := by
  decide

end CslibFrontierTests.MoserLocalLemma
