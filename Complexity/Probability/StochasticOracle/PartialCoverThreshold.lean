/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.PartialCoverGreedy
import Mathlib.Data.Nat.Find

/-!
# Exact rational repetition thresholds

For rational failure probabilities and budgets, the logarithmic repetition
threshold of [Wang2027], Theorem 4 (Section 5, PDF pp. 10–11), can be evaluated
by searching exact rational powers. This includes equality at an integral
logarithmic threshold, where approximate real logarithms need special care.
The search is executable; no binary time or space bound is claimed.

## Main results

* `rationalRepetitions_eq`: exact agreement with the real-log ceiling convention.
* `pow_le_iff_rationalRepetitions_le`: minimality of the computed threshold.
-/

public section
namespace Cslib.Probability.StochasticOracle.PartialCover.Instance

/-- A positive rational failure probability below one eventually meets any positive budget. -/
theorem exists_rational_power (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) : ∃ n : ℕ, q ^ n ≤ δ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqoner : (q : ℝ) < 1 := by exact_mod_cast hqone
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  refine ⟨repetitions q δ, ?_⟩
  have h := (pow_le_iff_repetitions_le hqr hqoner hδr (repetitions q δ)).mpr le_rfl
  exact_mod_cast h

/-- Exact search for the least repetition count meeting a rational failure budget.
The proofs justify termination and are erased when evaluating the search. -/
@[expose] def rationalRepetitions (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) : ℕ := Nat.find (exists_rational_power q δ hq hqone hδ)

/-- Search minimality, including budgets at least one (which give zero calls). -/
theorem pow_le_iff_rationalRepetitions_le (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) (n : ℕ) :
    q ^ n ≤ δ ↔ rationalRepetitions q δ hq hqone hδ ≤ n := by
  constructor
  · intro hn
    exact Nat.find_min' (exists_rational_power q δ hq hqone hδ) hn
  · intro hn
    exact (pow_le_pow_of_le_one hq.le hqone.le hn).trans
      (Nat.find_spec (exists_rational_power q δ hq hqone hδ))

/-- The executable rational search agrees exactly with the source's real logarithms. -/
theorem rationalRepetitions_eq (q δ : ℚ) (hq : 0 < q) (hqone : q < 1)
    (hδ : 0 < δ) :
    rationalRepetitions q δ hq hqone hδ = repetitions (q : ℝ) (δ : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqoner : (q : ℝ) < 1 := by exact_mod_cast hqone
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  apply Nat.le_antisymm
  · apply (pow_le_iff_rationalRepetitions_le q δ hq hqone hδ _).mp
    have h := (pow_le_iff_repetitions_le hqr hqoner hδr (repetitions q δ)).mpr le_rfl
    exact_mod_cast h
  · apply (pow_le_iff_repetitions_le hqr hqoner hδr _).mp
    have h := (pow_le_iff_rationalRepetitions_le q δ hq hqone hδ
      (rationalRepetitions q δ hq hqone hδ)).mpr le_rfl
    exact_mod_cast h

end Cslib.Probability.StochasticOracle.PartialCover.Instance

namespace Cslib.Algorithms.Lean.Multicover
open Cslib.Probability.StochasticOracle.PartialCover.Instance

/-- Greedy selection with exact executable rational threshold evaluation. -/
@[expose] def rationalBatch {E : Type} [DecidableEq E] [Fintype E]
    (as : List (Oracle E)) (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) :
    List (Oracle E) := batch as (rationalRepetitions q δ hq hqone hδ)

/-- The rational implementation emits exactly the batch analyzed with real logarithms.
For the source sufficient demand use the rational budget `(1-η)/n`. -/
theorem rationalBatch_eq {E : Type} [DecidableEq E] [Fintype E]
    (as : List (Oracle E)) (q δ : ℚ) (hq : 0 < q) (hqone : q < 1) (hδ : 0 < δ) :
    rationalBatch as q δ hq hqone hδ = batch as (repetitions (q : ℝ) (δ : ℝ)) := by
  rw [rationalBatch, rationalRepetitions_eq]

end Cslib.Algorithms.Lean.Multicover
