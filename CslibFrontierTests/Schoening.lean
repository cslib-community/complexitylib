/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.FineGrained.Schoening

/-! Schöning's random walk: a concrete satisfiable instance, the biased walk and the binomial
bound. -/

namespace CslibFrontierTests.Schoening

open Cslib.Logic.PL Cslib.Complexity.Schoening

/-- `(x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁ ∨ x₂)`: satisfiable, with clauses of at most three literals. -/
def φ : CNF (Fin 3) := [[(0, true), (1, true)], [(0, false), (1, true), (2, true)]]

theorem φ_satisfiable : φ.Satisfiable := ⟨fun _ => true, by decide⟩

theorem φ_three : ∀ c ∈ φ, c.length ≤ 3 := by decide

-- The hypotheses of `trial_success` are satisfiable: one trial succeeds with probability at least
-- `(3 / 4) ^ 3 / 10`.
example : (3 / 4 : ℝ) ^ 3 / (3 * 3 + 1) ≤ succeedProb φ (trial φ) := by
  simpa using trial_success φ_satisfiable φ_three

-- A satisfying start succeeds without any step.
example : succeedProb φ (walk φ 0 fun _ => true) = 1 := by
  rw [walk, succeedProb_pure, ite_eq_left (by decide)]

-- The biased walk for `k = 3`: from distance one, three steps reach `0` with probability
-- `1/3 + 2/3 · 1/3 · 1/3`.
example : hit 3 3 1 = 1 / 3 + 2 / 3 * (1 / 3 * (1 / 3)) := by
  simp only [hit_succ_succ, hit_zero_right, hit_zero_succ]
  norm_num

-- The middle binomial bound for `k = 3`, `i = 2`: `3⁶ ≤ C(6, 2) · 2⁴ · 7`.
example : 3 ^ (3 * 2) ≤ (3 * 2).choose 2 * (3 - 1) ^ (3 * 2 - 2) * (3 * 2 + 1) :=
  pow_le_choose_mul (by norm_num) 2

/-- `(x₀ ∨ x₁ ∨ x₂ ∨ x₃)`: a satisfiable 4-CNF on four variables. -/
def ψ : CNF (Fin 4) := [[(0, true), (1, true), (2, true), (3, true)]]

-- The general bound applies with `k = 4`: `(3/4) · (2/3)⁴ / 13`.
example : (3 / 4 : ℝ) * (2 / 3) ^ 4 / 13 ≤ succeedProb ψ (trial ψ) := by
  have h := trial_success_of_length_le (k := 4) (by norm_num) (φ := ψ)
    ⟨fun _ => true, by decide⟩ (by decide)
  norm_num at h ⊢
  linarith

end CslibFrontierTests.Schoening
