/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.General

/-! PPSZ for satisfiable formulas on a 3-CNF formula with two solutions, all-true and all-false:
it is not uniquely satisfiable, every variable is liquid at the start, and one round of PPSZ with
`w = 3` still succeeds with probability at least `2^{-(39/70) · 3}`. -/

namespace ComplexityTests.PPSZGeneral

open Cslib.Logic.PL Cslib.Complexity.PPSZ Finset

/-- The six clauses on three variables satisfied by both `x₀ = x₁ = x₂ = true` and
`x₀ = x₁ = x₂ = false`. -/
def ψ : CNF (Fin 3) :=
  [[(0, true), (1, true), (2, false)], [(0, true), (1, false), (2, true)],
    [(0, true), (1, false), (2, false)], [(0, false), (1, true), (2, true)],
    [(0, false), (1, true), (2, false)], [(0, false), (1, false), (2, true)]]

theorem ψ_true : ψ.eval (fun _ => true) = true := by decide

theorem ψ_false : ψ.eval (fun _ => false) = true := by decide

theorem ψ_sat : ψ.Satisfiable := ⟨_, ψ_true⟩

theorem ψ_len : ∀ c ∈ ψ, c.length ≤ 3 := by decide

-- `ψ` has two satisfying assignments, so the unique-SAT bound does not apply.
example : ¬ ∀ τ, ψ.eval τ = true → τ = fun _ => true := fun h => by
  simpa using congrFun (h _ ψ_false) 0

/-- No variable is frozen at the start: both of its values extend to solutions. -/
theorem not_frozen (x : Fin 3) : ¬ Frozen ψ (fun _ => none) x := fun h => by
  simpa using h.2 (fun _ => true) (fun _ => false) ⟨fun _ _ h => (by cases h), ψ_true⟩
    ⟨fun _ _ h => (by cases h), ψ_false⟩

/-- At the start every variable is liquid, so Hertli's cost is `3 p`. -/
example (w : ℕ) (p : ℝ) : totalCost ψ w p (fun _ => none) = 3 * p := by
  unfold totalCost
  rw [sum_congr rfl fun x _ => cost_of_not_frozen (not_frozen x) rfl, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- **Depth two, `w = 3`**: one round of PPSZ outputs a solution of `ψ` with probability at least
`2^{-(39/70) · 3}`. -/
example : (2 : ℝ) ^ (-(39 / 70 * 3 : ℝ)) ≤
    ∑ σ ∈ univ.filter (fun σ => ψ.eval σ = true), ((round ψ 3) fun x => some (σ x)).toReal := by
  exact_mod_cast round_success_of_satisfiable_three le_rfl ψ_sat ψ_len

/-- Depth one with clause width bound `4` and `w = 1`: the PPZ exponent `1 - 1/4`. -/
example : (2 : ℝ) ^ (-((1 - 1 / 4) * 3 : ℝ)) ≤
    ∑ σ ∈ univ.filter (fun σ => ψ.eval σ = true), ((round ψ 1) fun x => some (σ x)).toReal := by
  have h := round_success_of_satisfiable (k := 4) (h := 1) (w := 1) (by norm_num) ψ_sat
    (fun c hc => (ψ_len c hc).trans (by norm_num)) (by decide)
  rw [qbar_one (by norm_num)] at h
  exact_mod_cast h

/-- The threshold `p* = 1 - 1 / (2 ln 2)` is cleared by the depth-two exponent `39 / 70`. -/
example : 1 - 1 / (2 * Real.log 2) ≤ 39 / 70 := by
  have h := one_sub_one_div_two_mul_log_two_le_one_sub_qbar (k := 3) le_rfl 2
  rwa [qbar_three_two, show (1 : ℝ) - 31 / 70 = 39 / 70 by norm_num] at h

/-- **Hertli's theorem with an explicit error bound**: every guess probability is at most `1`, so
the trivial bound `p = 1`, which clears the threshold, gives success probability at least
`2^{-3}` on `ψ`, for every `w`. -/
example (w : ℕ) : (2 : ℝ) ^ (-(1 * 3 : ℝ)) ≤
    ∑ σ ∈ univ.filter (fun σ => ψ.eval σ = true), ((round ψ w) fun x => some (σ x)).toReal := by
  have hp : 1 - 1 / (2 * Real.log 2) ≤ (1 : ℝ) := by
    have : 0 < 1 / (2 * Real.log 2) := by have := Real.log_pos one_lt_two; positivity
    linarith
  exact_mod_cast round_success_ge_of_guess_le hp ψ_sat fun _ _ _ _ _ => guessProb_le_one

/-- The `ε`-form for `k = 3` and `ε = 1 / 100`, applied to `ψ`. -/
example : ∃ w : ℕ, (2 : ℝ) ^ (-((1 - mu 3 / ((3 : ℕ) - 1 : ℝ) + 1 / 100) * 3)) ≤
    ∑ σ ∈ univ.filter (fun σ => ψ.eval σ = true), ((round ψ w) fun x => some (σ x)).toReal := by
  obtain ⟨w, hw⟩ := round_success_limit le_rfl (1 / 100) (by norm_num)
  exact ⟨w, by exact_mod_cast hw 3 ψ ψ_sat ψ_len⟩

end ComplexityTests.PPSZGeneral
