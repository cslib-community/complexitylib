/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.Data.Code.OddCircuitAsymptotic
import CslibFrontier.Foundations.Data.Code.BallVolume
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy

/-!
# Tests: Saglam's asymptotic bound and Lemma 3.1

* The punctured ball of radius `2` in `𝔽₂⁴` has `4 + 6 = 10` words.
* The entropy lower bound on `C(4, 2) = 6` reads `16 = exp (4 log 2) ≤ 5 · 6`.
* The exponents: `γ(1 / 2) = 0`, `γ(ρ) ≥ c ρ` on `(0, 1 / 4]`, and the tail exponent at `y = 0`
  is `h(ρ)`, which is what `ksTailExponent_le` gives with `y = 0`.
* Parseval for a single word: `∑_y charSum {x} y ^ 2 = 2 ^ n`.
* The headline with `ε = 1 / 4` from the Kirshner–Samorodnitsky hypotheses.
-/

namespace CslibFrontierTests.OddCircuitAsymptotic

open Finset Real Cslib Cslib.Code

example : #{x : Fin 4 → ZMod 2 | x ≠ 0 ∧ hammingNorm x < 3} = 10 := by
  rw [card_filter_ne_zero_hammingNorm_lt]; decide

example : exp (4 * log 2) ≤ 30 := by
  have h := exp_mul_binEntropy_le_succ_mul_choose (n := 4) (w := 2) (by norm_num)
  norm_num [Nat.choose] at h
  rwa [one_div, binEntropy_two_inv] at h

example : ksGamma (1 / 2) = 0 := ksGamma_half

example : ∃ c > 0, ∀ ρ, 0 < ρ → ρ ≤ 1 / 4 → c * ρ ≤ ksGamma ρ := by
  obtain ⟨c, hc, h⟩ := exists_mul_le_ksGamma (ε := 1 / 4) (by norm_num)
  exact ⟨c, hc, fun ρ h0 h1 => h ρ h0 (by linarith)⟩

example (ρ : ℝ) : ksTailExponent ρ 0 = binEntropy ρ := by
  simp [ksTailExponent]

example (n : ℕ) (x : Fin n → ZMod 2) :
    ∑ y, charSum {x} y ^ 2 = 2 ^ n := by
  simpa using sum_charSum_sq ({x} : Finset (Fin n → ZMod 2))

/-- Saglam's theorem at `ε = 1 / 4`: distance up to `n / 4`, `Ω(n)` times the Gilbert–Varshamov
bound, from the imported Kirshner–Samorodnitsky bounds. -/
example (hKS : ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, KSThirdMomentBound n w ∧ KSTailBound n w) :
    ∃ c > 0, ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, K * logb 2 n ≤ d → (d : ℝ) ≤ n / 4 →
      ∃ m : ℕ, ∃ H : Matrix (Fin m) (Fin n) (ZMod 2),
        (d : ℕ∞) ≤ minDist (parityCheckCode H : Set (Fin n → ZMod 2)) ∧
          c * n * 2 ^ n ≤ Nat.card (parityCheckCode H) * ∑ i ∈ Ico 1 d, (n.choose i : ℝ) := by
  obtain ⟨c, hc, K, N, h⟩ :=
    exists_parityCheckCode_of_ks (ε := 1 / 4) (by norm_num) (by norm_num) hKS
  exact ⟨c, hc, K, N, fun n hn d h1 h2 => h n hn d h1 (by linarith)⟩

end CslibFrontierTests.OddCircuitAsymptotic
