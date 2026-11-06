/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Basic
public import Complexity.Probability.PMF
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Exact rational randomization

`rationalCoin` is an actual `ProbComp` program realizing any rational probability
in the unit interval. It draws a finite uniform ticket and distinguishes its two
summands. This uses the existing finite-uniform interface, without a claim of
strict worst-case fair-coin runtime. Exact rational sampling is used in the
policy implementation in [Wang2027], Theorem 1, PDF p. 7.

## Main results

* `rationalCoin_true`, `rationalCoin_false`: exact rational branch probabilities.
-/

public section
noncomputable section
namespace Cslib.ProbComp
open Finset Probability

private theorem tickets_nonempty (a b : ℕ) (h : 0 < a + b) : Nonempty (Fin a ⊕ Fin b) := by
  by_cases ha : 0 < a
  · exact ⟨Sum.inl ⟨0,ha⟩⟩
  · exact ⟨Sum.inr ⟨0,by omega⟩⟩

/-- Draw a ticket from either of two finite piles and report the selected pile. -/
@[expose] def ticketCoin (a b : ℕ) (h : 0 < a + b) : ProbComp Bool :=
  letI : Nonempty (Fin a ⊕ Fin b) := by exact tickets_nonempty a b h
  Sum.isLeft <$> uniform (Fin a ⊕ Fin b)

/-- The exact probability of selecting the first ticket pile. -/
theorem ticketCoin_true (a b : ℕ) (h : 0 < a + b) :
    (eval (ticketCoin a b h) true).toReal = (a : ℝ) / (a + b) := by
  classical
  simp only [ticketCoin, eval_map, eval_uniform, PMF.map_apply]
  rw [tsum_fintype, Fintype.sum_sum_type]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add, div_eq_mul_inv]

private theorem numerator_bounds (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    q.num.toNat ≤ q.den ∧ (q.num.toNat : ℚ) / q.den = q := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr h₀
  have hcast : (q.num.toNat : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have heq : (q.num.toNat : ℚ) / q.den = q := by
    rw [hcast, Rat.num_div_den]
  refine ⟨?_, heq⟩
  have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have := (div_le_one hd).mp (heq ▸ h₁)
  exact_mod_cast this

/-- Exact rational success probability through finite-uniform sampling. -/
@[expose] def rationalCoin (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) : ProbComp Bool :=
  ticketCoin q.num.toNat (q.den - q.num.toNat)
    (by rw [Nat.add_sub_of_le (numerator_bounds q h₀ h₁).1]; exact q.den_pos)

/-- Exact rational randomization, including zero and one. -/
theorem rationalCoin_true (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    (eval (rationalCoin q h₀ h₁) true).toReal = (q : ℝ) := by
  rw [rationalCoin, ticketCoin_true, ← Nat.cast_add,
    Nat.add_sub_of_le (numerator_bounds q h₀ h₁).1]
  have he := congrArg (fun x : ℚ => (x : ℝ)) (numerator_bounds q h₀ h₁).2
  simpa only [Rat.cast_div, Rat.cast_natCast] using he

/-- Probability of selecting the other branch. -/
theorem rationalCoin_false (q : ℚ) (h₀ : 0 ≤ q) (h₁ : q ≤ 1) :
    (eval (rationalCoin q h₀ h₁) false).toReal = 1 - (q : ℝ) := by
  have hsum := Probability.PMF.sum_toReal (eval (rationalCoin q h₀ h₁))
  rw [Fintype.sum_bool, rationalCoin_true] at hsum
  linarith

end Cslib.ProbComp
