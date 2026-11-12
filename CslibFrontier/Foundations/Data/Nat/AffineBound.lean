/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Filter.AtTopBot.Basic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Affine bounds on natural-number functions

Resource classes such as `DTIME` and `DSPACE` allow bounds `c₁ * t n + c₂` for some constants, so
a bound of the shape `t₁ n ≤ C * t₂ n + C` for all `n` puts the class of `t₁` inside the class of
`t₂`. This file proves the two facts that produce such bounds:

* a bound that holds for all but finitely many arguments holds everywhere up to an additive
  constant (`Nat.exists_le_add_of_eventually_le`), hence in the affine shape
  (`Nat.exists_le_mul_add_of_eventually_le`);
* an affine function of an affinely bounded quantity is affinely bounded
  (`Nat.mul_add_le_mul_add_of_le_mul_add`), which absorbs the constants of the bound into the
  constants of a class.

It also records the affine bound `(n + 1) ^ k ≤ 2 ^ k * n ^ k + 2 ^ k`
(`Nat.add_one_pow_le_two_pow_mul_add`), the case `c = 1` of `Nat.mul_add_one_pow_le_two_pow` in the
shape `C * g n + C`, which makes polynomial bounds in `n + 1` and in `n` interchangeable in such
classes.

## Main results

* `Nat.exists_le_add_of_eventually_le`: `(∀ᶠ n in atTop, f n ≤ g n) → ∃ C, ∀ n, f n ≤ g n + C`.
* `Nat.exists_le_mul_add_of_eventually_le`:
  `(∀ᶠ n in atTop, f n ≤ g n) → ∃ C, ∀ n, f n ≤ C * g n + C`.
* `Nat.mul_add_le_mul_add_of_le_mul_add`:
  `a ≤ c * b + d → c₁ * a + c₂ ≤ c₁ * c * b + (c₁ * d + c₂)`.
* `Nat.add_one_pow_le_two_pow_mul_add`: `(n + 1) ^ k ≤ 2 ^ k * n ^ k + 2 ^ k`.
-/

public section

open Filter

namespace Nat

/-- A bound that holds for all but finitely many arguments holds everywhere up to an additive
constant: the largest of the finitely many other values. -/
theorem exists_le_add_of_eventually_le {f g : ℕ → ℕ} (h : ∀ᶠ n in atTop, f n ≤ g n) :
    ∃ C, ∀ n, f n ≤ g n + C := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine ⟨(Finset.range N).sup f, fun n => ?_⟩
  rcases le_or_gt N n with hn | hn
  · exact (hN n hn).trans (Nat.le_add_right _ _)
  · exact (Finset.le_sup (Finset.mem_range.mpr hn)).trans (Nat.le_add_left _ _)

/-- A bound that holds for all but finitely many arguments gives an affine bound `C * g n + C`
everywhere. -/
theorem exists_le_mul_add_of_eventually_le {f g : ℕ → ℕ} (h : ∀ᶠ n in atTop, f n ≤ g n) :
    ∃ C, ∀ n, f n ≤ C * g n + C := by
  obtain ⟨C, hC⟩ := exists_le_add_of_eventually_le h
  refine ⟨C + 1, fun n => ?_⟩
  have := Nat.le_mul_of_pos_left (g n) (Nat.add_one_pos C)
  have := hC n
  omega

/-- An affine function of an affinely bounded quantity is affinely bounded: a bound
`a ≤ c * b + d` turns `c₁ * a + c₂` into `c₁ * c * b + (c₁ * d + c₂)`. -/
theorem mul_add_le_mul_add_of_le_mul_add {a b c d : ℕ} (h : a ≤ c * b + d) (c₁ c₂ : ℕ) :
    c₁ * a + c₂ ≤ c₁ * c * b + (c₁ * d + c₂) := by
  have := Nat.mul_le_mul_left c₁ h
  rw [Nat.mul_add, ← Nat.mul_assoc] at this
  omega

/-- Shifting the base of a power by one costs a constant factor and summand:
`(n + 1) ^ k ≤ 2 ^ k * n ^ k + 2 ^ k`, the shape `C * g n + C` of
`Nat.mul_add_one_pow_le_two_pow 1 k n`. -/
theorem add_one_pow_le_two_pow_mul_add (k n : ℕ) : (n + 1) ^ k ≤ 2 ^ k * n ^ k + 2 ^ k := by
  have h := Nat.mul_add_one_pow_le_two_pow 1 k n
  simp only [Nat.one_mul] at h
  have := Nat.one_le_two_pow (n := k)
  omega

end Nat
