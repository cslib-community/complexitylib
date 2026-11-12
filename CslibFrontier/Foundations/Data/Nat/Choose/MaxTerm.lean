/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Entropy-tight bounds on binomial coefficients in natural numbers

Write `n = a + b`. In the binomial expansion `n ^ n = (a + b) ^ n = ∑_j C(n, j) a ^ j b ^ (n - j)`,
the term `j = a` is the largest (`choose_mul_pow_mul_pow_le`), so it is at least the average,
`n ^ n ≤ (n + 1) C(n, a) a ^ a b ^ b` (`pow_le_succ_mul_choose_mul_pow_mul_pow`); and it is at most
the sum, `C(n, a) a ^ a b ^ b ≤ n ^ n` (`choose_mul_pow_mul_pow_le_pow`). For `s ≤ n - s`, every
term with `j ≤ s` is at least `C(n, j) s ^ s (n - s) ^ (n - s)`, so the partial sums satisfy
`(∑_{j ≤ s} C(n, j)) s ^ s (n - s) ^ (n - s) ≤ n ^ n` (`sum_choose_mul_pow_mul_pow_le_pow`).
These are `C(n, a) ≈ exp (n H(a / n))` up to the factor `n + 1`, with integer bases, so that
comparisons at fixed rational ratios reduce to comparisons of integers.

## Main results

* `Nat.choose_mul_pow_mul_pow_le`: the middle term of the expansion is the largest.
* `Nat.pow_le_succ_mul_choose_mul_pow_mul_pow`: the lower bound.
* `Nat.choose_mul_pow_mul_pow_le_pow`, `Nat.sum_choose_mul_pow_mul_pow_le_pow`: the upper bounds.
-/

public section

open Finset

namespace Nat

/-- The term `j` of `(a + b) ^ n` with `n = a + b`. -/
private def term (a b j : ℕ) : ℕ := (a + b).choose j * a ^ j * b ^ (a + b - j)

/-- One step of the expansion: `term (j + 1) (j + 1) b = term j (n - j) a`. -/
private theorem term_succ_mul (a b j : ℕ) (hj : j < a + b) :
    term a b (j + 1) * ((j + 1) * b) = term a b j * ((a + b - j) * a) := by
  unfold term
  have h := Nat.choose_succ_right_eq (a + b) j
  have e : a + b - j = (a + b - (j + 1)) + 1 := by omega
  rw [e, pow_succ b (a + b - (j + 1))] at *
  rw [pow_succ a j]
  calc (a + b).choose (j + 1) * (a ^ j * a) * b ^ (a + b - (j + 1)) * ((j + 1) * b)
      = ((a + b).choose (j + 1) * (j + 1)) * (a ^ j * a * (b ^ (a + b - (j + 1)) * b)) := by ring
    _ = ((a + b).choose j * (a + b - (j + 1) + 1)) * (a ^ j * a * (b ^ (a + b - (j + 1)) * b)) := by
        rw [h]; congr 2; omega
    _ = _ := by ring

private theorem term_mono_below (a b : ℕ) : ∀ j, j < a → term a b j ≤ term a b (j + 1) := by
  intro j hj
  have h := term_succ_mul a b j (by omega)
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · -- `b = 0`: only the last term survives
    unfold term
    simp only [add_zero]
    have : a - j ≠ 0 := by omega
    rw [zero_pow (by omega), mul_zero]
    exact Nat.zero_le _
  · have hle : (j + 1) * b ≤ (a + b - j) * a := by
      calc (j + 1) * b ≤ a * b := Nat.mul_le_mul_right _ hj
        _ ≤ a * (a + b - j) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := Nat.mul_comm _ _
    by_contra hlt
    push Not at hlt
    have : term a b (j + 1) * ((j + 1) * b) < term a b j * ((j + 1) * b) :=
      Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos (Nat.succ_pos _) hb)
    have := this.trans_le (Nat.mul_le_mul_left _ hle)
    omega

private theorem term_anti_above (a b : ℕ) : ∀ j, a ≤ j → j < a + b →
    term a b (j + 1) ≤ term a b j := by
  intro j hj hjn
  have h := term_succ_mul a b j hjn
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · unfold term
    simp only [zero_add]
    rw [zero_pow (by omega), mul_zero, zero_mul]
    exact Nat.zero_le _
  · have hle : (a + b - j) * a ≤ (j + 1) * b := by
      calc (a + b - j) * a ≤ b * a := Nat.mul_le_mul_right _ (by omega)
        _ ≤ b * (j + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := Nat.mul_comm _ _
    by_contra hlt
    push Not at hlt
    have hb : 0 < b := by omega
    have : term a b j * ((j + 1) * b) < term a b (j + 1) * ((j + 1) * b) :=
      Nat.mul_lt_mul_of_pos_right hlt (Nat.mul_pos (Nat.succ_pos _) hb)
    have := (Nat.mul_le_mul_left (term a b j) hle).trans_lt this
    omega

/-- **The middle term is the largest**: for `n = a + b` and `j ≤ n`,
`C(n, j) a ^ j b ^ (n - j) ≤ C(n, a) a ^ a b ^ b`. -/
theorem choose_mul_pow_mul_pow_le (a b j : ℕ) (hj : j ≤ a + b) :
    (a + b).choose j * a ^ j * b ^ (a + b - j) ≤ (a + b).choose a * a ^ a * b ^ b := by
  have hterm : term a b a = (a + b).choose a * a ^ a * b ^ b := by
    unfold term; rw [show a + b - a = b by omega]
  change term a b j ≤ _
  rw [← hterm]
  have below : ∀ k j, j + k = a → term a b j ≤ term a b a := by
    intro k
    induction k with
    | zero => intro j hj; rw [← hj, Nat.add_zero]
    | succ k ih =>
      intro j hj
      exact (term_mono_below a b j (by omega)).trans (ih (j + 1) (by omega))
  have above : ∀ k j, a + k = j → j ≤ a + b → term a b j ≤ term a b a := by
    intro k
    induction k with
    | zero => intro j hj _; rw [← hj, Nat.add_zero]
    | succ k ih =>
      intro j hj hjn
      obtain rfl : j = (a + k) + 1 := by omega
      exact (term_anti_above a b (a + k) (by omega) (by omega)).trans (ih (a + k) rfl (by omega))
  rcases le_or_gt j a with hja | hja
  · exact below (a - j) j (by omega)
  · exact above (j - a) j (by omega) hj

/-- **Lower bound** (entropy form): for `n = a + b`, `n ^ n ≤ (n + 1) C(n, a) a ^ a b ^ b`. -/
theorem pow_le_succ_mul_choose_mul_pow_mul_pow (a b : ℕ) :
    (a + b) ^ (a + b) ≤ (a + b + 1) * ((a + b).choose a * a ^ a * b ^ b) := by
  rw [add_pow]
  calc ∑ j ∈ range (a + b + 1), a ^ j * b ^ (a + b - j) * ((a + b).choose j : ℕ)
      ≤ ∑ _j ∈ range (a + b + 1), (a + b).choose a * a ^ a * b ^ b :=
        sum_le_sum fun j hj => by
          have := choose_mul_pow_mul_pow_le a b j (by simpa [Nat.lt_succ_iff] using hj)
          calc a ^ j * b ^ (a + b - j) * (a + b).choose j
              = (a + b).choose j * a ^ j * b ^ (a + b - j) := by ring
            _ ≤ _ := this
    _ = _ := by simp [sum_const]

/-- **Upper bound**: for `n = a + b`, `C(n, a) a ^ a b ^ b ≤ n ^ n`. -/
theorem choose_mul_pow_mul_pow_le_pow (a b : ℕ) :
    (a + b).choose a * a ^ a * b ^ b ≤ (a + b) ^ (a + b) := by
  rw [add_pow]
  have hb : a + b - a = b := by omega
  have := single_le_sum (f := fun j => a ^ j * b ^ (a + b - j) * ((a + b).choose j : ℕ))
    (fun j _ => Nat.zero_le _) (mem_range.mpr (show a < a + b + 1 by omega))
  simp only [hb] at this
  calc (a + b).choose a * a ^ a * b ^ b = a ^ a * b ^ b * (a + b).choose a := by ring
    _ ≤ _ := this

/-- **Upper bound on partial sums**: for `s ≤ n - s`,
`(∑_{j ≤ s} C(n, j)) s ^ s (n - s) ^ (n - s) ≤ n ^ n`. -/
theorem sum_choose_mul_pow_mul_pow_le_pow {n s : ℕ} (hs : s ≤ n - s) :
    (∑ j ∈ range (s + 1), n.choose j) * (s ^ s * (n - s) ^ (n - s)) ≤ n ^ n := by
  have hsn : s ≤ n := by omega
  have hn : s + (n - s) = n := by omega
  have key : ∀ j ≤ s, s ^ s * (n - s) ^ (n - s) ≤ s ^ j * (n - s) ^ (n - j) := by
    intro j hj
    have e1 : s ^ s = s ^ j * s ^ (s - j) := by rw [← pow_add]; congr 1; omega
    have e2 : (n - s) ^ (n - j) = (n - s) ^ (n - s) * (n - s) ^ (s - j) := by
      rw [← pow_add]; congr 1; omega
    rw [e1, e2]
    calc s ^ j * s ^ (s - j) * (n - s) ^ (n - s) = s ^ j * (n - s) ^ (n - s) * s ^ (s - j) := by
          ring
      _ ≤ s ^ j * (n - s) ^ (n - s) * (n - s) ^ (s - j) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
      _ = _ := by ring
  calc (∑ j ∈ range (s + 1), n.choose j) * (s ^ s * (n - s) ^ (n - s))
      = ∑ j ∈ range (s + 1), n.choose j * (s ^ s * (n - s) ^ (n - s)) := by rw [sum_mul]
    _ ≤ ∑ j ∈ range (s + 1), s ^ j * (n - s) ^ (n - j) * n.choose j :=
        sum_le_sum fun j hj => by
          rw [Nat.mul_comm (s ^ j * _)]
          exact Nat.mul_le_mul_left _ (key j (Nat.lt_succ_iff.mp (mem_range.mp hj)))
    _ ≤ ∑ j ∈ range (n + 1), s ^ j * (n - s) ^ (n - j) * n.choose j :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
          fun _ _ _ => Nat.zero_le _
    _ = n ^ n := by
        have := (add_pow s (n - s) n).symm
        rw [hn] at this
        simpa using this

end Nat
