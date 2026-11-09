/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PopulationCount.PolyTime
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring

/-!
# Radix grouping of weighted signed literals

The executable groups and exact reconstruction are the grouping step of
[ChenJiangZhu2027], Lemma A.1, equation (32) (PDF pp.28–29). Weights are nonnegative;
polarity belongs to the literal, not the coefficient. Groups include the zero digit as well,
which does not contribute to the value and preserves the same linear population-count budget.

## Main definitions

* `group`: actual filtered input positions for one radix digit and value.
* `value`: the ordinary weighted sum of signed literals on the original inputs.

## Main results

* `reconstruct`: the complete sum of grouped contributions is the original weighted value.
* `sum_group_lengths`: all groups at one position have exactly n members in total.
* `radix_budget`: an explicit square-root radix and a constant digit budget for weights ≤ n^c.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open scoped BigOperators

/-- Positive polarity reads x; negative polarity reads its complement. -/
@[expose] def literal (positive bit : Bool) : Bool := if positive then bit else !bit

/-- Actual original weighted value, with no independence assumption on the literals. -/
@[expose] def value {n : ℕ} (weights : Fin n → ℕ) (positive x : Fin n → Bool) : ℕ :=
  ∑ i, weights i * (literal (positive i) (x i)).toNat

/-- The digit at position a in radix P. -/
@[expose] def digit (P a w : ℕ) : ℕ := w / P ^ a % P

/-- Executable input positions with the indicated digit, in original input order. -/
@[expose] def group {n : ℕ} (weights : Fin n → ℕ) (P a q : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun i => decide (digit P a (weights i) = q)

private theorem group_sum {n : ℕ} (weights : Fin n → ℕ) (P a q : ℕ)
    (f : Fin n → ℕ) :
    ((group weights P a q).map f).sum =
      ∑ i, if digit P a (weights i) = q then f i else 0 := by
  have h := List.sum_map_ite (fun i : Fin n => digit P a (weights i) = q)
    f (fun _ => 0) (List.finRange n)
  simpa [group, List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def] using h.symm

private theorem sum_group {n P : ℕ} (weights : Fin n → ℕ) (a : ℕ)
    (f : Fin n → ℕ) :
    ∑ q : Fin P, ((group weights P a q).map f).sum =
      ∑ i : Fin n, if digit P a (weights i) < P then f i else 0 := by
  simp only [group_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : digit P a (weights i) < P
  · rw [Finset.sum_eq_single (⟨digit P a (weights i), h⟩ : Fin P)]
    · simp [h]
    · intro b _ hb
      have hn : digit P a (weights i) ≠ b.val := by
        intro he; apply hb; exact Fin.ext he.symm
      simp [hn]
    · simp
  · have hn (q : Fin P) : digit P a (weights i) ≠ q.val := by omega
    simp [hn, h]

/-- Exact total group population: there is one group per original position at each digit. -/
theorem sum_group_lengths {n P : ℕ} (hP : 0 < P) (weights : Fin n → ℕ) (a : ℕ) :
    ∑ q : Fin P, (group weights P a q).length = n := by
  have h := sum_group (P := P) weights a (fun _ => 1)
  simpa [digit, Nat.mod_lt _ hP] using h

private theorem weighted_groups {n P : ℕ} (hP : 0 < P) (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (a : ℕ) :
    ∑ q : Fin P, q.val * ((group weights P a q).map
      (fun i => (literal (positive i) (x i)).toNat)).sum =
      ∑ i : Fin n, digit P a (weights i) * (literal (positive i) (x i)).toNat := by
  simp only [group_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hd : digit P a (weights i) < P := Nat.mod_lt _ hP
  rw [Finset.sum_eq_single (⟨digit P a (weights i), hd⟩ : Fin P)]
  · simp
  · intro b _ hb
    have hn : digit P a (weights i) ≠ b.val := by
      intro he; apply hb; exact Fin.ext he.symm
    simp [hn]
  · simp

private theorem digits_sum (P d w : ℕ) :
    ∑ a ∈ Finset.range d, P ^ a * digit P a w = w % P ^ d := by
  induction d with
  | zero => simp [Nat.mod_one]
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    unfold digit
    rw [pow_succ, Nat.mod_mul]

/-- Equation (32), with exact literal correlations and zero coefficients retained. -/
theorem reconstruct {n P : ℕ} (hP : 0 < P) (d : ℕ) (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (hw : ∀ i, weights i < P ^ d) :
    ∑ a ∈ Finset.range d, P ^ a *
      (∑ q : Fin P, q.val * ((group weights P a q).map
        (fun i => (literal (positive i) (x i)).toNat)).sum) = value weights positive x := by
  simp_rw [weighted_groups hP, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold value
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Nat.mul_assoc]
  rw [← Finset.sum_mul, digits_sum P d (weights i), Nat.mod_eq_of_lt (hw i)]

/-- Half the binary ceiling-log, rounded up by one, including empty/singleton inputs. -/
@[expose] def height (n : ℕ) : ℕ := Nat.clog 2 (n + 1) / 2 + 1

/-- Square-root scale radix, always at least two. -/
@[expose] def radix (n : ℕ) : ℕ := 2 ^ height n

/-- For fixed integral c, this many digit positions suffice uniformly. -/
@[expose] def positions (c : ℕ) : ℕ := 2 * c + 1

/-- No weight truncation: the actual radix expansion covers every coefficient ≤ n^c. -/
theorem radix_budget (n c : ℕ) : 1 < radix n ∧
    n < (radix n) ^ 2 ∧ n ^ c < (radix n) ^ positions c := by
  have hh : 1 ≤ height n := by unfold height; omega
  have hP : 1 < radix n := by
    unfold radix
    exact Nat.one_lt_two_pow (by omega)
  have he : Nat.clog 2 (n + 1) ≤ 2 * height n := by unfold height; omega
  have hn : n < (radix n) ^ 2 := by
    have h := (Nat.le_pow_clog Nat.one_lt_two (n + 1)).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) he)
    simpa only [radix, ← pow_mul, Nat.mul_comm] using (Nat.lt_of_lt_of_le (Nat.lt_succ_self n) h)
  refine ⟨hP, hn, ?_⟩
  calc n ^ c ≤ ((radix n) ^ 2) ^ c := Nat.pow_le_pow_left hn.le c
    _ < ((radix n) ^ 2) ^ c * radix n :=
      by
        have hp : 0 < ((radix n) ^ 2) ^ c := by positivity
        nlinarith
    _ = (radix n) ^ positions c := by
      unfold positions
      rw [pow_add, pow_one, pow_mul]

end Cslib.Circuits.Boolean.WeightedSum
