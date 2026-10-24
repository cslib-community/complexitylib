/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Explicit bounds for the shallow-circuit recurrence

These elementary natural-number inequalities keep the size proof separate
from the circuit construction. All constants are independent of the input
length and the integer root scale.

## Main results

* `Cslib.Circuits.Boolean.ShallowSymmetric.construction_size_bound`: the size of the construction.

## References

* [V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*][LecomteRamakrishnan2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShallowSymmetric

open Finset

/-- Products of numbers below `2 ^ (a k)` and `2 ^ (b k)` are below `2 ^ ((a + b) k)`. -/
private theorem mul_le_two_pow_add_mul {k a b x y : ℕ} (hx : x ≤ 2 ^ (a * k))
    (hy : y ≤ 2 ^ (b * k)) : x * y ≤ 2 ^ ((a + b) * k) := by
  calc
    x * y ≤ 2 ^ (a * k) * 2 ^ (b * k) := Nat.mul_le_mul hx hy
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- Sums of numbers below `2 ^ (a k)` and `2 ^ (b k)` are below `2 ^ ((a + b + 1) k)`. -/
theorem add_le_two_pow_add_add_one_mul {k a b x y : ℕ} (hk : 1 ≤ k) (hx : x ≤ 2 ^ (a * k))
    (hy : y ≤ 2 ^ (b * k)) : x + y ≤ 2 ^ ((a + b + 1) * k) := by
  have hx' : x ≤ 2 ^ ((a + b) * k) := hx.trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))
  have hy' : y ≤ 2 ^ ((a + b) * k) := hy.trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))
  calc
    x + y ≤ 2 ^ ((a + b) * k) * 2 := by omega
    _ = 2 ^ ((a + b) * k + 1) := (pow_succ ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- A constant `c` is below `2 ^ (c k)` for `k ≥ 1`. -/
private theorem le_two_pow_mul (c k : ℕ) (hk : 1 ≤ k) : c ≤ 2 ^ (c * k) :=
  Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by omega) (by nlinarith))

/-- A bound for the entire finite construction, with only its three summary
parameters: input count, sum of moduli, and sum of squared moduli. -/
theorem construction_size_bound {k n U V B N A D E : ℕ} (hk : 1 ≤ k)
    (hn : n ≤ 2 ^ (N * k)) (hu : U ≤ A * k)
    (hv : V ≤ 2 ^ (D * k)) (hb : B ≤ 2 ^ (E * k)) :
    1 + (n + 1) * (1 + (3 ^ U * (n + 1)) * (2 + V * (B + 2))) ≤
      2 ^ ((2 * A + 2 * N + D + E + 8) * k) := by
  have h1 : 1 ≤ 2 ^ (0 * k) := by simp
  have h2 : 2 ≤ 2 ^ (1 * k) := by simpa using Nat.le_self_pow (by omega) 2
  have hn1 := add_le_two_pow_add_add_one_mul hk hn h1
  have hB2 := add_le_two_pow_add_add_one_mul hk hb h2
  have hU : 3 ^ U ≤ 2 ^ ((2 * A) * k) := by
    calc
      3 ^ U ≤ (2 ^ 2) ^ U := Nat.pow_le_pow_left (by norm_num) _
      _ = 2 ^ (2 * U) := (pow_mul ..).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have h := add_le_two_pow_add_add_one_mul hk h1
    (mul_le_two_pow_add_mul hn1 (add_le_two_pow_add_add_one_mul hk h1
      (mul_le_two_pow_add_mul (mul_le_two_pow_add_mul hU hn1) (add_le_two_pow_add_add_one_mul hk h2
        (mul_le_two_pow_add_mul hv hB2)))))
  convert h using 1
  congr 1
  ring

/-- Polynomial factors in the moduli fit into the exponential envelope. -/
theorem sum_sq_moduli_bound {r C k : ℕ} (hk : 1 ≤ k)
    (m : Fin r → ℕ) (hm : ∀ i, m i ≤ C * k) :
    ∑ i, (m i) ^ 2 ≤ 2 ^ ((r + 2 * C + 2) * k) := by
  have hC := le_two_pow_mul C k hk
  have hk' : k ≤ 2 ^ (1 * k) := by simpa using (Nat.lt_two_pow_self (n := k)).le
  have hCk := mul_le_two_pow_add_mul hC hk'
  have hsq := mul_le_two_pow_add_mul hCk hCk
  have h := mul_le_two_pow_add_mul (le_two_pow_mul r k hk) hsq
  calc
    ∑ i, (m i) ^ 2 ≤ ∑ _i : Fin r, (C * k) ^ 2 :=
      sum_le_sum fun i _ => Nat.pow_le_pow_left (hm i) 2
    _ = r * ((C * k) * (C * k)) := by simp [pow_two]
    _ ≤ _ := by
      convert h using 1
      congr 1
      ring

/-- Two blocks fit into the smaller instance used by the depth induction. -/
theorem pair_size_bound {n d k m : ℕ} (hk : 1 ≤ k) (hn : n ≤ k ^ (d + 2))
    (hm : k ≤ m) : 2 * (n / m + 1) ≤ (4 * k) ^ (d + 1) := by
  have hdiv : n / m ≤ k ^ (d + 1) := by
    apply Nat.div_le_of_le_mul
    calc
      n ≤ k ^ (d + 2) := hn
      _ = k * k ^ (d + 1) := by rw [pow_succ']
      _ ≤ m * k ^ (d + 1) := Nat.mul_le_mul_right _ hm
  have hp : 1 ≤ k ^ (d + 1) := Nat.one_le_pow _ _ hk
  calc
    2 * (n / m + 1) ≤ 4 * k ^ (d + 1) := by omega
    _ ≤ 4 ^ (d + 1) * k ^ (d + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 4)
    _ = _ := (mul_pow ..).symm

end Cslib.Circuits.Boolean.ShallowSymmetric
