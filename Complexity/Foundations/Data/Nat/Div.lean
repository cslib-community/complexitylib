/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Data/Nat/Defs.lean` or cslib)

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Dividing repeatedly by a power and quotient-remainder arithmetic

Facts about `n / b ^ j` for the stages of an argument that divides a quantity by `b` at each step,
and exact quotient identities for division by `m` with remainder strictly below `m`.

## Main results

* `Nat.le_div_pow_of_mul_pow_le`: lower bound on `n / b ^ j` when `a * b ^ d ≤ n` and `j ≤ d`.
* `Nat.mul_div_pow_succ_le`: `b * (n / b ^ (j + 1)) ≤ n / b ^ j`.
* `Nat.mul_add_div_of_lt`, `Nat.add_mul_div_of_lt`: dividing `k * m + i` or `i + k * m` by `m`
  when `i < m` yields `k`.
* `Nat.mul_add_div_fin`: the same for `i : Fin m`.
* `Nat.add_sub_mod_mod_eq_ite`: difference of remainders modulo `d`, in the form
  `(a + d - b % d) % d`.
* `Nat.add_sub_mod_mod_eq_of_modEq`: a modular difference is determined by its congruence.
* `Nat.sum_range_mul_ite_mod`: sums over `< n * ℓ` filtered by `q % ℓ = i` (for `i < ℓ`) equal sums
  of `k * ℓ + i` over `k < n`.
-/

@[expose] public section

namespace Nat

/-- If `a b ^ d ≤ n`, then `a ≤ n / b ^ j` for every `j ≤ d`. -/
theorem le_div_pow_of_mul_pow_le {a b d j n : ℕ} (hb : 0 < b) (hj : j ≤ d) (h : a * b ^ d ≤ n) :
    a ≤ n / b ^ j := by
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hb)]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb hj)) h

/-- Dividing by one more power of `b`: `b (n / b ^ (j + 1)) ≤ n / b ^ j`. -/
theorem mul_div_pow_succ_le (n b j : ℕ) : b * (n / b ^ (j + 1)) ≤ n / b ^ j := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact Nat.mul_div_le _ _

/-- Dividing `k * m + i` by `m` when `i < m` yields `k`. -/
theorem mul_add_div_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (k * m + i) / m = k := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi,
    Nat.zero_add]

/-- Dividing `i + k * m` by `m` when `i < m` yields `k`. -/
theorem add_mul_div_of_lt (k : ℕ) {i m : ℕ} (hi : i < m) : (i + k * m) / m = k := by
  rw [Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.zero_add]

/-- Dividing `k * m + i` by `m` for `i : Fin m` yields `k`. -/
theorem mul_add_div_fin (k : ℕ) {m : ℕ} (i : Fin m) : (k * m + i) / m = k :=
  mul_add_div_of_lt k i.isLt

/-- Difference of remainders modulo `d`, in the form `(a + d - b % d) % d`. -/
theorem add_sub_mod_mod_eq_ite (a b d : ℕ) (hd : 0 < d) :
    (a + d - b % d) % d = if a % d < b % d then a % d + d - b % d else a % d - b % d := by
  have ha := Nat.mod_lt a hd
  have hb := Nat.mod_lt b hd
  have hdiv := Nat.div_add_mod a d
  have he : a + d - b % d = (a % d + d - b % d) + d * (a / d) := by omega
  rw [he, Nat.add_mul_mod_self_left]
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show a % d + d - b % d = (a % d - b % d) + d by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- A modular difference is determined by the congruence it satisfies. -/
theorem add_sub_mod_mod_eq_of_modEq {a b c d : ℕ} (hd : 0 < d) (hc : c < d)
    (he : c + b ≡ a [MOD d]) : (a + d - b % d) % d = c := by
  have hb := Nat.mod_lt b hd
  have h1 : (a + d - b % d) + b ≡ c + b [MOD d] :=
    calc (a + d - b % d) + b ≡ (a + d - b % d) + b % d [MOD d] :=
          (Nat.mod_modEq b d).symm.add_left _
      _ = a + d := Nat.sub_add_cancel (by omega)
      _ ≡ a [MOD d] := Nat.add_modEq_right
      _ ≡ c + b [MOD d] := he.symm
  rw [Nat.ModEq.add_right_cancel' b h1, Nat.mod_eq_of_lt hc]

/-- Sums over the positions of `n` blocks of length `ℓ` whose position within the block is `i`, as
sums over the blocks. -/
theorem sum_range_mul_ite_mod {M : Type*} [AddCommMonoid M] (n : ℕ) {i ℓ : ℕ} (hi : i < ℓ)
    (F : ℕ → M) :
    ∑ q ∈ Finset.range (n * ℓ), (if q % ℓ = i then F q else 0) =
      ∑ k ∈ Finset.range n, F (k * ℓ + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have hmod (j : ℕ) (hj : j ∈ Finset.range ℓ) : (n * ℓ + j) % ℓ = j := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl fun j hj => by rw [hmod j hj]]
    simp [hi]

end Nat
