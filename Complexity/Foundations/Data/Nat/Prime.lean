/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.NumberTheory.Chebyshev

/-!
# Products of primes in an interval

The explicit affine disperser works over `𝔽_{2 ^ n}` for `n` a product of distinct primes from an
interval `(L, 4 L]`, kept below a target `T` by a greedy walk through the primes in increasing
order (`Cslib.selectBelow`). The walk either takes every prime or ends within a
factor `4 L` of `T` (`Cslib.prod_le_or_lt_mul_prod_selectBelow`), and Chebyshev's
bounds show that the product of all primes in `(L, 4 L]` is at least `4 ^ L` up to a factor
`(4 L + 1) ^ (4 √L + 5)` (`Cslib.four_pow_le_mul_prod_primesIoc`): the lower bound
`θ (4 L) ≥ 4 L log 2 - O(√L log L)` beats the upper bound `θ L ≤ 2 L log 2` by `2 L log 2`.

## Main definitions

* `Cslib.primesIoc`: the primes in `(a, b]`, in increasing order.
* `Cslib.selectBelow`: the greedy choice of primes with product at most `T`.

## Main results

* `Cslib.prod_selectBelow_le`: the chosen product is at most `T`.
* `Cslib.prod_le_or_lt_mul_prod_selectBelow`: either every prime is chosen or the
  product exceeds `T / B`, for `B` a bound on the primes.
* `Cslib.four_pow_le_mul_prod_primesIoc`: `4 ^ L` is at most
  `(4 L + 1) ^ (4 ⌊√L⌋ + 5)` times the product of the primes in `(L, 4 L]`.

## References

* [P. L. Chebyshev, *Mémoire sur les nombres premiers*][Chebyshev1852]
-/

@[expose] public section

namespace Cslib

/-- The primes `p` with `a < p ≤ b`, in increasing order. -/
def primesIoc (a b : ℕ) : List ℕ :=
  (List.range' (a + 1) (b - a)).filter Nat.Prime

/-- `p` is in `primesIoc a b` exactly when `p` is a prime with `a < p ≤ b`. -/
theorem mem_primesIoc {a b p : ℕ} : p ∈ primesIoc a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp only [primesIoc, List.mem_filter, List.mem_range'_1, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨by omega, by omega, hp⟩
  · rintro ⟨h1, h2, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp⟩

/-- `primesIoc a b` has no duplicates. -/
theorem nodup_primesIoc (a b : ℕ) : (primesIoc a b).Nodup :=
  List.Nodup.filter _ List.nodup_range'

/-- The greedy choice from a list `ps` of primes with product at most `T`: walk through `ps`,
keeping each prime that fits into the remaining budget. -/
def selectBelow : ℕ → List ℕ → List ℕ
  | _, [] => []
  | T, p :: ps => if p ≤ T then p :: selectBelow (T / p) ps else selectBelow T ps

/-- The greedy choice is a sublist of `ps`. -/
theorem selectBelow_sublist (T : ℕ) (ps : List ℕ) : (selectBelow T ps).Sublist ps := by
  induction ps generalizing T with
  | nil => exact List.Sublist.slnil
  | cons p ps ih =>
    simp only [selectBelow]
    split_ifs
    · exact (ih _).cons_cons p
    · exact (ih T).cons p

/-- The greedy choice has product at most the budget `T ≥ 1`. -/
theorem prod_selectBelow_le {T : ℕ} (hT : 1 ≤ T) (ps : List ℕ) : (selectBelow T ps).prod ≤ T := by
  induction ps generalizing T with
  | nil => simpa [selectBelow] using hT
  | cons p ps ih =>
    simp only [selectBelow]
    split_ifs with hp
    · rw [List.prod_cons]
      rcases Nat.eq_zero_or_pos p with rfl | hp0
      · simp
      · calc p * (selectBelow (T / p) ps).prod ≤ p * (T / p) :=
              Nat.mul_le_mul_left _ (ih ((Nat.one_le_div_iff hp0).2 hp))
          _ ≤ T := Nat.mul_div_le T p
    · exact ih hT

/-- **The greedy choice is large**: if every element of `ps` is positive and at most `B`, either
every element is chosen (the product of `ps` is at most the chosen product) or the chosen product
exceeds `T / B`. -/
theorem prod_le_or_lt_mul_prod_selectBelow {B : ℕ} (T : ℕ) {ps : List ℕ}
    (hps : ∀ p ∈ ps, 0 < p ∧ p ≤ B) :
    ps.prod ≤ (selectBelow T ps).prod ∨ T < B * (selectBelow T ps).prod := by
  induction ps generalizing T with
  | nil => simp [selectBelow]
  | cons p ps ih =>
    have hp := hps p List.mem_cons_self
    have hps' : ∀ q ∈ ps, 0 < q ∧ q ≤ B := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    simp only [selectBelow]
    split_ifs with hpT
    · rw [List.prod_cons, List.prod_cons]
      rcases ih (T / p) hps' with h | h
      · exact Or.inl (Nat.mul_le_mul_left _ h)
      · right
        rw [Nat.div_lt_iff_lt_mul hp.1] at h
        calc T < B * (selectBelow (T / p) ps).prod * p := h
          _ = B * (p * (selectBelow (T / p) ps).prod) := by ring
    · right
      have hpos : 0 < (selectBelow T ps).prod :=
        List.prod_pos fun q hq => (hps' q ((selectBelow_sublist T ps).subset hq)).1
      calc T < p := not_le.1 hpT
        _ ≤ B := hp.2
        _ ≤ B * (selectBelow T ps).prod := Nat.le_mul_of_pos_right _ hpos

/-- The product of `primesIoc a b` is the product of the primes in the interval `[a + 1, b]`. -/
theorem prod_primesIoc (a b : ℕ) :
    (primesIoc a b).prod = ∏ p ∈ Finset.Ico (a + 1) (b + 1) with p.Prime, p := by
  rw [Nat.Ico_eq_range', Finset.prod_eq_multiset_prod, Finset.filter_val,
    show b + 1 - (a + 1) = b - a by omega]
  simp [primesIoc, Multiset.filter_coe]

/-- **Chebyshev's bounds on primes in `(L, 4 L]`**: `4 ^ L ≤ (4 L + 1) ^ (4 ⌊√L⌋ + 5)` times
their product. -/
theorem four_pow_le_mul_prod_primesIoc (L : ℕ) :
    4 ^ L ≤ (4 * L + 1) ^ (4 * Nat.sqrt L + 5) * (primesIoc L (4 * L)).prod := by
  set P := (primesIoc L (4 * L)).prod
  have hP : primorial (4 * L) = primorial L * P := by
    rw [show P = _ from prod_primesIoc L (4 * L), show 4 * L = L + 3 * L by ring, primorial_add]
  have hPpos : 0 < P := List.prod_pos fun p hp => (mem_primesIoc.1 hp).2.2.pos
  have hPr : 0 < (P : ℝ) := by exact_mod_cast hPpos
  have hprim : 0 < (primorial L : ℝ) := by exact_mod_cast primorial_pos L
  -- Chebyshev's bounds `θ (4 L) ≥ 4 L log 2 - log (4 L + 1) - 2 √(4 L) log (4 L)`, `θ L ≤ L log 4`
  have h1 := Chebyshev.theta_ge (4 * L)
  have h2 := Chebyshev.theta_le_log4_mul_x (x := L) (Nat.cast_nonneg L)
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at h1 h2
  rw [hP, Nat.cast_mul (primorial L) P, Real.log_mul hprim.ne' hPr.ne'] at h1
  push_cast at h1
  have hsqrt4 : √(4 * (L : ℝ)) = 2 * √(L : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs : √(L : ℝ) ≤ Nat.sqrt L + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    exact_mod_cast (Nat.lt_succ_sqrt L).le.trans_eq (by rw [Nat.succ_eq_add_one]; ring)
  have hmul : √(L : ℝ) * Real.log (4 * L) ≤ (Nat.sqrt L + 1) * Real.log (4 * L + 1) := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp
    · have : (1 : ℝ) ≤ L := by exact_mod_cast hL
      exact mul_le_mul hs (Real.log_le_log (by positivity) (by linarith))
        (Real.log_nonneg (by linarith)) (by positivity)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have key : (L : ℝ) * Real.log 4 ≤ (4 * Nat.sqrt L + 5) * Real.log (4 * L + 1) + Real.log P := by
    rw [hsqrt4] at h1
    nlinarith
  -- exponentiate
  have hreal : ((4 ^ L : ℕ) : ℝ) ≤ (((4 * L + 1) ^ (4 * Nat.sqrt L + 5) * P : ℕ) : ℝ) := by
    rw [← Real.log_le_log_iff (by positivity) (by positivity)]
    push_cast
    rw [Real.log_pow, Real.log_mul (by positivity) hPr.ne', Real.log_pow]
    push_cast
    linarith
  exact_mod_cast hreal

end Cslib
