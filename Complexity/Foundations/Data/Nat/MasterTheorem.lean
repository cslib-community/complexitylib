/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# The master theorem for divide-and-conquer recurrences

`Nat.DivideConquerBound T a b n₀ T₀ f` says that `T` satisfies the divide-and-conquer inequality
`T n ≤ a T(⌈n/b⌉) + f n` above the threshold `n₀`, with `T n ≤ T₀` up to `n₀`. The recurrence is
stated in a form that cost functions satisfy directly. For every `n > n₀`, every `S` that bounds
`T` on `[0, ⌈n/b⌉]` gives `T n ≤ a S + f n`. Floors, ceilings and several subproblems of
different sizes up to `⌈n/b⌉` are therefore covered. `T` need not be monotone or satisfy an
equality.

The general bound unrolls the recursion: for monotone `f` and `n ≤ n₀ b ^ k`,

`T n ≤ a ^ k T₀ + ∑ i < k, a ^ i f (n₀ b ^ (k - i))`

(`Nat.DivideConquerBound.le_sum`). For `f n = c n ^ d` the sum is geometric with ratio `a / b ^ d`,
and the three cases of the master theorem follow with explicit constants. Write `K = ⌈log_b n⌉`.

* `a > b ^ d`: `(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ K`.
* `a = b ^ d`: `T n ≤ (b n) ^ d (T₀ + c n₀ ^ d K)` for `n ≠ 0`.
* `a < b ^ d`: `(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d` for `n ≠ 0`.

The first and third bounds hold for all `a`. They are trivial outside their case, where the
left factor is zero. The `n`-forms use `b ^ ⌈log_b n⌉ ≤ b n` (`Nat.pow_clog_le_mul`).
`Complexity.Foundations.Data.Nat.MasterTheoremAsymptotics` converts them into
`O(n ^ log_b a)`, `O(n ^ d log n)` and `O(n ^ d)`.

`Nat.add_mul_two_pow_le_mul_pow_of_halving` (`Complexity.Foundations.Data.Nat.HalvingRecurrence`)
remains the sharper tool for `b = 2`: it carries a subtracted lower-order term through the
induction, which some clients need.

These are upper bounds only. The source theorem is a `Θ` statement for equality recurrences.
Case 3 is proved for polynomial `f` only, not under the general regularity condition.

## Main definitions

* `Nat.DivideConquerBound`: the divide-and-conquer inequality with threshold and base bound.

## Main results

* `Nat.DivideConquerBound.le_sum`: the unrolled recursion; `Nat.DivideConquerBound.le_geom_sum`
  for `f n = c n ^ d`.
* `Nat.DivideConquerBound.sub_mul_le_pow`, `Nat.DivideConquerBound.le_pow_mul`,
  `Nat.DivideConquerBound.pow_sub_mul_le_pow`: the three cases for `n ≤ n₀ b ^ k`.
* `Nat.DivideConquerBound.sub_mul_le_pow_clog`, `Nat.DivideConquerBound.le_mul_pow_mul_clog`,
  `Nat.DivideConquerBound.pow_sub_mul_le_mul_pow`: the three cases in terms of `n`.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Theorem 4.1
  (the master theorem, Section 4.5), Lemmas 4.2–4.4 and Section 4.6.2 (floors and ceilings).
-/

public section

namespace Nat

open Finset

/-- `T` satisfies the divide-and-conquer inequality `T n ≤ a T(⌈n/b⌉) + f n` above `n₀`, with
`T n ≤ T₀` up to `n₀`. The recursive step quantifies over every bound `S` of `T` on
`[0, ⌈n/b⌉]`, so subproblems of any size up to `⌈n/b⌉` may be used. -/
structure DivideConquerBound (T : ℕ → ℕ) (a b n₀ T₀ : ℕ) (f : ℕ → ℕ) : Prop where
  /-- The base case: `T n ≤ T₀` for `n ≤ n₀`. -/
  base : ∀ n ≤ n₀, T n ≤ T₀
  /-- The recursive step: `T n ≤ a S + f n` whenever `S` bounds `T` up to `⌈n/b⌉`. -/
  step : ∀ n, n₀ < n → ∀ S, (∀ m ≤ (n + b - 1) / b, T m ≤ S) → T n ≤ a * S + f n

namespace DivideConquerBound

variable {T f : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Unrolling the recursion.** For monotone `f` and `n ≤ n₀ b ^ k`,
`T n ≤ a ^ k T₀ + ∑ i < k, a ^ i f (n₀ b ^ (k - i))`. -/
theorem le_sum (h : DivideConquerBound T a b n₀ T₀ f) (ha : 1 ≤ a) (hf : Monotone f) :
    ∀ k n, n ≤ n₀ * b ^ k →
      T n ≤ a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i)) := by
  intro k
  induction k with
  | zero =>
    intro n hn
    simpa using h.base n (by simpa using hn)
  | succ k ih =>
    intro n hn
    rcases le_or_gt n n₀ with hle | hlt
    · calc T n ≤ T₀ := h.base n hle
        _ ≤ a ^ (k + 1) * T₀ := Nat.le_mul_of_pos_left _ (Nat.pow_pos ha)
        _ ≤ _ := Nat.le_add_right _ _
    · set X := n₀ * b ^ k with hX
      have hn' : n ≤ X * b := by rw [hX, mul_assoc, ← pow_succ]; exact hn
      have hb : 0 < b := by
        rcases Nat.eq_zero_or_pos b with rfl | hb
        · simp only [mul_zero] at hn'; omega
        · exact hb
      have hm : (n + b - 1) / b ≤ X := by
        refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hb).mpr ?_)
        rw [Nat.succ_mul]
        omega
      calc T n ≤ a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) + f n :=
            h.step n hlt _ fun m hm' => ih m (hm'.trans hm)
        _ ≤ a * (a ^ k * T₀ + ∑ i ∈ range k, a ^ i * f (n₀ * b ^ (k - i))) +
            f (n₀ * b ^ (k + 1)) := Nat.add_le_add_left (hf hn) _
        _ = _ := by
          rw [sum_range_succ', mul_add, mul_sum]
          simp only [Nat.add_sub_add_right, Nat.sub_zero, pow_zero, one_mul, pow_succ',
            mul_assoc]
          ac_rfl

private theorem sum_pow_mul_poly (c d n₀ a b k : ℕ) :
    ∑ i ∈ range k, a ^ i * (c * (n₀ * b ^ (k - i)) ^ d) =
      c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k - i) d]
  ring

/-- The unrolled recursion for `f n = c n ^ d`. -/
theorem le_geom_sum (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    T n ≤ a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) := by
  have := h.le_sum ha (fun x y hxy => Nat.mul_le_mul_left c (Nat.pow_le_pow_left hxy d)) k n hn
  rwa [sum_pow_mul_poly] at this

end DivideConquerBound

/-! ### Geometric sums -/

/-- The sum `∑ i < k, a ^ i q ^ (k - i)` is `q` times Mathlib's `geom_sum₂` form. -/
private theorem sum_pow_mul_pow_sub (a q k : ℕ) :
    ∑ i ∈ range k, a ^ i * q ^ (k - i) = q * ∑ i ∈ range k, a ^ i * q ^ (k - 1 - i) := by
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have : k - i = (k - 1 - i) + 1 := by have := mem_range.mp hi; omega
  rw [this, pow_succ]
  ring

private theorem sum_pow_mul_pow_sub_self (q k : ℕ) :
    ∑ i ∈ range k, q ^ i * q ^ (k - i) = k * q ^ k := by
  rcases k with _ | k
  · simp
  · rw [sum_pow_mul_pow_sub, geom_sum₂_self, Nat.add_sub_cancel, Nat.cast_id]
    ring

/-! ### The three cases -/

namespace DivideConquerBound

variable {T : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1** (`a > b ^ d`), for `n ≤ n₀ b ^ k`:
`(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ k`. The bound holds for every `a ≥ 1`
and is trivial when `a ≤ b ^ d`. -/
theorem sub_mul_le_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    (a - b ^ d) * T n ≤ ((a - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * a ^ k := by
  have hT := h.le_geom_sum ha k n hn
  rcases le_or_gt (b ^ d) a with hq | hq
  · have hg : (a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) ≤ b ^ d * a ^ k := by
      calc (a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)
          = b ^ d * ((∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - 1 - i)) * (a - b ^ d)) := by
            rw [sum_pow_mul_pow_sub]; ring
        _ ≤ b ^ d * a ^ k := by
            rw [geom_sum₂_mul_of_ge hq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    calc (a - b ^ d) * T n
        ≤ (a - b ^ d) * (a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) :=
          Nat.mul_le_mul_left _ hT
      _ = (a - b ^ d) * a ^ k * T₀ +
            c * n₀ ^ d * ((a - b ^ d) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) := by ring
      _ ≤ (a - b ^ d) * a ^ k * T₀ + c * n₀ ^ d * (b ^ d * a ^ k) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ hg) _
      _ = _ := by ring
  · rw [Nat.sub_eq_zero_of_le hq.le]
    simp

/-- **Master theorem, case 2** (`a = b ^ d`), for `n ≤ n₀ b ^ k`:
`T n ≤ a ^ k (T₀ + c n₀ ^ d k)`. -/
theorem le_pow_mul (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (had : a = b ^ d) (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    T n ≤ a ^ k * (T₀ + c * n₀ ^ d * k) := by
  have hT := h.le_geom_sum ha k n hn
  rw [← had, sum_pow_mul_pow_sub_self] at hT
  calc T n ≤ _ := hT
    _ = _ := by ring

/-- **Master theorem, case 3** (`a < b ^ d`), for `n ≤ n₀ b ^ k`:
`(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b ^ d) ^ k`. The bound holds for every
`a ≥ 1` and is trivial when `a ≥ b ^ d`. -/
theorem pow_sub_mul_le_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d) (ha : 1 ≤ a)
    (k n : ℕ) (hn : n ≤ n₀ * b ^ k) :
    (b ^ d - a) * T n ≤ ((b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d) * (b ^ d) ^ k := by
  have hT := h.le_geom_sum ha k n hn
  rcases le_or_gt a (b ^ d) with hq | hq
  · have hg : (b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i) ≤ b ^ d * (b ^ d) ^ k := by
      calc (b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)
          = b ^ d * ((∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - 1 - i)) * (b ^ d - a)) := by
            rw [sum_pow_mul_pow_sub]; ring
        _ ≤ b ^ d * (b ^ d) ^ k := by
            rw [geom_sum₂_mul_of_le hq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have hak : a ^ k ≤ (b ^ d) ^ k := Nat.pow_le_pow_left hq k
    calc (b ^ d - a) * T n
        ≤ (b ^ d - a) * (a ^ k * T₀ + c * n₀ ^ d * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) :=
          Nat.mul_le_mul_left _ hT
      _ = (b ^ d - a) * a ^ k * T₀ +
            c * n₀ ^ d * ((b ^ d - a) * ∑ i ∈ range k, a ^ i * (b ^ d) ^ (k - i)) := by ring
      _ ≤ (b ^ d - a) * (b ^ d) ^ k * T₀ + c * n₀ ^ d * (b ^ d * (b ^ d) ^ k) := by
          exact Nat.add_le_add (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hak))
            (Nat.mul_le_mul_left _ hg)
      _ = _ := by ring
  · rw [Nat.sub_eq_zero_of_le hq.le]
    simp

end DivideConquerBound

/-! ### Bounds in terms of `n` -/

private theorem le_mul_pow_clog {b n₀ : ℕ} (hb : 1 < b) (hn₀ : 1 ≤ n₀) (n : ℕ) :
    n ≤ n₀ * b ^ clog b n :=
  (le_pow_clog hb n).trans (Nat.le_mul_of_pos_left _ hn₀)

namespace DivideConquerBound

variable {T : ℕ → ℕ} {a b n₀ T₀ c d : ℕ}

/-- **Master theorem, case 1** with `K = ⌈log_b n⌉`:
`(a - b ^ d) T n ≤ ((a - b ^ d) T₀ + c n₀ ^ d b ^ d) a ^ K`. -/
theorem sub_mul_le_pow_clog (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (n : ℕ) :
    (a - b ^ d) * T n ≤ ((a - b ^ d) * T₀ + c * n₀ ^ d * b ^ d) * a ^ clog b n :=
  h.sub_mul_le_pow ha _ n (le_mul_pow_clog hb hn₀ n)

/-- **Master theorem, case 2** with `K = ⌈log_b n⌉`: if `a = b ^ d` and `n ≠ 0`, then
`T n ≤ (b n) ^ d (T₀ + c n₀ ^ d K)`. -/
theorem le_mul_pow_mul_clog (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) (had : a = b ^ d) {n : ℕ} (hn : n ≠ 0) :
    T n ≤ (b * n) ^ d * (T₀ + c * n₀ ^ d * clog b n) := by
  refine (h.le_pow_mul ha had _ n (le_mul_pow_clog hb hn₀ n)).trans
    (Nat.mul_le_mul_right _ ?_)
  rw [had, ← pow_mul, mul_comm d, pow_mul]
  exact Nat.pow_le_pow_left (pow_clog_le_mul hb hn) d

/-- **Master theorem, case 3** in terms of `n`: if `n ≠ 0`, then
`(b ^ d - a) T n ≤ ((b ^ d - a) T₀ + c n₀ ^ d b ^ d) (b n) ^ d`. -/
theorem pow_sub_mul_le_mul_pow (h : DivideConquerBound T a b n₀ T₀ fun n => c * n ^ d)
    (ha : 1 ≤ a) (hb : 1 < b) (hn₀ : 1 ≤ n₀) {n : ℕ} (hn : n ≠ 0) :
    (b ^ d - a) * T n ≤ ((b ^ d - a) * T₀ + c * n₀ ^ d * b ^ d) * (b * n) ^ d := by
  refine (h.pow_sub_mul_le_pow ha _ n (le_mul_pow_clog hb hn₀ n)).trans
    (Nat.mul_le_mul_left _ ?_)
  rw [← pow_mul, mul_comm d, pow_mul]
  exact Nat.pow_le_pow_left (pow_clog_le_mul hb hn) d

end DivideConquerBound

end Nat
