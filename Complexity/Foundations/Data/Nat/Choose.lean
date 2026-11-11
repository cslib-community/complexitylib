/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (to Mathlib's `Mathlib/Combinatorics/Choose/Bounds.lean` or cslib)

public import Complexity.Init
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Scaling bounds for binomial coefficients

Scaling the ground set by `q` scales the number of `d`-subsets by at least `q ^ d`
(`Nat.pow_mul_choose_le_choose_mul`). Consequently a fixed `d`-subset of the ground set lies in at
most a `q ^ (-d)` fraction of the `k`-subsets when the ground set has at least `q k` elements
(`Nat.pow_mul_choose_sub_le_choose`). Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an
`m`-set by at most `(ℓ / (m - ℓ + 1)) ^ s` (`Nat.choose_sub_mul_pow_le`), so by at most
`q ^ (-s)` when `(q + 1) ℓ ≤ m` (`Nat.pow_mul_choose_sub_le_choose_of_mul_le`). Conversely,
descending factorials and binomial coefficients grow at least as fast as powers on larger ground
sets (`Nat.descFactorial_mul_pow_le`, `Nat.choose_mul_pow_le`), which gives the block-avoidance
estimate `2 ^ r * C(b * m - m, b * r) ≤ C(b * m, b * r)` (`Nat.two_pow_mul_choose_sub_le`).
Shrinking the ground set from `m` to `d` shrinks the number of `s`-subsets by at most
`((m + 1 - s) / (d + 1 - s)) ^ s` (`Nat.pow_mul_choose_le_choose_mul_pow`), the estimate behind
the Kővári–Sós–Turán bound.

## Main results

* `Nat.pow_mul_descFactorial_le`, `Nat.pow_mul_choose_le_choose_mul`,
  `Nat.pow_mul_choose_sub_le_choose`: scaling the ground set scales descending factorials and
  binomial coefficients.
* `Nat.choose_sub_mul_pow_le`, `Nat.pow_mul_choose_sub_le_choose_of_mul_le`: lowering the subset
  size scales the binomial coefficient.
* `Nat.pow_mul_choose_le_choose_mul_pow`: shrinking the ground set shrinks the binomial
  coefficient by at most a power.
* `Nat.descFactorial_mul_pow_le`, `Nat.choose_mul_pow_le`, `Nat.choose_mul_sub_mul_pow_le`,
  `Nat.two_mul_pred_pow_le`, `Nat.two_pow_mul_choose_sub_le`: power comparisons and the
  block-avoidance binomial estimate.
-/

@[expose] public section

namespace Nat

/-- Scaling the ground set by `q ≥ 1` scales a descending factorial by at least `q ^ d`. -/
theorem pow_mul_descFactorial_le {q : ℕ} (hq : 1 ≤ q) {k d : ℕ} (hd : d ≤ k) :
    q ^ d * k.descFactorial d ≤ (q * k).descFactorial d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hqk : q * (k - d) ≤ q * k - d := by
      rw [Nat.mul_sub_left_distrib]
      exact Nat.sub_le_sub_left (Nat.le_mul_of_pos_left d (by omega)) (q * k)
    rw [Nat.pow_succ, descFactorial_succ, descFactorial_succ]
    calc q ^ d * q * ((k - d) * k.descFactorial d)
        = (q * (k - d)) * (q ^ d * k.descFactorial d) := by ac_rfl
      _ ≤ (q * k - d) * (q * k).descFactorial d := Nat.mul_le_mul hqk (ih (by omega))

/-- Scaling the ground set by `q ≥ 1` scales the number of `d`-subsets by at least `q ^ d`. -/
theorem pow_mul_choose_le_choose_mul {q : ℕ} (hq : 1 ≤ q) {k d : ℕ} (hd : d ≤ k) :
    q ^ d * k.choose d ≤ (q * k).choose d := by
  have h := pow_mul_descFactorial_le hq hd
  rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose] at h
  refine Nat.le_of_mul_le_mul_left (c := d.factorial) ?_ (factorial_pos d)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- A `d`-subset of an `n`-set lies in at most a `q ^ (-d)` fraction of its `k`-subsets when
`q k ≤ n`. -/
theorem pow_mul_choose_sub_le_choose {q n k d : ℕ} (hq : 1 ≤ q) (hd : d ≤ k) (hn : q * k ≤ n) :
    q ^ d * (n - d).choose (k - d) ≤ n.choose k := by
  have h : q ^ d * k.choose d * (n - d).choose (k - d) ≤ n.choose d * (n - d).choose (k - d) :=
    Nat.mul_le_mul_right _ ((pow_mul_choose_le_choose_mul hq hd).trans (choose_le_choose d hn))
  rw [← choose_mul (n := n) hd] at h
  refine Nat.le_of_mul_le_mul_left (c := k.choose d) ?_ (choose_pos hd)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h

/-- Lowering `ℓ` by `s` scales the number of `ℓ`-subsets of an `m`-set by at most
`(ℓ / (m - ℓ + 1)) ^ s`. -/
theorem choose_sub_mul_pow_le {m ℓ s : ℕ} (hs : s ≤ ℓ) (hℓ : ℓ ≤ m) :
    m.choose (ℓ - s) * (m - ℓ + 1) ^ s ≤ m.choose ℓ * ℓ ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    -- one step down: `C(m, j) (m - j) = C(m, j + 1) (j + 1)` at `j = ℓ - s - 1`
    have hstep := choose_succ_right_eq m (ℓ - (s + 1))
    rw [show ℓ - (s + 1) + 1 = ℓ - s by omega] at hstep
    have h₁ : m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ≤ m.choose (ℓ - s) * ℓ :=
      calc m.choose (ℓ - (s + 1)) * (m - ℓ + 1)
          ≤ m.choose (ℓ - (s + 1)) * (m - (ℓ - (s + 1))) := Nat.mul_le_mul_left _ (by omega)
        _ = m.choose (ℓ - s) * (ℓ - s) := hstep.symm
        _ ≤ m.choose (ℓ - s) * ℓ := Nat.mul_le_mul_left _ (by omega)
    calc m.choose (ℓ - (s + 1)) * (m - ℓ + 1) ^ (s + 1)
        = m.choose (ℓ - (s + 1)) * (m - ℓ + 1) * (m - ℓ + 1) ^ s := by ring
      _ ≤ m.choose (ℓ - s) * ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_right _ h₁
      _ = m.choose (ℓ - s) * (m - ℓ + 1) ^ s * ℓ := by ring
      _ ≤ m.choose ℓ * ℓ ^ s * ℓ := Nat.mul_le_mul_right _ (ih (by omega))
      _ = m.choose ℓ * ℓ ^ (s + 1) := by ring

/-- If `ℓ` and `q ℓ` together fit into `m`, lowering `ℓ` by `s ≤ ℓ` divides the number of
`ℓ`-subsets of an `m`-set by at least `q ^ s`. -/
theorem pow_mul_choose_sub_le_choose_of_mul_le {m ℓ s q : ℕ} (hs : s ≤ ℓ)
    (hℓ : (q + 1) * ℓ ≤ m) : q ^ s * m.choose (ℓ - s) ≤ m.choose ℓ := by
  have hℓm : ℓ ≤ m := le_trans (Nat.le_mul_of_pos_left ℓ (by omega)) hℓ
  have hqℓ : q * ℓ ≤ m - ℓ + 1 := by
    have : (q + 1) * ℓ = q * ℓ + ℓ := by ring
    omega
  refine Nat.le_of_mul_le_mul_right (?_ : _ * (m - ℓ + 1) ^ s ≤ _ * (m - ℓ + 1) ^ s)
    (Nat.pow_pos (by omega))
  calc q ^ s * m.choose (ℓ - s) * (m - ℓ + 1) ^ s
      = q ^ s * (m.choose (ℓ - s) * (m - ℓ + 1) ^ s) := by ring
    _ ≤ q ^ s * (m.choose ℓ * ℓ ^ s) := Nat.mul_le_mul_left _ (choose_sub_mul_pow_le hs hℓm)
    _ = m.choose ℓ * (q * ℓ) ^ s := by rw [Nat.mul_pow]; ring
    _ ≤ m.choose ℓ * (m - ℓ + 1) ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hqℓ s)

/-- Descending factorials compare like powers: `s^{(k)} / n^{(k)} ≤ (s / n)^k` for `s ≤ n`. -/
theorem descFactorial_mul_pow_le {s n : ℕ} (h : s ≤ n) (k : ℕ) :
    s.descFactorial k * n ^ k ≤ s ^ k * n.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (s - k) * n ≤ s * (n - k) := by
      rcases le_or_gt k s with hks | hks
      · zify [hks, hks.trans h]
        nlinarith
      · rw [Nat.sub_eq_zero_of_le hks.le, zero_mul]
        exact Nat.zero_le _
    rw [descFactorial_succ, descFactorial_succ, pow_succ, pow_succ]
    calc (s - k) * s.descFactorial k * (n ^ k * n)
        = s.descFactorial k * n ^ k * ((s - k) * n) := by ring
      _ ≤ s ^ k * n.descFactorial k * (s * (n - k)) := Nat.mul_le_mul ih hk
      _ = s ^ k * s * ((n - k) * n.descFactorial k) := by ring

/-- For `a ≤ s`, `C(a, k) * s ^ k ≤ C(s, k) * a ^ k`. -/
theorem choose_mul_pow_le {a s : ℕ} (has : a ≤ s) (k : ℕ) :
    a.choose k * s ^ k ≤ s.choose k * a ^ k := by
  refine Nat.le_of_mul_le_mul_left ?_ (factorial_pos k)
  calc k.factorial * (a.choose k * s ^ k)
      = (k.factorial * a.choose k) * s ^ k := by ring
    _ = a.descFactorial k * s ^ k := by rw [← descFactorial_eq_factorial_mul_choose]
    _ ≤ a ^ k * s.descFactorial k := descFactorial_mul_pow_le has k
    _ = a ^ k * (k.factorial * s.choose k) := by rw [descFactorial_eq_factorial_mul_choose]
    _ = k.factorial * (s.choose k * a ^ k) := by ring

/-- Descending factorials on a smaller ground set:
`(d + 1 - s) ^ k m^{(k)} ≤ d^{(k)} (m + 1 - s) ^ k` for `k ≤ s ≤ d ≤ m`, since
`(d + 1 - s) (m - i) ≤ (d - i) (m + 1 - s)` for `i < s`. -/
private theorem pow_mul_descFactorial_le_descFactorial_mul_pow {d m s : ℕ} (hsd : s ≤ d)
    (hdm : d ≤ m) {k : ℕ} (hks : k ≤ s) :
    (d + 1 - s) ^ k * m.descFactorial k ≤ d.descFactorial k * (m + 1 - s) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (d + 1 - s) * (m - k) ≤ (d - k) * (m + 1 - s) := by
      obtain ⟨j, rfl⟩ : ∃ j, s = k + 1 + j := ⟨s - k - 1, by omega⟩
      obtain ⟨a, rfl⟩ : ∃ a, d = k + 1 + j + a := ⟨d - (k + 1 + j), by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, m = k + 1 + j + a + b := ⟨m - (k + 1 + j + a), by omega⟩
      rw [show k + 1 + j + a + 1 - (k + 1 + j) = a + 1 by omega,
        show k + 1 + j + a + b - k = 1 + j + a + b by omega,
        show k + 1 + j + a - k = 1 + j + a by omega,
        show k + 1 + j + a + b + 1 - (k + 1 + j) = a + b + 1 by omega]
      nlinarith [Nat.zero_le (b * j)]
    rw [descFactorial_succ, descFactorial_succ, pow_succ, pow_succ]
    calc (d + 1 - s) ^ k * (d + 1 - s) * ((m - k) * m.descFactorial k)
        = (d + 1 - s) ^ k * m.descFactorial k * ((d + 1 - s) * (m - k)) := by ring
      _ ≤ d.descFactorial k * (m + 1 - s) ^ k * ((d - k) * (m + 1 - s)) :=
          Nat.mul_le_mul (ih (by omega)) hk
      _ = (d - k) * d.descFactorial k * ((m + 1 - s) ^ k * (m + 1 - s)) := by ring

/-- Shrinking the ground set from `m` to `d ≤ m` shrinks the number of `s`-subsets by at most
`((m + 1 - s) / (d + 1 - s)) ^ s`: `(d + 1 - s) ^ s C(m, s) ≤ C(d, s) (m + 1 - s) ^ s`. -/
theorem pow_mul_choose_le_choose_mul_pow {d m s : ℕ} (hdm : d ≤ m) :
    (d + 1 - s) ^ s * m.choose s ≤ d.choose s * (m + 1 - s) ^ s := by
  rcases Nat.lt_or_ge d s with hds | hsd
  · rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · rw [show d + 1 - s = 0 by omega, zero_pow hs.ne', zero_mul]
      exact Nat.zero_le _
  refine Nat.le_of_mul_le_mul_left ?_ (factorial_pos s)
  have h := pow_mul_descFactorial_le_descFactorial_mul_pow hsd hdm le_rfl
  rw [descFactorial_eq_factorial_mul_choose, descFactorial_eq_factorial_mul_choose] at h
  calc s.factorial * ((d + 1 - s) ^ s * m.choose s)
      = (d + 1 - s) ^ s * (s.factorial * m.choose s) := by ring
    _ ≤ s.factorial * d.choose s * (m + 1 - s) ^ s := h
    _ = s.factorial * (d.choose s * (m + 1 - s) ^ s) := by ring

/-- `C(b * m - m, k) * b ^ k ≤ C(b * m, k) * (b - 1) ^ k`. -/
theorem choose_mul_sub_mul_pow_le (b m k : ℕ) :
    (b * m - m).choose k * b ^ k ≤ (b * m).choose k * (b - 1) ^ k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases k with _ | k <;> simp
  · have hbm : b * m - m = (b - 1) * m := by
      rw [Nat.sub_mul, one_mul]
    rw [hbm]
    have hle : (b - 1) * m ≤ b * m := Nat.mul_le_mul_right m (Nat.sub_le b 1)
    have h := choose_mul_pow_le hle k
    rw [Nat.mul_pow, Nat.mul_pow] at h
    have hpos : 0 < m ^ k := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc ((b - 1) * m).choose k * b ^ k * m ^ k
        = ((b - 1) * m).choose k * (b ^ k * m ^ k) := by ring
      _ ≤ (b * m).choose k * ((b - 1) ^ k * m ^ k) := h
      _ = (b * m).choose k * (b - 1) ^ k * m ^ k := by ring

/-- Bernoulli's inequality in `ℕ`: for `1 ≤ n`, `d ^ n + n * d ^ (n - 1) ≤ (d + 1) ^ n`. -/
private theorem pow_add_mul_pow_sub_one_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    d ^ n + n * d ^ (n - 1) ≤ (d + 1) ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  clear hn
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Nat.add_sub_cancel] at ih ⊢
    calc d ^ (k + 2) + (k + 2) * d ^ (k + 1)
        = (d ^ (k + 1) + (k + 1) * d ^ k) * d + d ^ (k + 1) := by ring
      _ ≤ (d ^ (k + 1) + (k + 1) * d ^ k) * d + d ^ (k + 1) + (k + 1) * d ^ k :=
          Nat.le_add_right _ _
      _ = (d ^ (k + 1) + (k + 1) * d ^ k) * (d + 1) := by ring
      _ ≤ (d + 1) ^ (k + 1) * (d + 1) := Nat.mul_le_mul_right (d + 1) ih
      _ = (d + 1) ^ (k + 2) := by ring

/-- For `1 ≤ b`, `2 * (b - 1) ^ b ≤ b ^ b`. -/
theorem two_mul_pred_pow_le {b : ℕ} (hb : 1 ≤ b) :
    2 * (b - 1) ^ b ≤ b ^ b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  have h := pow_add_mul_pow_sub_one_le d (Nat.succ_pos d)
  calc 2 * d ^ (d + 1)
      = d ^ (d + 1) + d * d ^ d := by ring
    _ ≤ d ^ (d + 1) + (d + 1) * d ^ d :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (d ^ d) (Nat.le_succ d)) _
    _ ≤ (d + 1) ^ (d + 1) := h

/-- For `1 ≤ b`, `2 ^ r * C(b * m - m, b * r) ≤ C(b * m, b * r)`. -/
theorem two_pow_mul_choose_sub_le {b m : ℕ} (hb : 1 ≤ b) (r : ℕ) :
    2 ^ r * (b * m - m).choose (b * r) ≤ (b * m).choose (b * r) := by
  have hpow : 2 ^ r * (b - 1) ^ (b * r) ≤ b ^ (b * r) := by
    calc 2 ^ r * (b - 1) ^ (b * r)
        = (2 * (b - 1) ^ b) ^ r := by rw [Nat.mul_pow, ← pow_mul]
      _ ≤ (b ^ b) ^ r := Nat.pow_le_pow_left (two_mul_pred_pow_le hb) r
      _ = b ^ (b * r) := by rw [← pow_mul]
  have hchoose := choose_mul_sub_mul_pow_le b m (b * r)
  have hpos : 0 < b ^ (b * r) := by positivity
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc 2 ^ r * (b * m - m).choose (b * r) * b ^ (b * r)
      = 2 ^ r * ((b * m - m).choose (b * r) * b ^ (b * r)) := by ring
    _ ≤ 2 ^ r * ((b * m).choose (b * r) * (b - 1) ^ (b * r)) :=
        Nat.mul_le_mul_left (2 ^ r) hchoose
    _ = (b * m).choose (b * r) * (2 ^ r * (b - 1) ^ (b * r)) := by ring
    _ ≤ (b * m).choose (b * r) * b ^ (b * r) :=
        Nat.mul_le_mul_left _ hpow

end Nat
