/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Filter.AtTopBot.Basic
import Cslib.Foundations.Data.Nat.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Parameters for fine mass production

Fix a rational copy exponent `γ = num / den < 1` and a slack `X`. Inputs of length `n` are split
into a prefix of `prefixWidth n ≈ (γ + (1 - γ) / (X + 1)) n` bits and a suffix of the remaining
`suffixWidth n ≥ (X / (X + 1)) (1 - γ) n` bits (`mul_le_suffixWidth`). The prefix is encoded in
line-parity codes on `K ^ dimension` over a field of `2 ^ fieldWidth n` elements, where
`fieldWidth n` is a multiple of `blockWidth` and `dimension ≤ 2 ^ blockWidth`. Batches have
`2 ^ depth n` requests, where `depth n = ⌊γ n⌋ + 1`.

The dimension is large enough that `(dimension - 2) * fieldWidth n` eventually exceeds
`depth n` by any fixed amount (`eventually_add_depth_le`): this is the projective-direction
budget of the scheduler. The field width leaves `3 log₂ (n + 2)` prefix bits unused
(`dimension_mul_fieldWidth_le`), so a single code copy is negligible against `2 ^ prefixWidth n`.

## Main definitions

* `Cslib.Circuits.Boolean.MassProduction.Fine.prefixWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.suffixWidth`: the input split.
* `Cslib.Circuits.Boolean.MassProduction.Fine.dimension`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.blockWidth`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.blocks`,
  `Cslib.Circuits.Boolean.MassProduction.Fine.fieldWidth`: the code geometry.
* `Cslib.Circuits.Boolean.MassProduction.Fine.depth`: the batch exponent.

## References

* Simplifies MassProduction/Nonuniform/{GeometricSlopes,BlockParameters,
  CoefficientParameters}.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction.Fine

open Filter

variable (num den X : ℕ)

/-- The prefix width `⌊n (den + num X) / ((X + 1) den)⌋`. -/
def prefixWidth (n : ℕ) : ℕ :=
  n * (den + num * X) / ((X + 1) * den)

/-- The suffix width, the rest of the input. -/
def suffixWidth (n : ℕ) : ℕ :=
  n - prefixWidth num den X n

/-- The dimension of the code geometry. -/
def dimension : ℕ :=
  4 * (den + num * X) + 3

/-- The block width of the field exponent: `dimension ≤ 2 ^ blockWidth`. -/
def blockWidth : ℕ :=
  Nat.clog 2 (dimension num den X)

/-- The number of blocks of the field exponent. -/
def blocks (n : ℕ) : ℕ :=
  (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) / (dimension num den X * blockWidth num den X)

/-- The field has `2 ^ fieldWidth n` elements. -/
def fieldWidth (n : ℕ) : ℕ :=
  blockWidth num den X * blocks num den X n

/-- Batches have `2 ^ depth n` requests. -/
def depth (n : ℕ) : ℕ :=
  num * n / den + 1

variable {num den X}

theorem prefixWidth_le (hnd : num ≤ den) (n : ℕ) : prefixWidth num den X n ≤ n := by
  rcases Nat.eq_zero_or_pos den with rfl | hden
  · simp [prefixWidth]
  apply Nat.div_le_of_le_mul
  calc n * (den + num * X) ≤ n * ((X + 1) * den) := by
        apply Nat.mul_le_mul_left
        nlinarith
    _ = (X + 1) * den * n := by ring

theorem prefixWidth_add_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    prefixWidth num den X n + suffixWidth num den X n = n :=
  Nat.add_sub_of_le (prefixWidth_le hnd n)

/-- The suffix keeps at least a `X / (X + 1)` fraction of `(1 - γ) n` bits. -/
theorem mul_le_suffixWidth (hnd : num ≤ den) (n : ℕ) :
    X * (den - num) * n ≤ (X + 1) * den * suffixWidth num den X n := by
  have hp : (X + 1) * den * prefixWidth num den X n ≤ n * (den + num * X) := by
    unfold prefixWidth
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨e, rfl⟩ : ∃ e, den = num + e := ⟨den - num, by omega⟩
  rw [show num + e - num = e by omega]
  unfold suffixWidth
  rw [Nat.mul_sub]
  have h1 : (X + 1) * (num + e) * n = n * (num + e + num * X) + X * e * n := by ring
  omega

private theorem three_le_dimension : 3 ≤ dimension num den X := by
  unfold dimension
  omega

theorem dimension_le_two_pow_blockWidth : dimension num den X ≤ 2 ^ blockWidth num den X :=
  Nat.le_pow_clog (by norm_num) _

theorem blockWidth_pos : 0 < blockWidth num den X := by
  unfold blockWidth
  have h := three_le_dimension (num := num) (den := den) (X := X)
  exact Nat.clog_pos (by norm_num) (by omega)

/-- The code points use all but `3 log₂ (n + 2)` of the prefix bits. -/
theorem dimension_mul_fieldWidth_le (n : ℕ) :
    dimension num den X * fieldWidth num den X n + 3 * Nat.log 2 (n + 2) ≤
      prefixWidth num den X n ∨ fieldWidth num den X n = 0 := by
  by_cases h : 3 * Nat.log 2 (n + 2) ≤ prefixWidth num den X n
  · left
    have := Nat.div_mul_le_self (prefixWidth num den X n - 3 * Nat.log 2 (n + 2))
      (dimension num den X * blockWidth num den X)
    unfold fieldWidth blocks
    calc dimension num den X * (blockWidth num den X *
          ((prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X))) + 3 * Nat.log 2 (n + 2)
        = (prefixWidth num den X n - 3 * Nat.log 2 (n + 2)) /
            (dimension num den X * blockWidth num den X) *
            (dimension num den X * blockWidth num den X) + 3 * Nat.log 2 (n + 2) := by ring
      _ ≤ prefixWidth num den X n := by omega
  · right
    unfold fieldWidth blocks
    rw [Nat.sub_eq_zero_of_le (by omega), Nat.zero_div, Nat.mul_zero]

/-- Linear growth eventually dominates any affine function of `log₂ (n + 2)`. -/
private theorem eventually_add_mul_log_le (A B : ℕ) :
    ∀ᶠ n in atTop, A + B * Nat.log 2 (n + 2) ≤ n := by
  filter_upwards [Nat.eventually_mul_log_le (2 * B + 1) one_lt_two,
    eventually_ge_atTop (2 * (A + 2 * B) + 4)] with n hlog hn
  have h2 : Nat.log 2 (n + 2) ≤ Nat.log 2 n + 1 := by
    calc Nat.log 2 (n + 2) ≤ Nat.log 2 (2 * n) := Nat.log_mono_right (by omega)
      _ = Nat.log 2 n + 1 := by
        rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  nlinarith

/-- The scheduler budget: `(dimension - 2) * fieldWidth n` eventually exceeds `depth n` by any
fixed amount. -/
theorem eventually_add_depth_le (hnd : num < den) (c : ℕ) :
    ∀ᶠ n in atTop, c + depth num den n ≤ (dimension num den X - 2) * fieldWidth num den X n := by
  set a := den + num * X with ha
  set ℓ := dimension num den X with hℓ
  set h := blockWidth num den X with hh
  set m := (X + 1) * den with hm
  have hℓa : ℓ = 4 * a + 3 := rfl
  have hhpos : 0 < h := blockWidth_pos
  have hmpos : 0 < m := Nat.mul_pos (by omega) (by omega)
  filter_upwards [eventually_add_mul_log_le (ℓ * m * c + ℓ * (X + 1) * den +
      (4 * a + 1) * (m + m * ℓ * h)) (3 * (4 * a + 1) * m)] with n hn
  set p := prefixWidth num den X n with hp
  set L := Nat.log 2 (n + 2) with hL
  set F := fieldWidth num den X n with hF
  set D := depth num den n with hD
  -- Floor bounds.
  have F1 : n * a < m * (p + 1) := by
    rw [hp, prefixWidth, ← ha, ← hm]
    exact Nat.lt_mul_div_succ _ hmpos
  have F2 : p < ℓ * F + ℓ * h + 3 * L := by
    have := Nat.lt_mul_div_succ (p - 3 * L) (Nat.mul_pos (by omega : 0 < ℓ) hhpos)
    rw [hF, fieldWidth, blocks]
    rw [← hp, ← hL, ← hℓ, ← hh]
    have e : ℓ * h * ((p - 3 * L) / (ℓ * h) + 1) =
        ℓ * (h * ((p - 3 * L) / (ℓ * h))) + ℓ * h := by ring
    omega
  have F3 : den * D ≤ num * n + den := by
    rw [hD, depth]
    have := Nat.div_mul_le_self (num * n) den
    nlinarith
  have F4 : ℓ * ((X + 1) * num) + 2 * a + 3 ≤ (4 * a + 1) * a := by
    obtain ⟨e, rfl⟩ : ∃ e, den = num + 1 + e := ⟨den - num - 1, by omega⟩
    rw [ha]
    nlinarith
  have hℓ2 : ℓ - 2 = 4 * a + 1 := by omega
  rw [hℓ2]
  -- Multiply the goal by `ℓ * m` and combine the scaled floor bounds.
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.mul_pos (by omega : 0 < ℓ) hmpos)
  have R1 : ℓ * m * (c + D) = ℓ * m * c + ℓ * (X + 1) * (den * D) := by rw [hm]; ring
  have R2 : ℓ * (X + 1) * (den * D) ≤ ℓ * (X + 1) * (num * n) + ℓ * (X + 1) * den := by
    have := Nat.mul_le_mul_left (ℓ * (X + 1)) F3
    have e : ℓ * (X + 1) * (num * n + den) = ℓ * (X + 1) * (num * n) + ℓ * (X + 1) * den := by
      ring
    omega
  have R3 : ℓ * (X + 1) * (num * n) + (2 * a + 3) * n ≤ (4 * a + 1) * (a * n) := by
    have := Nat.mul_le_mul_right n F4
    have e1 : (ℓ * ((X + 1) * num) + 2 * a + 3) * n =
        ℓ * (X + 1) * (num * n) + (2 * a + 3) * n := by ring
    have e2 : (4 * a + 1) * a * n = (4 * a + 1) * (a * n) := by ring
    omega
  have R4 : (4 * a + 1) * (a * n) ≤ (4 * a + 1) * (m * p) + (4 * a + 1) * m := by
    have := Nat.mul_le_mul_left (4 * a + 1) F1.le
    have e1 : (4 * a + 1) * (n * a) = (4 * a + 1) * (a * n) := by ring
    have e2 : (4 * a + 1) * (m * (p + 1)) = (4 * a + 1) * (m * p) + (4 * a + 1) * m := by ring
    omega
  have R5 : (4 * a + 1) * (m * p) + (4 * a + 1) * m ≤ ℓ * m * ((4 * a + 1) * F) +
      (4 * a + 1) * (m * ℓ * h) + 3 * (4 * a + 1) * m * L := by
    have : (4 * a + 1) * m * (p + 1) ≤ (4 * a + 1) * m * (ℓ * F + ℓ * h + 3 * L) :=
      Nat.mul_le_mul_left _ F2
    have e1 : (4 * a + 1) * m * (p + 1) = (4 * a + 1) * (m * p) + (4 * a + 1) * m := by ring
    have e2 : (4 * a + 1) * m * (ℓ * F + ℓ * h + 3 * L) = ℓ * m * ((4 * a + 1) * F) +
        (4 * a + 1) * (m * ℓ * h) + 3 * (4 * a + 1) * m * L := by ring
    omega
  have R6 : (4 * a + 1) * (m + m * ℓ * h) = (4 * a + 1) * m + (4 * a + 1) * (m * ℓ * h) := by
    ring
  have R7 : n ≤ (2 * a + 3) * n := Nat.le_mul_of_pos_left n (by omega)
  omega

/-- The prefix grows at least linearly: `n < (X + 1) * (prefixWidth n + 1)`. -/
private theorem lt_mul_prefixWidth_add_one (hden : 0 < den) (n : ℕ) :
    n < (X + 1) * (prefixWidth num den X n + 1) := by
  have F1 : n * (den + num * X) < (X + 1) * den * (prefixWidth num den X n + 1) :=
    Nat.lt_mul_div_succ _ (Nat.mul_pos (by omega) hden)
  have : n * den ≤ n * (den + num * X) := Nat.mul_le_mul_left _ (by omega)
  have e : (X + 1) * den * (prefixWidth num den X n + 1) =
      den * ((X + 1) * (prefixWidth num den X n + 1)) := by ring
  have e2 : n * den = den * n := by ring
  exact Nat.lt_of_mul_lt_mul_left (a := den) (by omega)

/-- Eventually the field exponent has at least `c` blocks. -/
theorem eventually_le_blocks (hden : 0 < den) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ blocks num den X n := by
  have hℓh : 0 < dimension num den X * blockWidth num den X :=
    Nat.mul_pos (by have := three_le_dimension (num := num) (den := den) (X := X); omega)
      blockWidth_pos
  filter_upwards [eventually_add_mul_log_le ((X + 1) * (c * (dimension num den X *
      blockWidth num den X) + 1)) (3 * (X + 1))] with n hn
  have hp := lt_mul_prefixWidth_add_one (X := X) (num := num) hden n
  unfold blocks
  apply (Nat.le_div_iff_mul_le hℓh).mpr
  have e : (X + 1) * (c * (dimension num den X * blockWidth num den X) + 1) +
      3 * (X + 1) * Nat.log 2 (n + 2) =
      (X + 1) * (c * (dimension num den X * blockWidth num den X) + 1 +
        3 * Nat.log 2 (n + 2)) := by ring
  have : c * (dimension num den X * blockWidth num den X) + 3 * Nat.log 2 (n + 2) ≤
      prefixWidth num den X n := by
    by_contra hlt
    have := Nat.mul_le_mul_left (X + 1) (show prefixWidth num den X n + 1 ≤
      c * (dimension num den X * blockWidth num den X) + 1 + 3 * Nat.log 2 (n + 2) by omega)
    omega
  omega

/-- Eventually the suffix has at least `c` bits, when the slack is positive. -/
theorem eventually_le_suffixWidth (hnd : num < den) (hX : 0 < X) (c : ℕ) :
    ∀ᶠ n in atTop, c ≤ suffixWidth num den X n := by
  filter_upwards [eventually_ge_atTop ((X + 1) * den * c)] with n hn
  have h := mul_le_suffixWidth (X := X) hnd.le n
  have h1 : n ≤ X * (den - num) * n :=
    Nat.le_mul_of_pos_left n (Nat.mul_pos hX (by omega))
  by_contra hlt
  have := Nat.mul_lt_mul_of_pos_left (show suffixWidth num den X n < c by omega)
    (Nat.mul_pos (by omega : 0 < X + 1) (by omega : 0 < den))
  omega

/-- Slack `X = 16 (P + 1)` in three factors costs less than `1 / (2 P)`. -/
theorem two_mul_slack_le (P : ℕ) :
    2 * P * ((16 * (P + 1) + 1) ^ 2 * (16 * (P + 1) + 2)) ≤ (2 * P + 1) * (16 * (P + 1)) ^ 3 := by
  nlinarith [Nat.zero_le (P ^ 3), Nat.zero_le (P ^ 2), Nat.zero_le P, Nat.zero_le (P ^ 4)]

/-- The leading-coefficient arithmetic of fine mass production. -/
theorem mul_add_le_of_slack {P n w p den num R L O : ℕ}
    (hsuffix : 16 * (P + 1) * (den - num) * n ≤ (16 * (P + 1) + 1) * den * w)
    (hsplit : n = p + w)
    (hR : 16 * (P + 1) * R ≤ (16 * (P + 1) + 2) * 2 ^ p)
    (hL : 16 * (P + 1) * w * L ≤ (16 * (P + 1) + 1) * 2 ^ w)
    (hO : 2 * P * (den - num) * n * O ≤ den * 2 ^ n) :
    P * (den - num) * n * (R * L + O) ≤ (P + 1) * den * 2 ^ n := by
  set X := 16 * (P + 1) with hX
  have hXpos : 0 < X := by omega
  have main : 2 * P * ((den - num) * n * (R * L)) ≤ (2 * P + 1) * (den * 2 ^ n) := by
    have h3 : X ^ 3 * ((den - num) * n * (R * L)) ≤
        (X + 1) ^ 2 * (X + 2) * (den * 2 ^ n) := by
      calc X ^ 3 * ((den - num) * n * (R * L)) = (X * (den - num) * n) * (X * R) * L * X := by
            ring
        _ ≤ ((X + 1) * den * w) * ((X + 2) * 2 ^ p) * L * X := by gcongr
        _ = (X + 1) * den * (X + 2) * 2 ^ p * (X * w * L) := by ring
        _ ≤ (X + 1) * den * (X + 2) * 2 ^ p * ((X + 1) * 2 ^ w) := by gcongr
        _ = (X + 1) ^ 2 * (X + 2) * (den * 2 ^ n) := by rw [hsplit, pow_add]; ring
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < X ^ 3 by positivity)
    calc X ^ 3 * (2 * P * ((den - num) * n * (R * L)))
        = 2 * P * (X ^ 3 * ((den - num) * n * (R * L))) := by ring
      _ ≤ 2 * P * ((X + 1) ^ 2 * (X + 2) * (den * 2 ^ n)) := Nat.mul_le_mul_left _ h3
      _ = 2 * P * ((X + 1) ^ 2 * (X + 2)) * (den * 2 ^ n) := by ring
      _ ≤ (2 * P + 1) * X ^ 3 * (den * 2 ^ n) :=
          Nat.mul_le_mul_right _ (hX ▸ two_mul_slack_le P)
      _ = X ^ 3 * ((2 * P + 1) * (den * 2 ^ n)) := by ring
  have e1 : 2 * (P * (den - num) * n * (R * L + O)) =
      2 * P * ((den - num) * n * (R * L)) + 2 * P * (den - num) * n * O := by ring
  have e2 : 2 * ((P + 1) * den * 2 ^ n) = (2 * P + 1) * (den * 2 ^ n) + den * 2 ^ n := by ring
  omega

/-- Any polynomial is eventually below `2 ^ (n / c)`. -/
private theorem eventually_mul_pow_le_two_pow_div (A E c : ℕ) (hc : 0 < c) :
    ∀ᶠ n in atTop, A * (n + 1) ^ E ≤ 2 ^ (n / c) := by
  have htend : Tendsto (fun n : ℕ => n / c) atTop atTop :=
    tendsto_atTop_atTop.mpr fun k => ⟨c * k, fun n hn =>
      (Nat.le_div_iff_mul_le hc).mpr (by rw [mul_comm]; exact hn)⟩
  filter_upwards [htend.eventually (Nat.eventually_mul_pow_le_pow (A * (2 * c) ^ E) E
    one_lt_two), eventually_ge_atTop c] with n hn hcn
  have hk : n + 1 ≤ 2 * c * (n / c) := by
    have := Nat.lt_mul_div_succ n hc
    have : 1 ≤ n / c := (Nat.le_div_iff_mul_le hc).mpr (by omega)
    nlinarith
  calc A * (n + 1) ^ E ≤ A * (2 * c * (n / c)) ^ E := by gcongr
    _ = A * (2 * c) ^ E * (n / c) ^ E := by rw [mul_pow]; ring
    _ ≤ 2 ^ (n / c) := hn

/-- The last, partly filled code copy is negligible: eventually
`X' * fieldWidth n * 2 ^ (dimension * fieldWidth n) ≤ 2 ^ prefixWidth n`. -/
theorem eventually_mul_two_pow_dimension_le (hnd : num ≤ den) (X' : ℕ) :
    ∀ᶠ n in atTop, X' * fieldWidth num den X n *
      2 ^ (dimension num den X * fieldWidth num den X n) ≤ 2 ^ prefixWidth num den X n := by
  filter_upwards [eventually_ge_atTop (8 * X')] with n hn
  rcases dimension_mul_fieldWidth_le (num := num) (den := den) (X := X) n with h | h
  · have hd := three_le_dimension (num := num) (den := den) (X := X)
    have hF : fieldWidth num den X n ≤ n := by
      have := prefixWidth_le (X := X) hnd n
      have : fieldWidth num den X n ≤ dimension num den X * fieldWidth num den X n :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hlog : n + 2 < 2 * 2 ^ Nat.log 2 (n + 2) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
      rw [pow_succ] at this
      omega
    have h8 : X' * fieldWidth num den X n ≤ 2 ^ (3 * Nat.log 2 (n + 2)) := by
      have hcube : (n + 2) ^ 3 ≤ 8 * 2 ^ (3 * Nat.log 2 (n + 2)) := by
        calc (n + 2) ^ 3 ≤ (2 * 2 ^ Nat.log 2 (n + 2)) ^ 3 := by gcongr
          _ = 8 * 2 ^ (3 * Nat.log 2 (n + 2)) := by rw [mul_pow, ← pow_mul]; ring_nf
      have : 8 * (X' * fieldWidth num den X n) ≤ (n + 2) ^ 3 := by
        calc 8 * (X' * fieldWidth num den X n) ≤ 8 * X' * n := by
              rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hF
          _ ≤ n * n := Nat.mul_le_mul_right _ hn
          _ ≤ (n + 2) ^ 3 := by nlinarith
      omega
    calc X' * fieldWidth num den X n * 2 ^ (dimension num den X * fieldWidth num den X n)
        ≤ 2 ^ (3 * Nat.log 2 (n + 2)) * 2 ^ (dimension num den X * fieldWidth num den X n) :=
          Nat.mul_le_mul_right _ h8
      _ = 2 ^ (dimension num den X * fieldWidth num den X n + 3 * Nat.log 2 (n + 2)) := by
          rw [← pow_add, add_comm]
      _ ≤ 2 ^ prefixWidth num den X n := Nat.pow_le_pow_right (by norm_num) h
  · simp [h]

/-- The prefix leaves a linear number of suffix bits: `n / ((X + 1) den) ≤ suffixWidth n`. -/
private theorem div_le_suffixWidth (hnd : num < den) (hX : 0 < X) (n : ℕ) :
    n / ((X + 1) * den) ≤ suffixWidth num den X n := by
  have h := mul_le_suffixWidth (X := X) hnd.le n
  have h1 : n ≤ X * (den - num) * n := Nat.le_mul_of_pos_left n (Nat.mul_pos hX (by omega))
  exact Nat.div_le_of_le_mul (by linarith)

/-- The scheduler exponent leaves a linear number of bits:
`n / dimension + depth n + fieldWidth n ≤ n + 1`. -/
theorem div_le_sub_depth_add_fieldWidth (hnd : num < den) (n : ℕ) :
    n / dimension num den X + depth num den n + fieldWidth num den X n ≤ n + 1 := by
  have hℓ3 : 3 ≤ dimension num den X := three_le_dimension
  -- `dimension * fieldWidth n ≤ n`.
  have hF : dimension num den X * fieldWidth num den X n ≤ n := by
    rcases dimension_mul_fieldWidth_le (num := num) (den := den) (X := X) n with h | h
    · have := prefixWidth_le (X := X) hnd.le n
      omega
    · rw [h]; omega
  -- `den * depth n ≤ num * n + den`.
  have hD : den * depth num den n ≤ num * n + den := by
    unfold depth
    have := Nat.div_mul_le_self (num * n) den
    nlinarith
  -- `2 den + dimension * num ≤ dimension * den`, since `num < den`.
  have h4 : 2 * den + dimension num den X * num ≤ dimension num den X * den := by
    have hd : 2 * den ≤ dimension num den X := by unfold dimension; nlinarith
    obtain ⟨e, he⟩ : ∃ e, den = num + 1 + e := ⟨den - num - 1, by omega⟩
    have e1 : dimension num den X * den = dimension num den X * num +
        dimension num den X * (1 + e) := by rw [he]; ring
    have e2 : dimension num den X ≤ dimension num den X * (1 + e) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hq : dimension num den X * (n / dimension num den X) ≤ n := Nat.mul_div_le n _
  generalize dimension num den X = ℓ at *
  -- Multiply the claim by `den * ℓ`.
  refine Nat.le_of_mul_le_mul_left (c := den * ℓ) ?_ (Nat.mul_pos (by omega) (by omega))
  have e1 : den * ℓ * (n / ℓ + depth num den n + fieldWidth num den X n) =
      den * (ℓ * (n / ℓ)) + ℓ * (den * depth num den n) + den * (ℓ * fieldWidth num den X n) := by
    ring
  have h1 : den * (ℓ * (n / ℓ)) ≤ den * n := Nat.mul_le_mul_left _ hq
  have h2 : ℓ * (den * depth num den n) ≤ ℓ * (num * n + den) := Nat.mul_le_mul_left _ hD
  have h3 : den * (ℓ * fieldWidth num den X n) ≤ den * n := Nat.mul_le_mul_left _ hF
  have e2 : ℓ * (num * n + den) = (ℓ * num) * n + ℓ * den := by ring
  have h5 : (2 * den + ℓ * num) * n ≤ (ℓ * den) * n := Nat.mul_le_mul_right n h4
  have e3 : den * ℓ * (n + 1) = (ℓ * den) * n + ℓ * den := by ring
  have e4 : (2 * den + ℓ * num) * n = den * n + den * n + (ℓ * num) * n := by ring
  omega

/-- **The overhead is negligible.** For any polynomial factor `A (n + 1) ^ E`, eventually
`2 P (den - num) n · A (2 ^ prefixWidth n + 2 ^ (depth n + fieldWidth n)) (n + 1) ^ E` is at most
`den 2 ^ n`. -/
theorem eventually_overhead_le (hnd : num < den) (hX : 0 < X) (P A E : ℕ) :
    ∀ᶠ n in atTop, 2 * P * (den - num) * n *
      (A * (2 ^ prefixWidth num den X n + 2 ^ (depth num den n + fieldWidth num den X n)) *
        (n + 1) ^ E) ≤ den * 2 ^ n := by
  set c := (X + 1) * den * dimension num den X with hc
  have hcpos : 0 < c := Nat.mul_pos (Nat.mul_pos (by omega) (by omega))
    (by have := three_le_dimension (num := num) (den := den) (X := X); omega)
  filter_upwards [eventually_mul_pow_le_two_pow_div (8 * P * den * A) (E + 1) c hcpos]
    with n hn
  set p := prefixWidth num den X n
  set q := depth num den n + fieldWidth num den X n
  have hp : n / c + p ≤ n := by
    have h1 := div_le_suffixWidth (X := X) hnd hX n
    have h2 := prefixWidth_add_suffixWidth (X := X) hnd.le n
    have : n / c ≤ n / ((X + 1) * den) := Nat.div_le_div_left (Nat.le_mul_of_pos_right _
      (by have := three_le_dimension (num := num) (den := den) (X := X); omega))
      (Nat.mul_pos (by omega) (by omega))
    omega
  have hq : n / c + q ≤ n + 1 := by
    have h1 := div_le_sub_depth_add_fieldWidth (X := X) hnd n
    have : n / c ≤ n / dimension num den X := Nat.div_le_div_left
      (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) (by omega)))
      (by have := three_le_dimension (num := num) (den := den) (X := X); omega)
    omega
  have hpow : 2 ^ p + 2 ^ q ≤ 4 * 2 ^ (n - n / c) := by
    have h1 : 2 ^ p ≤ 2 ^ (n - n / c) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ q ≤ 2 * 2 ^ (n - n / c) := by
      calc 2 ^ q ≤ 2 ^ (n - n / c + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 * 2 ^ (n - n / c) := by rw [pow_succ]; ring
    omega
  have hsplit : 2 ^ n = 2 ^ (n / c) * 2 ^ (n - n / c) := by
    rw [← pow_add]; congr 1; have := Nat.div_le_self n c; omega
  have hgap : den - num ≤ den := Nat.sub_le _ _
  calc 2 * P * (den - num) * n * (A * (2 ^ p + 2 ^ q) * (n + 1) ^ E)
      ≤ 2 * P * den * (n + 1) * (A * (4 * 2 ^ (n - n / c)) * (n + 1) ^ E) := by gcongr; omega
    _ = 8 * P * den * A * (n + 1) ^ (E + 1) * 2 ^ (n - n / c) := by ring
    _ ≤ 2 ^ (n / c) * 2 ^ (n - n / c) := Nat.mul_le_mul_right _ hn
    _ = 2 ^ n := hsplit.symm
    _ ≤ den * 2 ^ n := Nat.le_mul_of_pos_left _ (by omega)

end Cslib.Circuits.Boolean.MassProduction.Fine
