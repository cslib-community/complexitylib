/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Hypercontractivity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Kahn–Kalai–Linial theorem and Talagrand's inequality

Read a Boolean function `f` as the function `F = (-1) ^ f` with values `±1`. By the Poincaré
inequality the influences of `F` on its `n` coordinates average at least `Var[F] / n`; the
**Kahn–Kalai–Linial theorem** says that some coordinate has influence at least
`c · Var[F] · log n / n`, for an absolute constant `c > 0` [KahnKalaiLinial1988]. We prove it
with `c = 1 / 12` (`BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence`),
through an edge-isoperimetric form: if every coordinate has influence at most `δ`, then the total
influence is at least `1 / 6 · Var[F] · log (1 / δ)`
(`BitString.expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence`). This is a weaker form
of the KKL Edge-Isoperimetric Theorem in O'Donnell's exposition, proved by the same use of
hypercontractivity on the derivatives [O'Donnell, Section 9.6][ODonnell2014]. Here `Var[F]` is
written `𝔼 x, (F x - 𝔼 y, F y) ^ 2`, the Fourier weight of `F` on the nonempty sets.

The same argument, run separately on each coordinate, proves **Talagrand's inequality**
`Var[F] ≤ 6 ∑ᵢ Infᵢ[F] / log (1 / Infᵢ[F])`, for functions whose influences are all less than
one (`BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log`) [Talagrand1994]; the form
`Var[F] ≤ 7 ∑ᵢ Infᵢ[F] / (1 + log (1 / Infᵢ[F]))` holds for every Boolean function
(`BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`).

## Proof

The derivative `Dᵢ F` takes the values `0` and `±1`, so `‖Dᵢ F‖_{4/3} ^ 2 = Infᵢ[F] ^ (3/2)`
(`BitString.lpNorm_derivative_signVal`), and the `(4/3, 2)`-Hypercontractivity Theorem
`Stab_{1/3}[Dᵢ F] ≤ ‖Dᵢ F‖_{4/3} ^ 2` bounds the low-degree part of the Fourier weight on the sets
containing `i` (`BitString.mul_noiseStability_derivative`,
`BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le`):

  `∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 = 1/3 · Stab_{1/3}[Dᵢ F] ≤ 1/3 · Infᵢ[F] ^ (3/2)`.

The variance is `∑ᵢ ∑_{S ∋ i} F̂(S) ^ 2 / |S|`. For `A > 1` and every `m ≥ 1`,
`1 / m ≤ log 3 / log A + A 3 ^ (-m)`, according as `3 ^ m ≥ A` or not, so the weight on the sets
containing `i` is at most `log 3 / log A · Infᵢ[F] + A / 3 · Infᵢ[F] ^ (3/2)`. If
`Infᵢ[F] ≤ δ < 1`, the choice `A = δ ^ (-1/4)` and the bound `δ ^ (1/4) log (1 / δ) < 4` turn
this into `6 Infᵢ[F] / log (1 / δ)`.
Summing over `i` with a common `δ` gives the Kahn–Kalai–Linial bound, and taking `δ = Infᵢ[F]`
gives Talagrand's inequality.

## Main results

* `Cslib.BitString.sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le`: hypercontractivity
  bounds the low-degree weight on the sets containing a coordinate.
* `Cslib.BitString.expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence`: the
  Kahn–Kalai–Linial theorem, in the form "small influences force large total influence".
* `Cslib.BitString.exists_expect_sub_expect_sq_mul_log_card_div_le_influence`: the
  Kahn–Kalai–Linial theorem.
* `Cslib.BitString.expect_sub_expect_sq_le_six_mul_sum_influence_div_log`,
  `Cslib.BitString.expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`: Talagrand's
  inequality.

## References

* [J. Kahn, G. Kalai and N. Linial, *The influence of variables on Boolean
  functions*][KahnKalaiLinial1988]
* [M. Talagrand, *On Russo's approximate zero-one law*][Talagrand1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Hypercontractivity on the derivatives -/

/-- **Hypercontractivity bounds the low-degree weight on the sets containing a coordinate**: for a
Boolean function read as signs, `∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 ≤ 1/3 · Infᵢ[F] ^ (3/2)`, by the
`(4/3, 2)`-Hypercontractivity Theorem applied to the derivative in `i`
[O'Donnell, Corollary 9.12][ODonnell2014]. -/
theorem sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le (f : (ι → Bool) → Bool) (i : ι) :
    ∑ S with i ∈ S, (1 / 3 : ℝ) ^ #S * fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      influence i (fun x => signVal (f x)) * √(influence i fun x => signVal (f x)) / 3 := by
  set a := influence i fun x => signVal (f x)
  have ha : 0 ≤ a := influence_nonneg i _
  have hnorm : lpNorm (4 / 3) (derivative i fun x => signVal (f x)) ^ 2 = a * √a := by
    rw [lpNorm_derivative_signVal f i (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul ha,
      Real.sqrt_eq_rpow, show (4 / 3 : ℝ)⁻¹ * ((2 : ℕ) : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' ha (by norm_num), Real.rpow_one]
  have h := noiseStability_one_third_le (derivative i fun x => signVal (f x))
  rw [← mul_noiseStability_derivative]
  linarith

/-! ### The weight on the sets containing a coordinate -/

/-- The variance is the sum over the coordinates `i` of `∑_{S ∋ i} f̂(S) ^ 2 / |S|`: each
nonempty set shares its weight equally among its elements. -/
private theorem sum_sum_filter_mem_fourierCoeff_sq_div_card (f : (ι → Bool) → ℝ) :
    ∑ i, ∑ S with i ∈ S, fourierCoeff f S ^ 2 / #S = 𝔼 x, (f x - 𝔼 y, f y) ^ 2 := by
  rw [expect_sub_expect_sq_eq_sum_fourierCoeff_sq]
  simp only [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  split_ifs with hS
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (card_ne_zero.2 (nonempty_iff_ne_empty.2 hS)))]
  · simp [not_not.1 hS]

/-- The weight `∑_{S ∋ i} f̂(S) ^ 2 / |S|` is at most the influence of `i`. -/
theorem sum_filter_mem_fourierCoeff_sq_div_card_le_influence (f : (ι → Bool) → ℝ) (i : ι) :
    ∑ S with i ∈ S, fourierCoeff f S ^ 2 / #S ≤ influence i f := by
  rw [influence_eq_sum_fourierCoeff_sq]
  refine sum_le_sum fun S hS => div_le_self (sq_nonneg _) ?_
  exact Nat.one_le_cast.2 (card_pos.2 ⟨i, (mem_filter.1 hS).2⟩)

/-- **The degree threshold**: for `A > 1`, every `m` satisfies `1 ≤ m log 3 / log A` or
`1 < A 3 ^ (-m)`, according as `3 ^ m ≥ A` or not. -/
theorem one_le_mul_log_three_div_log_or_one_lt_mul_one_third_pow {A : ℝ} (hA : 1 < A) (m : ℕ) :
    1 ≤ m * (log 3 / log A) ∨ 1 < A * (1 / 3) ^ m := by
  have hlogA : 0 < log A := log_pos hA
  rcases le_or_gt A (3 ^ m) with h | h
  · left
    have hle : log A ≤ m * log 3 := by
      rw [← log_pow]
      exact log_le_log (by linarith) h
    rw [mul_div_assoc', le_div_iff₀ hlogA, one_mul]
    exact hle
  · right
    rw [one_div, inv_pow, ← div_eq_mul_inv, one_lt_div (by positivity)]
    exact h

/-- For `A > 1` and `m ≥ 1`, `1 / m ≤ log 3 / log A + A 3 ^ (-m)`. -/
private theorem inv_le_log_div_log_add {A : ℝ} (hA : 1 < A) {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ)⁻¹ ≤ log 3 / log A + A * (1 / 3) ^ m := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h3 : 0 ≤ log 3 / log A := div_nonneg (log_pos (by norm_num)).le (log_pos hA).le
  have hpow : 0 ≤ A * (1 / 3 : ℝ) ^ m := by
    have : (0 : ℝ) < A := by linarith
    positivity
  rcases one_le_mul_log_three_div_log_or_one_lt_mul_one_third_pow hA m with h | h
  · have : (m : ℝ)⁻¹ ≤ log 3 / log A := by
      rw [inv_le_iff_one_le_mul₀ hm', mul_comm]
      exact h
    linarith
  · have : (m : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hm)
    linarith

/-- **The weight on the sets containing a coordinate**: for a Boolean function read as signs and
every `A > 1`, `∑_{S ∋ i} F̂(S) ^ 2 / |S| ≤ log 3 / log A · Infᵢ[F] + A / 3 · Infᵢ[F] ^ (3/2)`. -/
private theorem sum_filter_mem_fourierCoeff_sq_div_card_le (f : (ι → Bool) → Bool) (i : ι) {A : ℝ}
    (hA : 1 < A) :
    ∑ S with i ∈ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 / #S ≤
      log 3 / log A * influence i (fun x => signVal (f x)) +
        A / 3 * (influence i (fun x => signVal (f x)) *
          √(influence i fun x => signVal (f x))) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have h := sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le f i
  calc ∑ S with i ∈ S, fourierCoeff F S ^ 2 / #S
      ≤ ∑ S with i ∈ S, (log 3 / log A * fourierCoeff F S ^ 2 +
          A * ((1 / 3) ^ #S * fourierCoeff F S ^ 2)) := by
        refine sum_le_sum fun S hS => ?_
        have hm : 1 ≤ #S := card_pos.2 ⟨i, (mem_filter.1 hS).2⟩
        have := mul_le_mul_of_nonneg_right (inv_le_log_div_log_add hA hm)
          (sq_nonneg (fourierCoeff F S))
        rw [div_eq_inv_mul]
        linarith
    _ = log 3 / log A * influence i F +
          A * ∑ S with i ∈ S, (1 / 3) ^ #S * fourierCoeff F S ^ 2 := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, influence_eq_sum_fourierCoeff_sq]
    _ ≤ log 3 / log A * influence i F + A / 3 * (influence i F * √(influence i F)) := by
        have hA0 : 0 ≤ A := by linarith
        have := mul_le_mul_of_nonneg_left h hA0
        rw [mul_div_assoc'] at this
        linarith [show A * (influence i F * √(influence i F)) / 3 =
          A / 3 * (influence i F * √(influence i F)) by ring]

/-- `x ^ (1/4) log (1 / x) < 4` on `0 < x ≤ 1`, written with `√√x`. -/
private theorem sqrt_sqrt_mul_log_inv_lt {x : ℝ} (hx : 0 < x) (hx' : x ≤ 1) :
    √√x * log x⁻¹ < 4 := by
  set u := √√x
  have hu : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)
  have hu1 : u ≤ 1 := Real.sqrt_le_one.2 (Real.sqrt_le_one.2 hx')
  have hlog : log x⁻¹ = -(4 * log u) := by
    have hx4 : x = u ^ 4 := by
      rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, Real.sq_sqrt (Real.sqrt_nonneg x),
        Real.sq_sqrt hx.le]
    rw [log_inv, hx4, log_pow]
    push_cast
    ring
  have h := abs_log_mul_self_lt u hu hu1
  have hneg : log u * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (log_nonpos hu.le hu1) hu.le
  rw [abs_of_nonpos hneg] at h
  rw [hlog]
  linarith

/-- **The weight on the sets containing a coordinate of small influence**: if
`Infᵢ[F] ≤ δ`, then `∑_{S ∋ i} F̂(S) ^ 2 / |S| · log (1 / δ) ≤ 6 Infᵢ[F]`. For `δ < 1` this is
`∑_{S ∋ i} F̂(S) ^ 2 / |S| ≤ 6 Infᵢ[F] / log (1 / δ)`; for `δ ≥ 1` the left side is at most
zero. -/
private theorem sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le (f : (ι → Bool) → Bool) (i : ι)
    {δ : ℝ} (hδ : influence i (fun x => signVal (f x)) ≤ δ) :
    (∑ S with i ∈ S, fourierCoeff (fun x => signVal (f x)) S ^ 2 / #S) * log δ⁻¹ ≤
      6 * influence i (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set a := influence i F
  set W := ∑ S with i ∈ S, fourierCoeff F S ^ 2 / #S
  have ha : 0 ≤ a := influence_nonneg i F
  have hW : 0 ≤ W := sum_nonneg fun S _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  rcases le_or_gt (log δ⁻¹) 0 with hL | hL
  · nlinarith
  -- now `0 < δ < 1`; take `A = δ ^ (-1/4) = (√√δ)⁻¹`
  obtain ⟨hδ0, hδ1⟩ := one_lt_inv_iff₀.1 ((log_pos_iff (inv_nonneg.2 (ha.trans hδ))).1 hL)
  set u := √√δ
  have hu : 0 < u := Real.sqrt_pos.2 (Real.sqrt_pos.2 hδ0)
  have hu1 : u < 1 :=
    (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact (Real.sqrt_lt' one_pos).2 (by simpa))
  have hu2 : √δ = u ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg δ)).symm
  have hlogA : log u⁻¹ = log δ⁻¹ / 4 := by
    have hδ4 : δ = u ^ 4 := by
      rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, ← hu2, Real.sq_sqrt hδ0.le]
    rw [log_inv, log_inv, hδ4, log_pow]
    push_cast
    ring
  have hmain := sum_filter_mem_fourierCoeff_sq_div_card_le f i (one_lt_inv_iff₀.2 ⟨hu, hu1⟩)
  have hAa : u⁻¹ / 3 * (a * √a) ≤ u / 3 * a := by
    have hsqrt : √a ≤ u ^ 2 := hu2 ▸ Real.sqrt_le_sqrt hδ
    have : u⁻¹ * √a ≤ u := by
      rw [inv_mul_le_iff₀ hu, ← sq]
      exact hsqrt
    nlinarith [Real.sqrt_nonneg a]
  have h4 := sqrt_sqrt_mul_log_inv_lt hδ0 hδ1.le
  have h3 : log 3 * a ≤ 1.1 * a := mul_le_mul_of_nonneg_right (by linarith [log_three_lt_d9]) ha
  have hua : u * log δ⁻¹ * a ≤ 4 * a := mul_le_mul_of_nonneg_right h4.le ha
  calc W * log δ⁻¹ ≤ (log 3 / log u⁻¹ * a + u / 3 * a) * log δ⁻¹ :=
        mul_le_mul_of_nonneg_right (hmain.trans (by linarith)) hL.le
    _ = 4 * (log 3 * a) + u * log δ⁻¹ * a / 3 := by
        have hL0 := hL.ne'
        have e : log 3 / (log δ⁻¹ / 4) * a * log δ⁻¹ = 4 * (log 3 * a) := by
          rw [div_div_eq_mul_div, mul_right_comm, div_mul_cancel₀ _ hL0]
          ring
        rw [hlogA, add_mul, e]
        ring
    _ ≤ 6 * a := by linarith

/-! ### The Kahn–Kalai–Linial theorem -/

/-- **The Kahn–Kalai–Linial theorem, edge-isoperimetric form**: if every coordinate has influence
at most `δ` on a Boolean function read as signs `F`, then `Var[F] · log (1 / δ) ≤ 6 I[F]`, that
is, the total influence is at least `1/6 · Var[F] · log (1 / δ)` [KahnKalaiLinial1988]
[Talagrand1994]. This is a weaker form of the KKL Edge-Isoperimetric Theorem of
[O'Donnell, Section 9.6][ODonnell2014]. For `δ ≥ 1` the left side is at most zero. -/
theorem expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence (f : (ι → Bool) → Bool) {δ : ℝ}
    (hδ : ∀ i, influence i (fun x => signVal (f x)) ≤ δ) :
    (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * log δ⁻¹ ≤
      6 * totalInfluence (fun x => signVal (f x)) := by
  rw [← sum_sum_filter_mem_fourierCoeff_sq_div_card, sum_mul, totalInfluence, mul_sum]
  exact sum_le_sum fun i _ => sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le f i (hδ i)

/-- `log n ≤ 2 √n`. -/
private theorem log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : log x ≤ 2 * √x := by
  have h := log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [log_sqrt hx.le] at h
  linarith

/-- **The Kahn–Kalai–Linial theorem**: some coordinate has influence at least
`Var[F] · log n / (12 n)` on a Boolean function read as signs `F` of `n ≥ 1` coordinates
[KahnKalaiLinial1988] [O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_expect_sub_expect_sq_mul_log_card_div_le_influence [Nonempty ι]
    (f : (ι → Bool) → Bool) :
    ∃ i, (𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2) * log (Fintype.card ι) /
      (12 * Fintype.card ι) ≤ influence i (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set V := 𝔼 x, (F x - 𝔼 y, F y) ^ 2
  set n : ℝ := (Fintype.card ι : ℝ)
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun i => influence i F) univ_nonempty
  refine ⟨i, ?_⟩
  set δ := influence i F
  have hδ0 : 0 ≤ δ := influence_nonneg i F
  have hn : 1 ≤ n := Nat.one_le_cast.2 Fintype.card_pos
  have hn0 : 0 < n := by linarith
  have hV0 : 0 ≤ V := expect_nonneg fun _ _ => sq_nonneg _
  have hV1 : V ≤ 1 := expect_sub_expect_sq_signVal_le_one f
  have hI : totalInfluence F ≤ n * δ :=
    calc totalInfluence F ≤ ∑ _j : ι, δ := sum_le_sum fun j _ => hi j (mem_univ j)
      _ = n * δ := by rw [sum_const, card_univ, nsmul_eq_mul]
  have hlogn : 0 ≤ log n := log_nonneg hn
  rw [div_le_iff₀ (by positivity)]
  rcases le_or_gt 1 (δ * √n) with h | h
  · -- a large influence: `V log n ≤ 2 √n ≤ 2 n δ`
    have hsq : √n * √n = n := Real.mul_self_sqrt hn0.le
    calc V * log n ≤ 1 * (2 * √n) := mul_le_mul hV1 (log_le_two_mul_sqrt hn0) hlogn zero_le_one
      _ ≤ 2 * √n * (δ * √n) := by nlinarith [Real.sqrt_nonneg n]
      _ = 2 * n * δ := by rw [show 2 * √n * (δ * √n) = 2 * (√n * √n) * δ by ring, hsq]
      _ ≤ δ * (12 * n) := by nlinarith
  · -- small influences: `log (1 / δ) ≥ log n / 2`
    rcases hδ0.lt_or_eq with hδ | hδ
    · have hlog : log n / 2 ≤ log δ⁻¹ := by
        rw [← log_sqrt hn0.le]
        refine log_le_log (Real.sqrt_pos.2 hn0) ?_
        rw [le_inv_comm₀ (Real.sqrt_pos.2 hn0) hδ, ← one_div, le_div_iff₀ (Real.sqrt_pos.2 hn0)]
        exact h.le
      have hkkl :=
        expect_sub_expect_sq_mul_log_inv_le_six_mul_totalInfluence f fun j => hi j (mem_univ j)
      nlinarith
    · -- no influence at all: `V ≤ I ≤ n δ = 0`
      have := expect_sub_expect_sq_le_totalInfluence F
      rw [← hδ] at hI ⊢
      nlinarith

/-! ### Talagrand's inequality -/

/-- **Talagrand's inequality**: for a Boolean function read as signs `F` whose influences are all
less than one, `Var[F] ≤ 6 ∑ᵢ Infᵢ[F] / log (1 / Infᵢ[F])` [Talagrand1994]. A coordinate of
influence one contributes `+∞` in the usual reading of the inequality; for an unconditional form
see `expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log`. -/
theorem expect_sub_expect_sq_le_six_mul_sum_influence_div_log (f : (ι → Bool) → Bool)
    (hf : ∀ i, influence i (fun x => signVal (f x)) < 1) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤
      6 * ∑ i, influence i (fun x => signVal (f x)) /
        log (influence i fun x => signVal (f x))⁻¹ := by
  rw [← sum_sum_filter_mem_fourierCoeff_sq_div_card, mul_sum]
  refine sum_le_sum fun i _ => ?_
  set a := influence i fun x => signVal (f x)
  have ha : 0 ≤ a := influence_nonneg i _
  have h := sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le f i le_rfl
  rcases ha.lt_or_eq with ha | ha
  · have hL : 0 < log a⁻¹ := log_pos (one_lt_inv_iff₀.2 ⟨ha, hf i⟩)
    rw [mul_div_assoc', le_div_iff₀ hL]
    exact h
  · rw [← ha, zero_div, mul_zero]
    exact ha ▸ sum_filter_mem_fourierCoeff_sq_div_card_le_influence _ i

/-- **Talagrand's inequality, unconditional form**: for every Boolean function read as signs `F`,
`Var[F] ≤ 7 ∑ᵢ Infᵢ[F] / (1 + log (1 / Infᵢ[F]))` [Talagrand1994]. -/
theorem expect_sub_expect_sq_le_seven_mul_sum_influence_div_one_add_log (f : (ι → Bool) → Bool) :
    𝔼 x, (signVal (f x) - 𝔼 y, signVal (f y)) ^ 2 ≤
      7 * ∑ i, influence i (fun x => signVal (f x)) /
        (1 + log (influence i fun x => signVal (f x))⁻¹) := by
  rw [← sum_sum_filter_mem_fourierCoeff_sq_div_card, mul_sum]
  refine sum_le_sum fun i _ => ?_
  set a := influence i fun x => signVal (f x)
  have ha : 0 ≤ a := influence_nonneg i _
  have hL : 0 ≤ log a⁻¹ := by
    rw [log_inv]
    exact neg_nonneg.2 (log_nonpos ha (influence_signVal_le_one f i))
  have hW := sum_filter_mem_fourierCoeff_sq_div_card_le_influence (fun x => signVal (f x)) i
  have hWL := sum_filter_mem_fourierCoeff_sq_div_card_mul_log_le f i le_rfl
  rw [mul_div_assoc', le_div_iff₀ (by linarith)]
  linarith

end Cslib.BitString
