/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Choose

/-!
# Negligibility of dyadic bounds and `fun_prop` closure rules

Inverse powers of two `((2 : ℝ≥0) ^ n)⁻¹` and `(1 : ℝ≥0) / 2 ^ n`, polynomial numerators
`(p n : ℝ≥0) / 2 ^ n`, birthday-bound ratios `((p n).choose 2 : ℝ≥0) / 2 ^ n`, and reindexed
dyadic tails `(1 : ℝ≥0) / 2 ^ f n` with `n ≤ f n` are negligible. An entropy surplus of twice the
security parameter gives geometric decay after taking a square root.

This module also registers pointwise `fun_prop` closure rules for `Cslib.Crypto.Negligible` beyond
those in `CslibFrontier.Crypto.Negligible`: nonnegative polynomial factors
(`Cslib.Crypto.PolynomiallyBoundedNNReal`, covering constants, `ℕ` casts, sums, products, and fixed
powers), division by constants and reciprocal-negligible denominators, positive integer powers,
geometric decay, finite range sums, and parameter reindexing along
`Cslib.Crypto.PolynomiallyLowerBounded` schedules (shifts, positive multiples, and division by a
positive constant).

## Main definitions

* `Cslib.Crypto.PolynomiallyBoundedNNReal`: `ℝ≥0`-valued functions bounded pointwise by a
  `PolynomiallyBounded` natural function.
* `Cslib.Crypto.PolynomiallyLowerBounded`: parameter schedules `g : ℕ → ℕ` satisfying
  `n ≤ c * (g n + 1) ^ d`, along which `Negligible` is preserved under composition.

## Main results

* `Cslib.Crypto.negligible_inv_two_pow`, `Cslib.Crypto.negligible_one_div_two_pow`,
  `Cslib.Crypto.negligible_const_div_two_pow`: dyadic base bounds.
* `Cslib.Crypto.negligible_inv_two_pow_of_eventually_le`,
  `Cslib.Crypto.negligible_inv_two_pow_of_le`,
  `Cslib.Crypto.negligible_inv_two_pow_comp_of_le`: reindexed dyadic bounds when `n ≤ f n`.
* `Cslib.PolynomiallyBounded.negligible_mul_inv_two_pow`,
  `Cslib.PolynomiallyBounded.negligible_div_two_pow`,
  `Cslib.PolynomiallyBounded.negligible_choose_two_mul_inv_two_pow`,
  `Cslib.PolynomiallyBounded.negligible_choose_two_div_two_pow`: polynomial and birthday numerators
  over `2 ^ n`.
* `Cslib.Crypto.Negligible.polynomiallyBoundedNNReal_mul`,
  `Cslib.Crypto.Negligible.mul_polynomiallyBoundedNNReal`,
  `Cslib.Crypto.Negligible.polynomiallyBoundedNNReal_div`,
  `Cslib.Crypto.Negligible.const_mul`, `Cslib.Crypto.Negligible.mul_const`,
  `Cslib.Crypto.Negligible.div_const_right`, `Cslib.Crypto.Negligible.mul_polynomiallyBounded`,
  `Cslib.Crypto.Negligible.polynomiallyBounded_div`, `Cslib.Crypto.Negligible.div_of_inv`,
  `Cslib.Crypto.Negligible.const_div`, `Cslib.Crypto.Negligible.inv_mul_left`,
  `Cslib.Crypto.Negligible.inv_mul_right`, `Cslib.Crypto.Negligible.inv_pow_add_const`,
  `Cslib.Crypto.Negligible.pow`, `Cslib.Crypto.Negligible.comp_polynomiallyLowerBounded`,
  `Cslib.Crypto.Negligible.shift_left`, `Cslib.Crypto.Negligible.mul_param_left`,
  `Cslib.Crypto.Negligible.mul_param_right`, `Cslib.Crypto.Negligible.sum_range_const`,
  `Cslib.Crypto.Negligible.sum_range_of_le`: pointwise closure rules for `Negligible`.
* `Cslib.Crypto.negligible_of_coe_le`, `Cslib.Crypto.negligible_of_eventually_coe_le`: comparison
  against real-valued upper bounds via `Real.toNNReal`.
* `Cslib.Crypto.sqrt_pow_two_div_pow_two_le`,
  `Cslib.Crypto.negligible_mul_sqrt_pow_two_div_pow_two`: square-root dyadic entropy estimates.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

attribute [fun_prop] negligible_geometric

/-! ### Polynomially bounded `ℝ≥0` factors -/

/-- A nonnegative real-valued function `P : ℕ → ℝ≥0` is polynomially bounded when it is dominated
pointwise by a `PolynomiallyBounded` natural function. Multiplying a negligible function by such a
factor preserves negligibility without requiring casts to be pulled to a single `Nat.cast` head. -/
@[fun_prop]
def PolynomiallyBoundedNNReal (P : ℕ → ℝ≥0) : Prop :=
  ∃ p : ℕ → ℕ, PolynomiallyBounded p ∧ ∀ n, P n ≤ p n

namespace PolynomiallyBoundedNNReal

variable {P Q : ℕ → ℝ≥0}

/-- Nonnegative constants are polynomially bounded. -/
@[fun_prop]
protected theorem const (c : ℝ≥0) : PolynomiallyBoundedNNReal (fun _ => c) := by
  obtain ⟨m, hm⟩ := exists_nat_ge c
  exact ⟨fun _ => m, .const m, fun _ => hm⟩

/-- Natural-cast polynomially bounded functions are polynomially bounded in `ℝ≥0`. -/
@[fun_prop]
protected theorem natCast {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    PolynomiallyBoundedNNReal (fun n => (p n : ℝ≥0)) :=
  ⟨p, hp, fun _ => le_rfl⟩

/-- Sums of polynomially bounded `ℝ≥0` functions are polynomially bounded. -/
@[fun_prop]
protected theorem add (hP : PolynomiallyBoundedNNReal P) (hQ : PolynomiallyBoundedNNReal Q) :
    PolynomiallyBoundedNNReal (fun n => P n + Q n) := by
  obtain ⟨p, hp, hPle⟩ := hP
  obtain ⟨q, hq, hQle⟩ := hQ
  refine ⟨fun n => p n + q n, hp.add hq, fun n => ?_⟩
  rw [Nat.cast_add]
  exact add_le_add (hPle n) (hQle n)

/-- Products of polynomially bounded `ℝ≥0` functions are polynomially bounded. -/
@[fun_prop]
protected theorem mul (hP : PolynomiallyBoundedNNReal P) (hQ : PolynomiallyBoundedNNReal Q) :
    PolynomiallyBoundedNNReal (fun n => P n * Q n) := by
  obtain ⟨p, hp, hPle⟩ := hP
  obtain ⟨q, hq, hQle⟩ := hQ
  refine ⟨fun n => p n * q n, hp.mul hq, fun n => ?_⟩
  rw [Nat.cast_mul]
  exact mul_le_mul' (hPle n) (hQle n)

/-- Fixed powers of polynomially bounded `ℝ≥0` functions are polynomially bounded. -/
@[fun_prop]
protected theorem pow (hP : PolynomiallyBoundedNNReal P) (d : ℕ) :
    PolynomiallyBoundedNNReal (fun n => P n ^ d) := by
  obtain ⟨p, hp, hPle⟩ := hP
  refine ⟨fun n => p n ^ d, hp.pow d, fun n => ?_⟩
  rw [Nat.cast_pow]
  exact pow_le_pow_left' (hPle n) d

/-- Dividing by a nonnegative constant preserves a polynomial bound in `ℝ≥0`. -/
@[fun_prop]
protected theorem div_const (hP : PolynomiallyBoundedNNReal P) (c : ℝ≥0) :
    PolynomiallyBoundedNNReal (fun n => P n / c) := by
  simpa only [div_eq_mul_inv] using hP.mul (.const c⁻¹)

/-- Reindexing along a polynomially bounded natural function preserves a polynomial bound in
`ℝ≥0`. -/
@[fun_prop]
protected theorem comp_polynomiallyBounded (hP : PolynomiallyBoundedNNReal P) {g : ℕ → ℕ}
    (hg : PolynomiallyBounded g) :
    PolynomiallyBoundedNNReal (fun n => P (g n)) := by
  obtain ⟨p, hp, hPle⟩ := hP
  exact ⟨fun n => p (g n), hp.comp hg, fun n => hPle (g n)⟩

end PolynomiallyBoundedNNReal

/-! ### Polynomially lower-bounded parameter schedules -/

/-- A parameter schedule `g : ℕ → ℕ` is polynomially lower-bounded when `n` is bounded by a
polynomial in `g n`. Composing a negligible function on the right with such a schedule preserves
negligibility. -/
@[fun_prop]
def PolynomiallyLowerBounded (g : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, n ≤ c * (g n + 1) ^ d

namespace PolynomiallyLowerBounded

variable {f g : ℕ → ℕ}

/-- A polynomially lower-bounded schedule tends to infinity. -/
theorem tendsto_atTop (hg : PolynomiallyLowerBounded g) :
    Filter.Tendsto g Filter.atTop Filter.atTop := by
  obtain ⟨c, d, hg⟩ := hg
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨c * b ^ d + 1, fun n hn => ?_⟩
  by_contra! hlt
  have hle : c * (g n + 1) ^ d ≤ c * b ^ d :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left hlt d)
  have := (hg n).trans hle
  omega

/-- Pointwise larger schedules remain polynomially lower-bounded. -/
theorem mono_of_le (hg : PolynomiallyLowerBounded g) (hle : ∀ n, g n ≤ f n) :
    PolynomiallyLowerBounded f := by
  obtain ⟨c, d, hg⟩ := hg
  refine ⟨c, d, fun n => (hg n).trans ?_⟩
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right (hle n) 1) d)

/-- The identity parameter is polynomially lower-bounded. -/
@[fun_prop]
protected theorem id : PolynomiallyLowerBounded (fun n => n) :=
  ⟨1, 1, fun n => by simp⟩

/-- Adding any nonnegative offset on the right preserves a polynomial lower bound. -/
@[fun_prop]
protected theorem add_right (hg : PolynomiallyLowerBounded g) (f : ℕ → ℕ) :
    PolynomiallyLowerBounded (fun n => g n + f n) :=
  hg.mono_of_le fun n => Nat.le_add_right (g n) (f n)

/-- Adding any nonnegative offset on the left preserves a polynomial lower bound. -/
@[fun_prop]
protected theorem add_left (f : ℕ → ℕ) (hg : PolynomiallyLowerBounded g) :
    PolynomiallyLowerBounded (fun n => f n + g n) :=
  hg.mono_of_le fun n => Nat.le_add_left (g n) (f n)

/-- Multiplying on the left by a positive natural preserves a polynomial lower bound. -/
@[fun_prop]
protected theorem mul_left {c : ℕ} (hc : 0 < c) (hg : PolynomiallyLowerBounded g) :
    PolynomiallyLowerBounded (fun n => c * g n) :=
  hg.mono_of_le fun n => Nat.le_mul_of_pos_left (g n) hc

/-- Multiplying on the right by a positive natural preserves a polynomial lower bound. -/
@[fun_prop]
protected theorem mul_right (hg : PolynomiallyLowerBounded g) {c : ℕ} (hc : 0 < c) :
    PolynomiallyLowerBounded (fun n => g n * c) :=
  hg.mono_of_le fun n => Nat.le_mul_of_pos_right (g n) hc

/-- Dividing by a positive natural constant preserves a polynomial lower bound. -/
@[fun_prop]
protected theorem div_const (hg : PolynomiallyLowerBounded g) {c : ℕ} (hc : 0 < c) :
    PolynomiallyLowerBounded (fun n => g n / c) := by
  obtain ⟨a, d, hg⟩ := hg
  refine ⟨a * c ^ d, d, fun n => ?_⟩
  have hstep : g n + 1 ≤ c * (g n / c + 1) := by
    have := Nat.mod_lt (g n) hc
    have := Nat.div_add_mod (g n) c
    nlinarith
  calc
    n ≤ a * (g n + 1) ^ d := hg n
    _ ≤ a * (c * (g n / c + 1)) ^ d := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hstep d)
    _ = a * c ^ d * (g n / c + 1) ^ d := by rw [Nat.mul_pow, Nat.mul_assoc]

/-- Positive powers preserve a polynomial lower bound. -/
@[fun_prop]
protected theorem pow (hg : PolynomiallyLowerBounded g) {k : ℕ} (hk : 0 < k) :
    PolynomiallyLowerBounded (fun n => g n ^ k) :=
  hg.mono_of_le fun n => Nat.le_self_pow hk.ne' (g n)

/-- Compositions of polynomially lower-bounded schedules are polynomially lower-bounded. -/
@[fun_prop]
protected theorem comp (hf : PolynomiallyLowerBounded f) (hg : PolynomiallyLowerBounded g) :
    PolynomiallyLowerBounded (fun n => f (g n)) := by
  obtain ⟨c₁, d₁, hf⟩ := hf
  obtain ⟨c₂, d₂, hg⟩ := hg
  refine ⟨c₂ * (c₁ + 1) ^ d₂, d₁ * d₂, fun n => ?_⟩
  have hinner : g n + 1 ≤ (c₁ + 1) * (f (g n) + 1) ^ d₁ := by
    have hp : 1 ≤ (f (g n) + 1) ^ d₁ := Nat.one_le_pow _ _ (Nat.succ_pos _)
    calc
      g n + 1 ≤ c₁ * (f (g n) + 1) ^ d₁ + (f (g n) + 1) ^ d₁ := Nat.add_le_add (hf (g n)) hp
      _ = (c₁ + 1) * (f (g n) + 1) ^ d₁ := by ring
  calc
    n ≤ c₂ * (g n + 1) ^ d₂ := hg n
    _ ≤ c₂ * ((c₁ + 1) * (f (g n) + 1) ^ d₁) ^ d₂ :=
      Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left hinner d₂)
    _ = c₂ * (c₁ + 1) ^ d₂ * (f (g n) + 1) ^ (d₁ * d₂) := by
      rw [Nat.mul_pow, Nat.pow_mul, Nat.mul_assoc]

end PolynomiallyLowerBounded

/-! ### Pointwise algebraic and parameter closure rules -/

/-- Reindexing a negligible bound along a polynomially lower-bounded schedule preserves
negligibility. -/
@[fun_prop]
theorem Negligible.comp_polynomiallyLowerBounded {ε : ℕ → ℝ≥0} {g : ℕ → ℕ}
    (hε : Negligible ε) (hg : PolynomiallyLowerBounded g) :
    Negligible (fun n => ε (g n)) := by
  obtain ⟨c, d, hle⟩ := hg
  exact hε.comp_of_polynomial_bound (bound := fun m => c * (m + 1) ^ d)
    (PolynomiallyLowerBounded.tendsto_atTop ⟨c, d, hle⟩) (by fun_prop)
    (Filter.Eventually.of_forall hle)

/-- Multiplying a negligible bound on the left by a polynomially bounded `ℝ≥0` factor preserves
negligibility. -/
@[fun_prop]
theorem Negligible.polynomiallyBoundedNNReal_mul {P ε : ℕ → ℝ≥0}
    (hP : PolynomiallyBoundedNNReal P) (hε : Negligible ε) :
    Negligible (fun n => P n * ε n) := by
  obtain ⟨p, hp, hPle⟩ := hP
  exact negligible_of_le (hε.polynomiallyBounded_mul hp) fun n =>
    mul_le_mul_of_nonneg_right (hPle n) zero_le

/-- Multiplying a negligible bound on the right by a polynomially bounded `ℝ≥0` factor preserves
negligibility. -/
@[fun_prop]
theorem Negligible.mul_polynomiallyBoundedNNReal {ε P : ℕ → ℝ≥0}
    (hε : Negligible ε) (hP : PolynomiallyBoundedNNReal P) :
    Negligible (fun n => ε n * P n) := by
  simpa only [mul_comm] using hε.polynomiallyBoundedNNReal_mul hP

/-- A polynomially bounded `ℝ≥0` numerator over a denominator with negligible reciprocal is
negligible. -/
@[fun_prop]
theorem Negligible.polynomiallyBoundedNNReal_div {P δ : ℕ → ℝ≥0}
    (hP : PolynomiallyBoundedNNReal P) (hδ : Negligible (fun n => (δ n)⁻¹)) :
    Negligible (fun n => P n / δ n) := by
  simpa only [div_eq_mul_inv] using hδ.polynomiallyBoundedNNReal_mul hP

/-- Multiplying a negligible bound on the left by a nonnegative constant preserves negligibility. -/
theorem Negligible.const_mul {ε : ℕ → ℝ≥0} (hε : Negligible ε) (c : ℝ≥0) :
    Negligible (fun n => c * ε n) :=
  hε.polynomiallyBoundedNNReal_mul (.const c)

/-- Multiplying a negligible bound on the right by a nonnegative constant preserves
negligibility. -/
theorem Negligible.mul_const {ε : ℕ → ℝ≥0} (hε : Negligible ε) (c : ℝ≥0) :
    Negligible (fun n => ε n * c) :=
  hε.mul_polynomiallyBoundedNNReal (.const c)

/-- Dividing a negligible bound by a nonnegative constant preserves negligibility. -/
@[fun_prop]
theorem Negligible.div_const_right {ε : ℕ → ℝ≥0} (hε : Negligible ε) (c : ℝ≥0) :
    Negligible (fun n => ε n / c) := by
  simpa only [div_eq_mul_inv] using hε.mul_const c⁻¹

/-- Multiplying a negligible bound on the right by a polynomially bounded factor preserves
negligibility. -/
theorem Negligible.mul_polynomiallyBounded {ε : ℕ → ℝ≥0} {p : ℕ → ℕ}
    (hε : Negligible ε) (hp : PolynomiallyBounded p) :
    Negligible (fun n => ε n * (p n : ℝ≥0)) :=
  hε.mul_polynomiallyBoundedNNReal (.natCast hp)

/-- Dividing a negligible bound by a function whose reciprocal is negligible preserves
negligibility. -/
@[fun_prop]
theorem Negligible.div_of_inv {ε δ : ℕ → ℝ≥0}
    (hε : Negligible ε) (hδ : Negligible (fun n => (δ n)⁻¹)) :
    Negligible (fun n => ε n / δ n) := by
  simpa only [div_eq_mul_inv] using hε.mul_fun hδ

/-- A polynomially bounded numerator over a denominator with negligible reciprocal is negligible. -/
theorem Negligible.polynomiallyBounded_div {p : ℕ → ℕ} {δ : ℕ → ℝ≥0}
    (hp : PolynomiallyBounded p) (hδ : Negligible (fun n => (δ n)⁻¹)) :
    Negligible (fun n => (p n : ℝ≥0) / δ n) :=
  Negligible.polynomiallyBoundedNNReal_div (.natCast hp) hδ

/-- A nonnegative constant over a denominator with negligible reciprocal is negligible. -/
theorem Negligible.const_div (c : ℝ≥0) {δ : ℕ → ℝ≥0}
    (hδ : Negligible (fun n => (δ n)⁻¹)) :
    Negligible (fun n => c / δ n) :=
  Negligible.polynomiallyBoundedNNReal_div (.const c) hδ

/-- Scaling inside a reciprocal on the left preserves negligibility. -/
theorem Negligible.inv_mul_left (c : ℝ≥0) {δ : ℕ → ℝ≥0}
    (hδ : Negligible (fun n => (δ n)⁻¹)) :
    Negligible (fun n => (c * δ n)⁻¹) := by
  simpa only [mul_inv] using hδ.const_mul c⁻¹

/-- Scaling inside a reciprocal on the right preserves negligibility. -/
theorem Negligible.inv_mul_right {δ : ℕ → ℝ≥0}
    (hδ : Negligible (fun n => (δ n)⁻¹)) (c : ℝ≥0) :
    Negligible (fun n => (δ n * c)⁻¹) := by
  simpa only [mul_comm] using Negligible.inv_mul_left c hδ

/-- Adding a fixed constant to the exponent of a reciprocal power preserves negligibility. -/
theorem Negligible.inv_pow_add_const {b : ℝ≥0} {f : ℕ → ℕ} (c : ℕ)
    (hf : Negligible (fun n => (b ^ f n)⁻¹)) :
    Negligible (fun n => (b ^ (f n + c))⁻¹) := by
  simpa only [pow_add, mul_inv] using hf.mul_const ((b ^ c)⁻¹)

/-- Positive integer powers preserve negligible decay. -/
@[fun_prop]
theorem Negligible.pow {ε : ℕ → ℝ≥0} (hε : Negligible ε) {k : ℕ} (hk : 0 < k) :
    Negligible (fun n => ε n ^ k) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  clear hk
  induction m with
  | zero => simpa only [pow_one] using hε
  | succ m ih => simpa only [pow_succ] using ih.mul_fun hε

/-- Shifting the security parameter by a left-hand additive constant preserves negligibility. -/
theorem Negligible.shift_left {ε : ℕ → ℝ≥0} (hε : Negligible ε) (c : ℕ) :
    Negligible (fun n => ε (c + n)) :=
  hε.comp_polynomiallyLowerBounded (.add_left _ .id)

/-- Scaling the security parameter on the left by a positive natural preserves negligibility. -/
theorem Negligible.mul_param_left {ε : ℕ → ℝ≥0} (hε : Negligible ε) {c : ℕ} (hc : 0 < c) :
    Negligible (fun n => ε (c * n)) :=
  hε.comp_polynomiallyLowerBounded (.mul_left hc .id)

/-- Scaling the security parameter on the right by a positive natural preserves negligibility. -/
theorem Negligible.mul_param_right {ε : ℕ → ℝ≥0} (hε : Negligible ε) {c : ℕ} (hc : 0 < c) :
    Negligible (fun n => ε (n * c)) :=
  hε.comp_polynomiallyLowerBounded (.mul_right .id hc)

/-- Summing a uniform negligible bound over a polynomially bounded `Finset.range` preserves
negligibility. -/
@[fun_prop]
theorem Negligible.sum_range_const {p : ℕ → ℕ} {ε : ℕ → ℝ≥0}
    (hp : PolynomiallyBounded p) (hε : Negligible ε) :
    Negligible (fun n => ∑ _i ∈ Finset.range (p n), ε n) := by
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
    hε.polynomiallyBounded_mul hp

/-- Summing indexed terms uniformly bounded by a negligible function over `Finset.range (p n)` is
negligible when `p` is polynomially bounded. -/
theorem Negligible.sum_range_of_le {p : ℕ → ℕ} {g : ℕ → ℕ → ℝ≥0} {ε : ℕ → ℝ≥0}
    (hp : PolynomiallyBounded p) (hε : Negligible ε)
    (hle : ∀ n, ∀ i < p n, g n i ≤ ε n) :
    Negligible (fun n => ∑ i ∈ Finset.range (p n), g n i) := by
  refine negligible_of_le (hε.polynomiallyBounded_mul hp) fun n => ?_
  calc
    ∑ i ∈ Finset.range (p n), g n i
      ≤ ∑ _i ∈ Finset.range (p n), ε n :=
        Finset.sum_le_sum fun i hi => hle n i (Finset.mem_range.mp hi)
    _ = (p n : ℝ≥0) * ε n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### Dyadic and birthday bounds -/

open Filter in
/-- Reindexing `(1 : ℝ≥0) / 2 ^ f n` along any schedule eventually satisfying `n ≤ f n` is
negligible. -/
theorem negligible_inv_two_pow_of_eventually_le {f : ℕ → ℕ} (h : ∀ᶠ n in atTop, n ≤ f n) :
    Negligible (fun n => (1 : ℝ≥0) / 2 ^ f n) := by
  refine negligible_of_eventually_le (negligible_geometric (ratio := 2⁻¹) (by norm_num)) ?_
  filter_upwards [h] with n hn
  rw [one_div, inv_pow]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hn)

/-- Any schedule satisfying `n ≤ f n` makes `(1 : ℝ≥0) / 2 ^ f n` negligible. -/
theorem negligible_inv_two_pow_of_le {f : ℕ → ℕ} (h : ∀ n, n ≤ f n) :
    Negligible (fun n => (1 : ℝ≥0) / 2 ^ f n) :=
  negligible_inv_two_pow_of_eventually_le (Filter.Eventually.of_forall h)

/-- Any schedule satisfying `n ≤ f n` makes `((2 : ℝ≥0) ^ f n)⁻¹` negligible. -/
theorem negligible_inv_two_pow_comp_of_le {f : ℕ → ℕ} (h : ∀ n, n ≤ f n) :
    Negligible (fun n => ((2 : ℝ≥0) ^ f n)⁻¹) := by
  simpa only [one_div] using negligible_inv_two_pow_of_le h

/-- The inverse power of two `((2 : ℝ≥0) ^ n)⁻¹` is negligible. -/
@[fun_prop]
theorem negligible_inv_two_pow : Negligible (fun n => ((2 : ℝ≥0) ^ n)⁻¹) :=
  negligible_inv_two_pow_comp_of_le fun _ => le_rfl

/-- The dyadic unit fraction `(1 : ℝ≥0) / 2 ^ n` is negligible. -/
@[fun_prop]
theorem negligible_one_div_two_pow : Negligible (fun n => (1 : ℝ≥0) / 2 ^ n) :=
  negligible_inv_two_pow_of_le fun _ => le_rfl

/-- A constant natural numerator over `2 ^ n` is negligible. -/
theorem negligible_const_div_two_pow (c : ℕ) :
    Negligible (fun n => (c : ℝ≥0) / 2 ^ n) :=
  Negligible.polynomiallyBounded_div (.const c) negligible_inv_two_pow

/-! ### Real-valued upper bounds -/

/-- A nonnegative function bounded pointwise in `ℝ` by `B n` is negligible when `Real.toNNReal ∘ B`
is negligible. -/
theorem negligible_of_coe_le {ε : ℕ → ℝ≥0} {B : ℕ → ℝ}
    (hB : Negligible (fun n => Real.toNNReal (B n))) (hle : ∀ n, (ε n : ℝ) ≤ B n) :
    Negligible ε :=
  negligible_of_le hB fun n => Real.toNNReal_coe (r := ε n) ▸ Real.toNNReal_mono (hle n)

open Filter in
/-- A nonnegative function eventually bounded in `ℝ` by `B n` is negligible when
`Real.toNNReal ∘ B` is negligible. -/
theorem negligible_of_eventually_coe_le {ε : ℕ → ℝ≥0} {B : ℕ → ℝ}
    (hB : Negligible (fun n => Real.toNNReal (B n)))
    (hle : ∀ᶠ n in atTop, (ε n : ℝ) ≤ B n) :
    Negligible ε :=
  negligible_of_eventually_le hB
    (hle.mono fun n hn => Real.toNNReal_coe (r := ε n) ▸ Real.toNNReal_mono hn)

/-! ### Square-root entropy estimates -/

/-- Twice the security parameter in surplus bits bounds the square-root ratio by `2⁻ⁿ`. -/
theorem sqrt_pow_two_div_pow_two_le {outputBits sourceBits n : ℕ}
    (hmargin : outputBits + 2 * n ≤ sourceBits) :
    NNReal.sqrt ((2 : ℝ≥0) ^ outputBits / 2 ^ sourceBits) ≤ (1 / 2 : ℝ≥0) ^ n := by
  rw [NNReal.sqrt_le_iff_le_sq]
  calc
    _ ≤ (2 : ℝ≥0) ^ outputBits / 2 ^ (outputBits + 2 * n) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ (by norm_num) hmargin)
    _ = _ := by
      rw [pow_add, mul_comm 2 n, pow_mul]
      simp only [one_div, inv_pow]
      field_simp

open Filter in
/-- A polynomial number of square-root dyadic errors is negligible under an eventual entropy
surplus of twice the security parameter. -/
theorem negligible_mul_sqrt_pow_two_div_pow_two
    {count outputBits sourceBits : ℕ → ℕ} (hcount : PolynomiallyBounded count)
    (hmargin : ∀ᶠ n in atTop, outputBits n + 2 * n ≤ sourceBits n) :
    Negligible (fun n => (count n : ℝ≥0) *
      NNReal.sqrt ((2 : ℝ≥0) ^ outputBits n / 2 ^ sourceBits n)) := by
  apply negligible_of_eventually_le
    ((negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).polynomiallyBounded_mul
      hcount)
  filter_upwards [hmargin] with n hn
  exact mul_le_mul' le_rfl (sqrt_pow_two_div_pow_two_le hn)

end Cslib.Crypto

namespace Cslib.PolynomiallyBounded

open scoped NNReal
open Cslib.Crypto

/-- A polynomially bounded factor times `((2 : ℝ≥0) ^ n)⁻¹` is negligible. -/
theorem negligible_mul_inv_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0) * ((2 : ℝ≥0) ^ n)⁻¹) :=
  negligible_inv_two_pow.polynomiallyBounded_mul hp

/-- A polynomially bounded numerator over `2 ^ n` is negligible. -/
theorem negligible_div_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    Negligible (fun n => (p n : ℝ≥0) / 2 ^ n) :=
  Negligible.polynomiallyBounded_div hp negligible_inv_two_pow

/-- A birthday pair count `(p n).choose 2` times `((2 : ℝ≥0) ^ n)⁻¹` is negligible when `p` is
polynomially bounded. -/
theorem negligible_choose_two_mul_inv_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    Negligible (fun n => ((p n).choose 2 : ℝ≥0) * ((2 : ℝ≥0) ^ n)⁻¹) :=
  hp.choose_two.negligible_mul_inv_two_pow

/-- A birthday pair count `(p n).choose 2` over `2 ^ n` is negligible when `p` is polynomially
bounded. -/
theorem negligible_choose_two_div_two_pow {p : ℕ → ℕ} (hp : PolynomiallyBounded p) :
    Negligible (fun n => ((p n).choose 2 : ℝ≥0) / 2 ^ n) :=
  hp.choose_two.negligible_div_two_pow

end Cslib.PolynomiallyBounded
