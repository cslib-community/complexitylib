/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.SupportBound
public import Mathlib.Analysis.Asymptotics.Defs
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

/-!
# Asymptotic lower bounds for bounded direct input support

The random-cut estimate gives a coefficient `1 / (2 * (1 - 2⁻ᵈ))` for input-reading gates
whose aggregated support on original inputs has size at most the fixed positive integer `d`.
The two Boolean fibers must be rectangle-free at a threshold with sublinear binary logarithm.
Internal predecessor fan-in, depth, fan-out, and real weights remain unrestricted.

For `d = 3`, incidence layouts improve the coefficient to `2 / 3`. The separate
support-at-most-two theorem gives the stronger coefficient `1` when `d = 2`.

This follows from the finite support bound. It does not construct an explicit family with the
required rectangle-freeness property.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.eventually_lt_inputGates_of_inputSupport_card_le`:
  the asymptotic bound for native programs and any fixed Boolean readout of their gate values.
* `Cslib.Circuits.Boolean.WeightedThreshold.eventually_lt_inputGates_of_inputSupport_card_le_three`:
  the coefficient `2 / 3` for direct support of size at most three.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Filter Asymptotics

private theorem eventually_mul_sqrt_le (T : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (T + 1 : ℝ) * Real.sqrt (2 * n) ≤ δ * n := by
  filter_upwards [eventually_ge_atTop ⌈2 * (T + 1 : ℝ) ^ 2 / δ ^ 2⌉₊] with n hn
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound : 2 * (T + 1 : ℝ) ^ 2 ≤ δ ^ 2 * n := by
    have hceil := (Nat.le_ceil (2 * (T + 1 : ℝ) ^ 2 / δ ^ 2)).trans
      (show (⌈2 * (T + 1 : ℝ) ^ 2 / δ ^ 2⌉₊ : ℝ) ≤ n by exact_mod_cast hn)
    have h := (div_le_iff₀ (sq_pos_of_pos hδ)).mp hceil
    nlinarith
  apply (sq_le_sq₀ (by positivity : 0 ≤ (T + 1 : ℝ) * Real.sqrt (2 * n))
    (mul_nonneg hδ.le hN)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), mul_pow]
  nlinarith [mul_le_mul_of_nonneg_right hbound hN]

private theorem eventually_lt_of_support_bounds {a : ℝ} (ha : 0 < a) (d : ℕ)
    {k : ℕ → ℕ} (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 0 < T ∧ ∀ᶠ n : ℕ in atTop, ∀ q : ℝ, 0 ≤ q →
      (n : ℝ) ≤ (a + d / T) * q + 2 * k n + (T + 1 : ℝ) * Real.sqrt (2 * n) →
      (1 / a - ε) * n < q := by
  let δ := a * ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨T, hT⟩ := exists_nat_gt ((d : ℝ) / (a * δ))
  have hTpos : (0 : ℝ) < T := lt_of_le_of_lt (by positivity) hT
  have hTnat : 0 < T := by exact_mod_cast hTpos
  have hcoeff : (d : ℝ) / T * (1 / a) ≤ δ := by
    have h := (div_lt_iff₀ (mul_pos ha hδ)).mp hT
    rw [show (d : ℝ) / T * (1 / a) = d / (T * a) by ring]
    apply (div_le_iff₀ (mul_pos hTpos ha)).mpr
    nlinarith
  refine ⟨T, hTnat, ?_⟩
  filter_upwards [hk.bound (half_pos hδ), eventually_mul_sqrt_le T hδ,
    eventually_ge_atTop 1] with n hnK hnRoot hn1
  intro q hq hbound
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hNpos : (0 : ℝ) < n := by exact_mod_cast hn1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (k n) : (0 : ℝ) ≤ k n),
    abs_of_nonneg hN] at hnK
  by_contra! hsmall
  have hqbound : q ≤ 1 / a * n := by nlinarith [mul_nonneg hε.le hN]
  have herror : (d : ℝ) / T * q ≤ δ * n := by
    calc
      (d : ℝ) / T * q ≤ (d / T) * (1 / a * n) := by gcongr
      _ = (d / T * (1 / a)) * n := by ring
      _ ≤ δ * n := mul_le_mul_of_nonneg_right hcoeff hN
  have hmain : a * q ≤ n - a * ε * n := by
    have h := mul_le_mul_of_nonneg_left hsmall ha.le
    have heq : a * ((1 / a - ε) * n) = n - a * ε * n := by
      field_simp
    rwa [heq] at h
  have hδeq : 4 * δ = a * ε := by dsimp [δ]; ring
  have hδn := congrArg (fun z : ℝ => z * n) hδeq
  have hpos := mul_pos (mul_pos ha hε) hNpos
  nlinarith

private theorem eventually_lt_of_three_support_bounds {k : ℕ → ℕ}
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∃ T : ℕ, ∀ᶠ n : ℕ in atTop, ∀ q : ℕ,
      2 * (n : ℝ) < (3 + 6 / (T + 1 : ℝ)) * q +
        (max 3 T : ℕ) * (Nat.log 2 (n + q) : ℝ) + 6 * k n + C →
      (2 / 3 - ε) * n < q := by
  obtain ⟨T, hT⟩ := exists_nat_gt ((6 : ℝ) / ε)
  have hcoeff : (6 : ℝ) / (T + 1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < T + 1)).mpr
    have h := (div_lt_iff₀ hε).mp hT
    nlinarith
  let D : ℝ := (max 3 T : ℕ)
  obtain ⟨m, hm⟩ := exists_nat_gt (4 * D / ε)
  have hDm : D ≤ (ε / 4) * m := by
    have h := (div_lt_iff₀ hε).mp hm
    linarith
  let B : ℝ := (ε / 4) * (m * m : ℕ)
  refine ⟨T, ?_⟩
  filter_upwards [hk.bound (show 0 < ε / 6 by positivity),
    eventually_ge_atTop ⌈2 * (B + C) / ε⌉₊] with n hnK hn
  intro q hbound
  have hN : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (k n) : (0 : ℝ) ≤ k n),
    abs_of_nonneg hN] at hnK
  by_contra! hsmall
  have hqn : (q : ℝ) ≤ n := by nlinarith [mul_nonneg hε.le hN]
  have herror : (6 : ℝ) / (T + 1) * q ≤ ε * n := by
    calc
      _ ≤ ((6 : ℝ) / (T + 1)) * n := mul_le_mul_of_nonneg_left hqn (by positivity)
      _ ≤ ε * n := mul_le_mul_of_nonneg_right hcoeff hN
  have hconstant : B + C ≤ ε / 2 * n := by
    have hceil := (Nat.le_ceil (2 * (B + C) / ε)).trans
      (show (⌈2 * (B + C) / ε⌉₊ : ℝ) ≤ n by exact_mod_cast hn)
    have h := (div_le_iff₀ hε).mp hceil
    linarith
  have hlog : D * (Nat.log 2 (n + q) : ℝ) + C ≤ ε * n := by
    have hmlog : (m : ℝ) * Nat.log 2 (n + q) ≤ (n : ℝ) + q + (m * m : ℕ) := by
      exact_mod_cast Nat.mul_log_le_add_sq Nat.one_lt_two m (n + q)
    have hDlog : D * (Nat.log 2 (n + q) : ℝ) ≤ (ε / 4) * (2 * (n : ℝ) + (m * m : ℕ)) :=
      calc D * (Nat.log 2 (n + q) : ℝ)
          ≤ ((ε / 4) * m) * (Nat.log 2 (n + q) : ℝ) :=
            mul_le_mul_of_nonneg_right hDm (Nat.cast_nonneg _)
        _ = (ε / 4) * ((m : ℝ) * Nat.log 2 (n + q)) := mul_assoc _ _ _
        _ ≤ (ε / 4) * ((n : ℝ) + q + (m * m : ℕ)) :=
            mul_le_mul_of_nonneg_left hmlog (by positivity)
        _ ≤ (ε / 4) * (2 * (n : ℝ) + (m * m : ℕ)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    dsimp only [B] at hconstant
    linarith
  dsimp only [D] at hlog
  nlinarith

/-- A family with both fibers `K(n)`-rectangle-free, with `K(n) ≤ 2 ^ k(n)` and `k(n) = o(n)`,
requires more than `(1 / (2 * (1 - 2⁻ᵈ)) - ε) n` input-reading gates for every `ε > 0` and all
sufficiently large `n`, when each gate directly reads at most `d > 0` original inputs.

The readout may be any Boolean function of the gate values. Internal predecessor fan-in,
depth, fan-out, and real coefficients are unrestricted. -/
theorem eventually_lt_inputGates_of_inputSupport_card_le {d : ℕ} (hd : 0 < d)
    {f : ∀ n, Cslib.BooleanFunction n} {K k : ℕ → ℕ}
    (hf : ∀ᶠ n in atTop, ∀ b : Bool, Frontier.RectangleFree {x | f n x = b} (K n))
    (hK : ∀ᶠ n in atTop, K n ≤ 2 ^ k n)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (g : ℕ) (p : Program signature n g)
      (readout : (Fin g → Bool) → Bool),
      (∀ x, readout (p.eval interpretation x) = f n x) →
      (∀ gate, (inputSupport p gate).card ≤ d) →
      (1 / (2 * (1 - (1 / 2 : ℝ) ^ d)) - ε) * n < (inputGates p).card := by
  have hpow : (1 / 2 : ℝ) ^ d < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (Nat.ne_zero_of_lt hd)
  have ha : 0 < 2 * (1 - (1 / 2 : ℝ) ^ d) := by linarith
  obtain ⟨T, hT, hnum⟩ := eventually_lt_of_support_bounds ha d hk hε
  filter_upwards [hf, hK, hnum] with n hfn hKn hn
  intro g p readout hreadout hsupport
  apply hn (inputGates p).card (Nat.cast_nonneg _)
  have hfinite := le_inputGates_of_inputSupport_card_le p readout hreadout hfn
    hsupport T hKn
  refine hfinite.trans ?_
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  gcongr
  linarith

/-- For direct support of size at most three, incidence layouts force more than
`(2 / 3 - ε) n` input-reading gates for all sufficiently large input lengths. -/
theorem eventually_lt_inputGates_of_inputSupport_card_le_three
    {f : ∀ n, Cslib.BooleanFunction n} {K k : ℕ → ℕ}
    (hf : ∀ᶠ n in atTop, ∀ b : Bool, Frontier.RectangleFree {x | f n x = b} (K n))
    (hK : ∀ᶠ n in atTop, K n ≤ 2 ^ k n)
    (hk : (fun n => (k n : ℝ)) =o[atTop] fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (g : ℕ) (p : Program signature n g)
      (readout : (Fin g → Bool) → Bool),
      (∀ x, readout (p.eval interpretation x) = f n x) →
      (∀ gate, (inputSupport p gate).card ≤ 3) →
      (2 / 3 - ε) * n < (inputGates p).card := by
  obtain ⟨T, hnum⟩ := eventually_lt_of_three_support_bounds hk hε 1
  filter_upwards [hf, hK, hnum] with n hfn hKn hn
  intro g p readout hreadout hsupport
  apply hn (inputGates p).card
  exact two_mul_lt_inputGates_of_inputSupport_card_le_three p readout hreadout hfn
    hsupport T hKn

end Cslib.Circuits.Boolean.WeightedThreshold
