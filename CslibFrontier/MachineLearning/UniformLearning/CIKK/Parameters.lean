/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Foundations.Analysis.SpecialFunctions.LogTwoPow
import Mathlib.Data.Nat.Log

/-!
# Parameters of the CIKK learner

The library's form of the learner of Carmosino, Impagliazzo, Kabanets and Kolokolova
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016] chains three stages:
- the Nisan–Wigderson reconstruction on the amplified function `Amp(f) = (f^k)^GL`;
- the reconstruction of the amplification (Goldreich–Levin candidates and the direct-product
  decoder);
- best-of selection.

The source composes only the first two reconstructions, each of which boosts its own confidence
[Carmosino, Impagliazzo, Kabanets and Kolokolova, proof of Theorem 3.2, p. 10:11]. The single
outer best-of selection, which replaces those per-stage boosts and gives the same result up to
constants, is the library's.

This file fixes the parameters of the last two stages as explicit numerals in three precision
exponents:
- `e`, for error `2^{-e}`;
- `g`, for a Nisan–Wigderson advantage and success probability of at least `2^{-g}`;
- `h`, for confidence `1 - 2^{-h}`.

It proves the inequalities the stages need:
- with `γ = 2^{-g}`, error `2^{-(e+1)}` for the amplification stage and
  `δ₀ = γ / 2^{K+3}` (`K = cikkMasks e g`):
  - the Goldreich–Levin list condition `k ≤ 2 (γ/2)² (2^K - 1)` (`cikkK_le_cikkMasks`);
  - the direct-product conditions `2s ≤ k` (`two_mul_cikkFixed_le_cikkK`),
    `64/ε · log (512/(ε δ₀²)) ≤ s` (`le_cikkFixed`) and `16/δ₀ · log (8/ε) ≤ m`
    (`le_cikkTrials`);
- for the outer best-of selection over a learner that succeeds with probability `γ δ₀² / 8`, with
  deviation `θ = 2^{-(e+2)}`: `log (2/η) ≤ p b` (`log_le_cikkRuns`) and `log (4b/η) ≤ 2 t θ²`
  (`log_le_cikkSamples`).

The direct-product length `k` is a power of two. With every quantity a power of two, the
conditions are linear in the exponents, after `log x ≤ N` for `0 < x ≤ 2 ^ N`
(`Real.log_le_of_le_two_pow`). This solves the condition `2s ≤ k`, which is a fixed point in `k`
because `s` grows with `log (1/δ₀)` and `δ₀` with `1/k`. It replaces the source's
`k = ⌈3c/ε · ln(1/γ)⌉ + 1` [Carmosino, Impagliazzo, Kabanets and Kolokolova, proof of
Theorem 4.3, step 1, p. 10:15]. For fixed `e`, `k` is linear in `g` (`cikkK_le`), and so is the
input length `k n + k` of `Amp(f)`.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.cikkK`: the direct-product length `k = 2 ^ cikkLogK e g`.
* `Cslib.MachineLearning.UniformLearning.cikkMasks`: the number `K` of Goldreich–Levin masks.
* `Cslib.MachineLearning.UniformLearning.cikkFixed`: the size `s` of the fixed position set of the
  direct-product decoder.
* `Cslib.MachineLearning.UniformLearning.cikkTrials`: the number `m` of decoder trials.
* `Cslib.MachineLearning.UniformLearning.cikkRuns`,
  `Cslib.MachineLearning.UniformLearning.cikkSamples`: the runs and sample points of best-of
  selection.

## Main results

* `Cslib.MachineLearning.UniformLearning.cikkK_le_cikkMasks`: the list condition.
* `Cslib.MachineLearning.UniformLearning.two_mul_cikkFixed_le_cikkK`,
  `Cslib.MachineLearning.UniformLearning.cikkFixed_le_cikkK`,
  `Cslib.MachineLearning.UniformLearning.le_cikkFixed`,
  `Cslib.MachineLearning.UniformLearning.le_cikkTrials`: the direct-product conditions.
* `Cslib.MachineLearning.UniformLearning.log_le_cikkRuns`,
  `Cslib.MachineLearning.UniformLearning.log_le_cikkSamples`: the conditions of the outer best-of
  selection.
* `Cslib.MachineLearning.UniformLearning.cikkK_le`: `k ≤ 2 ^ (e + 10) (6g + 3e + 36)`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

/-- The exponent of the direct-product length: `log₂ k = e + ⌈log₂ (6g + 3e + 36)⌉ + 9`. -/
def cikkLogK (e g : ℕ) : ℕ := e + Nat.clog 2 (6 * g + 3 * e + 36) + 9

/-- The direct-product length `k = 2 ^ cikkLogK e g` of the amplified function
`Amp(f) = (f^k)^GL`. -/
def cikkK (e g : ℕ) : ℕ := 2 ^ cikkLogK e g

/-- The number `K = 2g + log₂ k + 2` of Goldreich–Levin masks, so that `2^K - 1` masked copies
decode each of the `k` coordinates. -/
def cikkMasks (e g : ℕ) : ℕ := 2 * g + cikkLogK e g + 2

/-- The size `s = 2^{e+7} (6g + 2 log₂ k + e + 20)` of the fixed position set of the
direct-product decoder. -/
def cikkFixed (e g : ℕ) : ℕ := 2 ^ (e + 7) * (6 * g + 2 * cikkLogK e g + e + 20)

/-- The number `m = 2^{3g + log₂ k + 9} (e + 4)` of trials of the direct-product decoder. -/
def cikkTrials (e g : ℕ) : ℕ := 2 ^ (3 * g + cikkLogK e g + 9) * (e + 4)

/-- The number `b = (h + 1) 2^{7g + 2 log₂ k + 13}` of runs of best-of selection. -/
def cikkRuns (e g h : ℕ) : ℕ := (h + 1) * 2 ^ (7 * g + 2 * cikkLogK e g + 13)

/-- The number `t = 2^{2e+3} (7g + 2 log₂ k + 2h + 16)` of sample points of best-of selection. -/
def cikkSamples (e g h : ℕ) : ℕ := 2 ^ (2 * e + 3) * (7 * g + 2 * cikkLogK e g + 2 * h + 16)

/-- With `L = ⌈log₂ (6g + 3e + 36)⌉`: `6g + 3e + 36 ≤ 2 ^ L` and `2L + 2 ≤ 2 ^ L`. -/
private theorem clog_bounds (e g : ℕ) :
    6 * g + 3 * e + 36 ≤ 2 ^ Nat.clog 2 (6 * g + 3 * e + 36) ∧
      2 * Nat.clog 2 (6 * g + 3 * e + 36) + 2 ≤ 2 ^ Nat.clog 2 (6 * g + 3 * e + 36) := by
  have hX : 6 * g + 3 * e + 36 ≤ 2 ^ Nat.clog 2 (6 * g + 3 * e + 36) :=
    Nat.le_pow_clog (by norm_num) _
  refine ⟨hX, ?_⟩
  generalize Nat.clog 2 (6 * g + 3 * e + 36) = L at hX ⊢
  rcases Nat.lt_or_ge L 3 with hL | hL
  · have h4 : 2 ^ L ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h4
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
    have := Nat.lt_two_pow_self (n := m)
    have h8 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
    omega

/-- The Goldreich–Levin mask count is positive. -/
theorem cikkMasks_pos (e g : ℕ) : 0 < cikkMasks e g := by
  unfold cikkMasks
  omega

/-- **The list condition**: with `γ = 2^{-g}`, `k ≤ 2 (γ/2)² (2^K - 1)` for `K = cikkMasks e g`,
with `2^K - 1` computed in `ℕ`. -/
theorem cikkK_le_cikkMasks (e g : ℕ) :
    (cikkK e g : ℝ) ≤ 2 * (1 / 2 ^ g / 2) ^ 2 * ((2 ^ cikkMasks e g - 1 : ℕ) : ℝ) := by
  rw [Nat.cast_sub Nat.one_le_two_pow]
  simp only [cikkK, cikkMasks]
  generalize cikkLogK e g = j
  push_cast
  have ha : (1 : ℝ) ≤ 2 ^ g := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℝ) ^ (2 * g + j + 2) = 4 * (2 ^ g) ^ 2 * 2 ^ j := by ring
  have key : 2 * (1 / 2 ^ g / 2) ^ 2 * (4 * ((2 : ℝ) ^ g) ^ 2 * 2 ^ j - 1) =
      2 * 2 ^ j - 1 / (2 * (2 ^ g) ^ 2) := by
    field_simp
    ring
  have hsmall : 1 / (2 * ((2 : ℝ) ^ g) ^ 2) ≤ 2 ^ j := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := j) (by norm_num)]
  rw [hpow, key]
  linarith

/-- **Twice the fixed set fits**: `2s ≤ k`. -/
theorem two_mul_cikkFixed_le_cikkK (e g : ℕ) : 2 * cikkFixed e g ≤ cikkK e g := by
  obtain ⟨hX, h2L⟩ := clog_bounds e g
  simp only [cikkK, cikkFixed, cikkLogK]
  generalize Nat.clog 2 (6 * g + 3 * e + 36) = L at hX h2L ⊢
  have h1 : 2 ^ (e + L + 9) = 2 ^ (e + 7) * (4 * 2 ^ L) := by ring
  have h2 : 2 * (6 * g + 2 * (e + L + 9) + e + 20) ≤ 4 * 2 ^ L := by omega
  rw [h1]
  calc 2 * (2 ^ (e + 7) * (6 * g + 2 * (e + L + 9) + e + 20))
      = 2 ^ (e + 7) * (2 * (6 * g + 2 * (e + L + 9) + e + 20)) := by ring
    _ ≤ 2 ^ (e + 7) * (4 * 2 ^ L) := Nat.mul_le_mul_left _ h2

/-- **The fixed set is large enough**: with `ε = 2^{-(e+1)}` and `δ₀ = 2^{-g} / 2^{K+3}`,
`64/ε · log (512/(ε δ₀²)) ≤ s`. -/
theorem le_cikkFixed (e g : ℕ) :
    64 / (1 / 2 ^ (e + 1)) *
        Real.log (512 / (1 / 2 ^ (e + 1) * (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2)) ≤
      cikkFixed e g := by
  have h1 : (512 : ℝ) / (1 / 2 ^ (e + 1) * (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2) =
      2 ^ (6 * g + 2 * cikkLogK e g + e + 20) := by
    simp only [cikkMasks]
    field_simp
    ring
  have h2 : (64 : ℝ) / (1 / 2 ^ (e + 1)) = 2 ^ (e + 7) := by
    field_simp
    ring
  rw [h1, h2, cikkFixed, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact Real.log_le_of_le_two_pow (by positivity) le_rfl

/-- **Enough decoder trials**: with `ε = 2^{-(e+1)}` and `δ₀ = 2^{-g} / 2^{K+3}`,
`16/δ₀ · log (8/ε) ≤ m`. -/
theorem le_cikkTrials (e g : ℕ) :
    16 / (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) * Real.log (8 / (1 / 2 ^ (e + 1))) ≤
      cikkTrials e g := by
  have h1 : (16 : ℝ) / (1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) =
      2 ^ (3 * g + cikkLogK e g + 9) := by
    simp only [cikkMasks]
    field_simp
    ring
  have h2 : (8 : ℝ) / (1 / 2 ^ (e + 1)) = 2 ^ (e + 4) := by
    field_simp
    ring
  rw [h1, h2, cikkTrials, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact Real.log_le_of_le_two_pow (by positivity) le_rfl

/-- **Enough runs**: a learner that succeeds with probability `p = γ δ₀² / 8`, with `γ = 2^{-g}`
and `δ₀ = γ / 2^{K+3}`, has `log (2/η) ≤ p b` for `η = 2^{-h}`. -/
theorem log_le_cikkRuns (e g h : ℕ) :
    Real.log (2 / (1 / 2 ^ h)) ≤
      1 / 2 ^ g * ((1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8) * cikkRuns e g h := by
  have h1 : (1 : ℝ) / 2 ^ g * ((1 / 2 ^ g / 2 ^ (cikkMasks e g + 3)) ^ 2 / 8) * cikkRuns e g h =
      h + 1 := by
    simp only [cikkRuns, cikkMasks]
    push_cast
    field_simp
    ring
  have h2 : (2 : ℝ) / (1 / 2 ^ h) = 2 ^ (h + 1) := by
    field_simp
    ring
  rw [h1, h2]
  exact_mod_cast Real.log_le_of_le_two_pow (by positivity) le_rfl

/-- **Enough sample points**: `log (4b/η) ≤ 2 t θ²` for `η = 2^{-h}` and `θ = 2^{-(e+2)}`. -/
theorem log_le_cikkSamples (e g h : ℕ) :
    Real.log (4 * cikkRuns e g h / (1 / 2 ^ h)) ≤
      2 * cikkSamples e g h * (1 / 2 ^ (e + 2)) ^ 2 := by
  have h1 : (2 : ℝ) * cikkSamples e g h * (1 / 2 ^ (e + 2)) ^ 2 =
      7 * g + 2 * cikkLogK e g + 2 * h + 16 := by
    simp only [cikkSamples]
    push_cast
    field_simp
    ring
  have hh : (h : ℝ) + 1 ≤ 2 ^ h := by exact_mod_cast (Nat.lt_two_pow_self : h + 1 ≤ 2 ^ h)
  have hpow : (2 : ℝ) ^ (7 * g + 2 * cikkLogK e g + 2 * h + 15) =
      4 * (2 ^ h * 2 ^ (7 * g + 2 * cikkLogK e g + 13)) * 2 ^ h := by ring
  have hb : (0 : ℝ) < cikkRuns e g h := by unfold cikkRuns; positivity
  rw [h1]
  refine (Real.log_le_of_le_two_pow (k := 7 * g + 2 * cikkLogK e g + 2 * h + 15)
    (by positivity) ?_).trans ?_
  · rw [cikkRuns, hpow, div_eq_mul_inv, one_div, inv_inv]
    push_cast
    gcongr
  · push_cast
    linarith

/-- **`k` is linear in `g`**: `k ≤ 2 ^ (e + 10) (6g + 3e + 36)`. -/
theorem cikkK_le (e g : ℕ) : cikkK e g ≤ 2 ^ (e + 10) * (6 * g + 3 * e + 36) := by
  have hL : 0 < Nat.clog 2 (6 * g + 3 * e + 36) := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (x := 6 * g + 3 * e + 36) (by norm_num)
    (by omega)
  simp only [cikkK, cikkLogK]
  generalize Nat.clog 2 (6 * g + 3 * e + 36) = L at hL hlt ⊢
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rw [Nat.pred_succ] at hlt
  rw [show e + (m + 1) + 9 = e + 10 + m by omega, pow_add]
  exact Nat.mul_le_mul_left _ hlt.le

instance (e g h : ℕ) : NeZero (cikkRuns e g h) :=
  ⟨by unfold cikkRuns; positivity⟩

/-- The fixed set fits in the direct-product length: `s ≤ k`. -/
theorem cikkFixed_le_cikkK (e g : ℕ) : cikkFixed e g ≤ cikkK e g := by
  have := two_mul_cikkFixed_le_cikkK e g
  omega

instance (e g : ℕ) : Fact (cikkFixed e g ≤ cikkK e g) :=
  ⟨cikkFixed_le_cikkK e g⟩

end Cslib.MachineLearning.UniformLearning
