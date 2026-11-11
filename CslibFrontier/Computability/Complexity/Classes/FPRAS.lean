/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Nat.Log
import CslibFrontier.Probability.PMF.Event

/-!
# Fully polynomial randomized approximation schemes

A **fully polynomial randomized approximation scheme** (FPRAS) for a counting function
`f : α → ℕ` is a randomized algorithm that, given an instance `x`, a relative error `ε` and a
failure probability `δ`, outputs an estimate within relative error `ε` of `f x` with probability
at least `1 - δ`, in time polynomial in the length of `x`, in `1 / ε` and in `log (1 / δ)`
[Karp, Luby and Madras][KarpLubyMadras1989],
[Jerrum, Valiant and Vazirani][JerrumValiantVazirani1986],
[Mitzenmacher and Upfal, Section 11.2, Definition 11.2][MitzenmacherUpfal2017].

`Cslib.Complexity.IsFPRAS enc f A` parameterizes the relative error as `ε = 1 / p` and the
failure probability as `δ = 2 ^ (-t)`, for natural numbers `p` and `t` both written in unary. A
running time polynomial in the length of the encoded input `(x, p, t)` is then exactly a running
time polynomial in `|x|`, `1 / ε` and `log (1 / δ)`. The three requirements stay separate:

* **runtime**: `A` is a strict probabilistic polynomial-time program (`Cslib.Probability.IsPPTOn`)
  on the encoded input `(x, p, t)`;
* **relative error**: the output is a pair `(num, den)` of natural numbers, written in binary,
  standing for the rational estimate `num / den`, and success means
  `Cslib.Complexity.ApproxWithin (f x) p num den`: `den > 0` and
  `|num / den - f x| ≤ f x / p`;
* **failure probability**: success has probability at least `1 - (1 / 2) ^ t` whenever `p > 0`.

The relative-error condition is multiplicative, so it forces an exact answer on instances with
`f x = 0` (`Cslib.Complexity.ApproxWithin.num_eq_zero`). `Cslib.Complexity.IsFPRAS.approx` gives
the guarantee in the usual form for real `ε > 0` and `δ > 0`, running `A` on `p = ⌈1 / ε⌉` and
`t = ⌈log₂ ⌈1 / δ⌉⌉`.

## Main definitions

* `Cslib.Complexity.ApproxWithin`: a rational estimate within relative error `1 / p`.
* `Cslib.Complexity.IsFPRAS`: a fully polynomial randomized approximation scheme.
* `Cslib.Complexity.FPRAS`: the counting functions admitting one.

## Main results

* `Cslib.Complexity.ApproxWithin.num_eq_zero`: zero counts are computed exactly.
* `Cslib.Complexity.IsFPRAS.approx`: the guarantee for real relative error and failure
  probability.

## References

* [R. M. Karp, M. Luby, N. Madras, *Monte-Carlo approximation algorithms for enumeration
  problems*][KarpLubyMadras1989]
* [M. R. Jerrum, L. G. Valiant, V. V. Vazirani, *Random generation of combinatorial structures from
  a uniform distribution*][JerrumValiantVazirani1986]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*, Section 11.2, Definition
  11.2][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type}

/-- The rational estimate `num / den` is within relative error `1 / p` of the count `c`: the
denominator is positive and `|num / den - c| ≤ c / p`. -/
def ApproxWithin (c p num den : ℕ) : Prop :=
  0 < den ∧ |(num : ℝ) / den - c| ≤ (c : ℝ) / p

/-- A zero count must be estimated exactly: the numerator is zero. -/
theorem ApproxWithin.num_eq_zero {p num den : ℕ} (h : ApproxWithin 0 p num den) : num = 0 := by
  obtain ⟨hden, hle⟩ := h
  simp only [Nat.cast_zero, sub_zero, zero_div, abs_nonpos_iff, div_eq_zero_iff,
    Nat.cast_eq_zero] at hle
  exact hle.resolve_right (Nat.pos_iff_ne_zero.1 hden)

/-- **A fully polynomial randomized approximation scheme** for the counting function `f`, on
instances encoded by `enc`. The algorithm `A x p t` receives the instance `x`, the inverse
relative error `p` (so `ε = 1 / p`) and the confidence `t` (so `δ = 2 ^ (-t)`), with `p` and `t` in
unary. It is a strict probabilistic polynomial-time program on the encoded triple `(x, p, t)`,
outputs a pair `(num, den)` in binary, and for `p > 0` its estimate `num / den` is within relative
error `1 / p` of `f x` with probability at least `1 - (1 / 2) ^ t`. -/
def IsFPRAS (enc : α ↪ List Bool) (f : α → ℕ) (A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)) : Prop :=
  IsPPTOn (encPair enc (encPair encUnary encUnary)) (encPair encNat encNat)
      (Function.uncurry fun x => Function.uncurry (A x)) ∧
    ∀ x p t, 0 < p → 1 - (1 / 2 : ℝ) ^ t ≤
      ((ProbComp.eval (A x p t)).toOuterMeasure
        {out | ApproxWithin (f x) p out.1 out.2}).toReal

/-- The counting functions with a fully polynomial randomized approximation scheme, on instances
encoded by `enc`. -/
def FPRAS (enc : α ↪ List Bool) : Set (α → ℕ) :=
  {f | ∃ A, IsFPRAS enc f A}

/-- **The guarantee for real parameters.** Run with `p = ⌈1 / ε⌉` and
`t = ⌈log₂ ⌈1 / δ⌉⌉`, an FPRAS outputs an estimate within relative error `ε` of `f x` with
probability at least `1 - δ`. Since `p < 1 / ε + 1`, and `t < log₂ (1 / δ) + 2` when `δ ≤ 1`, the
running time is polynomial in `|x|`, `1 / ε` and `log (1 / δ)`. -/
theorem IsFPRAS.approx {enc : α ↪ List Bool} {f : α → ℕ} {A : α → ℕ → ℕ → ProbComp (ℕ × ℕ)}
    (hA : IsFPRAS enc f A) (x : α) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    1 - δ ≤ ((ProbComp.eval (A x ⌈ε⁻¹⌉₊ (Nat.clog 2 ⌈δ⁻¹⌉₊))).toOuterMeasure
      {out | 0 < out.2 ∧ |(out.1 : ℝ) / out.2 - f x| ≤ ε * f x}).toReal := by
  have hp : 0 < ⌈ε⁻¹⌉₊ := Nat.ceil_pos.2 (inv_pos.2 hε)
  have hpow : (1 / 2 : ℝ) ^ Nat.clog 2 ⌈δ⁻¹⌉₊ ≤ δ := by
    have hle : (⌈δ⁻¹⌉₊ : ℝ) ≤ 2 ^ Nat.clog 2 ⌈δ⁻¹⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num) _
    rw [one_div_pow, one_div]
    calc (2 ^ Nat.clog 2 ⌈δ⁻¹⌉₊ : ℝ)⁻¹ ≤ (δ⁻¹)⁻¹ :=
          inv_anti₀ (inv_pos.2 hδ) ((Nat.le_ceil _).trans hle)
      _ = δ := inv_inv δ
  have hinv : (1 : ℝ) / ⌈ε⁻¹⌉₊ ≤ ε := by
    rw [div_le_iff₀ (by exact_mod_cast hp), ← div_le_iff₀' hε, one_div]
    exact Nat.le_ceil _
  refine le_trans (sub_le_sub_left hpow 1) ((hA.2 x _ _ hp).trans ?_)
  apply ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
  apply MeasureTheory.measure_mono
  rintro ⟨num, den⟩ ⟨hden, hle⟩
  refine ⟨hden, hle.trans ?_⟩
  rw [div_eq_mul_one_div, mul_comm]
  exact mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg _)

end Cslib.Complexity
