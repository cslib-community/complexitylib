/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.FormulaMagnification
public import Complexity.Computability.MCSP.SuccinctNP.Words
public import Complexity.Foundations.Data.Nat.PolynomialBound.Rpow
import Complexity.Foundations.Analysis.Asymptotics.Exponential

/-!
# Stretched-exponential formula lower bounds from approximate MCSP

Oliveira and Santhanam's Theorem 17(ii) in the full version ECCC TR18-139
[OliveiraSanthanam2018, Section 3.1, printed p. 15]
magnifies an `N ^ (1 + ε)` formula lower bound for approximate MCSP with polynomial parameters
to a language in NP requiring more than `O(2 ^ (m ^ δ))` formula leaves for some `δ > 0`.
This module supplies that asymptotic consequence of the finite formula reduction.

The query length `q(n) = approxMCSPQueryEncLength n (s₂ n) (k n)` is polynomially bounded.
Choosing a sufficiently small positive `δ` makes `q(n) ^ δ = o(n)`. A language agreeing with
`SuccinctMCSP` whose formula size is `O(2 ^ (m ^ δ))` would therefore give approximate-MCSP
separators of size at most `N ^ (1 + ε)` at all sufficiently large lengths. Contraposition
produces the lower bound, and a binary NP language agreeing with `SuccinctMCSP` supplies the
literal NP witness.

The conclusion uses real-valued `Asymptotics.IsBigO` at `atTop`: it excludes every constant
multiple and allows arbitrary behavior at finitely many small input lengths. It is therefore
an asymptotic lower bound, not merely failure of a fixed pointwise size bound. The hardness
hypothesis holds at arbitrarily large truth-table lengths, and `N = 2 ^ n`.

As in the existing reduction, `k` is an integer inverse-error parameter (`δ_source = 1 / k`)
and the approximate-MCSP no-set has a non-strict agreement bound. We allow different thresholds
`s₁ ≤ s₂` and arbitrary polynomially bounded `s₂` and `k`, generalizing the source's
matching polynomial schedules. The unrestricted `SuccinctMCSP` verifier makes constructibility
assumptions on these schedules unnecessary.

## Main results

* `Cslib.Circuits.Boolean.eventually_exists_formula_separating_approxMCSP_of_isBigO`: an
  asymptotic formula bound for a language agreeing with `SuccinctMCSP` gives eventual
  `N ^ (1 + ε)` separators whenever the query-length power is sublinear.
* `Cslib.Circuits.Boolean.exists_pos_not_isBigO_formulaSize_of_approxMCSP_hard`: a common
  positive exponent witnesses stretched-exponential hardness for every agreeing language.
* `Cslib.Circuits.Boolean.exists_NP_not_isBigO_formulaSize_of_approxMCSP_poly_hard`: the NP
  language and positive exponent of Oliveira–Santhanam Theorem 17(ii).

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.Circuits.Boolean

open Asymptotics Filter

/-- **Forward asymptotic formula magnification.** Suppose a language agreeing with
`SuccinctMCSP` has formula leaf size `O(2 ^ (m ^ δ))`, and the `δ`th power of the reduction's
query length is `o(n)`. Then approximate MCSP has separators of size at most `N ^ (1 + ε)`
eventually, for every real `ε > 0`, where `N = 2 ^ n`.
This is the forward implication used in the full version ECCC TR18-139
[OliveiraSanthanam2018, Theorem 17(ii), printed p. 15]. -/
theorem eventually_exists_formula_separating_approxMCSP_of_isBigO
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hquery : (fun n => (approxMCSPQueryEncLength n (s₂ n) (k n) : ℝ) ^ δ)
      =o[atTop] (fun n => (n : ℝ)))
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    (hsize : (fun m => (formulaSize (L.slice m) : ℝ))
      =O[atTop] (fun m => (2 : ℝ) ^ ((m : ℝ) ^ δ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      (F.leafSize : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  obtain ⟨C, hC, hbound⟩ := hsize.exists_pos
  have hbound' : ∀ᶠ m in atTop,
      (formulaSize (L.slice m) : ℝ) ≤ C * (2 : ℝ) ^ ((m : ℝ) ^ δ) := by
    filter_upwards [hbound.bound] with m hm
    simpa only [Real.norm_natCast, Real.norm_eq_abs, Nat.abs_cast,
      abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)] using hm
  obtain ⟨M, hM⟩ := eventually_atTop.mp hbound'
  have hsmall := hquery.eventually_mul_natCeil_two_rpow_le C hC.le 2 hε
  filter_upwards [hsmall, eventually_ge_atTop M] with n hn hnM
  let q := approxMCSPQueryEncLength n (s₂ n) (k n)
  let B := ⌈C * (2 : ℝ) ^ ((q : ℝ) ^ δ)⌉₊
  obtain ⟨F, hF, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_agrees hag (hk n) (hs n)
      (card_computableFunctions_le_two_pow n (s₂ n)) (B := B) (by
        intro m hm
        have hlen : n ≤ SuccinctMCSP.ofFunctionEncLength n m (s₂ n) := by
          simp only [SuccinctMCSP.ofFunctionEncLength]
          omega
        have hle : SuccinctMCSP.ofFunctionEncLength n m (s₂ n) ≤ q :=
          ofFunctionEncLength_le_approxMCSPQueryEncLength hm
        have hexp : (2 : ℝ) ^ ((SuccinctMCSP.ofFunctionEncLength n m (s₂ n) : ℝ) ^ δ)
            ≤ (2 : ℝ) ^ ((q : ℝ) ^ δ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle) hδ)
        have hreal := (hM _ (hnM.trans hlen)).trans
          (mul_le_mul_of_nonneg_left hexp hC.le)
        exact_mod_cast hreal.trans (Nat.le_ceil _))
  have hn' : 2 * (B : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn
  have hF' : (F.leafSize : ℝ) ≤ ((2 : ℝ) ^ n + 1) * (B : ℝ) := by
    exact_mod_cast hF
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.one_le_two_pow (n := n))
  refine ⟨F, hF'.trans ?_, hyes, hno⟩
  calc
    ((2 : ℝ) ^ n + 1) * (B : ℝ) ≤ (2 : ℝ) ^ n * (2 * (B : ℝ)) := by
      calc
        ((2 : ℝ) ^ n + 1) * (B : ℝ) ≤ (2 * (2 : ℝ) ^ n) * (B : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg B)
        _ = (2 : ℝ) ^ n * (2 * (B : ℝ)) := by ring
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ (ε * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [show (n : ℝ) + ε * n = (n : ℝ) * (1 + ε) by ring]
      rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_cast

/-- **Oliveira–Santhanam Theorem 17(ii), for every language agreeing with `SuccinctMCSP`**,
from the full version ECCC TR18-139
[OliveiraSanthanam2018, Section 3.1, Theorem 17(ii), printed p. 15].
With polynomially bounded circuit-size and inverse-error parameters, approximate-MCSP formula
hardness above `N ^ (1 + ε)` at arbitrarily large lengths gives a positive `δ` such that no
agreeing language has formula size `O(2 ^ (m ^ δ))`. -/
theorem exists_pos_not_isBigO_formulaSize_of_approxMCSP_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_poly : PolynomiallyBounded s₂) (hk_poly : PolynomiallyBounded k)
    {ε : ℝ} (hε : 0 < ε)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < (F.leafSize : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ L : Language Bool,
      (∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L) →
      ¬ ((fun m => (formulaSize (L.slice m) : ℝ))
        =O[atTop] (fun m => (2 : ℝ) ^ ((m : ℝ) ^ δ))) := by
  obtain ⟨δ, hδ, hquery⟩ :=
    (polynomiallyBounded_approxMCSPQueryEncLength hs₂_poly hk_poly).exists_pos_rpow_isLittleO
  refine ⟨δ, hδ, fun L hag hsize => ?_⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exists_formula_separating_approxMCSP_of_isBigO hs hk hδ.le hquery hag hsize hε)
  obtain ⟨n, hn, hhardn⟩ := hhard N
  obtain ⟨F, hF, hyes, hno⟩ := hN n hn
  exact (hhardn F hyes hno).not_ge hF

/-- **Oliveira–Santhanam Theorem 17(ii), with a binary NP language witness**,
from the full version ECCC TR18-139
[OliveiraSanthanam2018, Section 3.1, Theorem 17(ii), printed p. 15].
An `N ^ (1 + ε)` approximate-MCSP formula lower bound with polynomial parameters implies that
some binary language in NP has no `O(2 ^ (m ^ δ))` formula-size bound for a positive `δ`. -/
theorem exists_NP_not_isBigO_formulaSize_of_approxMCSP_poly_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_poly : PolynomiallyBounded s₂) (hk_poly : PolynomiallyBounded k)
    {ε : ℝ} (hε : 0 < ε)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < (F.leafSize : ℝ)) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      ∃ δ : ℝ, 0 < δ ∧ ¬ ((fun m => (formulaSize (L.slice m) : ℝ))
        =O[atTop] (fun m => (2 : ℝ) ^ ((m : ℝ) ^ δ))) := by
  obtain ⟨δ, hδ, hhardδ⟩ := exists_pos_not_isBigO_formulaSize_of_approxMCSP_hard
    hs hk hs₂_poly hk_poly hε hhard
  obtain ⟨L, hL, hag⟩ := SuccinctMCSP.exists_language_mem_NP
  exact ⟨L, hL, δ, hδ, hhardδ L hag⟩

end Cslib.Circuits.Boolean
