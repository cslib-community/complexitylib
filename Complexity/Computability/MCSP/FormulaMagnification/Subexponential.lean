/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.FormulaMagnification
public import Complexity.Foundations.Data.Nat.Subexponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Formula magnification with subexponential parameters

Oliveira and Santhanam's Theorem 17(iii) [OliveiraSanthanam2018, Section 3.1, p. 15]
magnifies an `N ^ (1 + ε)` formula lower bound for approximate MCSP, with circuit-size threshold
`s(n) = 2 ^ o(n)` and inverse approximation error `1 / δ(n) = 2 ^ o(n)`, to a superpolynomial
formula lower bound for an NP language. This module supplies the asymptotic step after the
finite, explicit reduction in `FormulaMagnification`.

The encoded query length `approxMCSPQueryEncLength n (s n) (k n)` is subexponentially bounded
whenever `s` and `k` are. Consequently, polynomial-size formulas for `SuccinctMCSP` would give,
for every positive integer `d` and all sufficiently large `n`, separating formulas of leaf size
at most `2 ^ (n + n / d)`. Arbitrarily large input lengths with a lower bound exceeding this
quantity therefore imply `NP ⊄ FormulaPolyOn SuccinctMCSP.enc`.

Here `N = 2 ^ n`, and integer division makes `2 ^ (n + n / d)` differ from `N ^ (1 + 1 / d)`
by a factor smaller than two. Positive integers `d` give arbitrarily small positive excess
exponents. The `rpow` corollaries give the source's real-exponent bound `N ^ (1 + ε)` directly,
for every real `ε > 0`. The inverse-error parameter is the integer `k`, representing `δ = 1 / k`,
and the approximate-MCSP no-set uses the existing non-strict agreement bound. The circuit thresholds
may differ (`s₁ ≤ s₂`); taking them equal recovers the source's single threshold. No
constructibility assumptions on the parameter schedules are needed here: the NP conclusion
uses the single, unrestricted language `SuccinctMCSP`, whose instances carry their thresholds
and samples explicitly.

## Main results

* `Cslib.Circuits.Boolean.subexponentiallyBounded_computableFunctionsLogBound`: the circuit
  counting exponent remains subexponential for a subexponential size threshold.
* `Cslib.Circuits.Boolean.subexponentiallyBounded_approxMCSPQueryEncLength`: the query length of
  the magnification reduction remains subexponential.
* `Cslib.Circuits.Boolean.eventually_exists_formula_separating_approxMCSP_of_mem_FormulaPolyOn`:
  polynomial-size formulas for `SuccinctMCSP` yield the eventual `2 ^ (n + n / d)` upper bound.
* `Cslib.Circuits.Boolean.not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_subexp_hard`,
  `Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_subexp_hard`: the
  subexponential-parameter consequence of Theorem 17(iii).
* `Circuits.Boolean.eventually_exists_formula_separating_approxMCSP_rpow_of_mem_FormulaPolyOn`,
  `Cslib.Circuits.Boolean.not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_rpow_hard`,
  `Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_rpow_hard`: the forward bound
  and hardness consequences with the source's real exponent `N ^ (1 + ε)`.

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.Circuits.Boolean

open Filter

/-- The explicit circuit-counting exponent is subexponentially bounded whenever the
circuit-size threshold is. A polynomial upper bound suffices here, so the ceiling logarithm in
the counting exponent does not require a separate asymptotic estimate. -/
theorem subexponentiallyBounded_computableFunctionsLogBound {s : ℕ → ℕ}
    (hs : SubexponentiallyBounded s) :
    SubexponentiallyBounded (fun n => computableFunctionsLogBound n (s n)) := by
  have hbound : SubexponentiallyBounded
      (fun n => (s n + 1) * (2 * (n + s n + 1) + 3)) :=
    (hs.add (.const 1)).mul
      (((SubexponentiallyBounded.const 2).mul
        ((SubexponentiallyBounded.id.add hs).add (.const 1))).add (.const 3))
  exact hbound.mono_of_le fun n => computableFunctionsLogBound_le_poly n (s n)

/-- The encoded query length in the approximate-MCSP formula reduction is subexponential
when both the circuit-size threshold and the inverse-error parameter are subexponential. -/
theorem subexponentiallyBounded_approxMCSPQueryEncLength {s k : ℕ → ℕ}
    (hs : SubexponentiallyBounded s) (hk : SubexponentiallyBounded k) :
    SubexponentiallyBounded (fun n => approxMCSPQueryEncLength n (s n) (k n)) := by
  have hq : SubexponentiallyBounded
      (fun n => k n * (computableFunctionsLogBound n (s n) + 2)) :=
    hk.mul ((subexponentiallyBounded_computableFunctionsLogBound hs).add (.const 2))
  have h8n : SubexponentiallyBounded (fun n => 8 * n + 10) :=
    ((SubexponentiallyBounded.const 8).mul SubexponentiallyBounded.id).add (.const 10)
  have h4n : SubexponentiallyBounded (fun n => 4 * n + 3) :=
    ((SubexponentiallyBounded.const 4).mul SubexponentiallyBounded.id).add (.const 3)
  exact (h4n.add (hq.mul h8n)).add hs

/-- **Forward form of Oliveira–Santhanam Theorem 17(iii)**
[OliveiraSanthanam2018, Section 3.1, Lemma 16 and Theorem 17(iii), pp. 14–15].
If the circuit-size threshold `s₂` and inverse-error parameter `k` are subexponential, then
polynomial-size formulas for `SuccinctMCSP` yield approximate-MCSP separating formulas of leaf
size at most `2 ^ (n + n / d)` for every positive integer `d` and all sufficiently large `n`. -/
theorem eventually_exists_formula_separating_approxMCSP_of_mem_FormulaPolyOn
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    (hmem : SuccinctMCSP ∈ FormulaPolyOn SuccinctMCSP.enc) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ 2 ^ (n + n / d) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  obtain ⟨c, hc⟩ := mem_FormulaPolyOn_iff_exists_mem_FormulaSIZEOn.mp hmem
  have hquery := subexponentiallyBounded_approxMCSPQueryEncLength hs₂_subexp hk_subexp
  have hsubexp : SubexponentiallyBounded
      (fun n => 2 * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c)) :=
    (SubexponentiallyBounded.const 2).mul
      ((SubexponentiallyBounded.const c).mul ((hquery.add (.const 1)).pow c))
  have hmono : Monotone (fun m => c * (m + 1) ^ c) := fun _ _ hm =>
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) c)
  filter_upwards [hsubexp.eventually_le_two_pow_div d hd] with n hn
  obtain ⟨F, hF, hyes, hno⟩ :=
    exists_formula_separating_approxMCSP_of_mem_FormulaSIZEOn hs hk hmono hc n
  refine ⟨F, hF.trans ?_, hyes, hno⟩
  calc
    (2 ^ n + 1) * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c)
        ≤ (2 * 2 ^ n) * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c) := by
          apply Nat.mul_le_mul_right
          have := Nat.one_le_two_pow (n := n)
          omega
    _ = 2 ^ n * (2 * (c * (approxMCSPQueryEncLength n (s₂ n) (k n) + 1) ^ c)) := by
        ac_rfl
    _ ≤ 2 ^ n * 2 ^ (n / d) := Nat.mul_le_mul_left _ hn
    _ = 2 ^ (n + n / d) := (pow_add 2 n (n / d)).symm

/-- **Oliveira–Santhanam Theorem 17(iii), for `SuccinctMCSP`**
[OliveiraSanthanam2018, Section 3.1, Theorem 17(iii), p. 15].
For subexponential circuit-size and inverse-error parameters, a formula lower bound exceeding
`2 ^ (n + n / d)` at arbitrarily large lengths, for some positive `d`, implies that
`SuccinctMCSP` has no polynomial-size De Morgan formulas under its existing encoding. -/
theorem not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_subexp_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    {d : ℕ} (hd : 0 < d)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      2 ^ (n + n / d) < F.leafSize) :
    SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc := by
  intro hmem
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exists_formula_separating_approxMCSP_of_mem_FormulaPolyOn
      hs hk hs₂_subexp hk_subexp hmem d hd)
  obtain ⟨n, hn, hhardn⟩ := hhard N
  obtain ⟨F, hF, hyes, hno⟩ := hN n hn
  exact (hhardn F hyes hno).not_ge hF

/-- **Oliveira–Santhanam Theorem 17(iii): `NP ⊄ Formula[poly]`**
[OliveiraSanthanam2018, Section 3.1, Theorem 17(iii), p. 15].
The subexponential-parameter approximate-MCSP lower bound rules out containment of NP in
polynomial-size De Morgan formulas, with `SuccinctMCSP` supplying the NP witness. -/
theorem not_NP_subset_FormulaPolyOn_of_approxMCSP_subexp_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    {d : ℕ} (hd : 0 < d)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      2 ^ (n + n / d) < F.leafSize) :
    ¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc) :=
  fun hsub => not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_subexp_hard
    hs hk hs₂_subexp hk_subexp hd hhard (hsub SuccinctMCSP.mem_NP)

/-- **Real-exponent forward form of Oliveira–Santhanam Theorem 17(iii)**
[OliveiraSanthanam2018, Section 3.1, Theorem 17(iii), p. 15].
Under subexponential circuit-size and inverse-error parameters, polynomial-size formulas for
`SuccinctMCSP` give approximate-MCSP separators of leaf size at most `N ^ (1 + ε)` eventually,
for every real `ε > 0`, where `N = 2 ^ n`. -/
theorem eventually_exists_formula_separating_approxMCSP_rpow_of_mem_FormulaPolyOn
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    (hmem : SuccinctMCSP ∈ FormulaPolyOn SuccinctMCSP.enc) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      (F.leafSize : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) := by
  obtain ⟨d, hd⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_exists_formula_separating_approxMCSP_of_mem_FormulaPolyOn
    hs hk hs₂_subexp hk_subexp hmem (d + 1) (Nat.succ_pos d)] with n hn
  obtain ⟨F, hF, hyes, hno⟩ := hn
  have hdiv : ((n / (d + 1) : ℕ) : ℝ) ≤ (n : ℝ) * ε := by
    refine Nat.cast_div_le.trans ?_
    simpa only [div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using
      mul_le_mul_of_nonneg_left hd.le (Nat.cast_nonneg n)
  refine ⟨F, (show (F.leafSize : ℝ) ≤ (2 ^ (n + n / (d + 1)) : ℕ) by
    exact_mod_cast hF).trans ?_, hyes, hno⟩
  calc
    ((2 ^ (n + n / (d + 1)) : ℕ) : ℝ)
        = (2 : ℝ) ^ ((n + n / (d + 1) : ℕ) : ℝ) := by
          simp only [Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ (2 : ℝ) ^ ((n : ℝ) * (1 + ε)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast
        nlinarith
    _ = ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) := by
        rw [Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_cast

/-- **Oliveira–Santhanam Theorem 17(iii), with a real excess exponent**
[OliveiraSanthanam2018, Section 3.1, Theorem 17(iii), p. 15].
For subexponential circuit-size and inverse-error parameters, approximate-MCSP formula lower
bounds exceeding `N ^ (1 + ε)` at arbitrarily large lengths, with a fixed real `ε > 0`, imply
that `SuccinctMCSP` has no polynomial-size De Morgan formulas. -/
theorem not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_rpow_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    {ε : ℝ} (hε : 0 < ε)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < (F.leafSize : ℝ)) :
    SuccinctMCSP ∉ FormulaPolyOn SuccinctMCSP.enc := by
  intro hmem
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exists_formula_separating_approxMCSP_rpow_of_mem_FormulaPolyOn
      hs hk hs₂_subexp hk_subexp hmem hε)
  obtain ⟨n, hn, hhardn⟩ := hhard N
  obtain ⟨F, hF, hyes, hno⟩ := hN n hn
  exact (hhardn F hyes hno).not_ge hF

/-- **Oliveira–Santhanam Theorem 17(iii): `N ^ (1 + ε)` hardness implies
`NP ⊄ Formula[poly]`**, with real `ε > 0`
[OliveiraSanthanam2018, Section 3.1, Theorem 17(iii), p. 15]. -/
theorem not_NP_subset_FormulaPolyOn_of_approxMCSP_rpow_hard
    {s₁ s₂ k : ℕ → ℕ} (hs : ∀ n, s₁ n ≤ s₂ n) (hk : ∀ n, 1 ≤ k n)
    (hs₂_subexp : SubexponentiallyBounded s₂) (hk_subexp : SubexponentiallyBounded k)
    {ε : ℝ} (hε : 0 < ε)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s₁ →
        F.eval interpretation T = true) →
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ ApproxMCSP.noSet s₂ k →
        F.eval interpretation T = false) →
      ((2 ^ n : ℕ) : ℝ) ^ (1 + ε) < (F.leafSize : ℝ)) :
    ¬ (Complexity.NP SuccinctMCSP.enc ⊆ FormulaPolyOn SuccinctMCSP.enc) :=
  fun hsub => not_succinctMCSP_mem_FormulaPolyOn_of_approxMCSP_rpow_hard
    hs hk hs₂_subexp hk_subexp hε hhard (hsub SuccinctMCSP.mem_NP)

end Cslib.Circuits.Boolean
