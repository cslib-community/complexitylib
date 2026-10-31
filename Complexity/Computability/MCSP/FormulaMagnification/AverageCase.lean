/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.FormulaMagnification.Subexponential
public import Complexity.Computability.MCSP.SuccinctNP.Words

/-!
# Subexponential zero-error average-case formula magnification

This module supplies the asymptotic step after the finite one-sided projection in
`FormulaMagnification`, following [OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21].
For subexponential circuit-size and loss schedules, its encoded query length is subexponential.
Polynomial-size formulas for any binary language agreeing with succinct MCSP therefore give,
for every positive integer `d` and all sufficiently large `n`, a formula on `N = 2 ^ n` variables
with at most `2 ^ (n / d)` leaves and the existing one-sided counting guarantee.

These formulas are unknown masks: `true` means unknown, while `false` certifies that the input
truth table has circuit complexity above the threshold. With loss `r = n`, the unknown fraction
is at most `2 ^ (-n)`. In particular this is eventually at most the `1 / n` allowance in
[OliveiraSanthanam2018, Appendix A, Definition 43, p. 34], where `n` is the truth table's arity,
not its length `N`. The formal statements retain exact natural-number counts.

The quantifier order is `∀ d > 0, ∀ᶠ n, ∃ F`. The lower-bound consequence uses arbitrarily large
hard lengths at one fixed positive reciprocal exponent. No single simultaneously subexponential
formula family is inferred from this order. Arbitrary parameter schedules need no computability
assumption: the single binary NP witness receives the thresholds and samples in its input.
The concrete rounded `2 ^ (sqrt n)` specialization and a conventional ternary-device formulation
of Theorem 5 are separate from this asymptotic one-sided result.

## Main results

* `Cslib.Circuits.Boolean.subexponentiallyBounded_avgCaseMCSPQueryEncLength`: closure of the
  average-case query length under subexponential schedules.
* `Cslib.Circuits.Boolean.eventually_exists_formula_zero_error_average_case_of_mem_FormulaPoly`:
  the forward bound with the exact one-sided count.
* `Cslib.Circuits.Boolean.not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard`: the
  fixed-exponent lower-bound contrapositive for any agreeing binary language.
* `Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard`:
  the corresponding binary NP-language witness.

## References

* [I. C. Oliveira, R. Santhanam, *Hardness Magnification for Natural
  Problems*][OliveiraSanthanam2018]
-/

public section

namespace Cslib.Circuits.Boolean

open Filter

/-- The average-case encoded query length is subexponential when both its circuit-size
threshold and its loss parameter are subexponential. -/
theorem subexponentiallyBounded_avgCaseMCSPQueryEncLength {s r : ℕ → ℕ}
    (hs : SubexponentiallyBounded s) (hr : SubexponentiallyBounded r) :
    SubexponentiallyBounded (fun n => avgCaseMCSPQueryEncLength n (s n) (r n)) := by
  have hq := (subexponentiallyBounded_computableFunctionsLogBound hs).add hr
  have h8n : SubexponentiallyBounded (fun n => 8 * n + 10) :=
    ((SubexponentiallyBounded.const 8).mul SubexponentiallyBounded.id).add (.const 10)
  have h4n : SubexponentiallyBounded (fun n => 4 * n + 3) :=
    ((SubexponentiallyBounded.const 4).mul SubexponentiallyBounded.id).add (.const 3)
  exact (h4n.add (hq.mul h8n)).add hs

open Classical in
/-- Asymptotic forward form of the finite one-sided projection
[OliveiraSanthanam2018, Section 3.3, Theorem 27, p. 21]. The formula accepts all small-circuit
truth tables; its acceptance set is the unknown set of the zero-error device. -/
theorem eventually_exists_formula_zero_error_average_case_of_mem_FormulaPoly
    {s r : ℕ → ℕ} (hs : SubexponentiallyBounded s) (hr : SubexponentiallyBounded r)
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    (hL : L ∈ FormulaPoly) (d : ℕ) (hd : 0 < d) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ 2 ^ (n / d) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - r n) := by
  obtain ⟨c, hc⟩ := mem_FormulaPoly_iff_exists_mem_FormulaSIZE.mp hL
  have hquery := subexponentiallyBounded_avgCaseMCSPQueryEncLength hs hr
  have hbound : SubexponentiallyBounded
      (fun n => c * (avgCaseMCSPQueryEncLength n (s n) (r n) + 1) ^ c) :=
    (SubexponentiallyBounded.const c).mul ((hquery.add (.const 1)).pow c)
  have hsample := (subexponentiallyBounded_computableFunctionsLogBound hs).add hr
  filter_upwards [hsample.eventually_le_two_pow_div 1 (by decide),
    hbound.eventually_le_two_pow_div d hd] with n hn hsize
  have ht : computableFunctionsLogBound n (s n) + r n ≤ 2 ^ n := by
    simpa only [Nat.div_one] using hn
  obtain ⟨F, hF, hyes, hcard⟩ := exists_formula_zero_error_average_case_of_agrees hag ht
  exact ⟨F, hF.trans ((hc _).trans hsize), hyes, hcard⟩

open Classical in
/-- Subexponential-threshold one-sided average-case hardness at arbitrarily large lengths
rules out polynomial-size formulas for any binary language agreeing with succinct MCSP.
The loss is `r = n`, so at most a `2 ^ (-n)` fraction of truth tables are unknown. -/
theorem not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard
    {s : ℕ → ℕ} (hs : SubexponentiallyBounded s) {d : ℕ} (hd : 0 < d)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) →
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - n) →
      2 ^ (n / d) < F.leafSize)
    {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L) :
    L ∉ FormulaPoly := by
  intro hL
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_exists_formula_zero_error_average_case_of_mem_FormulaPoly
      hs SubexponentiallyBounded.id hag hL d hd)
  obtain ⟨n, hn, hhardn⟩ := hhard N
  obtain ⟨F, hF, hyes, hcard⟩ := hN n hn
  exact (hhardn F hyes hcard).not_ge hF

open Classical in
/-- A fixed-exponent one-sided average-case formula lower bound for a subexponential MCSP
threshold yields a binary NP language without polynomial-size De Morgan formulas. The language
agrees with succinct MCSP on encoded instances; its other words use the existing total verifier.
This does not require the canonical encoding image itself to be a binary NP language. -/
theorem exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard
    {s : ℕ → ℕ} (hs : SubexponentiallyBounded s) {d : ℕ} (hd : 0 < d)
    (hhard : ∀ N : ℕ, ∃ n ≥ N, ∀ F : Formula signature (2 ^ n),
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet s →
        F.eval interpretation T = true) →
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - n) →
      2 ^ (n / d) < F.leafSize) :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ Complexity.NP Turing.MultiTapeTM.encBits ∧
      L ∉ FormulaPoly := by
  obtain ⟨L, hL, hag⟩ := SuccinctMCSP.exists_language_mem_NP
  exact ⟨L, hL, not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard hs hd hhard hag⟩

end Cslib.Circuits.Boolean
