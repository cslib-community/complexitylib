/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.BitString.BinarySymmetricChannel
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Order.Filter.AtTopBot.Defs
import Complexity.Probability.BitString.BinarySymmetricChannel.Achievability
import Complexity.Probability.BitString.BinarySymmetricChannel.StrongConverse
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The capacity of the binary symmetric channel

A rate `R` is *achievable* on the binary symmetric channel `BSC_p`
(`Cslib.BitString.IsAchievableRate`) if for every `ε > 0` and all sufficiently large `n` some code
with `2 ^ ⌈R n⌉₊` codewords of length `n` and some decoder have *maximal* error probability at most
`ε`. Shannon's noisy-channel coding theorem for `BSC_p` says that the achievable rates are exactly
the rates below the capacity `1 - h₂(p)`, where `h₂(p) = Real.binEntropy p / Real.log 2` is the
binary entropy in bits: reliable communication is possible below capacity and impossible above it,
the notion of capacity in [Guruswami, Rudra and Sudan, Section 6.2.2][GuruswamiRudraSudan2019].

* Below capacity, `Cslib.BitString.eventually_exists_code_decodingError_le` (random codes,
  `p < 1 / 2`) gives achievability; rates `R ≤ 0` are achieved by a single codeword, and
  `p > 1 / 2` reduces to `1 - p` by complementing the received word
  (`Cslib.BitString.isAchievableRate_symm`).
* Above capacity, the strong converse
  (`Cslib.BitString.eventually_one_sub_le_expect_decodingError`) shows that even the average error
  tends to `1`.

So the capacity `1 - h₂(p)` is the least upper bound of the achievable rates
(`Cslib.BitString.isLUB_isAchievableRate`, `Cslib.BitString.sSup_isAchievableRate`), for every
`p ∈ [0, 1]`. Whether the capacity itself is achievable depends on second-order terms and is not
settled here; `Cslib.BitString.isAchievableRate_iff_lt` covers every other rate.

## Main definitions

* `Cslib.BitString.IsAchievableRate`: achievable rates on `BSC_p`.

## Main results

* `Cslib.BitString.isAchievableRate_of_lt`: rates below capacity are achievable.
* `Cslib.BitString.not_isAchievableRate_of_lt`: rates above capacity are not.
* `Cslib.BitString.isLUB_isAchievableRate`, `Cslib.BitString.sSup_isAchievableRate`: the capacity
  of `BSC_p` is `1 - h₂(p)`.

## References

* [C. E. Shannon, *A Mathematical Theory of Communication*][Shannon1948]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019], draft of
  26 August 2025
-/

public section

namespace Cslib.BitString

open Filter
open scoped BigOperators unitInterval

/-- A rate `R` is **achievable** on `BSC_p` if for every `ε > 0` and all sufficiently large `n`
there is a code with `2 ^ ⌈R n⌉₊` codewords of length `n` and a decoder whose maximal error
probability is at most `ε`. This notion is specific to the binary symmetric channel on bit strings;
general discrete memoryless channels would need their own definition. -/
@[expose] def IsAchievableRate (p : I) (R : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∃ (E : Fin (2 ^ ⌈R * n⌉₊) → BitString n)
    (D : BitString n → Fin (2 ^ ⌈R * n⌉₊)), ∀ m, decodingError p E D m ≤ ε

/-- Rates `R ≤ 0` are achievable: a single codeword is never misdecoded. -/
theorem isAchievableRate_of_nonpos (p : I) {R : ℝ} (hR : R ≤ 0) : IsAchievableRate p R := by
  intro ε hε
  refine Eventually.of_forall fun n => ?_
  have h0 : ⌈R * n⌉₊ = 0 := Nat.ceil_eq_zero.mpr (mul_nonpos_of_nonpos_of_nonneg hR n.cast_nonneg)
  have h1 : (2 : ℕ) ^ ⌈R * n⌉₊ = 1 := by rw [h0, pow_zero]
  have hsub : ∀ m m' : Fin (2 ^ ⌈R * n⌉₊), m = m' := fun m m' => by
    have hm : m.val < 1 := lt_of_lt_of_eq m.isLt h1
    have hm' : m'.val < 1 := lt_of_lt_of_eq m'.isLt h1
    ext
    omega
  refine ⟨fun _ _ => false, fun _ => ⟨0, by positivity⟩, fun m => ?_⟩
  classical
  rw [decodingError_eq_bernoulliAverage]
  have : (fun e : BitString n =>
      if (⟨0, by positivity⟩ : Fin (2 ^ ⌈R * n⌉₊)) ≠ m then (1 : ℝ) else 0) = fun _ => 0 :=
    funext fun _ => ite_eq_right fun h => absurd (hsub _ _) h
  rw [this, bernoulliAverage_const]
  exact hε.le

/-- Achievability on `BSC_p` and on `BSC_{1 - p}` are equivalent: complement the received word
before decoding. -/
theorem isAchievableRate_symm (p : I) (R : ℝ) :
    IsAchievableRate (σ p) R ↔ IsAchievableRate p R := by
  have key (q : I) : IsAchievableRate q R → IsAchievableRate (σ q) R := fun h ε hε =>
    (h ε hε).mono fun n ⟨E, D, hD⟩ =>
      ⟨E, fun y => D fun i => !y i, fun m => (decodingError_symm q E D m).trans_le (hD m)⟩
  exact ⟨fun h => unitInterval.symm_symm p ▸ key (σ p) h, key p⟩

/-- **Achievability**: every rate below the capacity `1 - h₂(p)` of `BSC_p` is achievable, for every
`p ∈ [0, 1]`. -/
theorem isAchievableRate_of_lt (p : I) {R : ℝ} (hR : R < 1 - Real.binEntropy p / Real.log 2) :
    IsAchievableRate p R := by
  rcases le_or_gt R 0 with hR0 | hR0
  · exact isAchievableRate_of_nonpos p hR0
  have key (q : I) (hq : (q : ℝ) < 1 / 2) (hRq : R < 1 - Real.binEntropy q / Real.log 2) :
      IsAchievableRate q R := fun ε hε =>
    (eventually_exists_code_decodingError_le q hq hRq hε).mono fun n ⟨E, hE⟩ => by
      have : Nonempty (Fin (2 ^ ⌈R * n⌉₊)) := ⟨⟨0, by positivity⟩⟩
      obtain ⟨D, hD⟩ := exists_isNearestDecoder E
      exact ⟨E, D, hE D hD⟩
  rcases lt_trichotomy (p : ℝ) (1 / 2) with hp | hp | hp
  · exact key p hp hR
  · rw [hp, one_div, Real.binEntropy_two_inv, div_self (Real.log_pos one_lt_two).ne',
      sub_self] at hR
    exact absurd hR0 (not_lt.mpr hR.le)
  · refine (isAchievableRate_symm p R).mp (key (σ p) ?_ ?_)
    · rw [unitInterval.coe_symm_eq]
      linarith
    · rwa [unitInterval.coe_symm_eq, Real.binEntropy_one_sub]

/-- **The converse**: no rate above the capacity `1 - h₂(p)` of `BSC_p` is achievable, for every
`p ∈ [0, 1]`. By the strong converse even the average error of such codes tends to `1`. -/
theorem not_isAchievableRate_of_lt (p : I) {R : ℝ} (hR : 1 - Real.binEntropy p / Real.log 2 < R) :
    ¬ IsAchievableRate p R := by
  intro h
  obtain ⟨n, ⟨E, D, hD⟩, hn⟩ :=
    ((h (1 / 4) (by norm_num)).and
      (eventually_one_sub_le_expect_decodingError p hR (ε := 1 / 2) (by norm_num))).exists
  have : Nonempty (Fin (2 ^ ⌈R * n⌉₊)) := ⟨⟨0, by positivity⟩⟩
  have hM : R * n ≤ Real.logb 2 (Fintype.card (Fin (2 ^ ⌈R * n⌉₊))) := by
    rw [Fintype.card_fin, Nat.cast_pow, Nat.cast_two, Real.logb_pow,
      Real.logb_self_eq_one one_lt_two, mul_one]
    exact Nat.le_ceil _
  have h1 := hn E D hM
  have h2 : 𝔼 m, decodingError p E D m ≤ 1 / 4 :=
    Finset.expect_le Finset.univ_nonempty fun m _ => hD m
  linarith

/-- **Shannon's noisy-channel coding theorem for the binary symmetric channel**: the capacity
`1 - h₂(p)` is the least upper bound of the achievable rates of `BSC_p`, for every `p ∈ [0, 1]`. -/
theorem isLUB_isAchievableRate (p : I) :
    IsLUB {R | IsAchievableRate p R} (1 - Real.binEntropy p / Real.log 2) :=
  ⟨fun _ hR => not_lt.mp fun h => not_isAchievableRate_of_lt p h hR,
    fun _ hb => le_of_forall_lt_imp_le_of_dense fun _ ha => hb (isAchievableRate_of_lt p ha)⟩

/-- **The capacity of `BSC_p` is `1 - h₂(p)`**: the supremum of its achievable rates. -/
theorem sSup_isAchievableRate (p : I) :
    sSup {R | IsAchievableRate p R} = 1 - Real.binEntropy p / Real.log 2 :=
  (isLUB_isAchievableRate p).csSup_eq ⟨0, isAchievableRate_of_nonpos p le_rfl⟩

/-- Away from the capacity, a rate is achievable on `BSC_p` exactly when it is below the capacity
`1 - h₂(p)`. -/
theorem isAchievableRate_iff_lt (p : I) {R : ℝ} (hR : R ≠ 1 - Real.binEntropy p / Real.log 2) :
    IsAchievableRate p R ↔ R < 1 - Real.binEntropy p / Real.log 2 :=
  ⟨fun h => lt_of_le_of_ne ((isLUB_isAchievableRate p).1 h) hR, isAchievableRate_of_lt p⟩

end Cslib.BitString
