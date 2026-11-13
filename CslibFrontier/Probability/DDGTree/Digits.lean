/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.DDGTree.Biased
public import Cslib.Foundations.Data.Nat.PolynomialBound
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A coin of any bias from fair bits, by comparing with its binary digits

Let `d : ℕ → Bool` be a binary expansion of `ρ = ∑ᵢ dᵢ 2^{-(i+1)}`. Every `ρ ∈ [0, 1]` has one;
`ρ = 1` uses the expansion `0.111⋯`. The tree `coinOfDigits d` reads fair bits
`b₀ b₁ ⋯` and compares them with `d₀ d₁ ⋯`. At the first index `i` with `bᵢ ≠ dᵢ` it outputs `dᵢ`,
that is, whether the uniform number `0.b₀b₁⋯` lies below `ρ`. It outputs `true` with probability
exactly `ρ` (`coinOfDigits_generates`). It is still running after `n` flips exactly when the first
`n` bits match, with probability `2⁻ⁿ`. Hence it reads exactly `2` bits in expectation
(`expectedFlips_coinOfDigits`), independently of `ρ`
([Arora and Barak, Lemma 7.14]).

The digit `dₙ` is needed only when flip `n + 1` is read. If computing it costs `w n`, the expected
total digit cost is `∑ₙ w n 2⁻ⁿ` (`expectedCostWith_coinOfDigits`), which is finite for every
polynomially bounded `w` (`expectedCostWith_coinOfDigits_lt_top`). This is the expected-`O(1)`
bound of the lemma for a fixed `ρ` whose digits are computable in polynomial time.
`Cslib.Probability.DDGTree.exists_digitTime_expectedCostWith_coinOfDigits_lt_top` instantiates
`w` with the time bound of a multitape machine computing the digits.

## Main definitions

* `Cslib.Probability.DDGTree.coinOfDigits`: the digit-comparison tree.

## Main results

* `Cslib.Probability.DDGTree.coinOfDigits_generates`: it generates the coin of bias `ρ`.
* `Cslib.Probability.DDGTree.expectedFlips_coinOfDigits`: exactly `2` expected fair bits.
* `Cslib.Probability.DDGTree.expectedCostWith_coinOfDigits`,
  `Cslib.Probability.DDGTree.expectedCostWith_coinOfDigits_lt_top`: geometrically weighted digit
  costs, finite for polynomially bounded costs.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Lemma 7.14
  (2007 draft numbering).
-/

public section

open scoped ENNReal unitInterval
open Filter Topology

namespace Cslib.Probability

namespace DDGTree

/-- Compare fair bits with the digits `d`, and output the digit at the first disagreement. -/
@[expose] def coinOfDigitsOutput : (ℕ → Bool) → List Bool → Option Bool
  | _, [] => none
  | d, b :: w => if b = d 0 then coinOfDigitsOutput (fun i => d (i + 1)) w else some (d 0)

theorem coinOfDigitsOutput_append_singleton :
    ∀ (d : ℕ → Bool) (w : List Bool) (a x : Bool), coinOfDigitsOutput d w = some a →
      coinOfDigitsOutput d (w ++ [x]) = some a
  | _, [], _, _, h => by simp [coinOfDigitsOutput] at h
  | d, b :: w, a, x, h => by
    by_cases hb : b = d 0
    · simp only [coinOfDigitsOutput, hb, ↓reduceIte, List.cons_append] at h ⊢
      exact coinOfDigitsOutput_append_singleton _ w a x h
    · simpa [coinOfDigitsOutput, hb] using h

/-- The tree that compares fair bits with the binary digits `d` of a bias and outputs the digit at
the first disagreement. -/
@[expose] def coinOfDigits (d : ℕ → Bool) : DDGTree Bool where
  output := coinOfDigitsOutput d
  output_append_singleton := coinOfDigitsOutput_append_singleton d

/-- The masses after `n` fair bits: still comparing with probability `2⁻ⁿ`, and having output `x`
with the probability of the first disagreement among the first `n` digits being at a digit `x`. -/
theorem run_coinOfDigits (n : ℕ) :
    ∀ d : ℕ → Bool, (coinOfDigits d).run n none = 2⁻¹ ^ n ∧
      ∀ x, (coinOfDigits d).run n (some x) =
        ∑ i ∈ Finset.range n, if d i = x then (2⁻¹ : ℝ≥0∞) ^ (i + 1) else 0 := by
  induction n with
  | zero => intro d; simp [coinOfDigits, coinOfDigitsOutput]
  | succ n ih =>
    intro d
    have hsame : (coinOfDigits d).child (d 0) = coinOfDigits (fun i => d (i + 1)) := by
      ext w
      simp [coinOfDigits, coinOfDigitsOutput]
    have hdiff : ((coinOfDigits d).child (!d 0)).run n = PMF.pure (some (d 0)) :=
      run_eq_pure_of_output_nil (by simp [coinOfDigits, coinOfDigitsOutput]) n
    obtain ⟨ihn, ihs⟩ := ih (fun i => d (i + 1))
    have hstep : ∀ o, (coinOfDigits d).run (n + 1) o =
        2⁻¹ * (coinOfDigits fun i => d (i + 1)).run n o + 2⁻¹ * PMF.pure (some (d 0)) o := by
      intro o
      rw [run_succ, PMF.bind_apply, tsum_bool]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_bool, Nat.cast_ofNat]
      cases h0 : d 0
      · have h1 := hsame; have h2 := hdiff
        rw [h0] at h1 h2
        rw [Bool.not_false] at h2
        rw [h1, h2]
      · have h1 := hsame; have h2 := hdiff
        rw [h0] at h1 h2
        rw [Bool.not_true] at h2
        rw [h1, h2, add_comm]
    refine ⟨?_, fun x => ?_⟩
    · rw [hstep, ihn]
      simp [pow_succ']
    · rw [hstep, ihs, Finset.sum_range_succ', Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp [pow_succ']
      · by_cases hx : d 0 = x
        · simp [hx]
        · simp [hx, PMF.pure_apply, Ne.symm hx]

/-- The comparison stops with probability one: it is running after `n` bits with probability
`2⁻ⁿ`. -/
theorem run_coinOfDigits_none (d : ℕ → Bool) (n : ℕ) : (coinOfDigits d).run n none = 2⁻¹ ^ n :=
  (run_coinOfDigits n d).1

theorem outputProb_coinOfDigits (d : ℕ → Bool) (x : Bool) :
    (coinOfDigits d).outputProb x = ∑' i, if d i = x then (2⁻¹ : ℝ≥0∞) ^ (i + 1) else 0 := by
  rw [ENNReal.tsum_eq_iSup_nat, outputProb]
  simp only [(run_coinOfDigits _ d).2]

/-- **Exact biased coin from fair bits** ([Arora and Barak, Lemma 7.14]): if `d` is a binary
expansion of `ρ`, the digit-comparison tree generates the coin of bias `ρ`. -/
theorem coinOfDigits_generates {d : ℕ → Bool} {ρ : I}
    (hd : HasSum (fun i => if d i then (2⁻¹ : ℝ) ^ (i + 1) else 0) ρ) :
    (coinOfDigits d).Generates (PMF.coin ρ) := by
  have htrue : (coinOfDigits d).outputProb true = ENNReal.ofReal ρ := by
    rw [outputProb_coinOfDigits, ← hd.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hd.summable]
    refine tsum_congr fun i => ?_
    split_ifs <;> simp [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos, ENNReal.inv_pow]
  have hall : (coinOfDigits d).outputProb true + (coinOfDigits d).outputProb false = 1 := by
    rw [outputProb_coinOfDigits, outputProb_coinOfDigits, ← tsum_add]
    have : ∀ i, ((if d i = true then (2⁻¹ : ℝ≥0∞) ^ (i + 1) else 0) +
        if d i = false then (2⁻¹ : ℝ≥0∞) ^ (i + 1) else 0) = 2⁻¹ ^ (i + 1) := by
      intro i; cases d i <;> simp
    simp only [this, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top
  intro x
  cases x
  · rw [PMF.coin_apply, ite_eq_right Bool.false_ne_true, ENNReal.ofReal_sub _ ρ.2.1,
      ENNReal.ofReal_one, ← htrue, ← hall, ENNReal.add_sub_cancel_left]
    exact htrue ▸ ENNReal.ofReal_ne_top
  · rw [PMF.coin_apply, ite_eq_left rfl, htrue]

/-- Expected total digit cost: with cost `w n` for the digit compared at flip `n + 1`, the expected
cost is `∑ₙ w n 2⁻ⁿ`. -/
theorem expectedCostWith_coinOfDigits (d : ℕ → Bool) (w : ℕ → ℝ≥0∞) :
    (coinOfDigits d).expectedCostWith (PMF.uniformOfFintype Bool) w = ∑' n, w n * 2⁻¹ ^ n := by
  simp [expectedCostWith, ← run_eq_runWith, run_coinOfDigits_none]

/-- **Expected two fair bits** ([Arora and Barak, Lemma 7.14]): the comparison reads exactly two
fair bits in expectation, for every bias. -/
theorem expectedFlips_coinOfDigits (d : ℕ → Bool) : (coinOfDigits d).expectedFlips = 2 := by
  rw [expectedFlips_eq_expectedFlipsWith, expectedFlipsWith_eq_expectedCostWith,
    expectedCostWith_coinOfDigits]
  simp [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two]

/-- A polynomially bounded digit cost has finite expectation. -/
theorem expectedCostWith_coinOfDigits_lt_top (d : ℕ → Bool) {w : ℕ → ℕ}
    (hw : PolynomiallyBounded w) :
    (coinOfDigits d).expectedCostWith (PMF.uniformOfFintype Bool) (fun n => w n) < ⊤ := by
  obtain ⟨C, k, hC⟩ := polynomiallyBounded_iff_le.mp hw
  rw [expectedCostWith_coinOfDigits]
  have hsum : Summable fun n : ℕ => (C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k * 2⁻¹ ^ n := by
    have hg : Summable fun m : ℕ => (m : ℝ) ^ k * 2⁻¹ ^ m :=
      summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)
    have hg1 := (summable_nat_add_iff 1).mpr hg
    refine (hg1.mul_left ((2 : ℝ) * C)).congr fun n => ?_
    simp only [pow_succ]
    push_cast
    ring_nf
  calc ∑' n, (w n : ℝ≥0∞) * 2⁻¹ ^ n
      ≤ ∑' n : ℕ, ENNReal.ofReal ((C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k * 2⁻¹ ^ n) := by
        refine tsum_le_tsum fun n => ?_
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hC n)
    _ = ENNReal.ofReal (∑' n : ℕ, (C : ℝ) * ((n + 1 : ℕ) : ℝ) ^ k * 2⁻¹ ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end DDGTree

end Cslib.Probability
