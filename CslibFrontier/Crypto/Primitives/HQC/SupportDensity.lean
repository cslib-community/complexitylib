/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.HQC.SupportSampling
public import CslibFrontier.Languages.Probabilistic.Expect
public import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Probability.PMF.Event

/-!
# Finite-bit density bounds for HQC support sampling

## Main definitions

* `Cslib.Crypto.HQC.supportLowerDensity`, `Cslib.Crypto.HQC.supportUpperDensity`: products of
  the per-word floor-count and floor-plus-one-count density factors.

## Main results

* `Cslib.Crypto.HQC.sampleSupport2_density_bounds`: the actual finite-bit product bounds.
* `Cslib.Crypto.HQC.sampleSupport2_expect_bounds`, `Cslib.Crypto.HQC.sampleSupport2_payoff_bounds`:
  extended nonnegative and finite real-valued nonnegative payoff bounds.
* `Cslib.Crypto.HQC.sampleSupport2_event_bounds`: the same factors bound every event.
* `Cslib.Crypto.HQC.supportLowerDensity_toReal`, `Cslib.Crypto.HQC.supportUpperDensity_toReal`:
  equality with the source's remainder expressions.

## References

* [HQC specification, version 5.1][HQC2026], §6.2.3, Proposition 6.2.1 and Lemma 6.5, p. 65.
  The density bounds assume independent uniform words. The payoff corollary needs nonnegative
  values; the printed claim for arbitrary real-valued payoffs is false.
-/

public section

namespace Cslib.Crypto.HQC

open Finset Probability
open scoped ENNReal

/-- Product of the minimum fibre counts, divided by the ideal uniform point masses.
For `M = 2^width` and `d = n - (offset + j)`, each factor is `1 - (M % d) / M`. -/
@[expose] noncomputable def supportLowerDensity (width n offset count : ℕ) : ℝ≥0∞ :=
  ∏ j : Fin count,
    (((2 ^ width / (n - (offset + j.val)) * (n - (offset + j.val)) : ℕ) : ℝ≥0∞) /
      (2 ^ width : ℕ))

/-- Product of the upper fibre counts, divided by the ideal uniform point masses.
Each factor is `1 + (d - (M % d)) / M`, including the source's slack when the remainder is zero. -/
@[expose] noncomputable def supportUpperDensity (width n offset count : ℕ) : ℝ≥0∞ :=
  ∏ j : Fin count,
    ((((2 ^ width / (n - (offset + j.val)) + 1) * (n - (offset + j.val)) : ℕ) : ℝ≥0∞) /
      (2 ^ width : ℕ))

/-- Exact fibre bounds for one actual word, compared with its ideal interval draw. -/
theorem sampleCandidate_density_bounds {width n offset : ℕ} (h : offset < n) (r : ℕ) :
    (((2 ^ width / (n - offset) * (n - offset) : ℕ) : ℝ≥0∞) / (2 ^ width : ℕ)) *
        ProbComp.eval (idealCandidate n offset) r ≤
      ProbComp.eval (sampleCandidate width n offset) r ∧
    ProbComp.eval (sampleCandidate width n offset) r ≤
      ((((2 ^ width / (n - offset) + 1) * (n - offset) : ℕ) : ℝ≥0∞) /
        (2 ^ width : ℕ)) * ProbComp.eval (idealCandidate n offset) r := by
  let : NeZero (n - offset) := ⟨by omega⟩
  have hd : 0 < n - offset := by omega
  have hM : 0 < 2 ^ width := by positivity
  have hword := PMF.uniformOfFintype_mul_div_bounds hM hd
  have hlo := PMF.mul_map_apply_le (fun k => (hword k).1)
    (fun k : Fin (n - offset) => offset + k.val) r
  have hhi := PMF.map_apply_le_mul (fun k => (hword k).2)
    (fun k : Fin (n - offset) => offset + k.val) r
  simp only [eval_sampleCandidate, idealCandidate, dite_eq_left h,
    ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def] at *
  exact ⟨hlo, hhi⟩

/-- The independent word factors multiply through the actual collision-replacement program. -/
theorem sampleSupportFrom_density_bounds {width n offset count : ℕ} (h : offset + count ≤ n)
    (S : Finset ℕ) :
    supportLowerDensity width n offset count *
        ProbComp.eval (sampleSupportFrom (idealCandidate n) offset count) S ≤
      ProbComp.eval (sampleSupportFrom (sampleCandidate width n) offset count) S ∧
    ProbComp.eval (sampleSupportFrom (sampleCandidate width n) offset count) S ≤
      supportUpperDensity width n offset count *
        ProbComp.eval (sampleSupportFrom (idealCandidate n) offset count) S := by
  induction count generalizing offset S with
  | zero =>
    simp only [supportLowerDensity, supportUpperDensity, Fin.prod_univ_zero, one_mul,
      sampleSupportFrom, OracleComp.pi_zero]
    exact ⟨le_rfl, le_rfl⟩
  | succ count ih =>
    have hoff : offset < n := by omega
    have htail : offset + 1 + count ≤ n := by omega
    have hlo := PMF.mul_bind_apply_le_of_mul_le
      (fun r => (sampleCandidate_density_bounds (width := width) hoff r).1)
      (fun r T => PMF.mul_map_apply_le (fun U => (ih htail U).1)
        (fun U => U.collisionInsert offset r) T) S
    have hhi := PMF.bind_apply_le_mul_of_le_mul
      (fun r => (sampleCandidate_density_bounds (width := width) hoff r).2)
      (fun r T => PMF.map_apply_le_mul (fun U => (ih htail U).2)
        (fun U => U.collisionInsert offset r) T) S
    rw [eval_sampleSupportFrom_succ, eval_sampleSupportFrom_succ]
    simpa only [supportLowerDensity, supportUpperDensity, Fin.prod_univ_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using
      And.intro hlo hhi

/-- **HQC Proposition 6.2.1:** actual fixed-width sampling is sandwiched between the two
explicit product factors times the uniform fixed-weight law. This also covers weight zero. -/
theorem sampleSupport2_density_bounds {width n count : ℕ} (h : count ≤ n) (S : Finset ℕ) :
    supportLowerDensity width n 0 count *
        PMF.uniformOfFinset ((range n).powersetCard count)
          (powersetCard_nonempty.mpr (by simpa only [card_range] using h)) S ≤
      ProbComp.eval (sampleSupport2 width n count) S ∧
    ProbComp.eval (sampleSupport2 width n count) S ≤
      supportUpperDensity width n 0 count *
        PMF.uniformOfFinset ((range n).powersetCard count)
          (powersetCard_nonempty.mpr (by simpa only [card_range] using h)) S := by
  have hb := sampleSupportFrom_density_bounds (width := width) (offset := 0) (by omega :
    0 + count ≤ n) S
  rw [eval_idealSupport (by omega)] at hb
  simpa only [sampleSupport2, Nat.Ico_zero_eq_range] using hb

/-- The upper density is finite, so converting its bounds to real probabilities is sound. -/
theorem supportUpperDensity_ne_top (width n offset count : ℕ) :
    supportUpperDensity width n offset count ≠ ⊤ := by
  apply ENNReal.prod_ne_top
  intro j _
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)

/-- **Corrected HQC Lemma 6.5:** the density bounds transfer to every nonnegative payoff.
Using extended nonnegative values also permits unbounded payoffs without summability premises. -/
theorem sampleSupport2_expect_bounds {width n count : ℕ} (h : count ≤ n)
    (V : Finset ℕ → ℝ≥0∞) :
    supportLowerDensity width n 0 count *
        ProbComp.expect (sampleSupportFrom (idealCandidate n) 0 count) V ≤
      ProbComp.expect (sampleSupport2 width n count) V ∧
    ProbComp.expect (sampleSupport2 width n count) V ≤
      supportUpperDensity width n 0 count *
        ProbComp.expect (sampleSupportFrom (idealCandidate n) 0 count) V := by
  have hb := sampleSupportFrom_density_bounds (width := width) (offset := 0)
    (by omega : 0 + count ≤ n)
  constructor
  · simp only [ProbComp.expect, ← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun S => by
      simpa only [sampleSupport2, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_right (hb S).1 (V S)
  · simp only [ProbComp.expect, ← ENNReal.tsum_mul_left]
    exact tsum_le_tsum fun S => by
      simpa only [sampleSupport2, mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_right (hb S).2 (V S)

/-- Every event probability obeys the same bounds, stated with the program-level probability
notation. No event-specific sampling or cryptographic hypothesis is required. -/
theorem sampleSupport2_event_bounds {width n count : ℕ} (h : count ≤ n)
    (E : Set (Finset ℕ)) [DecidablePred (· ∈ E)] :
    (supportLowerDensity width n 0 count).toReal *
        Pr[(fun S => decide (S ∈ E)) <$> sampleSupportFrom (idealCandidate n) 0 count] ≤
      Pr[(fun S => decide (S ∈ E)) <$> sampleSupport2 width n count] ∧
    Pr[(fun S => decide (S ∈ E)) <$> sampleSupport2 width n count] ≤
      (supportUpperDensity width n 0 count).toReal *
        Pr[(fun S => decide (S ∈ E)) <$> sampleSupportFrom (idealCandidate n) 0 count] := by
  have hb := sampleSupport2_expect_bounds (width := width) h (E.indicator 1)
  simp only [ProbComp.expect, ← PMF.toOuterMeasure_eq_tsum_mul_indicator] at hb
  simp only [ProbComp.probability_map_decide_mem]
  constructor
  · simpa only [ENNReal.toReal_mul] using
      ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) hb.1
  · simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top (supportUpperDensity_ne_top width n 0 count)
        (PMF.toOuterMeasure_ne_top _ _)) hb.2

/-- The finite real-valued expectation form of corrected Lemma 6.5. Only values on valid
supports must be nonnegative, since both samplers are supported there. -/
theorem sampleSupport2_payoff_bounds {width n count : ℕ} (h : count ≤ n)
    (V : Finset ℕ → ℝ) (hV : ∀ S ∈ (range n).powersetCard count, 0 ≤ V S) :
    (supportLowerDensity width n 0 count).toReal *
        (∑ S ∈ (range n).powersetCard count,
          Pr[(· == S) <$> sampleSupportFrom (idealCandidate n) 0 count] * V S) ≤
      ∑ S ∈ (range n).powersetCard count, Pr[(· == S) <$> sampleSupport2 width n count] * V S ∧
    (∑ S ∈ (range n).powersetCard count,
        Pr[(· == S) <$> sampleSupport2 width n count] * V S) ≤
      (supportUpperDensity width n 0 count).toReal *
        ∑ S ∈ (range n).powersetCard count,
          Pr[(· == S) <$> sampleSupportFrom (idealCandidate n) 0 count] * V S := by
  have hb := sampleSupportFrom_density_bounds (width := width) (offset := 0)
    (by omega : 0 + count ≤ n)
  simp only [ProbComp.probability_map_beq, Finset.mul_sum, ← mul_assoc]
  constructor
  · apply Finset.sum_le_sum
    intro S hS
    apply mul_le_mul_of_nonneg_right _ (hV S hS)
    simpa only [sampleSupport2, ENNReal.toReal_mul] using
      ENNReal.toReal_mono (PMF.apply_ne_top _ _) (hb S).1
  · apply Finset.sum_le_sum
    intro S hS
    apply mul_le_mul_of_nonneg_right _ (hV S hS)
    simpa only [sampleSupport2, ENNReal.toReal_mul] using ENNReal.toReal_mono
      (ENNReal.mul_ne_top (supportUpperDensity_ne_top width n 0 count) (PMF.apply_ne_top _ _))
      (hb S).2

private theorem lower_factor_real {M d : ℕ} (hM : 0 < M) :
    (((M / d * d : ℕ) : ℝ) / M) = 1 - (M % d : ℕ) / (M : ℝ) := by
  have heq : ((M / d * d : ℕ) : ℝ) + (M % d : ℕ) = (M : ℝ) := by
    exact_mod_cast (by simpa only [Nat.mul_comm] using Nat.div_add_mod M d)
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp
  linarith

private theorem upper_factor_real {M d : ℕ} (hM : 0 < M) (hd : 0 < d) :
    ((((M / d + 1) * d : ℕ) : ℝ) / M) = 1 + ((d : ℝ) - (M % d : ℕ)) / (M : ℝ) := by
  have heq : (M / d + 1) * d = M + (d - M % d) := by
    have hm := Nat.mod_lt M hd
    have hdiv := Nat.div_add_mod M d
    rw [Nat.mul_comm d (M / d)] at hdiv
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [heq, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt M hd)), add_div,
    div_self hM']

/-- The proved lower factors are exactly the remainder factors printed in Equation (16). -/
theorem supportLowerDensity_toReal (width n offset count : ℕ) :
    (supportLowerDensity width n offset count).toReal =
      ∏ j : Fin count, (1 - (2 ^ width % (n - (offset + j.val)) : ℕ) / (2 ^ width : ℝ)) := by
  rw [supportLowerDensity, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    lower_factor_real (M := 2 ^ width) (d := n - (offset + j.val)) (by positivity)

/-- The proved upper factors retain precisely the slack printed in Equation (16). -/
theorem supportUpperDensity_toReal {width n offset count : ℕ} (h : offset + count ≤ n) :
    (supportUpperDensity width n offset count).toReal =
      ∏ j : Fin count,
        (1 + ((n - (offset + j.val) : ℕ) -
          (2 ^ width % (n - (offset + j.val)) : ℕ)) / (2 ^ width : ℝ)) := by
  rw [supportUpperDensity, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    Nat.cast_pow, Nat.cast_ofNat]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    upper_factor_real (M := 2 ^ width) (d := n - (offset + j.val)) (by positivity)
      (by have := j.isLt; omega)

end Cslib.Crypto.HQC
