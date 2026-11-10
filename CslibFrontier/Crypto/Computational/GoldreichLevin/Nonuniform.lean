/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldreichLevin.Decoding
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Foundations.Data.BitString.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Nonuniform Goldreich–Levin decoding

Goldreich–Levin decoding [GoldreichLevin1989] recovers a string `x` from a predictor for its
parities `x ⬝ r` with agreement `1 / 2 + ε`, with probability at least `1 / 2` over random masks
and for one of `2 ^ k` guesses (`Cslib.Crypto.GoldreichLevin.decode_failure_le_half`). This module
turns that into a statement about fixed choices, as needed for nonuniform reconstruction: for a
family of predictors `pred x` with targets `target x`, if a set `good` of indices has agreement at
least `1 / 2 + ε`, then one fixed choice of masks and of the guess makes the corrected-majority
candidate equal to the target for at least `#good / 2 ^ (k + 1)` of the indices
(`Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq`). The proof averages the success
probability over the masks and over a uniformly random guess.

## Main results

* `Cslib.Crypto.GoldreichLevin.agreement_eq_card_div`: agreement as a count.
* `Cslib.Crypto.GoldreichLevin.card_le_two_mul_card_filter_mem_candidates`: the counting form of
  the decoding guarantee.
* `Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq`: fixed masks and guess recover a
  `1 / 2 ^ (k + 1)` fraction of the good targets.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Finset Cslib.Probability MeasureTheory
open scoped ENNReal

variable {n k : ℕ}

/-- **Agreement as a count**: the fraction of queries on which the predictor is right. -/
theorem agreement_eq_card_div (predictor : BitString n → Bool) (x : BitString n) :
    agreement predictor x = (#{r | predictor r = x ⬝ᵥ r} : ℝ) / 2 ^ n := by
  rw [agreement, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, smul_eq_mul, score, mul_ite, mul_one, mul_zero]
  rw [← sum_filter, sum_const, nsmul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp [BitString, div_eq_mul_inv]

/-- **The decoding guarantee in counting form.** If a predictor agrees with the parities of `x` on
a `1 / 2 + ε` fraction of queries and `n ≤ 2 * ε ^ 2 * (2 ^ k - 1)`, then `x` is a candidate for at
least half of the choices of the `k` masks. -/
theorem card_le_two_mul_card_filter_mem_candidates (predictor : BitString n → Bool)
    (x : BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ agreement predictor x)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) :
    Fintype.card (Fin k → BitString n) ≤
      2 * #{masks : Fin k → BitString n | x ∈ candidates predictor masks} := by
  classical
  have hfail := decode_failure_le_half predictor x ε hε hk h hsize
  rw [decode, PMF.toOuterMeasure_map_apply,
    show (candidates predictor ⁻¹' {list | x ∉ list}) = {masks | x ∉ candidates predictor masks}
      from rfl, PMF.toOuterMeasure_uniformOfFintype] at hfail
  have hne : (Fintype.card (Fin k → BitString n) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← div_eq_mul_inv, ENNReal.div_le_iff hne (ENNReal.natCast_ne_top _)] at hfail
  have hfail' : (#{masks : Fin k → BitString n | x ∉ candidates predictor masks} : ℝ≥0∞) ≤
      1 / 2 * Fintype.card (Fin k → BitString n) := by simpa using hfail
  have hbad : 2 * #{masks : Fin k → BitString n | x ∉ candidates predictor masks} ≤
      Fintype.card (Fin k → BitString n) := by
    have h2 : (2 : ℝ≥0∞) * #{masks : Fin k → BitString n | x ∉ candidates predictor masks} ≤
        Fintype.card (Fin k → BitString n) := by
      calc (2 : ℝ≥0∞) * #{masks : Fin k → BitString n | x ∉ candidates predictor masks}
          ≤ 2 * (1 / 2 * Fintype.card (Fin k → BitString n)) := by gcongr
        _ = Fintype.card (Fin k → BitString n) := by
            rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
              one_mul]
    exact_mod_cast h2
  have hsplit := card_filter_add_card_filter_not
    (s := (univ : Finset (Fin k → BitString n))) (fun masks => x ∈ candidates predictor masks)
  rw [card_univ] at hsplit
  omega

/-- **Nonuniform Goldreich–Levin decoding.** Let `pred x` be predictors for the parities of
`target x`, indexed by a finite type, and let every index of `good` have agreement at least
`1 / 2 + ε`, with `n ≤ 2 * ε ^ 2 * (2 ^ k - 1)` and `k ≥ 1`. Then for some fixed masks and guess the
corrected-majority candidate equals the target for at least `#good / 2 ^ (k + 1)` indices. -/
theorem exists_card_candidate_eq {X : Type*} [Fintype X] (pred : X → BitString n → Bool)
    (target : X → BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) (good : Finset X)
    (hgood : ∀ x ∈ good, 1 / 2 + ε ≤ agreement (pred x) (target x)) :
    ∃ (masks : Fin k → BitString n) (guess : BitString k),
      #good ≤ 2 ^ (k + 1) * #{x | candidate (pred x) masks guess = target x} := by
  classical
  by_contra hcon
  push Not at hcon
  -- the number of successes summed over all masks and guesses
  set M := Fintype.card (Fin k → BitString n)
  have hsum : #good * M ≤ 2 * ∑ mg : (Fin k → BitString n) × BitString k,
      #{x | candidate (pred x) mg.1 mg.2 = target x} := by
    have hswap : ∑ mg : (Fin k → BitString n) × BitString k,
        #{x | candidate (pred x) mg.1 mg.2 = target x} =
          ∑ x, #{mg : (Fin k → BitString n) × BitString k |
            candidate (pred x) mg.1 mg.2 = target x} := by
      simp only [card_filter]
      exact sum_comm
    rw [hswap]
    calc #good * M = ∑ _x ∈ good, M := by rw [sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ good, 2 * #{masks : Fin k → BitString n | target x ∈ candidates (pred x) masks} :=
          sum_le_sum fun x hx => card_le_two_mul_card_filter_mem_candidates (pred x) (target x)
            ε hε hk (hgood x hx) hsize
      _ ≤ ∑ x ∈ good, 2 * #{mg : (Fin k → BitString n) × BitString k |
            candidate (pred x) mg.1 mg.2 = target x} := by
          refine sum_le_sum fun x _ => Nat.mul_le_mul_left 2 ?_
          refine card_le_card_of_injOn (fun masks =>
            (masks, if h : target x ∈ candidates (pred x) masks then
              (mem_image.1 h).choose else 0)) (fun masks hm => ?_) (fun _ _ _ _ h =>
                (Prod.ext_iff.1 h).1)
          rw [mem_coe, mem_filter] at hm ⊢
          refine ⟨mem_univ _, ?_⟩
          simp only [dite_eq_left hm.2]
          exact (mem_image.1 hm.2).choose_spec.2
      _ ≤ 2 * ∑ x, #{mg : (Fin k → BitString n) × BitString k |
            candidate (pred x) mg.1 mg.2 = target x} := by
          rw [← mul_sum]
          exact Nat.mul_le_mul_left 2 (sum_le_sum_of_subset (subset_univ _))
  have hlt : 2 ^ (k + 1) * ∑ mg : (Fin k → BitString n) × BitString k,
      #{x | candidate (pred x) mg.1 mg.2 = target x} <
        ∑ _mg : (Fin k → BitString n) × BitString k, #good := by
    rw [mul_sum]
    have : (univ : Finset ((Fin k → BitString n) × BitString k)).Nonempty := univ_nonempty
    exact sum_lt_sum_of_nonempty this fun mg _ => hcon mg.1 mg.2
  rw [sum_const, card_univ, Fintype.card_prod, smul_eq_mul] at hlt
  have hG : Fintype.card (BitString k) = 2 ^ k := BitString.card
  rw [hG] at hlt
  have : 2 ^ (k + 1) * ∑ mg : (Fin k → BitString n) × BitString k,
      #{x | candidate (pred x) mg.1 mg.2 = target x} ≥ 2 ^ k * (#good * M) := by
    rw [pow_succ, mul_comm (2 ^ k) 2, mul_assoc]
    nlinarith [hsum]
  nlinarith

end Cslib.Crypto.GoldreichLevin
