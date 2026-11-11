/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldreichLevin.Decoding
public import Mathlib.Data.Finset.Density
import CslibFrontier.Foundations.Data.Finset.Sampling
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
probability over the masks and over a uniformly random guess
(`Cslib.Crypto.GoldreichLevin.card_mul_le_two_mul_sum_card_candidate_eq`).

The same sum gives a density form: a `#good / (2 ^ (k + 2) * #X)` fraction of the choices of
masks and guess each recover a `1 / 2 ^ (k + 2)` fraction of the good targets
(`Cslib.Crypto.GoldreichLevin.dens_filter_candidate_eq_ge`). Reverse averaging also finds the good
indices: if the predictors agree with the parities on a `1 / 2 + ε` fraction of all pairs, then an
`ε / 2` fraction of the indices have agreement `1 / 2 + ε / 2`
(`Cslib.Crypto.GoldreichLevin.dens_filter_agreement_ge`). Both use
`Fintype.expect_sub_le_dens_filter`.

## Main results

* `Cslib.Crypto.GoldreichLevin.agreement_eq_card_div`: agreement as a count.
* `Cslib.Crypto.GoldreichLevin.card_le_two_mul_card_filter_mem_candidates`: the counting form of
  the decoding guarantee.
* `Cslib.Crypto.GoldreichLevin.card_mul_le_two_mul_sum_card_candidate_eq`: the decoding count
  summed over masks and guesses.
* `Cslib.Crypto.GoldreichLevin.exists_card_candidate_eq`: fixed masks and guess recover a
  `1 / 2 ^ (k + 1)` fraction of the good targets.
* `Cslib.Crypto.GoldreichLevin.dens_filter_candidate_eq_ge`: the density form, for a fraction of
  the masks and guesses.
* `Cslib.Crypto.GoldreichLevin.dens_filter_agreement_ge`,
  `Cslib.Crypto.GoldreichLevin.card_filter_agreement_ge`: averaging from agreement over pairs to
  agreement per index.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

public section

namespace Cslib.Crypto.GoldreichLevin

open Finset Cslib.Probability MeasureTheory
open scoped ENNReal BigOperators

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

/-- **The Goldreich–Levin count, summed over masks and guesses.** Let `pred x` be predictors for
the parities of `target x`, and let every index of `good` have agreement at least `1 / 2 + ε`, with
`n ≤ 2 * ε ^ 2 * (2 ^ k - 1)` and `k ≥ 1`. Summed over all masks and guesses, the number of indices
whose corrected-majority candidate equals the target is at least half of `#good` times the number
of masks. -/
theorem card_mul_le_two_mul_sum_card_candidate_eq {X : Type*} [Fintype X]
    (pred : X → BitString n → Bool) (target : X → BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) (good : Finset X)
    (hgood : ∀ x ∈ good, 1 / 2 + ε ≤ agreement (pred x) (target x)) :
    #good * Fintype.card (Fin k → BitString n) ≤ 2 * ∑ mg : (Fin k → BitString n) × BitString k,
      #{x | candidate (pred x) mg.1 mg.2 = target x} := by
  classical
  have hswap : ∑ mg : (Fin k → BitString n) × BitString k,
      #{x | candidate (pred x) mg.1 mg.2 = target x} =
        ∑ x, #{mg : (Fin k → BitString n) × BitString k |
          candidate (pred x) mg.1 mg.2 = target x} := by
    simp only [card_filter]
    exact sum_comm
  rw [hswap]
  calc #good * Fintype.card (Fin k → BitString n)
      = ∑ _x ∈ good, Fintype.card (Fin k → BitString n) := by rw [sum_const, smul_eq_mul]
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
  set M := Fintype.card (Fin k → BitString n)
  have hsum := card_mul_le_two_mul_sum_card_candidate_eq pred target ε hε hk hsize good hgood
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

/-- **Nonuniform Goldreich–Levin decoding, density form.** Under the hypotheses of
`exists_card_candidate_eq`, the corrected-majority candidate equals the target for at least
`#good / 2 ^ (k + 2)` indices for at least a `#good / (2 ^ (k + 2) * #X)` fraction of the masks and
guesses. This is reverse averaging (`Fintype.expect_sub_le_dens_filter`) applied to the sum
`card_mul_le_two_mul_sum_card_candidate_eq`. -/
theorem dens_filter_candidate_eq_ge {X : Type*} [Fintype X] [Nonempty X]
    (pred : X → BitString n → Bool) (target : X → BitString n) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) (good : Finset X)
    (hgood : ∀ x ∈ good, 1 / 2 + ε ≤ agreement (pred x) (target x)) :
    (#good : ℝ) / (2 ^ (k + 2) * Fintype.card X) ≤
      (dens {mg : (Fin k → BitString n) × BitString k |
        #good ≤ 2 ^ (k + 2) * #{x | candidate (pred x) mg.1 mg.2 = target x}} : ℝ) := by
  classical
  have hX : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  let c : (Fin k → BitString n) × BitString k → ℕ :=
    fun mg => #{x | candidate (pred x) mg.1 mg.2 = target x}
  let F : (Fin k → BitString n) × BitString k → ℝ := fun mg => c mg / Fintype.card X
  have hF : ∀ mg, F mg ≤ 1 := fun mg => by
    refine div_le_one_of_le₀ ?_ hX.le
    exact_mod_cast card_le_univ _
  -- the average of `F` is at least `#good / (2 ^ (k + 1) * #X)`
  have hsum := card_mul_le_two_mul_sum_card_candidate_eq pred target ε hε hk hsize good hgood
  have hM : (Fintype.card ((Fin k → BitString n) × BitString k) : ℝ) =
      Fintype.card (Fin k → BitString n) * 2 ^ k := by
    rw [Fintype.card_prod, BitString.card]
    push_cast
    ring
  have hMpos : (0 : ℝ) < Fintype.card (Fin k → BitString n) := Nat.cast_pos.2 Fintype.card_pos
  have hexp : (#good : ℝ) / (2 ^ (k + 1) * Fintype.card X) ≤ 𝔼 mg, F mg := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, hM]
    simp only [F, ← Finset.sum_div]
    rw [div_div, le_div_iff₀ (by positivity)]
    have hsum' : (#good : ℝ) * Fintype.card (Fin k → BitString n) ≤
        2 * ∑ mg : (Fin k → BitString n) × BitString k, (c mg : ℝ) := by
      exact_mod_cast hsum
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc (#good : ℝ) * (Fintype.card X * (Fintype.card (Fin k → BitString n) * 2 ^ k))
        = 2 ^ k * Fintype.card X * (#good * Fintype.card (Fin k → BitString n)) := by ring
      _ ≤ 2 ^ k * Fintype.card X * (2 * ∑ mg, (c mg : ℝ)) := by gcongr
      _ = (∑ mg, (c mg : ℝ)) * (2 ^ (k + 1) * Fintype.card X) := by ring
  -- reverse averaging at half the mean
  set θ : ℝ := #good / (2 ^ (k + 2) * Fintype.card X)
  have hθ : 0 ≤ θ := by positivity
  have hrev := Fintype.expect_sub_le_dens_filter hF hθ
  have hcongr : (univ.filter fun mg => θ ≤ F mg) = univ.filter fun mg =>
      #good ≤ 2 ^ (k + 2) * c mg := by
    refine filter_congr fun mg _ => ?_
    simp only [θ, F]
    rw [div_le_div_iff₀ (by positivity) hX,
      show (c mg : ℝ) * (2 ^ (k + 2) * Fintype.card X) = 2 ^ (k + 2) * c mg * Fintype.card X by
        ring, mul_le_mul_iff_of_pos_right hX]
    exact_mod_cast Iff.rfl
  have hhalf : θ = #good / (2 ^ (k + 1) * Fintype.card X) - θ := by
    simp only [θ, pow_succ]
    field_simp
    ring
  calc (#good : ℝ) / (2 ^ (k + 2) * Fintype.card X) = θ := rfl
    _ ≤ 𝔼 mg, F mg - θ := by linarith
    _ ≤ (dens (univ.filter fun mg => θ ≤ F mg) : ℝ) := hrev
    _ = _ := by rw [hcongr]

/-- **Averaging for Goldreich–Levin.** If predictors `pred x` agree with the parities of
`target x` on a `1 / 2 + ε` fraction of all pairs `(x, r)`, with `0 ≤ ε`, then at least an
`ε / 2` fraction of the indices `x` have agreement at least `1 / 2 + ε / 2`. This is reverse
averaging (`Fintype.expect_sub_le_dens_filter`) for the agreement, which is at most `1`. -/
theorem dens_filter_agreement_ge {X : Type*} [Fintype X] [Nonempty X]
    (pred : X → BitString n → Bool) (target : X → BitString n) {ε : ℝ} (hε : 0 ≤ ε)
    (hagree : (1 / 2 + ε) * (Fintype.card X * 2 ^ n) ≤
      #{xr : X × BitString n | pred xr.1 xr.2 = target xr.1 ⬝ᵥ xr.2}) :
    ε / 2 ≤ (dens {x | 1 / 2 + ε / 2 ≤ agreement (pred x) (target x)} : ℝ) := by
  classical
  have hX : (0 : ℝ) < Fintype.card X := Nat.cast_pos.2 Fintype.card_pos
  have hsplit : (#{xr : X × BitString n | pred xr.1 xr.2 = target xr.1 ⬝ᵥ xr.2} : ℝ) =
      ∑ x, (#{r | pred x r = target x ⬝ᵥ r} : ℝ) := by
    rw [← Nat.cast_sum]
    congr 1
    rw [card_filter, Fintype.sum_prod_type]
    exact sum_congr rfl fun x _ => (card_filter _ _).symm
  have hexp : 1 / 2 + ε ≤ 𝔼 x, agreement (pred x) (target x) := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, le_div_iff₀ hX]
    simp only [agreement_eq_card_div, ← Finset.sum_div]
    rw [le_div_iff₀ (by positivity), ← hsplit]
    linarith
  have hrev := Fintype.expect_sub_le_dens_filter (fun x => agreement_le_one (pred x) (target x))
    (θ := 1 / 2 + ε / 2) (by positivity)
  linarith

/-- **Averaging for Goldreich–Levin, counting form.** If predictors `pred x` agree with the
parities of `target x` on a `1 / 2 + ε` fraction of all pairs `(x, r)`, with `0 ≤ ε`, then at least
`ε / 2 * #X` indices have agreement at least `1 / 2 + ε / 2`. -/
theorem card_filter_agreement_ge {X : Type*} [Fintype X] [Nonempty X]
    (pred : X → BitString n → Bool) (target : X → BitString n) {ε : ℝ} (hε : 0 ≤ ε)
    (hagree : (1 / 2 + ε) * (Fintype.card X * 2 ^ n) ≤
      #{xr : X × BitString n | pred xr.1 xr.2 = target xr.1 ⬝ᵥ xr.2}) :
    ε / 2 * Fintype.card X ≤ (#{x | 1 / 2 + ε / 2 ≤ agreement (pred x) (target x)} : ℝ) := by
  have h := dens_filter_agreement_ge pred target hε hagree
  rwa [nnratCast_dens, le_div_iff₀ (Nat.cast_pos.2 Fintype.card_pos)] at h

end Cslib.Crypto.GoldreichLevin
