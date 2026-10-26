/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Weight

/-!
# Cover's enumerative coding for weight-bounded Boolean words

Cover's lexicographic rank (`Cslib.BitString.coverRank`) and greedy threshold decoder
(`Cslib.BitString.coverDecode`) establish an explicit bijection between words `z : Fin q → Bool` of
Hamming weight at most `e` and indices below the Hamming-ball size
`B(q, e) = ∑ j ∈ range (e + 1), q.choose j` (`Cslib.BitString.ballSize`).

## Main definitions

* `Cslib.BitString.coverRank`: Cover's lexicographic rank of a weight-bounded Boolean word.
* `Cslib.BitString.coverDecode`: Cover's greedy threshold decoder recovering a word of weight at
  most `e` from its rank below `ballSize q e`.

## Main results

* `Cslib.BitString.coverRank_lt_ballSize`, `Cslib.BitString.weight_coverDecode_le`,
  `Cslib.BitString.coverRank_coverDecode`, `Cslib.BitString.coverDecode_coverRank`: mutual inverse
  and weight bounds for Cover's enumerative coding.

## References

* [T. M. Cover, *Enumerative source encoding*][Cover1973]
* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 4]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- Cover's lexicographic rank of a word `z : Fin q → Bool` among words of weight at most `e`. -/
def coverRank : {q : ℕ} → ℕ → (Fin q → Bool) → ℕ
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | q + 1, e + 1, z =>
    if z 0 then
      ballSize q (e + 1) + coverRank e (fun i : Fin q => z i.succ)
    else
      coverRank (e + 1) (fun i : Fin q => z i.succ)

/-- Cover's greedy threshold decoder recovering a word `z : Fin q → Bool` of weight at most `e`
from its rank `t < ballSize q e`. -/
def coverDecode : (q e t : ℕ) → Fin q → Bool
  | 0, _, _, i => i.elim0
  | _ + 1, 0, _, _ => false
  | q + 1, e + 1, t, i =>
    let b := decide (ballSize q (e + 1) ≤ t)
    Fin.cases b (fun j =>
      if b then coverDecode q e (t - ballSize q (e + 1)) j
      else coverDecode q (e + 1) t j) i

/-- Every word `z : Fin q → Bool` of weight at most `e` has `coverRank e z < ballSize q e`. -/
theorem coverRank_lt_ballSize {q : ℕ} (e : ℕ) (z : Fin q → Bool) (hz : weight z ≤ e) :
    coverRank e z < ballSize q e := by
  induction q generalizing e with
  | zero =>
    simp [coverRank]
  | succ q ih =>
    cases e with
    | zero =>
      simp [coverRank]
    | succ e =>
      rw [coverRank, ballSize_succ_succ]
      have hcons := weight_cons_succ z
      cases h0 : z 0
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hz' : weight (fun i : Fin q => z i.succ) ≤ e + 1 := by
          simp only [h0, Bool.toNat_false, zero_add] at hcons
          omega
        exact (ih (e + 1) _ hz').trans_le (Nat.le_add_right _ _)
      · simp only [↓reduceIte]
        have hz' : weight (fun i : Fin q => z i.succ) ≤ e := by
          simp only [h0, Bool.toNat_true] at hcons
          omega
        exact Nat.add_lt_add_left (ih e _ hz') _

/-- Every decoded word `coverDecode q e t` has Hamming weight at most `e`. -/
theorem weight_coverDecode_le (q e t : ℕ) :
    weight (coverDecode q e t) ≤ e := by
  induction q generalizing e t with
  | zero =>
    simp [weight]
  | succ q ih =>
    cases e with
    | zero =>
      change weight (fun _ : Fin (q + 1) => false) ≤ 0
      simp [weight]
    | succ e =>
      rw [weight_cons_succ]
      by_cases ht : ballSize q (e + 1) ≤ t
      · have h0 : coverDecode (q + 1) (e + 1) t 0 = true := by
          simp [coverDecode, ht]
        have htail : (fun i : Fin q => coverDecode (q + 1) (e + 1) t i.succ) =
            coverDecode q e (t - ballSize q (e + 1)) := by
          funext i
          simp [coverDecode, ht]
        rw [h0, htail]
        have := ih e (t - ballSize q (e + 1))
        simp only [Bool.toNat_true]
        omega
      · have h0 : coverDecode (q + 1) (e + 1) t 0 = false := by
          simp [coverDecode, ht]
        have htail : (fun i : Fin q => coverDecode (q + 1) (e + 1) t i.succ) =
            coverDecode q (e + 1) t := by
          funext i
          simp [coverDecode, ht]
        rw [h0, htail]
        have := ih (e + 1) t
        simp only [Bool.toNat_false, zero_add]
        exact this

/-- Ranking a decoded word `coverDecode q e t` for `t < ballSize q e` recovers `t`. -/
@[simp]
theorem coverRank_coverDecode {q e t : ℕ} (ht : t < ballSize q e) :
    coverRank e (coverDecode q e t) = t := by
  induction q generalizing e t with
  | zero =>
    simp only [ballSize_zero_left] at ht
    simp only [coverRank]
    omega
  | succ q ih =>
    cases e with
    | zero =>
      simp only [ballSize_zero_right] at ht
      simp only [coverRank]
      omega
    | succ e =>
      rw [ballSize_succ_succ] at ht
      by_cases hle : ballSize q (e + 1) ≤ t
      · have h0 : coverDecode (q + 1) (e + 1) t 0 = true := by
          simp [coverDecode, hle]
        have htail : (fun i : Fin q => coverDecode (q + 1) (e + 1) t i.succ) =
            coverDecode q e (t - ballSize q (e + 1)) := by
          funext i
          simp [coverDecode, hle]
        rw [coverRank, h0]
        simp only [↓reduceIte, htail]
        rw [ih (by omega)]
        omega
      · have h0 : coverDecode (q + 1) (e + 1) t 0 = false := by
          simp [coverDecode, hle]
        have htail : (fun i : Fin q => coverDecode (q + 1) (e + 1) t i.succ) =
            coverDecode q (e + 1) t := by
          funext i
          simp [coverDecode, hle]
        rw [coverRank, h0]
        simp only [Bool.false_eq_true, ↓reduceIte, htail]
        exact ih (by omega)

/-- A word of weight at most `0` is identically `false`. -/
private theorem eq_false_of_weight_le_zero {q : ℕ} {z : Fin q → Bool} (hz : weight z ≤ 0)
    (i : Fin q) : z i = false := by
  by_contra h
  have hpos : 0 < weight z := card_pos.mpr ⟨i, by simp [Bool.eq_true_of_not_eq_false h]⟩
  omega

/-- Decoding the rank `coverRank e z` of a word `z : Fin q → Bool` with `weight z ≤ e` recovers
`z`. -/
@[simp]
theorem coverDecode_coverRank {q e : ℕ} (z : Fin q → Bool) (hz : weight z ≤ e) :
    coverDecode q e (coverRank e z) = z := by
  induction q generalizing e with
  | zero =>
    funext i
    exact i.elim0
  | succ q ih =>
    cases e with
    | zero =>
      funext i
      rw [eq_false_of_weight_le_zero hz i]
      rfl
    | succ e =>
      have hcons := weight_cons_succ z
      cases h0 : z 0
      · have hz' : weight (fun i : Fin q => z i.succ) ≤ e + 1 := by
          simp only [h0, Bool.toNat_false, zero_add] at hcons
          omega
        have hlt : coverRank (e + 1) (fun i : Fin q => z i.succ) < ballSize q (e + 1) :=
          coverRank_lt_ballSize (e + 1) _ hz'
        have hnot : ¬ ballSize q (e + 1) ≤ coverRank (e + 1) z := by
          simpa [coverRank, h0] using hlt
        funext i
        refine Fin.cases (by simp [coverDecode, hnot, h0]) (fun j => ?_) i
        have hstep : coverDecode (q + 1) (e + 1) (coverRank (e + 1) z) j.succ =
            coverDecode q (e + 1) (coverRank (e + 1) (fun k : Fin q => z k.succ)) j := by
          simp [coverDecode, coverRank, h0, not_le.mpr hlt]
        rw [hstep, ih _ hz']
      · have hz' : weight (fun i : Fin q => z i.succ) ≤ e := by
          simp only [h0, Bool.toNat_true] at hcons
          omega
        have hle : ballSize q (e + 1) ≤ coverRank (e + 1) z := by simp [coverRank, h0]
        funext i
        refine Fin.cases (by simp [coverDecode, hle, h0]) (fun j => ?_) i
        have hstep : coverDecode (q + 1) (e + 1) (coverRank (e + 1) z) j.succ =
            coverDecode q e (coverRank e (fun k : Fin q => z k.succ)) j := by
          simp [coverDecode, coverRank, h0]
        rw [hstep, ih _ hz']

end Cslib.BitString
