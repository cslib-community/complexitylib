/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Foundations.Data.Code.RadialDecoding
public import CslibFrontier.Probability.PMF.Coin
public import Mathlib.Data.Fin.VecNotation

/-! The code `{00, 11}` with weight-one noise: deterministic ties, null observations,
a singleton code, and a biased-prior counterexample, checked through ordinary imports. -/

public section

namespace CslibFrontierTests.RadialDecoding

open Cslib Cslib.BitString Cslib.Probability
open scoped ENNReal

abbrev encode (b : Bool) : Fin 2 → Bool := ![b, b]
abbrev decode (y : Fin 2 → Bool) : Bool := y 0 && y 1
abbrev received : Fin 2 → Bool := ![false, true]

example : Function.Injective encode := fun _ _ h => congrFun h 0

theorem nearest_decode : IsNearestDecoder encode decode := by
  intro y b
  have hy : y = ![y 0, y 1] := by ext i; fin_cases i <;> rfl
  rw [hy]
  cases y 0 <;> cases y 1 <;> cases b <;> decide

theorem nearest_received : nearestMessages encode received = Finset.univ := by
  ext b
  simp only [mem_nearestMessages, Finset.mem_univ, iff_true]
  intro b'
  cases b <;> cases b' <;> decide

noncomputable def noise : PMF (Fin 2 → Bool) :=
  PMF.uniformOfFinset {![false, true], ![true, false]} (by simp)

theorem noise_apply (e : Fin 2 → Bool) :
    noise e = if hammingNorm e = 1 then (2 : ℝ≥0∞)⁻¹ else 0 := by
  have he : e = ![e 0, e 1] := by ext i; fin_cases i <;> rfl
  rw [noise, PMF.uniformOfFinset_apply, he]
  cases e 0 <;> cases e 1 <;>
    norm_num [hammingNorm, funext_iff, Fin.forall_fin_succ, Finset.univ_fin2,
      Finset.filter_insert, Finset.filter_singleton, Bool.zero_eq_false]

theorem radial_noise : IsRadial noise := by
  intro u v huv
  rw [noise_apply, noise_apply, huv]

theorem noise_encode_add_received (b : Bool) : noise (encode b + received) = (2 : ℝ≥0∞)⁻¹ := by
  rw [noise_apply]
  have h : hammingNorm (encode b + received) = 1 := by cases b <;> decide
  simp only [h, ite_true]

theorem correct_mass :
    (additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise
      (received, decode received)).toReal = 1 / 4 := by
  rw [additiveNoiseJoint_apply, PMF.uniformOfFintype_apply, noise_encode_add_received]
  norm_num [ENNReal.toReal_mul]

theorem nearest_mass :
    ((additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
      {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received}).toReal = 1 / 2 := by
  rw [← nearestMessages_card_mul_joint encode nearest_decode radial_noise,
    ENNReal.toReal_mul, correct_mass, nearest_received]
  norm_num

example :
    (additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise
      (received, decode received)).toReal /
      ((additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
        {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received}).toReal = 1 / 2 := by
  rw [correct_mass, nearest_mass]
  norm_num

example :
    additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise (received, decode received) /
      (additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
        {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received} = (2 : ℝ≥0∞)⁻¹ := by
  have hpos : 0 < ((additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
      {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received}).toReal := by
    rw [nearest_mass]
    norm_num
  have h := nearestMessages_conditional_success encode nearest_decode radial_noise received
    (ne_of_gt (ENNReal.toReal_pos_iff.mp hpos).1)
  simpa only [nearest_received, Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat] using h

-- The joint identity covers an impossible received word, without conditioning on it.
example : (additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
    {p | p.1 = encode false ∧ p.2 ∈ nearestMessages encode (encode false)} = 0 := by
  rw [← nearestMessages_card_mul_joint encode nearest_decode radial_noise,
    additiveNoiseJoint_apply, noise_apply]
  have h : hammingNorm (encode (decode (encode false)) + encode false) = 0 := by decide
  rw [h]
  norm_num

-- The weight-refined theorem has satisfiable decoder and radiality hypotheses.
example (r : ℕ) :
    ((additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
      {p | decode p.1 ≠ p.2 ∧ p.2 ∈ nearestMessages encode p.1 ∧
        (nearestMessages encode p.1).card = 2 ∧ hammingNorm (encode p.2 + p.1) = r}).toReal =
      1 / 2 * ((additiveNoiseJoint encode (PMF.uniformOfFintype Bool) noise).toOuterMeasure
        {p | p.2 ∈ nearestMessages encode p.1 ∧ (nearestMessages encode p.1).card = 2 ∧
          hammingNorm (encode p.2 + p.1) = r}).toReal :=
  twoWayTie_failure_eq_half encode nearest_decode radial_noise r

-- A one-message code has a singleton tie set for every received word.
example : IsNearestDecoder (fun _ : Unit => encode false) (fun _ => ()) := fun _ _ => le_rfl

example (y : Fin 2 → Bool) : (nearestMessages (fun _ : Unit => encode false) y).card = 1 := by
  simp [nearestMessages]

-- A 3/4 prior on 00 changes conditional success for the same tie rule and radial noise.
noncomputable def biasedPrior : PMF Bool := Probability.PMF.coin ⟨1 / 4, by norm_num⟩

theorem biased_correct_mass :
    (additiveNoiseJoint encode biasedPrior noise (received, decode received)).toReal = 3 / 8 := by
  rw [additiveNoiseJoint_apply, ENNReal.toReal_mul, noise_encode_add_received,
    biasedPrior, Probability.PMF.coin_apply_toReal]
  norm_num [decode, received]

theorem biased_nearest_mass :
    ((additiveNoiseJoint encode biasedPrior noise).toOuterMeasure
      {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received}).toReal = 1 / 2 := by
  rw [nearestMessages_event_eq_sum, nearest_received, Fintype.sum_bool]
  simp only [additiveNoiseJoint_apply, noise_encode_add_received]
  rw [← add_mul, show biasedPrior true + biasedPrior false = 1 from by
    simpa only [tsum_fintype, Fintype.sum_bool] using biasedPrior.tsum_coe]
  norm_num

example :
    (additiveNoiseJoint encode biasedPrior noise (received, decode received)).toReal /
      ((additiveNoiseJoint encode biasedPrior noise).toOuterMeasure
        {p | p.1 = received ∧ p.2 ∈ nearestMessages encode received}).toReal = 3 / 4 := by
  rw [biased_correct_mass, biased_nearest_mass]
  norm_num

-- Source-shaped specialization: messages are the actual codewords, with subtype inclusion.
abbrev repetitionCode : Finset (Fin 2 → Bool) := {encode false, encode true}

instance : Nonempty repetitionCode := ⟨⟨encode false, by simp⟩⟩

def codeDecode (y : Fin 2 → Bool) : repetitionCode :=
  ⟨encode (decode y), by cases decode y <;> simp⟩

theorem nearest_codeDecode : IsNearestDecoder Subtype.val codeDecode := by
  rintro y ⟨c, hc⟩
  simp only [repetitionCode, Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · exact nearest_decode y false
  · exact nearest_decode y true

example (y : Fin 2 → Bool) :
    (nearestMessages (Subtype.val : repetitionCode → Fin 2 → Bool) y).card *
        additiveNoiseJoint Subtype.val (PMF.uniformOfFintype repetitionCode) noise
          (y, codeDecode y) =
      (additiveNoiseJoint Subtype.val (PMF.uniformOfFintype repetitionCode) noise).toOuterMeasure
        {p | p.1 = y ∧ p.2 ∈ nearestMessages Subtype.val y} :=
  nearestMessages_card_mul_joint Subtype.val nearest_codeDecode radial_noise y

end CslibFrontierTests.RadialDecoding
