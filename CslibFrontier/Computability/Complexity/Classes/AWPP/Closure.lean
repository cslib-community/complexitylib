/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AWPP
public import CslibFrontier.Foundations.Order.BooleanSubalgebra
import Mathlib.Data.Rat.Cast.Order

/-!
# Boolean closure of AWPP

Three fixed rounds of the majority-of-three polynomial `t²(3 - 2t)` reduce the
error from one third to at most one eighth. Products then give intersection,
and complement gives the remaining Boolean operations. This is a constant-size
specialization of the gap amplification method of [Fenner][Fenner2003]. Uniform error
reduction to a polynomially bounded input-dependent exponent is proved in
`CslibFrontier/Computability/Complexity/Classes/AWPP/Amplification.lean`.

## Main results

* `exists_AWPP_gap_eighth`: an AWPP witness with error at most one eighth.
* `inter_mem_AWPP`, `union_mem_AWPP`, `diff_mem_AWPP`, `symmDiff_mem_AWPP`.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

@[expose] public section

namespace Cslib.Complexity

open scoped symmDiff

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

private def majorityRatio (t : ℚ) : ℚ := t ^ 2 * (3 - 2 * t)

private theorem majorityRatio_mono {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    majorityRatio a ≤ majorityRatio b := by
  have hp := mul_nonneg (show 0 ≤ b - a by linarith)
    (add_nonneg
      (mul_nonneg (show 0 ≤ 3 * (1 - b) by linarith) (show 0 ≤ a + b by linarith))
      (mul_nonneg (show 0 ≤ b - a by linarith) (show 0 ≤ b + 2 * a by linarith)))
  dsimp [majorityRatio]
  nlinarith only [hp]

private theorem majorityRatio_bounds {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ majorityRatio t ∧ majorityRatio t ≤ 1 := by
  constructor
  · simpa [majorityRatio] using majorityRatio_mono (by norm_num : (0 : ℚ) ≤ 0) h0 h1
  · simpa [majorityRatio, show (3 : ℚ) - 2 = 1 by norm_num] using
      majorityRatio_mono h0 h1 (by norm_num : (1 : ℚ) ≤ 1)

private theorem majorityRatio_compl (t : ℚ) : majorityRatio (1 - t) = 1 - majorityRatio t := by
  dsimp [majorityRatio]
  ring

private theorem majorityRatio_three_le {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1 / 3) :
    majorityRatio (majorityRatio (majorityRatio t)) ≤ 1 / 8 := by
  have hb := majorityRatio_bounds h0 (by linarith : t ≤ 1)
  have hb' := majorityRatio_bounds hb.1 hb.2
  have h := majorityRatio_mono h0 h1 (by norm_num : (1 : ℚ) / 3 ≤ 1)
  have h' := majorityRatio_mono hb.1 h
    (by norm_num [majorityRatio] : majorityRatio (1 / 3) ≤ 1)
  have h'' := majorityRatio_mono hb'.1 h'
    (by norm_num [majorityRatio] : majorityRatio (majorityRatio (1 / 3)) ≤ 1)
  exact h''.trans (by norm_num [majorityRatio])

private def majorityGap (g D : α → ℤ) : α → ℤ := g * g * (D + D + D - (g + g))

private theorem majorityGap_mem {g D : α → ℤ} (hg : g ∈ GapP enc) (hD : D ∈ GapP enc) :
    majorityGap g D ∈ GapP enc :=
  GapP.mul_mem (GapP.mul_mem hg hg)
    (GapP.sub_mem' (GapP.add_mem (GapP.add_mem hD hD) hD) (GapP.add_mem hg hg))

private theorem majorityGap_ratio (g D : α → ℤ) (a : α) (hD : D a ≠ 0) :
    (majorityGap g D a : ℚ) / (D a : ℚ) ^ 3 = majorityRatio ((g a : ℚ) / D a) := by
  have hD' : (D a : ℚ) ≠ 0 := by exact_mod_cast hD
  simp only [majorityGap, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, Int.cast_mul,
    Int.cast_sub, Int.cast_add, majorityRatio]
  field_simp
  ring

/-- AWPP witnesses can have error at most one eighth, using three fixed majority rounds. -/
theorem exists_AWPP_gap_eighth (hA : A ∈ AWPP enc) :
    ∃ g ∈ GapP enc, ∃ p : Polynomial ℕ, ∀ a,
      (0 ≤ g a ∧ g a ≤ (2 : ℤ) ^ p.eval (enc a).length) ∧
      (a ∈ A → 7 * (2 : ℤ) ^ p.eval (enc a).length ≤ 8 * g a) ∧
      (a ∉ A → 8 * g a ≤ (2 : ℤ) ^ p.eval (enc a).length) := by
  obtain ⟨g, hg, p, hA⟩ := hA
  let D : α → ℤ := fun a => 2 ^ p.eval (enc a).length
  have hD : D ∈ GapP enc := GapP.two_pow_mem p
  let g1 := majorityGap g D
  let g2 := majorityGap g1 (D ^ 3)
  let g3 := majorityGap g2 ((D ^ 3) ^ 3)
  have hD3 : D ^ 3 ∈ GapP enc := GapP.pow_mem hD 3
  have hD9 : (D ^ 3) ^ 3 ∈ GapP enc := GapP.pow_mem hD3 3
  have hg3 : g3 ∈ GapP enc :=
    majorityGap_mem (majorityGap_mem (majorityGap_mem hg hD) hD3) hD9
  refine ⟨g3, hg3, p * 27, fun a => ?_⟩
  have hpos : 0 < D a := by dsimp [D]; positivity
  have hposQ : (0 : ℚ) < D a := by exact_mod_cast hpos
  have hpow : (2 : ℤ) ^ (p * 27).eval (enc a).length = ((D a ^ 3) ^ 3) ^ 3 := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, D, ← pow_mul]
    congr 1
    ring
  have hratio : (g3 a : ℚ) / (((D a : ℚ) ^ 3) ^ 3) ^ 3 =
      majorityRatio (majorityRatio (majorityRatio ((g a : ℚ) / D a))) := by
    have h1 := majorityGap_ratio g D a (ne_of_gt hpos)
    have h2 := majorityGap_ratio g1 (D ^ 3) a
      (by simpa using pow_ne_zero 3 (ne_of_gt hpos))
    have h3 := majorityGap_ratio g2 ((D ^ 3) ^ 3) a
      (by simpa using pow_ne_zero 3 (pow_ne_zero 3 (ne_of_gt hpos)))
    change (g1 a : ℚ) / (D a : ℚ) ^ 3 = _ at h1
    simp only [Pi.pow_apply, Int.cast_pow] at h2 h3
    change (g2 a : ℚ) / ((D a : ℚ) ^ 3) ^ 3 = _ at h2
    change (g3 a : ℚ) / (((D a : ℚ) ^ 3) ^ 3) ^ 3 = _ at h3
    rw [h3, h2, h1]
  obtain ⟨⟨h0, h1⟩, hy, hn⟩ := hA a
  have h0Q : (0 : ℚ) ≤ g a := by exact_mod_cast h0
  have h1Q : (g a : ℚ) ≤ D a := by exact_mod_cast h1
  have ht0 : (0 : ℚ) ≤ (g a : ℚ) / D a := div_nonneg h0Q hposQ.le
  have ht1 : (g a : ℚ) / D a ≤ 1 := (div_le_one hposQ).mpr h1Q
  have hb := majorityRatio_bounds ht0 ht1
  have hb' := majorityRatio_bounds hb.1 hb.2
  have hb'' := majorityRatio_bounds hb'.1 hb'.2
  have hden : (0 : ℚ) < (((D a : ℚ) ^ 3) ^ 3) ^ 3 := by positivity
  rw [hpow]
  constructor
  · constructor
    · have := (le_div_iff₀ hden).mp (hratio ▸ hb''.1)
      simp only [zero_mul] at this
      exact_mod_cast this
    · have := (div_le_one hden).mp (hratio ▸ hb''.2)
      exact_mod_cast this
  · constructor
    · intro ha
      have hyQ : 2 * (D a : ℚ) ≤ 3 * (g a : ℚ) := by exact_mod_cast hy ha
      have ht : 1 - (g a : ℚ) / D a ≤ 1 / 3 := by
        apply (sub_le_iff_le_add).mpr
        have : (2 : ℚ) / 3 ≤ (g a : ℚ) / D a := by
          apply (le_div_iff₀ hposQ).mpr
          linarith
        linarith
      have hh := majorityRatio_three_le (sub_nonneg.mpr ht1) ht
      rw [majorityRatio_compl, majorityRatio_compl, majorityRatio_compl, ← hratio] at hh
      have : (7 : ℚ) / 8 ≤ (g3 a : ℚ) / (((D a : ℚ) ^ 3) ^ 3) ^ 3 := by linarith
      have := (le_div_iff₀ hden).mp this
      have : 7 * (((D a : ℚ) ^ 3) ^ 3) ^ 3 ≤ 8 * (g3 a : ℚ) := by linarith
      exact_mod_cast this
    · intro ha
      have hnQ : 3 * (g a : ℚ) ≤ D a := by exact_mod_cast hn ha
      have ht : (g a : ℚ) / D a ≤ 1 / 3 := by
        apply (div_le_iff₀ hposQ).mpr
        linarith
      have hh := majorityRatio_three_le ht0 ht
      rw [← hratio] at hh
      have := (div_le_iff₀ hden).mp hh
      have : 8 * (g3 a : ℚ) ≤ (((D a : ℚ) ^ 3) ^ 3) ^ 3 := by linarith
      exact_mod_cast this

/-- Multiplying witnesses with error at most one eighth recognizes intersection. -/
theorem inter_mem_AWPP (hA : A ∈ AWPP enc) (hB : B ∈ AWPP enc) : A ∩ B ∈ AWPP enc := by
  obtain ⟨g, hg, p, hA⟩ := exists_AWPP_gap_eighth hA
  obtain ⟨h, hh, q, hB⟩ := exists_AWPP_gap_eighth hB
  refine ⟨g * h, GapP.mul_mem hg hh, p + q, fun a => ?_⟩
  obtain ⟨⟨hg0, hg1⟩, hgy, hgn⟩ := hA a
  obtain ⟨⟨hh0, hh1⟩, hhy, hhn⟩ := hB a
  have hD : (0 : ℤ) ≤ 2 ^ p.eval (enc a).length := by positivity
  have hE : (0 : ℤ) ≤ 2 ^ q.eval (enc a).length := by positivity
  simp only [Polynomial.eval_add, pow_add, Pi.mul_apply]
  refine ⟨⟨mul_nonneg hg0 hh0, mul_le_mul hg1 hh1 hh0 hD⟩, ?_, ?_⟩
  · rintro ⟨ha, hb⟩
    have hm := mul_le_mul (hgy ha) (hhy hb)
      (by positivity : (0 : ℤ) ≤ 7 * 2 ^ q.eval (enc a).length)
      (by positivity : (0 : ℤ) ≤ 8 * g a)
    nlinarith [mul_nonneg hD hE]
  · intro hab
    by_cases ha : a ∈ A
    · have hb : a ∉ B := fun hb => hab ⟨ha, hb⟩
      have hm := mul_le_mul hg1 (hhn hb) (by positivity : (0 : ℤ) ≤ 8 * h a) hD
      nlinarith [mul_nonneg hg0 hh0]
    · have hm := mul_le_mul (hgn ha) hh1 hh0 hD
      nlinarith [mul_nonneg hg0 hh0]

/-- `AWPP` as a Boolean subalgebra of `Set α`. -/
def AWPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (AWPP enc) (BPP_subset_AWPP (P_subset_BPP empty_mem_P)) (fun _ => compl_mem_AWPP)
    (fun _ _ => inter_mem_AWPP)

@[simp]
theorem AWPP.coe_booleanSubalgebra : (AWPP.booleanSubalgebra enc : Set (Set α)) = AWPP enc := rfl

@[simp]
theorem AWPP.mem_booleanSubalgebra : A ∈ AWPP.booleanSubalgebra enc ↔ A ∈ AWPP enc := Iff.rfl

/-- Union follows by De Morgan's law. -/
theorem union_mem_AWPP (hA : A ∈ AWPP enc) (hB : B ∈ AWPP enc) : A ∪ B ∈ AWPP enc :=
  (AWPP.booleanSubalgebra enc).sup_mem hA hB

/-- AWPP is closed under set difference. -/
theorem diff_mem_AWPP (hA : A ∈ AWPP enc) (hB : B ∈ AWPP enc) : A \ B ∈ AWPP enc :=
  (AWPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- AWPP is closed under symmetric difference. -/
theorem symmDiff_mem_AWPP (hA : A ∈ AWPP enc) (hB : B ∈ AWPP enc) :
    A ∆ B ∈ AWPP enc :=
  (AWPP.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
