/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.RoutedBinPreparation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Fourth-root regularity of actual unrouted bins

The numerator is literally `boundedRoutedBinCutoff` with the polynomial switch on
`[1/2,1]` and constant routing one. Separated adjacent scales factor the fine-bin
switch difference into a switch and a complementary switch. Clipping the scalar
multiplier away from zero then supplies fourth-root regularity, including signed
inputs. This scalar bridge proves no recursive parent accuracy or resource bound.
The proof is original; the bin definitions retain their documented source mapping.

## Main results

* `exists_boundedRoutedBinCutoff_root_lipschitz`: a constant depending only on the
  cap and adjacent ratio controls every bin and every real input.
* `boundedRoutedBinCutoff_succ_factor`: equality with the separated switch product.
* `DenseBinRecipe.polynomialUnrouted_numerator_laws`: range and light support of the
  concrete polynomial recipe, paired with the existing preparation laws.
-/

public section
namespace Matrix
open Cslib

private theorem product_bound {f g : ℝ → ℝ} {A B L M : ℝ}
    (hf : ∀ x, |f x| ≤ A) (hg : ∀ x, |g x| ≤ B)
    (hl : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hm : ∀ x y, |g x - g y| ≤ M * |x - y|)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (x y : ℝ) :
    |f x * g x - f y * g y| ≤ (L * B + A * M) * |x - y| := by
  calc
    _ = |(f x - f y) * g x + f y * (g x - g y)| := by congr 1; ring
    _ ≤ |f x - f y| * |g x| + |f y| * |g x - g y| := by
      simpa only [abs_mul] using abs_add_le ((f x - f y) * g x) (f y * (g x - g y))
    _ ≤ (L * |x - y|) * B + A * (M * |x - y|) :=
      add_le_add ((mul_le_mul_of_nonneg_left (hg x) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hl x y) hB))
        (mul_le_mul (hf y) (hm x y) (abs_nonneg _) hA)
    _ = _ := by ring

private theorem clipped_root_lipschitz {C : ℝ} (hC : 1 ≤ C) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      |max (1 / 2) (min C x) ^ (4⁻¹ : ℝ) -
        max (1 / 2) (min C y) ^ (4⁻¹ : ℝ)| ≤ L * |x - y| := by
  have hf : ContDiffOn ℝ 1 (fun x : ℝ => x ^ (4⁻¹ : ℝ)) (Set.Icc (1 / 2) C) := by
    apply ContDiffOn.rpow_const_of_ne contDiffOn_id
    intro x hx
    change x ≠ 0
    linarith [hx.1]
  obtain ⟨K, hK⟩ := hf.exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc
  have hc : (1 / 2 : ℝ) ≤ C := by linarith
  refine ⟨K, K.coe_nonneg, fun x y => ?_⟩
  have mem (z : ℝ) : max (1 / 2) (min C z) ∈ Set.Icc (1 / 2) C :=
    ⟨le_max_left _ _, max_le hc (min_le_left _ _)⟩
  have hp := ((LipschitzWith.id.const_min C).const_max (1 / 2)).dist_le_mul x y
  have hb := hK.dist_le_mul _ (mem x) _ (mem y)
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hp hb
  exact hb.trans (mul_le_mul_of_nonneg_left hp K.coe_nonneg)

private theorem switch_difference {r d : ℝ} (hr : 2 ≤ r) :
    polynomialSwitch4 (1 / 2) 1 d - polynomialSwitch4 (1 / 2) 1 (d / r) =
      polynomialSwitch4 (1 / 2) 1 d * (1 - polynomialSwitch4 (1 / 2) 1 (d / r)) := by
  by_cases hd : 1 ≤ d
  · rw [polynomialSwitch4_of_ge (by norm_num) hd, one_mul]
  · have hz : polynomialSwitch4 (1 / 2) 1 (d / r) = 0 :=
      polynomialSwitch4_of_le (by norm_num) ((div_le_iff₀ (by linarith : 0 < r)).mpr
        (by linarith [not_le.mp hd]))
    rw [hz, sub_zero, sub_zero, mul_one]

/-- Exact fine-bin factorization on separated adjacent scales. Routing is constantly one. -/
theorem boundedRoutedBinCutoff_succ_factor {b : ℕ → ℝ} (hb : ∀ i, 0 < b i)
    {r : ℝ} (hr : 2 ≤ r) (hstep : ∀ i, b i = r * b (i + 1))
    (cap d : ℝ) (i : ℕ) :
    boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap (i + 1) (fun _ => 1) d =
      d * (polynomialSwitch4 (1 / 2) 1 d *
        (1 - polynomialSwitch4 (1 / 2) 1 (d / r))) := by
  have heq : b (i + 1) * d / b i = d / r := by
    rw [hstep i]
    field_simp [(hb (i + 1)).ne', (by linarith : r ≠ 0)]
  by_cases hd : d < 0
  · have hz := polynomialSwitch4_of_le (by norm_num : (1 / 2 : ℝ) < 1)
      (by linarith : d ≤ 1 / 2)
    simp only [boundedRoutedBinCutoff, Nat.succ_ne_zero, ↓reduceIte, hd, hz,
      zero_mul, mul_zero]
  · simp only [boundedRoutedBinCutoff, Nat.succ_ne_zero, ↓reduceIte, hd,
      routedBinCutoff, binWeight, mul_one, mul_div_cancel_left₀ _ (hb _).ne', heq]
    rw [switch_difference hr]

private theorem weighted_root_bound {C : ℝ} (hC : 1 ≤ C) {k : ℝ → ℝ}
    (hk : ∀ x, k x ∈ Set.Icc 0 1)
    (hroot : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      |k x ^ (4⁻¹ : ℝ) - k y ^ (4⁻¹ : ℝ)| ≤ L * |x - y|) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      |(max (1 / 2) (min C x) * k x) ^ (4⁻¹ : ℝ) -
        (max (1 / 2) (min C y) * k y) ^ (4⁻¹ : ℝ)| ≤ L * |x - y| := by
  obtain ⟨A, hA, ha⟩ := clipped_root_lipschitz hC
  obtain ⟨B, hB, hb⟩ := hroot
  have hC0 : 0 ≤ C := by linarith
  have hc (x : ℝ) : 0 ≤ max (1 / 2) (min C x) := by
    linarith [le_max_left (1 / 2 : ℝ) (min C x)]
  have hf (x : ℝ) : |max (1 / 2) (min C x) ^ (4⁻¹ : ℝ)| ≤ C ^ (4⁻¹ : ℝ) := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hc x) _)]
    exact Real.rpow_le_rpow (hc x) (max_le (by linarith) (min_le_left _ _)) (by norm_num)
  have hg (x : ℝ) : |k x ^ (4⁻¹ : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hk x).1 _)]
    exact Real.rpow_le_one (hk x).1 (hk x).2 (by norm_num)
  refine ⟨A * 1 + C ^ (4⁻¹ : ℝ) * B, by positivity, fun x y => ?_⟩
  rw [Real.mul_rpow (hc x) (hk x).1, Real.mul_rpow (hc y) (hk y).1]
  exact product_bound hf hg ha hb (Real.rpow_nonneg hC0 _) zero_le_one x y

/-- Every actual unrouted bounded numerator has a globally Lipschitz fourth root on
separated constant-ratio scales. The constant depends only on the top cap and ratio,
and is chosen before the scales, bin index and real inputs. No child-value bound occurs. -/
theorem exists_boundedRoutedBinCutoff_root_lipschitz {cap r : ℝ}
    (hr : 2 ≤ r) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = r * b (i + 1)) → ∀ i v w,
      |boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap i (fun _ => 1) v ^
          (4⁻¹ : ℝ) -
        boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap i (fun _ => 1) w ^
          (4⁻¹ : ℝ)| ≤ L * |v - w| := by
  let χ : ℝ → ℝ := polynomialSwitch4 (1 / 2) 1
  have hχ (x : ℝ) : χ x ∈ Set.Icc 0 1 :=
    ⟨polynomialSwitch4_nonneg _ _ _, polynomialSwitch4_le_one _ _ _⟩
  have hz (x : ℝ) (hx : x ≤ 1 / 2) : χ x = 0 :=
    polynomialSwitch4_of_le (by norm_num) hx
  obtain ⟨K, hK⟩ := exists_lipschitzWith_polynomialSwitch4_root (1 / 2) 1
  obtain ⟨Lt, hLt, ht⟩ := weighted_root_bound (le_max_left 1 cap) hχ
    ⟨K, K.coe_nonneg, fun x y => by simpa only [Real.dist_eq] using hK.dist_le_mul x y⟩
  let k : ℝ → ℝ := fun d => χ d * (1 - χ (d / r))
  have hk (x : ℝ) : k x ∈ Set.Icc 0 1 :=
    ⟨mul_nonneg (hχ x).1 (sub_nonneg.mpr (hχ _).2),
      (mul_le_of_le_one_right (hχ x).1 (by linarith [(hχ (x / r)).1])).trans (hχ x).2⟩
  obtain ⟨D, hD, hd⟩ := exists_abs_switch_product_root_sub_le (1 / 2) 1 (1 / 2) 1
  have hr0 : 0 < r := by linarith
  have hkr : ∃ L : ℝ, 0 ≤ L ∧ ∀ x y,
      |k x ^ (4⁻¹ : ℝ) - k y ^ (4⁻¹ : ℝ)| ≤ L * |x - y| := by
    refine ⟨D * (1 + r⁻¹), by positivity, fun x y => ?_⟩
    have h := hd x (x / r) y (y / r)
    change |k x ^ (4⁻¹ : ℝ) - k y ^ (4⁻¹ : ℝ)| ≤ _ at h
    rw [← sub_div, abs_div, abs_of_pos hr0] at h
    exact h.trans_eq (by ring)
  obtain ⟨Lf, hLf, hf⟩ := weighted_root_bound (by linarith : 1 ≤ r) hk hkr
  refine ⟨max Lt Lf, le_max_of_le_left hLt, fun b hb hstep i v w => ?_⟩
  cases i with
  | zero =>
    let c : ℝ → ℝ := fun d => min cap (max 0 d)
    have hcC (d : ℝ) : c d ≤ max 1 cap := (min_le_left _ _).trans (le_max_right _ _)
    have heq (d : ℝ) :
        boundedRoutedBinCutoff χ b cap 0 (fun _ => 1) d =
          max (1 / 2) (min (max 1 cap) (c d)) * χ (c d) := by
      simp only [boundedRoutedBinCutoff, ↓reduceIte, routedBinCutoff, binWeight,
        mul_div_cancel_left₀ _ (hb 0).ne', mul_one]
      change c d * χ (c d) = _
      rw [min_eq_right (hcC d)]
      by_cases hh : c d ≤ 1 / 2
      · rw [hz _ hh, mul_zero, mul_zero]
      · rw [max_eq_right (not_le.mp hh).le]
    change |boundedRoutedBinCutoff χ b cap 0 (fun _ => 1) v ^ _ -
      boundedRoutedBinCutoff χ b cap 0 (fun _ => 1) w ^ _| ≤ _
    rw [heq v, heq w]
    have hc := ((LipschitzWith.id.const_max 0).const_min cap).dist_le_mul v w
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
    exact (ht (c v) (c w)).trans ((mul_le_mul_of_nonneg_left hc hLt).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
  | succ i =>
    have heq (d : ℝ) :
        boundedRoutedBinCutoff χ b cap (i + 1) (fun _ => 1) d =
          max (1 / 2) (min r d) * k d := by
      rw [boundedRoutedBinCutoff_succ_factor hb hr hstep]
      change d * k d = _
      by_cases hh : d ≤ 1 / 2
      · have hk0 : k d = 0 := by simp only [k, hz d hh, zero_mul]
        rw [hk0, mul_zero, mul_zero]
      by_cases hu : r ≤ d
      · have hk0 : k d = 0 := by
          have h1 : χ (d / r) = 1 := polynomialSwitch4_of_ge (by norm_num)
            ((one_le_div hr0).mpr hu)
          simp only [k, h1, sub_self, mul_zero]
        rw [hk0, mul_zero, mul_zero]
      · rw [min_eq_right (not_le.mp hu).le, max_eq_right (not_le.mp hh).le]
    change |boundedRoutedBinCutoff χ b cap (i + 1) (fun _ => 1) v ^ _ -
      boundedRoutedBinCutoff χ b cap (i + 1) (fun _ => 1) w ^ _| ≤ _
    rw [heq v, heq w]
    exact (hf v w).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

/-- Top-bin saturation is literal clipping, including a zero cap. -/
theorem boundedRoutedBinCutoff_zero_saturates {χ : ℝ → ℝ} {b : ℕ → ℝ}
    {cap v w : ℝ} (hcap : 0 ≤ cap) (hv : cap ≤ v) (hw : cap ≤ w) :
    boundedRoutedBinCutoff χ b cap 0 (fun _ => 1) v =
      boundedRoutedBinCutoff χ b cap 0 (fun _ => 1) w := by
  simp only [boundedRoutedBinCutoff, ↓reduceIte,
    max_eq_right (hcap.trans hv), max_eq_right (hcap.trans hw),
    min_eq_left hv, min_eq_left hw]

/-- Above the adjacent scale ratio, the actual unrouted fine numerator vanishes. -/
theorem boundedRoutedBinCutoff_succ_eq_zero {b : ℕ → ℝ} (hb : ∀ i, 0 < b i)
    {r : ℝ} (hr : 2 ≤ r) (hstep : ∀ i, b i = r * b (i + 1))
    (cap : ℝ) (i : ℕ) {d : ℝ} (hd : r ≤ d) :
    boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap (i + 1) (fun _ => 1) d = 0 := by
  rw [boundedRoutedBinCutoff_succ_factor hb hr hstep]
  have hz := polynomialSwitch4_of_ge (by norm_num : (1 / 2 : ℝ) < 1)
    ((one_le_div (by linarith : 0 < r)).mpr hd)
  rw [hz, sub_self, mul_zero, mul_zero]

namespace DenseBinRecipe

/-- Concrete unrouted polynomial numerator and existing valid polynomial preparation.
The scale hypotheses are supplied separately, rather than asserted by evaluation. -/
@[expose] noncomputable def polynomialUnrouted
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (b : ℕ → ℝ) (cap : ℝ) : DenseBinRecipe where
  χ := polynomialSwitch4 (1 / 2) 1
  scales := b
  cap := cap
  route := fun _ => 1
  h := polynomialPrepCutoff4 HP.θ
  ρ := HP.ρ
  K := HP.K

/-- Range and light-input support of every numerator in the concrete recipe. -/
theorem polynomialUnrouted_numerator_laws
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {b : ℕ → ℝ} {cap : ℝ}
    (hb : ∀ i, 0 < b i) (hstep : ∀ i, b i = 16 * b (i + 1)) (hcap : 0 ≤ cap) :
    let R := polynomialUnrouted HP b cap
    ∀ i d, boundedRoutedBinCutoff R.χ R.scales R.cap i R.route d ∈ Set.Icc 0 (max cap 16) ∧
      (d ≤ 1 / 2 → boundedRoutedBinCutoff R.χ R.scales R.cap i R.route d = 0) := by
  have hanti : Antitone b := antitone_nat_of_succ_le fun i => by
    have h := hb (i + 1)
    rw [hstep i]
    linarith
  intro R i d
  have hzero (x : ℝ) (hx : x ≤ 1 / 2) : polynomialSwitch4 (1 / 2) 1 x = 0 :=
    polynomialSwitch4_of_le (by norm_num) hx
  constructor
  · exact boundedRoutedBinCutoff_mem_Icc hcap (by positivity) (le_max_left _ _)
      (monotone_polynomialSwitch4 (by norm_num)) hzero
      (fun _ h => polynomialSwitch4_of_ge (by norm_num) h)
      (fun x => ⟨polynomialSwitch4_nonneg _ _ _, polynomialSwitch4_le_one _ _ _⟩)
      hb hanti (fun j => by
        rw [hstep j, mul_div_cancel_right₀ _ (hb _).ne']
        exact le_max_right _ _)
      (fun _ => 1) (fun _ => ⟨zero_le_one, le_rfl⟩) i d
  · exact fun hd => boundedRoutedBinCutoff_eq_zero hcap hzero hb hanti hd i (fun _ => 1)

end DenseBinRecipe

end Matrix
