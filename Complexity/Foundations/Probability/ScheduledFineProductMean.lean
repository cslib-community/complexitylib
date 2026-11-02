/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ScheduledProductMean
public import Complexity.Foundations.Probability.FineProductMean

/-!
# Scheduled fine-product means

Actual nested terminal masks on a product seed space are changed before taking powers.
The actual density ratio stays in the sample coefficient; comparable nominal rates pay the
resulting cubic scale cost using the two child induction bounds at the schedule's last budget.
Factors may depend jointly on both seed coordinates.

This is the fine-product portion of [OpenAI2026LogSpace, Lemmas 7.3 and 7.6], printed
pp. 36--41, revision `7ef5c0cc`. We use fourth rather than eighth moments and restrict scale
offsets to integers. This does not assemble the full estimator or establish native RL = L.

## Main results

* `Cslib.LogSpaceEstimation.scheduled_fineProductMean_le`: the coupled product comparison.
* `Matrix.scheduled_fine_correctionAtom_denseAtom_mean_le`: the actual gated atom application.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.LogSpaceEstimation

variable {V : Type*} [Fintype V]

/-- For a fine bin, the fourth power of the norm cost is exactly the cube of the scale ratio times
the source-release ratio. Neither nominal rate is replaced by an actual hit probability. -/
theorem fine_cost_pow_four {a b u u' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hu' : 0 < u') {h : ℤ} (hh : h < 0)
    (hscale : Real.logb 2 (b / a) = (h : ℝ)) :
    (binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4)) ^ 4 =
      (b / a) ^ 3 * (u' / u) := by
  have hhR : (h : ℝ) < 0 := by exact_mod_cast hh
  rw [binNormCost, ite_eq_right (not_le.mpr hhR), mul_pow]
  have hpow (r : ℝ) : ((2 : ℝ) ^ (r / 4)) ^ 4 = (2 : ℝ) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  rw [hpow, hpow]
  have heq : (4 - 1 : ℝ) * (h : ℝ) = (h : ℝ) * 3 := by ring
  rw [heq, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← hscale,
    Real.rpow_logb (by norm_num) (by norm_num) (div_pos hb ha),
    Real.rpow_logb (by norm_num) (by norm_num) (div_pos hu' hu)]
  norm_num

/-- A child root-moment induction hypothesis at the scheduled budget pays the fine scale
and source costs. The output is an explicit parent-precision bound, not an assumed aggregate. -/
theorem scheduled_fine_error_le {A a a' b c₁ u u' C E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (M d c i i' : ℕ) (hc : 0 < c) (h : ℤ) (hh : h < 0) (hi : i' + 1 ≤ i)
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hba' : c₁ * b ≤ a')
    (hu : 0 < u) (huu' : u ≤ u') (hscale : Real.logb 2 (b / a) = (h : ℝ))
    (hE : E ≤ (C * (2 : ℝ) ^
      (-precision (16 * c) A (lastBudget M d c h) i' a' u')) ^ 4) :
    (b / a) ^ 3 * (u' / u) * E ≤
      (C * (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) *
        ((2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
          (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant h)) ^ 4 := by
  have hbin := (binNormCost_pos 4 (h : ℝ)).le
  have hu' := hu.trans_le huu'
  have hcost := scheduled_child_cost_le_of_rate_le hA M d c i i' hc h hi ha hb hc₁ hba'
    hu huu' hscale
  have hweighted := mul_le_mul_of_nonneg_left hcost hC
  have hpower := pow_le_pow_left₀ (by positivity) hweighted 4
  calc
    _ ≤ (b / a) ^ 3 * (u' / u) * (C * (2 : ℝ) ^
        (-precision (16 * c) A (lastBudget M d c h) i' a' u')) ^ 4 :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (C * (binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c h) i' a' u'))) ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, fine_cost_pow_four ha hb hu (hu.trans_le huu') hh hscale]
      ring
    _ ≤ _ := by convert hpower using 1; ring

/-- The actual fine-product conditional mean error, paid by the two earlier child root-moment
bounds. The correction child's endpoint rate may only dominate a constant multiple of the bin
rate. The sample retains the actual importance ratio `πa / πb` and midpoint normalization. -/
theorem scheduled_fineProductMean_le {Γ Υ : Type*} [Fintype Γ] [Fintype Υ]
    {Kf Kr Kc : ℕ} {N u a b f πa πb πf Ca cb CF CB : ℝ}
    (X : Γ → V → Prop) (Ya Yb : Υ → V → Prop) (Z : (Γ × Υ) → V → Prop)
    [∀ γ x, Decidable (X γ x)] [∀ τ y, Decidable (Ya τ y)] [∀ τ y, Decidable (Yb τ y)]
    [∀ σ z, Decidable (Z σ z)]
    (hN : 0 < N) (hu : 0 < u) (hb : 0 < b) (hba : b ≤ a)
    (hf : 0 < f) (hπa : 0 < πa) (hπb : 0 < πb) (hπf : 0 < πf)
    (hCa : 0 ≤ Ca) (hcb : 0 < cb) (hupper : πa ≤ Ca * a) (hlower : cb * b ≤ πb)
    (hYaπ : ∀ y, (dens {τ | Ya τ y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {τ | Yb τ y} : ℝ) = πb) (hsub : ∀ τ y, Yb τ y → Ya τ y)
    (hCF : 0 ≤ CF) (hCB : 0 ≤ CB) {F F' B B' : (Γ × Υ) → V → V → ℝ}
    (hF : ∀ σ x z, 0 ≤ F σ x z) (hF' : ∀ σ x z, 0 ≤ F' σ x z)
    (hB : ∀ σ z y, 0 ≤ B σ z y) (hB' : ∀ σ z y, 0 ≤ B' σ z y)
    (hFbound : ∀ σ x z, F σ x z ≤ CF) (hF'bound : ∀ σ x z, F' σ x z ≤ CF)
    (hBbound : ∀ σ z y, B σ z y ≤ CB) (hB'bound : ∀ σ z y, B' σ z y ≤ CB)
    (hleft : ∀ σ x, X σ.1 x → #{z ∈ ({z | Z σ z} : Finset V) | F σ x z ≠ 0} ≤ Kf)
    (hleft' : ∀ σ x, X σ.1 x → #{z ∈ ({z | Z σ z} : Finset V) | F' σ x z ≠ 0} ≤ Kf)
    (hrow : ∀ σ z, Z σ z → #{y ∈ ({y | Yb σ.2 y} : Finset V) | B σ z y ≠ 0} ≤ Kr)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ.1 x} : Finset V) | F' σ x z ≠ 0} ≤ Kc)
    (hBsupport : ∀ σ z y, ¬ Yb σ.2 y → B σ z y = 0)
    (hB'support : ∀ σ z y, ¬ Yb σ.2 y → B' σ z y = 0)
    {A C c₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hc₁ : 0 < c₁)
    (hbf : c₁ * b ≤ f) (huf : u ≤ f)
    (M d c i iF iB : ℕ) (hc : 0 < c) (offset : ℤ) (hoffset : offset < 0)
    (hiF : iF + 1 ≤ i) (hiB : iB + 1 ≤ i)
    (hscale : Real.logb 2 (b / a) = (offset : ℝ))
    (hleftError : rootDistPow 4 N u (fun σ x => X σ.1 x) Z F F' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iF f u)) ^ 4)
    (hrightError : rootDistPow 4 N f Z (fun σ y => Yb σ.2 y) B B' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iB b f)) ^ 4) :
    let payment := (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
      (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant offset
    let E := fun σ x y => (∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y) -
      ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y
    rowNormPow 4 N u (fun (σ : Γ × Υ) x => X σ.1 x) (fun σ y => Ya σ.2 y)
        (fun _ x y => conditionalTableMean (fun σ x => X σ.1 x) (fun σ y => Ya σ.2 y)
          (fun σ x y => (b / a) * (f / πf) * (πa / πb) * E σ x y) x y) ≤
      ((f / πf) ^ 4 * (Ca / cb)) *
        (((4 : ℝ) * ((Kf : ℝ) * CF * CB) ^ ((4 - 1 : ℝ) / 4)) ^ 4 *
          (2 ^ (2 * (4 - 1)) * (4 : ℝ) ^ 4) *
          (CB * Kr * (C * (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) * payment) ^ 4 +
            CF * Kc * (C * payment) ^ 4)) := by
  dsimp only
  have ha := hb.trans_le hba
  have hprod := Cslib.rowNormPow_fineProductMean_le X Ya Yb Z
    (by decide : 4 ≠ 0) hN hu hb hba hf hπa hπb hπf hCa hcb hupper hlower
    hYaπ hYbπ hsub hCF hCB hF hF' hB hB' hFbound hF'bound hBbound hB'bound
    hleft hleft' hrow hcol hBsupport hB'support
  have hpayF := scheduled_fine_error_le hA hC M d c i iF hc offset hoffset hiF
    ha hb hc₁ hbf hu (le_refl u) hscale hleftError
  have hpayB := scheduled_fine_error_le hA hC M d c i iB hc offset hoffset hiB
    ha hb (by norm_num : (0 : ℝ) < 1) (by simp) hu huf hscale hrightError
  simp only [div_self hu.ne', mul_one] at hpayF
  simp only [Real.logb_one, neg_zero, zero_div, Real.rpow_zero, mul_one] at hpayB
  refine hprod.trans ?_
  calc
    _ = ((f / πf) ^ 4 * (Ca / cb)) *
        (((4 : ℝ) * ((Kf : ℝ) * CF * CB) ^ ((4 - 1 : ℝ) / 4)) ^ 4 *
          (2 ^ (2 * (4 - 1)) * (4 : ℝ) ^ 4) *
          (CB * Kr * ((b / a) ^ 3 * rootDistPow 4 N u (fun σ x => X σ.1 x) Z F F') +
            CF * Kc * ((b / a) ^ 3 * (f / u) *
              rootDistPow 4 N f Z (fun σ y => Yb σ.2 y) B B'))) := by
                norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat]
                ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hpayF (by positivity))
          (mul_le_mul_of_nonneg_left hpayB (by positivity))) (by positivity)) (by positivity)

end Cslib.LogSpaceEstimation

namespace Matrix

open Cslib Cslib.LogSpaceEstimation

variable {Γ Υ V ι κ υ : Type*} [Fintype Γ] [Fintype Υ] [Fintype V]
  [Fintype ι] [Fintype κ] [Fintype υ]
  {KF Kc KB : ℕ} {N u f b : ℝ} {I : ℝ → ℝ → ℝ} {τ Q hF ρF k hB ρB : ℝ → ℝ}
  {X : ι → V → Prop} {Z Zt : κ → V → Prop} {Y Yt : υ → V → Prop}
  [∀ t x, Decidable (X t x)] [∀ t z, Decidable (Z t z)] [∀ t z, Decidable (Zt t z)]
  [∀ t y, Decidable (Y t y)] [∀ t y, Decidable (Yt t y)]

/-- The scheduled fine comparison for actual correction and dense atoms. All row and incoming
caps follow from the actual gates. The two raw estimates and multipliers may share both seeds.
The broad endpoint mask and the actual fine hit density are kept distinct from nominal rates. -/
theorem scheduled_fine_correctionAtom_denseAtom_mean_le
    (drawF : Γ → ι × κ) (drawB : Υ → υ)
    (G G' H H' : (Γ × Υ) → Matrix V V ℝ) (g g' : (Γ × Υ) → V → ℝ)
    (Ya : Υ → V → Prop) [∀ t y, Decidable (Ya t y)]
    (hN : 0 < N) (hu : 0 < u) (hf : 0 < f) (hb : 0 < b)
    {a πa πb πf Ca cb AF AB : ℝ} (hba : b ≤ a)
    (hπa : 0 < πa) (hπb : 0 < πb) (hπf : 0 < πf) (hCa : 0 ≤ Ca) (hcb : 0 < cb)
    (hupper : πa ≤ Ca * a) (hlower : cb * b ≤ πb)
    (hYaπ : ∀ y, (dens {t | Ya t y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {t | Yt (drawB t) y} : ℝ) = πb)
    (hsub : ∀ t y, Yt (drawB t) y → Ya t y)
    (hQ0 : ∀ v, 0 ≤ Q v) (hk0 : ∀ v, 0 ≤ k v)
    (hρF0 : ∀ r, 0 ≤ ρF r) (hρF1 : ∀ r, ρF r ≤ 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1)
    (hρB0 : ∀ r, 0 ≤ ρB r) (hρB1 : ∀ r, ρB r ≤ 1)
    (hg0 : ∀ σ z, 0 ≤ g σ z) (hg1 : ∀ σ z, g σ z ≤ 1)
    (hg'0 : ∀ σ z, 0 ≤ g' σ z) (hg'1 : ∀ σ z, g' σ z ≤ 1)
    (hAF : 0 ≤ AF) (hAB : 0 ≤ AB) (hQbound : ∀ v, Q v ≤ AF) (hkbound : ∀ v, k v ≤ AB)
    (hKF : 0 < KF) (hKc : 0 < Kc) (hKB : 0 < KB)
    (hIQ : ∀ v r, Q v ≠ 0 → ρF r ≠ 0 → I v r = 1)
    {gF : ℝ} (hgF : gF ≤ 1) (hτclose : ∀ r, gF ≤ r → τ r = 0)
    (hZt : ∀ t z, Zt t z → Z t z) (hYt : ∀ t y, Yt t y → Y t y)
    {eF rF eB rB : ℝ} (heF : 0 ≤ eF) (hQzero : ∀ v, v ≤ eF → Q v = 0)
    (hrF : rF ≤ eF) (hρFclose : ∀ r, rF ≤ r → ρF r = 0)
    (heB : 0 ≤ eB) (hkzero : ∀ v, v ≤ eB → k v = 0)
    (hrB : rB ≤ eB) (hρBclose : ∀ r, rB ≤ r → ρB r = 0)
    {A C c₁ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hc₁ : 0 < c₁)
    (hbf : c₁ * b ≤ f) (huf : u ≤ f)
    (M d c i iF iB : ℕ) (hc : 0 < c) (offset : ℤ) (hoffset : offset < 0)
    (hiF : iF + 1 ≤ i) (hiB : iB + 1 ≤ i)
    (hscale : Real.logb 2 (b / a) = (offset : ℝ)) :
    let F := fun σ => correctionAtom I τ KF Kc f (G σ) X Z Zt Q hF ρF (g σ) (drawF σ.1)
    let F' := fun σ => correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ.1)
    let B := fun σ => denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ.2)
    let B' := fun σ => denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ.2)
    let Xu := fun γ x => X (drawF γ).1 x
    let Zf := fun σ z => Zt (drawF σ.1).2 z
    let payment := (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
      (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant offset
    rootDistPow 4 N u (fun σ x => Xu σ.1 x) Zf F F' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iF f u)) ^ 4 →
    rootDistPow 4 N f Zf (fun σ y => Y (drawB σ.2) y) B B' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iB b f)) ^ 4 →
    rowNormPow 4 N u (fun (σ : Γ × Υ) x => Xu σ.1 x) (fun σ y => Ya σ.2 y)
      (fun _ x y => conditionalTableMean (fun σ x => Xu σ.1 x) (fun σ y => Ya σ.2 y)
        (fun σ x y => (b / a) * (f / πf) * (πa / πb) *
          ((∑ z ∈ ({z | Zf σ z} : Finset V), F σ x z * B σ z y) -
            ∑ z ∈ ({z | Zf σ z} : Finset V), F' σ x z * B' σ z y)) x y) ≤
      ((f / πf) ^ 4 * (Ca / cb)) *
        (((4 : ℝ) * ((KF : ℝ) * (2 * AF) * (2 * AB)) ^ ((4 - 1 : ℝ) / 4)) ^ 4 *
          (2 ^ (2 * (4 - 1)) * (4 : ℝ) ^ 4) *
          ((2 * AB) * KB * (C * (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) * payment) ^ 4 +
            (2 * AF) * Kc * (C * payment) ^ 4)) := by
  classical
  dsimp only
  intro hleftError hrightBroad
  have hrightError := (Cslib.rowNormPow_mono_terminal (p := 4) (by positivity : 0 ≤ N * f)
    (X := fun (σ : Γ × Υ) z => Zt (drawF σ.1).2 z)
    (Y := fun σ y => Yt (drawB σ.2) y) (Y' := fun σ y => Y (drawB σ.2) y)
    (fun σ y => hYt (drawB σ.2) y)
    (fun σ z y => (denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ.2) z y) ^ (4⁻¹ : ℝ) -
      (denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ.2) z y) ^ (4⁻¹ : ℝ))).trans hrightBroad
  have hFbound (J : Matrix V V ℝ) (v : V → ℝ) (hv0 : ∀ z, 0 ≤ v z)
      (hv1 : ∀ z, v z ≤ 1) (t : ι × κ) (x z : V) :
      correctionAtom I τ KF Kc f J X Z Zt Q hF ρF v t x z ≤ 2 * AF := by
    calc
      _ ≤ |correctionAtom I τ KF Kc f J X Z Zt Q hF ρF v t x z| := le_abs_self _
      _ ≤ 2 * |Q (J x z / f)| * |v z| := abs_correctionAtom_le hρF0 hρF1 hτ0 hτ1 _ _ _
      _ = 2 * Q (J x z / f) * v z := by rw [abs_of_nonneg (hQ0 _), abs_of_nonneg (hv0 _)]
      _ ≤ (2 * AF) * 1 := mul_le_mul
        (mul_le_mul_of_nonneg_left (hQbound _) (by norm_num)) (hv1 z) (hv0 z) (by positivity)
      _ = _ := mul_one _
  have hBbound (J : Matrix V V ℝ) (t : υ) (z y : V) :
      denseAtom Y Yt k hB ρB KB b J t z y ≤ 2 * AB := by
    calc
      _ ≤ |denseAtom Y Yt k hB ρB KB b J t z y| := le_abs_self _
      _ ≤ 2 * |k (J z y / b)| := abs_denseAtom_le hρB0 hρB1 _ _ _
      _ = 2 * k (J z y / b) := by rw [abs_of_nonneg (hk0 _)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hkbound _) (by norm_num)
  have hleftCap (J : Matrix V V ℝ) (v : V → ℝ) (t : ι × κ) (x : V) :
      #{z ∈ ({z | Zt t.2 z} : Finset V) |
        correctionAtom I τ KF Kc f J X Z Zt Q hF ρF v t x z ≠ 0} ≤ KF := by
    refine (card_le_card ?_).trans
      (card_filter_correctionAtom_row_ne_zero_lt (I := I) (τ := τ) (Kc := Kc)
        (f := f) (G := J) (X := X) (Y := Z) (Yt := Zt) (h := hF) (g₀ := v)
        hKF heF hQzero hrF hρFclose t x).le
    intro z hz
    have hzZ : Zt t.2 z := by
      simpa only [mem_filter, mem_univ, true_and] using (mem_filter.mp hz).1
    refine mem_filter.mpr ⟨?_, (mem_filter.mp hz).2⟩
    simpa only [mem_filter, mem_univ, true_and] using hZt t.2 z hzZ
  refine scheduled_fineProductMean_le (fun γ x => X (drawF γ).1 x) Ya
    (fun t y => Yt (drawB t) y) (fun σ z => Zt (drawF σ.1).2 z)
    hN hu hb hba hf hπa hπb hπf hCa hcb hupper hlower hYaπ hYbπ hsub
    (by positivity) (by positivity)
    (fun σ => correctionAtom_nonneg hQ0 hρF0 hτ0 (hg0 σ) (drawF σ.1))
    (fun σ => correctionAtom_nonneg hQ0 hρF0 hτ0 (hg'0 σ) (drawF σ.1))
    (fun σ => denseAtom_nonneg hk0 hρB0 (drawB σ.2))
    (fun σ => denseAtom_nonneg hk0 hρB0 (drawB σ.2))
    (fun σ => hFbound (G σ) (g σ) (hg0 σ) (hg1 σ) (drawF σ.1))
    (fun σ => hFbound (G' σ) (g' σ) (hg'0 σ) (hg'1 σ) (drawF σ.1))
    (fun σ => hBbound (H σ) (drawB σ.2)) (fun σ => hBbound (H' σ) (drawB σ.2))
    (fun σ x _ => hleftCap (G σ) (g σ) (drawF σ.1) x)
    (fun σ x _ => hleftCap (G' σ) (g' σ) (drawF σ.1) x) ?_ ?_ ?_ ?_
    hA hC hc₁ hbf huf M d c i iF iB hc offset hoffset hiF hiB hscale hleftError hrightError
  · intro σ z _
    refine (card_le_card ?_).trans
      (card_filter_denseAtom_ne_zero_lt (h := hB) (a := b) (G := H σ)
        hYt hKB heB hkzero hrB hρBclose (drawB σ.2) z).le
    intro y hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩
  · intro σ z _
    exact (card_filter_correctionAtom_col_ne_zero_lt hKc hIQ hgF hτclose (drawF σ.1) z).le
  · intro σ z y hy
    simp [denseAtom, hy]
  · intro σ z y hy
    simp [denseAtom, hy]

end Matrix
