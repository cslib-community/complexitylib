/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.EstimatorSchedule
public import CslibFrontier.Computability.LogSpaceDerandomization.ConditionalProductMean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scheduled comparisons for correction--dense sample means

The child induction bounds are root errors at the actual last budget of the slack schedule.
The correction child may use a rate larger than a fixed multiple of the bin rate. We pay its
rate mismatch explicitly. The right child is measured on its broad endpoint domain and restarts
at the midpoint rate, so its source-release factor is paid by its own precision gain.

The application below takes the actual correction and dense atoms, derives their support caps
from their gates, averages their concrete product on the retained source/endpoint slice, and
bounds the resulting root error from the two child bounds. The children can share the entire
environment; no independence of estimated values is used. The conditional mean using true atoms
is identified by `Matrix.expect_correctionAtom_mul_denseAtom` on the separate product-seed model
of that theorem. Here arbitrary seed maps also allow coupled induction comparisons.

This is the coarse-product part of [OpenAI2026LogSpace, Lemmas 7.3 and 7.6], using (7.9)--(7.12),
revision `7ef5c0cc`, printed pp. 34--41. The source has eighth moments; here the exponent is four,
the initial scale margin is one quarter, and the scheduled margin is one eighth. This does not
assemble copy/reward/detector tasks, fine products, raw paired differences, walks, noise sums,
compression or the recursive estimator. Those remain obligations of issue #1721.

## Main results

* `Cslib.LogSpaceEstimation.scheduled_child_cost_le_of_rate_le`: scheduled rate comparability.
* `Cslib.LogSpaceEstimation.scheduled_coarse_error_le`: payment of a child moment hypothesis.
* `Cslib.LogSpaceEstimation.special_correction_available`: the sparse correction term is available.
* `Matrix.scheduled_correctionAtom_denseAtom_mean_le`: actual conditional product application.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 7.2--7.6 (23 September 2026, unrefereed preprint).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.LogSpaceEstimation

/-- The scheduled child may use any endpoint rate at least `c₁` times the bin rate.
The fixed penalty is independent of scale, budget and source rate. -/
theorem scheduled_child_cost_le_of_rate_le {A a a' b c₁ u u' : ℝ} (hA : 0 ≤ A)
    (M d c i i' : ℕ) (hc : 0 < c) (h : ℤ) (hi : i' + 1 ≤ i)
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hba' : c₁ * b ≤ a')
    (hu : 0 < u) (huu' : u ≤ u') (hscale : Real.logb 2 (b / a) = (h : ℝ)) :
    binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c h) i' a' u') ≤
      (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) *
        ((2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
          (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant h) := by
  have hbase := child_cost_mul_accuracy_le_of_rate_le (s := 4) (K := 16 * c)
    (by norm_num) hA M (lastBudget M d c h) i i' hi ha hb hc₁ hba' hu huu'
  rw [hscale, scaleMargin_four] at hbase
  refine hbase.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hloss : (M : ℝ) - lastBudget M d c h ≤ d + c * (1 + (h.natAbs : ℝ)) := by
    have hnat := budget_loss_le M d c h
    have hle : lastBudget M d c h ≤ M := Nat.sub_le _ _
    exact_mod_cast hnat
  rw [scaleMajorant, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right (show (0 : ℝ) < 16 * c by positivity)).2 hloss
  have heq : ((d : ℝ) + c * (1 + (h.natAbs : ℝ))) / (16 * c) =
      (d : ℝ) / (16 * c) + (1 + (h.natAbs : ℝ)) / 16 := by field_simp
  rw [heq] at hdiv
  have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
  have hn : (0 : ℝ) ≤ h.natAbs := Nat.cast_nonneg _
  rw [habs]
  linarith

/-- For a coarse bin, the fourth power of the norm cost is exactly the scale ratio times
the source-release ratio. Neither nominal rate is replaced by an actual hit probability. -/
theorem coarse_cost_pow_four {a b u u' : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hu' : 0 < u') {h : ℤ} (hh : 0 ≤ h)
    (hscale : Real.logb 2 (b / a) = (h : ℝ)) :
    (binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4)) ^ 4 =
      (b / a) * (u' / u) := by
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  rw [binNormCost, ite_eq_left hhR, mul_pow]
  have hpow (r : ℝ) : ((2 : ℝ) ^ (r / 4)) ^ 4 = (2 : ℝ) ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    norm_num
  rw [hpow, hpow, ← hscale,
    Real.rpow_logb (by norm_num) (by norm_num) (div_pos hb ha),
    Real.rpow_logb (by norm_num) (by norm_num) (div_pos hu' hu)]

/-- A child root-moment induction hypothesis at the scheduled budget pays the coarse scale
and source costs. The output is an explicit parent-precision bound, not an assumed aggregate. -/
theorem scheduled_coarse_error_le {A a a' b c₁ u u' C E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (M d c i i' : ℕ) (hc : 0 < c) (h : ℤ) (hh : 0 ≤ h) (hi : i' + 1 ≤ i)
    (ha : 0 < a) (hb : 0 < b) (hc₁ : 0 < c₁) (hba' : c₁ * b ≤ a')
    (hu : 0 < u) (huu' : u ≤ u') (hscale : Real.logb 2 (b / a) = (h : ℝ))
    (hE : E ≤ (C * (2 : ℝ) ^
      (-precision (16 * c) A (lastBudget M d c h) i' a' u')) ^ 4) :
    (b / a) * (u' / u) * E ≤
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
    _ ≤ (b / a) * (u' / u) * (C * (2 : ℝ) ^
        (-precision (16 * c) A (lastBudget M d c h) i' a' u')) ^ 4 :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (C * (binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c h) i' a' u'))) ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, coarse_cost_pow_four ha hb hu (hu.trans_le huu') hh hscale]
      ring
    _ ≤ _ := by convert hpower using 1; ring

/-- The sparse `-E` term is available even when its stage rate is finer than the parent's
endpoint rate. The admissibility bound `a ≤ 2^L * f` bounds that negative offset. A fixed
rank reserve depending on `L` pays its entire cutoff; coarse offsets use activity directly.
This is the special-correction availability step in the proof of Lemma 7.6. -/
theorem special_correction_available {A a f u : ℝ} (M c i L : ℕ) (h : ℤ)
    (hc : 0 < c) (hA : 1 + (L : ℝ) ≤ A) (hi : 1 ≤ i)
    (ha : 0 < a) (ha1 : a ≤ 1) (hf : 0 < f) (hf1 : f ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1) (haf : a ≤ (2 : ℝ) ^ L * f)
    (hscale : Real.logb 2 (f / a) = (h : ℝ))
    (hactive : 0 < precision (16 * c) A M i a u) : scaleCutoff c h < M := by
  have hA1 : 1 ≤ A := by linarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  rcases le_or_gt 0 h with hh | hh
  · exact coarse_scale_available M c i h hc hA1 hi hh ha ha1 hf hf1 hu hu1 hscale hactive
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) ha haf
  rw [Real.logb_mul (by positivity : (2 : ℝ) ^ L ≠ 0) hf.ne', Real.logb_pow] at hlog
  have hlow : -(L : ℝ) ≤ h := by
    rw [Real.logb_div hf.ne' ha.ne'] at hscale
    norm_num at hlog
    linarith
  have habs : (h.natAbs : ℝ) ≤ L := by
    have heq : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
    rw [abs_of_neg (show (h : ℝ) < 0 by exact_mod_cast hh)] at heq
    linarith
  have hla := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ha.le ha1
  have hlu := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu.le hu1
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hAi : 1 + (L : ℝ) ≤ A * i := hA.trans (le_mul_of_one_le_right (zero_le_one.trans hA1) hiR)
  have hM : (16 * c : ℝ) * (1 + (L : ℝ)) < M := by
    have hdiv : 1 + (L : ℝ) < (M : ℝ) / (16 * c) := by
      dsimp only [precision] at hactive
      linarith
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    simpa only [mul_comm] using
      (lt_div_iff₀ (show (0 : ℝ) < 16 * c by positivity)).mp hdiv
  have hcut : ((scaleCutoff c h : ℕ) : ℝ) < M := by
    simp only [scaleCutoff, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have : (c : ℝ) * (1 + (h.natAbs : ℝ)) ≤ c * (1 + (L : ℝ)) := by gcongr
    have hcR : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith
  exact_mod_cast hcut

end Cslib.LogSpaceEstimation

namespace Matrix

open Cslib Cslib.LogSpaceEstimation

variable {Ω V ι κ υ : Type*} [Fintype Ω] [Fintype V] [Fintype ι] [Fintype κ] [Fintype υ]
  {KF Kc KB : ℕ} {N u f b : ℝ} {I : ℝ → ℝ → ℝ} {τ Q hF ρF k hB ρB : ℝ → ℝ}
  {X : ι → V → Prop} {Z Zt : κ → V → Prop} {Y Yt : υ → V → Prop}
  [∀ t x, Decidable (X t x)] [∀ t z, Decidable (Z t z)] [∀ t z, Decidable (Zt t z)]
  [∀ t y, Decidable (Y t y)] [∀ t y, Decidable (Yt t y)]

/-- The actual coarse correction--dense conditional mean at the schedule's last budget.
The only error hypotheses are the two earlier child root bounds. Atom gates discharge both
support caps. The correction rate need only satisfy `c₁ * b ≤ f`; the right child restarts at
rate `f ≥ u`. This does not identify arbitrary coupled seed maps with the independent true-mean
model: use `Matrix.expect_correctionAtom_mul_denseAtom` for that separate identity. -/
theorem scheduled_correctionAtom_denseAtom_mean_le
    (drawF : Ω → ι × κ) (drawB : Ω → υ)
    (G G' H H' : Ω → Matrix V V ℝ) (g g' : Ω → V → ℝ)
    (hN : 0 < N) (hu : 0 < u) (hf : 0 < f)
    (hQ0 : ∀ v, 0 ≤ Q v) (hk0 : ∀ v, 0 ≤ k v)
    (hρF0 : ∀ r, 0 ≤ ρF r) (hρF1 : ∀ r, ρF r ≤ 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1)
    (hρB0 : ∀ r, 0 ≤ ρB r) (hρB1 : ∀ r, ρB r ≤ 1)
    (hg0 : ∀ σ z, 0 ≤ g σ z) (hg'0 : ∀ σ z, 0 ≤ g' σ z) (hg'1 : ∀ σ z, g' σ z ≤ 1)
    {AF AB : ℝ} (hAF : 0 ≤ AF) (hAB : 0 ≤ AB)
    (hQbound : ∀ σ x z, Q (G' σ x z / f) ≤ AF)
    (hkbound : ∀ σ z y, k (H σ z y / b) ≤ AB)
    (hKc : 0 < Kc) (hIQ : ∀ v r, Q v ≠ 0 → ρF r ≠ 0 → I v r = 1)
    {gF : ℝ} (hgF : gF ≤ 1) (hτclose : ∀ r, gF ≤ r → τ r = 0)
    (hYt : ∀ t y, Yt t y → Y t y) (hKB : 0 < KB)
    {eB gB : ℝ} (heB : 0 ≤ eB) (hkzero : ∀ v, v ≤ eB → k v = 0)
    (hgB : gB ≤ eB) (hρBclose : ∀ r, gB ≤ r → ρB r = 0)
    {A a c₁ C πf : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (ha : 0 < a) (hab : a ≤ b)
    (hc₁ : 0 < c₁) (hbf : c₁ * b ≤ f) (huf : u ≤ f) (hπf : 0 < πf)
    (M d c i iF iB : ℕ) (hc : 0 < c) (offset : ℤ) (hoffset : 0 ≤ offset)
    (hiF : iF + 1 ≤ i) (hiB : iB + 1 ≤ i)
    (hscale : Real.logb 2 (b / a) = (offset : ℝ)) :
    let F := fun σ => correctionAtom I τ KF Kc f (G σ) X Z Zt Q hF ρF (g σ) (drawF σ)
    let F' := fun σ => correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ)
    let B := fun σ => denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ)
    let B' := fun σ => denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ)
    let Xu := fun σ x => X (drawF σ).1 x
    let Zf := fun σ z => Zt (drawF σ).2 z
    let Ya := fun σ y => Yt (drawB σ) y
    let payment := (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
      (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant offset
    rootDistPow 4 N u Xu Zf F F' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iF f u)) ^ 4 →
    rootDistPow 4 N f Zf (fun σ y => Y (drawB σ) y) B B' ≤
      (C * (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c offset) iB b f)) ^ 4 →
    rootDistPow 4 N u Xu Ya
        (fun _ x y => (b / a) * (f / πf) * conditionalTableMean Xu Ya
          (fun σ x y => ∑ z ∈ ({z | Zf σ z} : Finset V), F σ x z * B σ z y) x y)
        (fun _ x y => (b / a) * (f / πf) * conditionalTableMean Xu Ya
          (fun σ x y => ∑ z ∈ ({z | Zf σ z} : Finset V), F' σ x z * B' σ z y) x y) ≤
      (2048 * 16384 : ℝ) * (f / πf) *
        ((2 * AB) * KB * (C * (2 : ℝ) ^ (-Real.logb 2 c₁ / 2) * payment) ^ 4 +
          (2 * AF) * Kc * (C * payment) ^ 4) := by
  classical
  dsimp only
  intro hleft hright
  have hrightUsage := (Cslib.rowNormPow_mono_terminal (p := 4) (by positivity : 0 ≤ N * f)
    (X := fun σ z => Zt (drawF σ).2 z)
    (Y := fun σ y => Yt (drawB σ) y) (Y' := fun σ y => Y (drawB σ) y)
    (fun σ y => hYt (drawB σ) y)
    (fun σ z y => (denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ) z y) ^ (4⁻¹ : ℝ) -
      (denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ) z y) ^ (4⁻¹ : ℝ))).trans hright
  have hb := ha.trans_le hab
  have hprod := correctionAtom_denseAtom_rootDistPow_le
    (X := X) (Z := Z) (Zt := Zt) (Y := Y) (Yt := Yt)
    (KF := KF) (I := I) (τ := τ) (Q := Q) (hF := hF) (ρF := ρF)
    (k := k) (hB := hB) (ρB := ρB) (b := b) drawF drawB G G' H H' g g'
    (by decide : 4 ≠ 0) hN hu hf hQ0 hk0 hρF0 hρF1 hτ0 hτ1 hρB0 hρB1
    hg0 hg'0 hg'1 hAF hAB hQbound hkbound hKc hIQ hgF hτclose hYt hKB heB hkzero hgB hρBclose
  have hmean := Cslib.rootDistPow_conditionalTableMean_mul_le (by decide : 4 ≠ 0) hN hu
    (X := fun σ x => X (drawF σ).1 x) (Y := fun σ y => Yt (drawB σ) y)
    (H := fun σ x y => ∑ z ∈ ({z | Zt (drawF σ).2 z} : Finset V),
      correctionAtom I τ KF Kc f (G σ) X Z Zt Q hF ρF (g σ) (drawF σ) x z *
        denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ) z y)
    (H' := fun σ x y => ∑ z ∈ ({z | Zt (drawF σ).2 z} : Finset V),
      correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ) x z *
        denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ) z y)
    (c := (b / a) * (f / πf)) (by positivity)
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg
      (correctionAtom_nonneg hQ0 hρF0 hτ0 (hg0 σ) (drawF σ) x z)
      (denseAtom_nonneg hk0 hρB0 (drawB σ) z y))
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg
      (correctionAtom_nonneg hQ0 hρF0 hτ0 (hg'0 σ) (drawF σ) x z)
      (denseAtom_nonneg hk0 hρB0 (drawB σ) z y))
  have hpayF := scheduled_coarse_error_le hA hC M d c i iF hc offset hoffset hiF
    ha (ha.trans_le hab) hc₁ hbf hu (le_refl u) hscale hleft
  have hpayB := scheduled_coarse_error_le hA hC M d c i iB hc offset hoffset hiB
    ha (ha.trans_le hab) (by norm_num : (0 : ℝ) < 1) (by simp) hu huf hscale hrightUsage
  simp only [div_self hu.ne', mul_one] at hpayF
  simp only [Real.logb_one, neg_zero, zero_div, Real.rpow_zero, mul_one] at hpayB
  dsimp only at hprod
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.cast_ofNat, one_div_div] at hprod hmean
  refine hmean.trans ((mul_le_mul_of_nonneg_left hprod (by positivity)).trans ?_)
  calc
    _ = (2048 * 16384 : ℝ) * (f / πf) *
        ((2 * AB) * KB * ((b / a) * rootDistPow 4 N u
            (fun σ x => X (drawF σ).1 x) (fun σ z => Zt (drawF σ).2 z)
            (fun σ => correctionAtom I τ KF Kc f (G σ) X Z Zt Q hF ρF (g σ) (drawF σ))
            (fun σ => correctionAtom I τ KF Kc f (G' σ) X Z Zt Q hF ρF (g' σ) (drawF σ))) +
          (2 * AF) * Kc * ((b / a) * (f / u) * rootDistPow 4 N f
            (fun σ z => Zt (drawF σ).2 z) (fun σ y => Yt (drawB σ) y)
            (fun σ => denseAtom Y Yt k hB ρB KB b (H σ) (drawB σ))
            (fun σ => denseAtom Y Yt k hB ρB KB b (H' σ) (drawB σ)))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hpayF (by positivity))
        (mul_le_mul_of_nonneg_left hpayB (by positivity))) (by positivity)

end Matrix
