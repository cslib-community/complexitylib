/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPreparationPayment
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Relative RAW payment and weighted preparation sensitivity

The denominator is clipped after the joint mean. Its inverse fourth root has
fourth-power Lipschitz coefficient `1/8`. The exact decoder error keeps the actual
nonnegative numerator, including the RAW gates and maximum multiplier.

A relative RAW allowance is additional information, not a consequence of ordinary
RAW accuracy. With a checked reference range `0 ≤ G ≤ d*f`, it pays the existing
sparse incoming preparation estimate with coefficient `(L*(1+Kc)*(1+d))^4`.
Without a rate-uniform reference range this need not improve the ordinary payment:
`G ≤ 1` gives `d = 1/f`. Recursive propagation of this extra allowance is not proved.
These are original local estimates; they do not assert a full hierarchy invariant.

## Main results

* `inverse_fourth_root_fourth_le`: sharp fourth-power denominator sensitivity.
* `preparation_relative_row_moment`: actual sparse relative RAW payment.
* `correctionRequest_weighted_root_error`: exact masked numerator identity.
* `BudgetData.evaluate_preparation_relative_root`: successful PREP, its weighted
  clipped mean and the fixed-RAW/MAX rooted consumer.
-/

public section
noncomputable section
namespace Matrix.FourthRootHierarchyParams
open Cslib Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix

/-- The derivative calculation on the actual clipped denominator interval. -/
theorem inverse_fourth_root_fourth_le {a b : ℝ}
    (ha : a ∈ Set.Icc (1 / 2 : ℝ) 1) (hb : b ∈ Set.Icc (1 / 2 : ℝ) 1) :
    |a ^ (-(4⁻¹ : ℝ)) - b ^ (-(4⁻¹ : ℝ))| ^ 4 ≤ |a - b| ^ 4 / 8 := by
  let C : ℝ := (1 / 4) * (1 / 2 : ℝ) ^ (-(5 / 4 : ℝ))
  have hd := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun x : ℝ => x ^ (-(4⁻¹ : ℝ)))
    (f' := fun x : ℝ => -(4⁻¹ : ℝ) * x ^ (-(4⁻¹ : ℝ) - 1))
    (s := Set.Icc (1 / 2 : ℝ) 1) (C := C)
    (fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (by linarith [hx.1]))).hasDerivWithinAt)
    (fun x hx => ?_) (convex_Icc _ _) hb ha
  · rw [Real.norm_eq_abs, Real.norm_eq_abs] at hd
    have hc : C ^ 4 = (1 / 8 : ℝ) := by
      dsimp only [C]
      rw [mul_pow, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ (-(5 / 4 : ℝ))) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    have hp := pow_le_pow_left₀ (abs_nonneg _) hd 4
    simpa only [mul_pow, hc, div_eq_mul_inv, one_mul, mul_comm] using hp
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1]) _)]
    norm_num only [abs_neg, abs_inv, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    change (1 / 4 : ℝ) * x ^ (-(5 / 4 : ℝ)) ≤ (1 / 4) * _
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 4)
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by norm_num)

/-- Exact rooted error of a fixed nonnegative numerator. No factor of the terminal
rate appears outside the dimensionless clipped denominator. -/
theorem numerator_root_error {n a b : ℝ} (hn : 0 ≤ n) (ha : 0 < a) (hb : 0 < b) :
    |(n / a) ^ (4⁻¹ : ℝ) - (n / b) ^ (4⁻¹ : ℝ)| ^ 4 =
      n * |a ^ (-(4⁻¹ : ℝ)) - b ^ (-(4⁻¹ : ℝ))| ^ 4 := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Real.mul_rpow hn (inv_nonneg.mpr ha.le),
    Real.mul_rpow hn (inv_nonneg.mpr hb.le), Real.inv_rpow ha.le, Real.inv_rpow hb.le,
    ← Real.rpow_neg ha.le, ← Real.rpow_neg hb.le, ← mul_sub, abs_mul, mul_pow,
    abs_of_nonneg (Real.rpow_nonneg hn _), ← Real.rpow_natCast,
    ← Real.rpow_mul hn]
  norm_num

/-- The actual numerator is retained before any global cap is used. -/
theorem numerator_clipped_root_fourth_le {n : ℝ} (hn : 0 ≤ n) (v w : ℝ) :
    |(n / NormalizedRow.clip v) ^ (4⁻¹ : ℝ) -
      (n / NormalizedRow.clip w) ^ (4⁻¹ : ℝ)| ^ 4 ≤
      n * |NormalizedRow.clip v - NormalizedRow.clip w| ^ 4 / 8 := by
  have hv := NormalizedRow.clip_bounds v
  have hw := NormalizedRow.clip_bounds w
  rw [numerator_root_error hn (by linarith [hv.1]) (by linarith [hw.1])]
  exact (mul_le_mul_of_nonneg_left (inverse_fourth_root_fourth_le hv hw) hn).trans_eq
    (by ring)

/-- A checked reference range converts ordinary relative error into RAW error.
The approximate table is signed and unbounded; its support is never replaced by
canonical support. The factor `f` is explicit and cancels only the sparse transfer's
inverse rate, not the cost of proving the relative premise. -/
theorem raw_relative_row_moment {Ω V : Type*} [Fintype Ω] [Fintype V]
    {N u f d : ℝ} (hNu : 0 ≤ N * u) (hf : 0 < f) (_hd : 0 ≤ d)
    (X U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (U σ y)]
    (A G : Ω → Matrix V V ℝ) (hG : ∀ σ x y, G σ x y ∈ Set.Icc 0 (d * f)) :
    rowNormPow 4 N u X U (fun σ x y => A σ x y - G σ x y) ≤
      (f * (1 + d)) ^ 4 * rowNormPow 4 N u X U
        (fun σ x y => (A σ x y - G σ x y) / (f + G σ x y)) := by
  apply rowNormPow_le_mul hNu
  intro σ x y _ _
  have hden : 0 < f + G σ x y := by linarith [(hG σ x y).1]
  have he : |A σ x y - G σ x y| =
      (f + G σ x y) * |(A σ x y - G σ x y) / (f + G σ x y)| := by
    rw [abs_div, abs_of_pos hden]
    field_simp
  rw [he]
  have hb : f + G σ x y ≤ f * (1 + d) := by nlinarith [(hG σ x y).2]
  simpa only [mul_pow] using pow_le_pow_left₀
    (mul_nonneg hden.le (abs_nonneg _))
    (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) 4

/-- Actual row and incoming sparsity pay PREP from relative RAW accuracy under an
explicit reference range. Both gate supports are supplied by `preparation_row_moment`.
Ordinary accuracy may be retained simultaneously; it does not imply this premise. -/
theorem preparation_relative_row_moment (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (Ω V : Type*) [Fintype Ω] [Fintype V]
      (X U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (U σ y)]
      (Kc : ℕ), 0 < Kc → ∀ (f d : ℝ), 0 < f → 0 ≤ d →
    ∀ (A G : Ω → Matrix V V ℝ), (∀ σ x y, G σ x y ∈ Set.Icc 0 (d * f)) →
    ∀ (N u : ℝ), 0 ≤ N * u →
    rowNormPow 4 N u X U (fun σ x y =>
      correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (A σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | U σ w} x y -
        correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K Kc f (G σ)
          (polynomialPrepCutoff4 HP.θ) HP.ρ {z | X σ z} {w | U σ w} x y) ≤
      (L * (1 + Kc) * (1 + d)) ^ 4 * rowNormPow 4 N u X U
        (fun σ x y => (A σ x y - G σ x y) / (f + G σ x y)) := by
  obtain ⟨L, hL, h⟩ := HP.preparation_row_moment
  refine ⟨L, hL, ?_⟩
  intro Ω V instΩ instV X U instX instU Kc hKc f d hf hd A G hG N u hNu
  apply (h Ω V X U Kc hKc f hf A G N u hNu).trans
  apply (mul_le_mul_of_nonneg_left (raw_relative_row_moment hNu hf hd X U A G hG)
    (by positivity : 0 ≤ (L * (1 + Kc) / f) ^ 4)).trans_eq
  rw [← mul_assoc, ← mul_pow]
  congr 2
  field_simp

end Matrix.FourthRootHierarchyParams

namespace Matrix.HierarchyParams.H4RankEnvironment
open Cslib Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type*} [Fintype V] {k : ℕ}

/-- The literal fixed RAW/MAX numerator, with its own actual row and incoming ranks. -/
@[expose] def correctionNumerator (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (raw : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x y : V) : ℝ :=
  HP.toHierarchyParams.atomCutoff (raw σ x y / r.terminal.rate) *
    (rowGate HP.ρ HP.K r.terminal.rate (raw σ)
      {v | r.terminal.retains (channels D) σ (ident v)} x *
    incomingGate (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
      ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate (raw σ)
      {v | r.source.retains (channels D) σ (ident v)}
      {v | r.terminal.retains (channels D) σ (ident v)} y) * HP.γ (maximum σ y)

/-- All three actual gates are nonnegative even for signed, unbounded RAW. -/
theorem correctionNumerator_nonneg (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (raw : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x y : V) :
    0 ≤ correctionNumerator HP D ident r raw maximum σ x y :=
  mul_nonneg (mul_nonneg (HP.toHierarchyParams.atomCutoff_nonneg _)
    (mul_nonneg (HP.ρ_nonneg _) (HP.incomingCutoff_nonneg _))) (HP.γ_nonneg _)

/-- A cap on the actual numerator follows from its own three gate values. -/
theorem correctionNumerator_le (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (raw : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ)
    (σ : Environment P J) (x y : V) :
    correctionNumerator HP D ident r raw maximum σ x y ≤ HP.Q HP.toHierarchyParams.atomCap := by
  unfold correctionNumerator
  apply le_trans (mul_le_of_le_one_right
    (mul_nonneg (HP.toHierarchyParams.atomCutoff_nonneg _)
      (mul_nonneg (HP.ρ_nonneg _) (HP.incomingCutoff_nonneg _))) (HP.γ_le_one _))
  apply le_trans (mul_le_of_le_one_right (HP.toHierarchyParams.atomCutoff_nonneg _) ?_)
    (HP.toHierarchyParams.atomCutoff_le _)
  exact (mul_le_of_le_one_right (HP.ρ_nonneg _) (HP.incomingCutoff_le_one _)).trans
    (HP.ρ_le_one _)

/-- Numerator-weighted clipped mean error is paid before any decoder reduction.
The fourth root of the weight expresses its literal weighted fourth moment using
`rowNormPow`; it is not a new metric or a paid-moment hypothesis. -/
theorem correctionNumerator_clipped_mean_moment_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hs : 0 ≤ r.source.rate) (raw W G : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) :
    let X := fun τ v => r.source.retains (channels D) τ (ident v)
    let U := fun τ v => r.usage.retains (channels D) τ (ident v)
    let c := FourthRootHierarchyParams.NormalizedRow.clip
    rowNormPow 4 P r.source.rate X U (fun σ x y =>
      correctionNumerator HP D ident r raw maximum σ x y ^ (4⁻¹ : ℝ) *
        (c (rowSliceMean X U W x y) - c (rowSliceMean X U G x y))) ≤
      HP.Q HP.toHierarchyParams.atomCap * rowNormPow 4 P r.source.rate X U
        (fun _ x y => rowSliceMean X U W x y - rowSliceMean X U G x y) := by
  dsimp only
  apply rowNormPow_le_mul (mul_nonneg (Nat.cast_nonneg P) hs)
  intro σ x y _ _
  have hn := correctionNumerator_nonneg HP D ident r raw maximum σ x y
  have hp : (correctionNumerator HP D ident r raw maximum σ x y ^ (4⁻¹ : ℝ)) ^ 4 =
      correctionNumerator HP D ident r raw maximum σ x y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    norm_num
  have hc (a b : ℝ) : |FourthRootHierarchyParams.NormalizedRow.clip a -
      FourthRootHierarchyParams.NormalizedRow.clip b| ≤ |a - b| := by
    apply (abs_max_sub_max_le_max _ _ _ _).trans
    apply max_le
    · simp only [sub_self, abs_zero]; exact abs_nonneg _
    · exact (abs_min_sub_min_le_max _ _ _ _).trans (by simp)
  rw [abs_mul, mul_pow, abs_of_nonneg (Real.rpow_nonneg hn _), hp]
  exact mul_le_mul (correctionNumerator_le HP D ident r raw maximum σ x y)
    (pow_le_pow_left₀ (abs_nonneg _) (hc _ _) 4) (by positivity)
    (HP.Q_nonneg _)

set_option backward.isDefEq.respectTransparency false in
/-- Exact formula on the original environment. The clip is outside the mean. -/
theorem correctionRequest_numerator (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : Admissible r) (raw prep : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) :
    correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊
      raw prep maximum σ x y =
    if r.usage.retains (channels D) σ (ident y) then
      correctionNumerator HP D ident r raw maximum σ x y /
        FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean
          (fun τ v => r.source.retains (channels D) τ (ident v))
          (fun τ v => r.usage.retains (channels D) τ (ident v)) prep x y)
    else 0 := by
  rw [correctionRequest, dite_eq_left hr]
  dsimp only
  rw [CorrectionRowRecipe.normalized, normalizer_full D ident r hr prep x y]
  simp only [Equiv.piSplitAt_apply, coordinate, CorrectionRowTask.Channel.retains,
    channels, hr.2.1, correctionNumerator, FourthRootHierarchyParams.NormalizedRow.clip]
  split_ifs
  · rw [div_mul_eq_mul_div]
  · rfl

/-- The exact weighted integrand. The usage indicator, actual RAW/MAX numerator
and clipped joint means are preserved, with no independence or extra rate factor. -/
theorem correctionRequest_weighted_root_error
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : Admissible r) (raw W G : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) :
    let X := fun τ v => r.source.retains (channels D) τ (ident v)
    let U := fun τ v => r.usage.retains (channels D) τ (ident v)
    let c := FourthRootHierarchyParams.NormalizedRow.clip
    let output := fun prep => correctionRequest D ident r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    |output W σ x y ^ (4⁻¹ : ℝ) - output G σ x y ^ (4⁻¹ : ℝ)| ^ 4 =
      if U σ y then correctionNumerator HP D ident r raw maximum σ x y *
        |c (rowSliceMean X U W x y) ^ (-(4⁻¹ : ℝ)) -
          c (rowSliceMean X U G x y) ^ (-(4⁻¹ : ℝ))| ^ 4 else 0 := by
  dsimp only
  rw [correctionRequest_numerator HP D ident r hr,
    correctionRequest_numerator HP D ident r hr]
  split_ifs
  · exact FourthRootHierarchyParams.numerator_root_error
      (correctionNumerator_nonneg HP D ident r raw maximum σ x y)
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _))
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_left _ _))
  · simp

/-- Sharp fixed-numerator sensitivity to the clipped joint means. This is a
pointwise transfer, not an assumption that its weighted right-hand side is paid. -/
theorem correctionRequest_weighted_root_fourth_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : Admissible r) (raw W G : Environment P J → Matrix V V ℝ)
    (maximum : Environment P J → V → ℝ) (σ : Environment P J) (x y : V) :
    let X := fun τ v => r.source.retains (channels D) τ (ident v)
    let U := fun τ v => r.usage.retains (channels D) τ (ident v)
    let c := FourthRootHierarchyParams.NormalizedRow.clip
    let output := fun prep => correctionRequest D ident r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    |output W σ x y ^ (4⁻¹ : ℝ) - output G σ x y ^ (4⁻¹ : ℝ)| ^ 4 ≤
      if U σ y then correctionNumerator HP D ident r raw maximum σ x y *
        |c (rowSliceMean X U W x y) - c (rowSliceMean X U G x y)| ^ 4 / 8 else 0 := by
  dsimp only
  rw [correctionRequest_weighted_root_error HP D ident r hr]
  split_ifs
  · exact (mul_le_mul_of_nonneg_left
      (FourthRootHierarchyParams.inverse_fourth_root_fourth_le
        (FourthRootHierarchyParams.NormalizedRow.clip_bounds _)
        (FourthRootHierarchyParams.NormalizedRow.clip_bounds _))
      (correctionNumerator_nonneg HP D ident r raw maximum σ x y)).trans_eq (by ring)
  · exact le_rfl

/-- Integrate the exact numerator-weighted reduction on the same source/usage masks. -/
theorem correctionRequest_weighted_root_moment_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (ident : V → ZMod P) (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (hr : Admissible r) (hs : 0 ≤ r.source.rate)
    (raw W G : Environment P J → Matrix V V ℝ) (maximum : Environment P J → V → ℝ) :
    let X := fun τ v => r.source.retains (channels D) τ (ident v)
    let U := fun τ v => r.usage.retains (channels D) τ (ident v)
    let c := FourthRootHierarchyParams.NormalizedRow.clip
    let output := fun prep => correctionRequest D ident r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    rootDistPow 4 P r.source.rate X U (output W) (output G) ≤
      (1 / 8 : ℝ) * rowNormPow 4 P r.source.rate X U (fun σ x y =>
        correctionNumerator HP D ident r raw maximum σ x y ^ (4⁻¹ : ℝ) *
          (c (rowSliceMean X U W x y) - c (rowSliceMean X U G x y))) := by
  dsimp only
  apply rowNormPow_le_mul (mul_nonneg (Nat.cast_nonneg P) hs)
  intro σ x y _ hy
  have h := correctionRequest_weighted_root_fourth_le HP D ident r hr raw W G maximum σ x y
  dsimp only at h
  rw [ite_eq_left hy] at h
  have hn := correctionNumerator_nonneg HP D ident r raw maximum σ x y
  have hp : (correctionNumerator HP D ident r raw maximum σ x y ^ (4⁻¹ : ℝ)) ^ 4 =
      correctionNumerator HP D ident r raw maximum σ x y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    norm_num
  rw [abs_mul, mul_pow, abs_of_nonneg (Real.rpow_nonneg hn _), hp]
  exact h.trans_eq (by ring)

end Matrix.HierarchyParams.H4RankEnvironment

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib Finset
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Literal successful PREP, stationarity, sparse gates and a relative RAW allowance
pay the actual fixed-RAW/MAX root consumer. The reference range and relative accuracy
are new hypotheses; ordinary accuracy and positive own-input precision remain separate.
The gate constant `L` is selected at HP before requests, rates, fields and histories.
The final coefficient is `Q(atomCap)/8 * (L*(1+d))^4`; a uniform use must also fix
`d` before geometry. For relative allowance `ε = 2^(-p_child)`, payment into a
parent fraction `η` requires `coefficient ≤ η * 2^(4*(p_child-p_parent))`, by
`preparation_bias_salary_iff`. This is an additional scalar guard and relative IH;
no production charge, precision or availability policy is changed. -/
theorem evaluate_preparation_relative_root :
    ∃ L : ℝ, 0 ≤ L ∧
    ∀ (P : ℕ) [Fact P.Prime] (B : BudgetData HP P) (M : ℕ) (pilot : Bool)
      (i : Fin HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
    r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i) →
    Admissible r → 0 < B.requestPrecision M r → B.childBudget M < M →
    r.usage = r.terminal → 0 ≤ r.source.rate → 0 < r.terminal.rate →
    ∀ (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ),
    let q := { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
    0 < B.requestPrecision (B.childBudget M) q →
    B.evaluate (B.childBudget M) q = some (.row A) →
    B.evaluate M r = some (.row W) →
    ∀ (d ε : ℝ), 0 ≤ d →
    (∀ x y, B.canonicalPreparationInput pilot i r x y ∈ Set.Icc 0 (d * r.terminal.rate)) →
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let U := fun σ y => r.usage.retains (channels B.padding) σ y
    rowNormPow 4 P r.source.rate X U (fun σ x y =>
      (A σ x y - B.canonicalPreparationInput pilot i r x y) /
        (r.terminal.rate + B.canonicalPreparationInput pilot i r x y)) ≤ ε ^ 4 →
    ∀ (s u : Fin 3) (_hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P)),
    r.source = gridChannel s ks ss → r.usage = gridChannel u ku su →
    ∀ (raw : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (maximum : Environment P 3 → ZMod P → ℝ),
    let output := fun prep => correctionRequest B.padding id r
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff
      HP.γ HP.K ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum
    let V := B.incomingPreparation r (fun _ => B.canonicalPreparationInput pilot i r)
    rowNormPow 4 P r.source.rate X U (fun σ x y =>
      correctionNumerator HP B.padding id r raw maximum σ x y ^ (4⁻¹ : ℝ) *
        (FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U W x y) -
          FourthRootHierarchyParams.NormalizedRow.clip (rowSliceMean X U V x y))) ≤
      HP.Q HP.toHierarchyParams.atomCap * (L * (1 + d)) ^ 4 * ε ^ 4 ∧
    rootDistPow 4 P r.source.rate X U (output W) (output V) ≤
      HP.Q HP.toHierarchyParams.atomCap / 8 * (L * (1 + d)) ^ 4 * ε ^ 4 := by
  obtain ⟨L, hL, hreg⟩ := HP.preparation_relative_row_moment
  let Kc := ⌈4 * (1 + 32 * HP.R)⌉₊
  refine ⟨L * (1 + Kc), by positivity, ?_⟩
  intro P instP B M pilot i r hr had hp hm hu hs hf A W q _hqp hA hW
    d ε hd hG X U hrel s u hsu ks ku ss su hsource husage raw maximum output V
  let G := fun _ : Environment P 3 => B.canonicalPreparationInput pilot i r
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hs
  have hmean : (fun (_ : Environment P 3) x y => rowSliceMean X U W x y -
      rowSliceMean X U (B.incomingPreparation r G) x y) =
      (fun _ => rowSliceMean X U (fun σ x y =>
        B.incomingPreparation r A σ x y - B.incomingPreparation r G σ x y)) := by
    funext σ x y
    rw [B.evaluate_preparation_mean M pilot i r hr hp hm A W hA hW
      s u hsu ks ku ss su hsource husage]
    simp only [rowSliceMean, expect_sub_distrib, X, U]
  have hb := hreg (Environment P 3) (ZMod P) X U Kc
    (Nat.ceil_pos.mpr (by linarith [HP.R_var])) r.terminal.rate d hf hd A G
    (fun _ x y => hG x y) P r.source.rate hNu
  have hpaid : rowNormPow 4 P r.source.rate X U
      (fun _ x y => rowSliceMean X U W x y -
        rowSliceMean X U (B.incomingPreparation r G) x y) ≤
      (L * (1 + Kc) * (1 + d)) ^ 4 * ε ^ 4 := by
    rw [hmean]
    apply (rowNormPow_sliceMean_fourth_le hNu X U _).trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hrel (by positivity))
    simpa only [incomingPreparation, hu, X, U, G, Kc] using hb
  have hw := correctionNumerator_clipped_mean_moment_le HP B.padding id r hs raw W
    (B.incomingPreparation r G) maximum
  have hweight := hw.trans (mul_le_mul_of_nonneg_left hpaid (HP.Q_nonneg _))
  refine ⟨hweight.trans_eq (by ring), ?_⟩
  have hout := correctionRequest_weighted_root_moment_le HP B.padding id r had hs raw W
    (B.incomingPreparation r G) maximum
  exact hout.trans ((mul_le_mul_of_nonneg_left hweight (by norm_num : (0 : ℝ) ≤ 1 / 8)).trans_eq
    (by ring))

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
