/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.StreamArithmetic.Primitives
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Certified stream recipes for logspace smooth estimators and row compression

This module composes the primitive certified stream operations of
[OpenAI2026LogSpace, Sections 10.2--10.6] into uniform exact signed-digit stream recipes for the
smooth estimator and row-compression building blocks used in the logspace derandomization.

All allowance and intrinsic-storage coefficients `(coeffA, coeffB, coeffC, intrinsicCoeff)` depend
only on the scale/support exponent parameter `κ` and child recipe coefficients, never on `d`, `m`,
`n`, `K`, or the support list `items`. For `Cslib.RowCompression.newDefault` and
`Cslib.RowCompression.update`, intermediate piecewise-linear combinations whose unscaled range
exceeds `[-1, 1]` are evaluated at dyadically rescaled magnitudes (`/ 4`, `/ 16`, `/ 32`, `/ 64`)
inside `[-1, 1]` and then restored to exact unscaled values via `shiftClip`. As in `Interface` and
`Primitives`, these recipes certify exact stream values and annotated `QueryProg` bounds prior to
native machine compilation, and row-compression ranks use the zero-padded detector rank
`Finset.kthLargest` (`zeroPaddedRankListRecipe`).

## Main definitions

* `Cslib.StreamArithmetic.FixedRecipe` and `Cslib.StreamArithmetic.FixedRecipe.guardStruct`: helper
  bundle pinning `slack`, `ValidEnv`, and `targetVal` in its type so DAG combinators expose their
  specification in `O(1)` without unfolding multi-stage compositions.
* `Cslib.StreamArithmetic.UniformStreamRecipe.abs`: exact absolute-value stream recipe
  `|R| = max R (-R)`.
* `Cslib.StreamArithmetic.clippedAtomInvRecipe`: certified recipe computing
  `1 / (2 * max (1 / 2) (min 1 q))`.
* `Cslib.StreamArithmetic.polynomialTransition4Recipe`,
  `Cslib.StreamArithmetic.dyadicSwitchNormRecipe`,
  `Cslib.StreamArithmetic.dyadicWeightNormRecipe`: certified recipes computing
  `Cslib.polynomialTransition4`, `Cslib.SignedDigitStream.dyadicSwitch`, and
  `Cslib.SignedDigitStream.dyadicWeight`.
* `Cslib.StreamArithmetic.invScaledNormRecipe`, `Cslib.StreamArithmetic.invOneAddScaledRecipe`,
  `Cslib.StreamArithmetic.rationalRamp4NormRecipe`: certified recipes computing the dyadic
  reciprocal leaf factor, `1 / (1 + max 0 (2 ^ m * q))`, and
  `Cslib.rationalRamp4Unit (2 ^ m * q) / 2 ^ m` for `m ≤ κ * d`.
* `Cslib.StreamArithmetic.RowStreamIdx`, `Cslib.StreamArithmetic.RowSupportValidEnv`,
  `Cslib.StreamArithmetic.RowUpdateValidEnv`: operand stream index and normalized environment
  preconditions for two-coordinate row compression (`Cslib.RowCompression`).
* `Cslib.StreamArithmetic.rowCompressionThresholdPrim`,
  `Cslib.StreamArithmetic.rowCompressionNewDefaultPrim`,
  `Cslib.StreamArithmetic.rowCompressionUpdatePrim`,
  `Cslib.StreamArithmetic.rowCompressionNewDefaultRecipe`,
  `Cslib.StreamArithmetic.rowCompressionUpdateRecipe`: certified primitive and composite recipes
  for `Cslib.RowCompression.threshold`, `Cslib.RowCompression.newDefault`, and
  `Cslib.RowCompression.update`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 4.1, 8.2, and 10.2--10.6 (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.StreamArithmetic

open Cslib.SignedDigitStream Finset

universe u u' v

section FixedRecipeCombinators

/-- Equality of the four resource-bound coefficients of two `UniformStreamRecipe`s. -/
@[expose] def sameCoeffs {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    (R₁ : UniformStreamRecipe Op₁ Struct) (R₂ : UniformStreamRecipe Op₂ Struct) : Prop :=
  R₁.coeffA = R₂.coeffA ∧ R₁.coeffB = R₂.coeffB ∧
    R₁.coeffC = R₂.coeffC ∧ R₁.intrinsicCoeff = R₂.intrinsicCoeff

/-- Quadruple of allowance and intrinsic-storage coefficients of a certified stream recipe. -/
private structure RecipeCoeffs where
  coeffA : ℕ
  coeffB : ℕ
  coeffC : ℕ
  intrinsicCoeff : ℕ
  deriving DecidableEq

/-- Project the four resource-bound coefficients of a `UniformStreamRecipe`. -/
private def UniformStreamRecipe.coeffs {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : RecipeCoeffs where
  coeffA := R.coeffA
  coeffB := R.coeffB
  coeffC := R.coeffC
  intrinsicCoeff := R.intrinsicCoeff

private theorem UniformStreamRecipe.coeffs_eq_of_sameCoeffs {Op₁ : Type u} {Op₂ : Type u'}
    {Struct : Type v} {R₁ : UniformStreamRecipe Op₁ Struct}
    {R₂ : UniformStreamRecipe Op₂ Struct} (h : sameCoeffs R₁ R₂) :
    R₁.coeffs = R₂.coeffs := by
  obtain ⟨ha, hb, hc, hi⟩ := h
  unfold UniformStreamRecipe.coeffs
  rw [ha, hb, hc, hi]

private theorem sameCoeffs_of_coeffs_eq {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {R₁ : UniformStreamRecipe Op₁ Struct} {R₂ : UniformStreamRecipe Op₂ Struct}
    (h : R₁.coeffs = R₂.coeffs) : sameCoeffs R₁ R₂ :=
  ⟨congrArg RecipeCoeffs.coeffA h, congrArg RecipeCoeffs.coeffB h,
    congrArg RecipeCoeffs.coeffC h, congrArg RecipeCoeffs.intrinsicCoeff h⟩

/-- Certified stream recipe pinned to slack `d`, environment validity predicate `V`, and semantic
function `valFn` in its type. Keeping combinator bodies non-`@[expose]` while exposing
`FixedRecipe.toRecipe` makes `.slack`, `.ValidEnv`, and `.targetVal` reduce in one step without
unfolding multi-stage arithmetic DAGs. -/
structure FixedRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d)
    (V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (valFn : (Op → ℝ) → (Struct → Bool) → ℝ) where
  /-- Underlying certified `UniformStreamRecipe` packaged by this `FixedRecipe`. -/
  inner : UniformStreamRecipe Op Struct
  slack_eq : inner.slack = d
  valid_imp : ∀ {env sEnv}, V env sEnv → inner.ValidEnv env sEnv
  target_eq : ∀ {env sEnv}, V env sEnv →
    inner.targetVal (fun op => streamVal (env op)) sEnv =
      valFn (fun op => streamVal (env op)) sEnv

/-- Project a `FixedRecipe` back to a `UniformStreamRecipe` with immediate definitional access to
`slack := d`, `ValidEnv := V`, and `targetVal := valFn`. -/
@[expose] noncomputable def FixedRecipe.toRecipe {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d}
    {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {valFn : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V valFn) : UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv := V
  targetVal := valFn
  digitProg := F.inner.digitProg
  coeffA := F.inner.coeffA
  coeffB := F.inner.coeffB
  coeffC := F.inner.coeffC
  intrinsicCoeff := F.inner.intrinsicCoeff
  abs_targetVal_le_one hV := by
    rw [← F.target_eq hV]
    exact F.inner.abs_targetVal_le_one (F.valid_imp hV)
  emits_signed hV := F.inner.emits_signed (F.valid_imp hV)
  emits_exact hV := by
    rw [F.inner.emits_exact (F.valid_imp hV), F.target_eq hV]
  allowance t env sEnv _ hev := by
    have h := F.inner.allowance t env sEnv hev
    rwa [F.slack_eq] at h
  intrinsic_bound t env sEnv := by
    have h := F.inner.intrinsic_bound t env sEnv
    rwa [F.slack_eq] at h

/-- Equality of the four resource coefficients of two `FixedRecipe`s. -/
private def FixedRecipe.sameCoeffs {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {d₁ d₂ : ℕ} {hd₁ : 1 ≤ d₁} {hd₂ : 1 ≤ d₂}
    {V₁ : (Op₁ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {V₂ : (Op₂ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ : (Op₁ → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : (Op₂ → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : FixedRecipe d₁ hd₁ V₁ f₁) (F₂ : FixedRecipe d₂ hd₂ V₂ f₂) : Prop :=
  Cslib.StreamArithmetic.sameCoeffs F₁.toRecipe F₂.toRecipe

/-- Project the four resource coefficients of a `FixedRecipe`. -/
private def FixedRecipe.coeffs {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) : RecipeCoeffs :=
  F.inner.coeffs

private theorem FixedRecipe.coeffs_toRecipe {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) : F.toRecipe.coeffs = F.inner.coeffs :=
  rfl

private theorem FixedRecipe.coeffs_eq_of_sameCoeffs {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {d₁ d₂ : ℕ} {hd₁ : 1 ≤ d₁} {hd₂ : 1 ≤ d₂}
    {V₁ : (Op₁ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {V₂ : (Op₂ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ : (Op₁ → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : (Op₂ → ℝ) → (Struct → Bool) → ℝ}
    {F₁ : FixedRecipe d₁ hd₁ V₁ f₁} {F₂ : FixedRecipe d₂ hd₂ V₂ f₂}
    (h : F₁.sameCoeffs F₂) : F₁.coeffs = F₂.coeffs :=
  UniformStreamRecipe.coeffs_eq_of_sameCoeffs h

private theorem FixedRecipe.sameCoeffs_of_coeffs_eq {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {d₁ d₂ : ℕ} {hd₁ : 1 ≤ d₁} {hd₂ : 1 ≤ d₂}
    {V₁ : (Op₁ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {V₂ : (Op₂ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ : (Op₁ → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : (Op₂ → ℝ) → (Struct → Bool) → ℝ}
    {F₁ : FixedRecipe d₁ hd₁ V₁ f₁} {F₂ : FixedRecipe d₂ hd₂ V₂ f₂}
    (h : F₁.coeffs = F₂.coeffs) : F₁.sameCoeffs F₂ :=
  Cslib.StreamArithmetic.sameCoeffs_of_coeffs_eq h

/-- Wrap any `UniformStreamRecipe` as a `FixedRecipe`. -/
noncomputable def FixedRecipe.ofRecipe {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) :
    FixedRecipe R.slack R.slack_pos R.ValidEnv R.targetVal where
  inner := R
  slack_eq := rfl
  valid_imp h := h
  target_eq _ := rfl

/-- Strengthen the precondition of a `FixedRecipe` to `V₂`. -/
noncomputable def FixedRecipe.weaken {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d}
    {V₁ V₂ : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V₁ f)
    (hV : ∀ {env sEnv}, V₂ env sEnv → V₁ env sEnv) :
    FixedRecipe d hd V₂ f where
  inner := F.inner
  slack_eq := F.slack_eq
  valid_imp h := F.valid_imp (hV h)
  target_eq h := F.target_eq (hV h)

/-- Replace the semantic value function of a `FixedRecipe` with an extensionally equal expression
on valid environments. -/
noncomputable def FixedRecipe.congrVal {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d}
    {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f)
    (g : (Op → ℝ) → (Struct → Bool) → ℝ)
    (hEq : ∀ {env sEnv}, V env sEnv →
      f (fun op => streamVal (env op)) sEnv =
        g (fun op => streamVal (env op)) sEnv) :
    FixedRecipe d hd V g where
  inner := F.inner
  slack_eq := F.slack_eq
  valid_imp := F.valid_imp
  target_eq h := (F.target_eq h).trans (hEq h)

/-- Constant rational `FixedRecipe` for `|q| ≤ 1`. -/
noncomputable def FixedRecipe.const {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (q : ℚ) (hq : |q| ≤ 1) (κ : ℕ := 0) :
    FixedRecipe d hd V (fun _ _ => (q : ℝ)) where
  inner := ratRecipe d hd q hq κ
  slack_eq := rfl
  valid_imp _ := trivial
  target_eq _ := rfl

/-- Variable `FixedRecipe` reading operand stream `op` under `V`. -/
noncomputable def FixedRecipe.var {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (op : Op) (hOp : ∀ {env sEnv}, V env sEnv → IsNormSignedStream (env op)) :
    FixedRecipe d hd V (fun val _ => val op) where
  inner := varRecipe d hd op
  slack_eq := rfl
  valid_imp h := hOp h
  target_eq _ := rfl

/-- Exact negation on `FixedRecipe`. -/
noncomputable def FixedRecipe.neg {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) :
    FixedRecipe d hd V (fun val sEnv => -f val sEnv) where
  inner := F.toRecipe.neg
  slack_eq := rfl
  valid_imp h := h
  target_eq _ := rfl

/-- Exact pairwise average `(F₁ + F₂) / 2` on `FixedRecipe`. -/
noncomputable def FixedRecipe.pairAvg {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : FixedRecipe d hd V f₁) (F₂ : FixedRecipe d hd V f₂) :
    FixedRecipe d hd V (fun val sEnv => (f₁ val sEnv + f₂ val sEnv) / 2) where
  inner := F₁.toRecipe.pairAvg F₂.toRecipe rfl
  slack_eq := rfl
  valid_imp h := ⟨h, h⟩
  target_eq _ := rfl

/-- Exact binary maximum on `FixedRecipe`. -/
noncomputable def FixedRecipe.max {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : FixedRecipe d hd V f₁) (F₂ : FixedRecipe d hd V f₂) :
    FixedRecipe d hd V (fun val sEnv => Max.max (f₁ val sEnv) (f₂ val sEnv)) where
  inner := F₁.toRecipe.max F₂.toRecipe rfl
  slack_eq := rfl
  valid_imp h := ⟨h, h⟩
  target_eq _ := rfl

/-- Exact binary minimum on `FixedRecipe`. -/
noncomputable def FixedRecipe.min {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : FixedRecipe d hd V f₁) (F₂ : FixedRecipe d hd V f₂) :
    FixedRecipe d hd V (fun val sEnv => Min.min (f₁ val sEnv) (f₂ val sEnv)) where
  inner := F₁.toRecipe.min F₂.toRecipe rfl
  slack_eq := rfl
  valid_imp h := ⟨h, h⟩
  target_eq _ := rfl

/-- Exact stream multiplication on `FixedRecipe`. -/
noncomputable def FixedRecipe.mul {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : FixedRecipe d hd V f₁) (F₂ : FixedRecipe d hd V f₂) :
    FixedRecipe d hd V (fun val sEnv => f₁ val sEnv * f₂ val sEnv) where
  inner := F₁.toRecipe.mul F₂.toRecipe rfl
  slack_eq := rfl
  valid_imp h := ⟨h, h⟩
  target_eq _ := rfl

/-- Exact absolute value `|F| = max F (-F)` on `FixedRecipe`. -/
noncomputable def FixedRecipe.abs {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) :
    FixedRecipe d hd V (fun val sEnv => |f val sEnv|) :=
  (F.max F.neg).congrVal (fun val sEnv => |f val sEnv|)
    (fun _ => abs_eq_max_neg.symm)

/-- Exact absolute-value stream recipe `|R| = max R (-R)`. -/
@[expose] noncomputable def UniformStreamRecipe.abs {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct :=
  (FixedRecipe.ofRecipe R).abs.toRecipe

/-- Exact shift-and-clip `max (-1) (min 1 (2 ^ v * F))` on `FixedRecipe`. -/
noncomputable def FixedRecipe.shiftClip {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) :
    FixedRecipe d hd V (fun val sEnv => shiftClipVal v (f val sEnv)) where
  inner := F.toRecipe.shiftClip v κ hv
  slack_eq := rfl
  valid_imp h := h
  target_eq _ := rfl

/-- Exact `[1 / 4, 1]` scaled reciprocal `1 / (64 * F)` on `FixedRecipe`. -/
noncomputable def FixedRecipe.recip64 {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f)
    (hMem : ∀ {env sEnv}, V env sEnv →
      f (fun op => streamVal (env op)) sEnv ∈ Set.Icc (1 / 4 : ℝ) 1) :
    FixedRecipe d hd V (fun val sEnv => 1 / (64 * f val sEnv)) where
  inner := F.toRecipe.recip64
  slack_eq := rfl
  valid_imp h := ⟨h, hMem h⟩
  target_eq _ := rfl

/-- Static parameter conditional branch on `FixedRecipe`. -/
noncomputable def FixedRecipe.dite {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    (P : Prop) [Decidable P]
    {f₁ : P → (Op → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : ¬ P → (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : (h : P) → FixedRecipe d hd V (f₁ h))
    (F₂ : (h : ¬ P) → FixedRecipe d hd V (f₂ h)) :
    FixedRecipe d hd V (fun val sEnv => if h : P then f₁ h val sEnv else f₂ h val sEnv) :=
  if hP : P then
    (F₁ hP).congrVal _ (fun _ => by simp only [hP, ↓reduceDIte])
  else
    (F₂ hP).congrVal _ (fun _ => by simp only [hP, ↓reduceDIte])

/-- Structural indicator guard on `FixedRecipe`: emits `F` when `sEnv sOp = true` and `0` when
`sEnv sOp = false`, requiring `V` only when `sEnv sOp = true`. -/
noncomputable def FixedRecipe.guardStruct {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) (sOp : Struct) :
    FixedRecipe d hd (fun env sEnv => sEnv sOp = true → V env sEnv)
      (fun val sEnv => if sEnv sOp then f val sEnv else 0) where
  inner := F.toRecipe.guardStruct sOp
  slack_eq := rfl
  valid_imp h := h
  target_eq _ := rfl

/-- Constant-stream coefficient quadruple matching `ratRecipe _ _ _ _ κ`. -/
private def RecipeCoeffs.const (κ : ℕ := 0) : RecipeCoeffs :=
  ⟨0, 0, 0, κ + 8⟩

/-- Stage-composition law on `RecipeCoeffs` matching `UniformStreamRecipe.comp`. -/
private def RecipeCoeffs.comp (p c : RecipeCoeffs) : RecipeCoeffs :=
  let B := max p.coeffB (max c.coeffB c.intrinsicCoeff)
  let a₁ := p.coeffA + (B - p.coeffB) * p.coeffC
  let a₂ := c.coeffA + B * c.coeffC
  { coeffA := a₁ + a₂ + 4
    coeffB := B
    coeffC := p.coeffC + c.coeffC
    intrinsicCoeff := max p.intrinsicCoeff (max (a₁ + 4 + c.intrinsicCoeff) B) }

/-- Coordinatewise maximum of two `RecipeCoeffs` quadruples. -/
private def RecipeCoeffs.max (x y : RecipeCoeffs) : RecipeCoeffs where
  coeffA := Max.max x.coeffA y.coeffA
  coeffB := Max.max x.coeffB y.coeffB
  coeffC := Max.max x.coeffC y.coeffC
  intrinsicCoeff := Max.max x.intrinsicCoeff y.intrinsicCoeff

/-- Binary-primitive composition law matching `composeBinPrim`. -/
private def RecipeCoeffs.compBin (p x y : RecipeCoeffs) : RecipeCoeffs :=
  p.comp (x.max y)

private def pairAvgPrimCoeffs : RecipeCoeffs := ⟨46, 0, 4, 54⟩
private def maxPrimCoeffs : RecipeCoeffs := ⟨48, 6, 4, 48⟩
private def minPrimCoeffs : RecipeCoeffs := ⟨48, 6, 4, 48⟩
private def mulPrimCoeffs : RecipeCoeffs := ⟨66, 1, 16, 84⟩
private def shiftClipPrimCoeffs (κ : ℕ) : RecipeCoeffs :=
  ⟨(6 * κ + 44) + 8, 6, κ + 4, (6 * κ + 44) + 8⟩
private noncomputable def recip64PrimCoeffs : RecipeCoeffs :=
  (recip64Prim (Struct := Unit) 1 le_rfl).coeffs

private theorem FixedRecipe.coeffs_dite {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    (P : Prop) [Decidable P]
    {f₁ : P → (Op → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : ¬ P → (Op → ℝ) → (Struct → Bool) → ℝ}
    (F₁ : (h : P) → FixedRecipe d hd V (f₁ h))
    (F₂ : (h : ¬ P) → FixedRecipe d hd V (f₂ h)) :
    (FixedRecipe.dite P F₁ F₂).inner.coeffs =
      if hP : P then (F₁ hP).inner.coeffs else (F₂ hP).inner.coeffs := by
  unfold FixedRecipe.dite
  split_ifs with hP <;> rfl

private theorem FixedRecipe.coeffs_const {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (q : ℚ) (hq : |q| ≤ 1) (κ : ℕ := 0) :
    (FixedRecipe.const (Struct := Struct) d hd V q hq κ).inner.coeffs =
      RecipeCoeffs.const κ :=
  rfl

private theorem FixedRecipe.coeffs_var {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (op : Op) (hOp : ∀ {env sEnv}, V env sEnv → IsNormSignedStream (env op)) :
    (FixedRecipe.var (Struct := Struct) d hd V op hOp).inner.coeffs = ⟨4, 0, 0, 4⟩ :=
  rfl

private theorem FixedRecipe.coeffs_neg {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) :
    F.neg.inner.coeffs = F.inner.coeffs :=
  rfl

private theorem FixedRecipe.coeffs_pairAvg {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (A : FixedRecipe d hd V f₁) (B : FixedRecipe d hd V f₂) :
    (A.pairAvg B).inner.coeffs = pairAvgPrimCoeffs.compBin A.inner.coeffs B.inner.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.coeffs_max {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (A : FixedRecipe d hd V f₁) (B : FixedRecipe d hd V f₂) :
    (A.max B).inner.coeffs = maxPrimCoeffs.compBin A.inner.coeffs B.inner.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.coeffs_min {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (A : FixedRecipe d hd V f₁) (B : FixedRecipe d hd V f₂) :
    (A.min B).inner.coeffs = minPrimCoeffs.compBin A.inner.coeffs B.inner.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.coeffs_mul {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ f₂ : (Op → ℝ) → (Struct → Bool) → ℝ}
    (A : FixedRecipe d hd V f₁) (B : FixedRecipe d hd V f₂) :
    (A.mul B).inner.coeffs = mulPrimCoeffs.compBin A.inner.coeffs B.inner.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.coeffs_abs {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) :
    F.abs.inner.coeffs = maxPrimCoeffs.compBin F.inner.coeffs F.inner.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.coeffs_shiftClip {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (F : FixedRecipe d hd V f) (v : ℤ) (κ : ℕ) (hv : v ≤ ((κ * d : ℕ) : ℤ)) :
    (F.shiftClip v κ hv).inner.coeffs = (shiftClipPrimCoeffs κ).comp F.inner.coeffs :=
  Eq.symm rfl

private theorem UniformStreamRecipe.coeffs_recip64 {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) :
    R.recip64.coeffs = recip64PrimCoeffs.comp R.coeffs :=
  Eq.symm rfl

private theorem FixedRecipe.sameCoeffs_toRecipe {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    {d₁ d₂ : ℕ} {hd₁ : 1 ≤ d₁} {hd₂ : 1 ≤ d₂}
    {V₁ : (Op₁ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {V₂ : (Op₂ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ : (Op₁ → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : (Op₂ → ℝ) → (Struct → Bool) → ℝ}
    {F₁ : FixedRecipe d₁ hd₁ V₁ f₁} {F₂ : FixedRecipe d₂ hd₂ V₂ f₂}
    (h : F₁.sameCoeffs F₂) :
    Cslib.StreamArithmetic.sameCoeffs F₁.toRecipe F₂.toRecipe :=
  h

private theorem shiftClipVal_sub_of_mem_unit {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    shiftClipVal 1 ((a + -b) / 2) = a - b := by
  unfold shiftClipVal
  have hmul : (2 : ℝ) ^ (1 : ℤ) * ((a + -b) / 2) = a - b := by
    norm_num
    ring
  rw [hmul, min_eq_right (by linarith), max_eq_right (by linarith)]

end FixedRecipeCombinators

section ClippedAtomAndPolynomialSwitch

/-- `FixedRecipe` computing the clipped stochastic-atom inverse
`1 / (2 * max (1 / 2) (min 1 (R.targetVal val sEnv)))`. -/
noncomputable def clippedAtomInvFixed {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) :
    FixedRecipe R.slack R.slack_pos R.ValidEnv
      (fun val sEnv => 1 / (2 * Max.max (1 / 2) (Min.min 1 (R.targetVal val sEnv)))) :=
  let d := R.slack
  let hd := R.slack_pos
  let V := R.ValidEnv
  let RF := FixedRecipe.ofRecipe R
  let halfF := FixedRecipe.const d hd V (1 / 2) (by norm_num)
  let oneF := FixedRecipe.const d hd V 1 (by norm_num)
  let clamped := (halfF.max (oneF.min RF)).congrVal
    (fun val sEnv => Max.max (1 / 2) (Min.min 1 (R.targetVal val sEnv)))
    (fun _ => by push_cast; rfl)
  let inv64 := clamped.recip64 (fun _ => clippedAtomDenom_mem_Icc _)
  let shifted := inv64.shiftClip 5 5 (by exact_mod_cast Nat.le_mul_of_pos_right 5 hd)
  shifted.congrVal
    (fun val sEnv => 1 / (2 * Max.max (1 / 2) (Min.min 1 (R.targetVal val sEnv))))
    (fun _ => shiftClipVal_clippedAtomInv _)

/-- Certified `UniformStreamRecipe` computing the clipped stochastic-atom inverse
`1 / (2 * max (1 / 2) (min 1 (R.targetVal val sEnv)))` in `O(1)` stages. -/
@[expose] noncomputable def clippedAtomInvRecipe {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct :=
  (clippedAtomInvFixed R).toRecipe

/-- `FixedRecipe` computing the degree-7 smooth switch `Cslib.polynomialTransition4 (f val sEnv)`.
-/
noncomputable def polynomialTransition4Fixed {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (RF : FixedRecipe d hd V f) :
    FixedRecipe d hd V (fun val sEnv => Cslib.polynomialTransition4 (f val sEnv)) :=
  let zeroF := FixedRecipe.const d hd V 0 (by norm_num)
  let oneF := FixedRecipe.const d hd V 1 (by norm_num)
  let uF := (zeroF.max (oneF.min RF)).congrVal
    (fun val sEnv => Max.max 0 (Min.min 1 (f val sEnv)))
    (fun _ => by push_cast; rfl)
  let oneMinusU := ((oneF.pairAvg uF.neg).shiftClip 1 1
      (by exact_mod_cast Nat.le_mul_of_pos_right 1 hd)).congrVal
    (fun val sEnv => 1 - Max.max 0 (Min.min 1 (f val sEnv)))
    (fun {env sEnv} _ => by
      push_cast
      exact shiftClipVal_sub_of_mem_unit zero_le_one le_rfl
        (le_max_left 0 _) (max_le zero_le_one (min_le_left 1 _)))
  let u2 := uF.mul uF
  let u4 := u2.mul u2
  let v2 := oneMinusU.mul oneMinusU
  let v3 := v2.mul oneMinusU
  let c1 := FixedRecipe.const d hd V (1 / 32) (by norm_num)
  let c2 := FixedRecipe.const d hd V (1 / 8) (by norm_num)
  let c3 := FixedRecipe.const d hd V (5 / 16) (by norm_num)
  let c4 := FixedRecipe.const d hd V (5 / 8) (by norm_num)
  let branch1 := c1.pairAvg (c2.mul oneMinusU)
  let branch2 := (c3.mul v2).pairAvg (c4.mul v3)
  let polyAvg := branch1.pairAvg branch2
  let prodF := u4.mul polyAvg
  let raw := prodF.shiftClip 7 7 (by exact_mod_cast Nat.le_mul_of_pos_right 7 hd)
  raw.congrVal
    (fun val sEnv => Cslib.polynomialTransition4 (f val sEnv))
    (fun {env sEnv} _ => by
      set t := f (fun op => streamVal (env op)) sEnv
      rw [polynomialTransition4_eq_shiftClip t]
      congr 1
      push_cast
      ring)

private def poly4Coeffs (c : RecipeCoeffs) : RecipeCoeffs :=
  let c0 := RecipeCoeffs.const 0
  let u := maxPrimCoeffs.compBin c0 (minPrimCoeffs.compBin c0 c)
  let oneMinusU := (shiftClipPrimCoeffs 1).comp (pairAvgPrimCoeffs.compBin c0 u)
  let u2 := mulPrimCoeffs.compBin u u
  let u4 := mulPrimCoeffs.compBin u2 u2
  let v2 := mulPrimCoeffs.compBin oneMinusU oneMinusU
  let v3 := mulPrimCoeffs.compBin v2 oneMinusU
  let branch1 := pairAvgPrimCoeffs.compBin c0 (mulPrimCoeffs.compBin c0 oneMinusU)
  let branch2 := pairAvgPrimCoeffs.compBin
    (mulPrimCoeffs.compBin c0 v2) (mulPrimCoeffs.compBin c0 v3)
  let polyAvg := pairAvgPrimCoeffs.compBin branch1 branch2
  (shiftClipPrimCoeffs 7).comp (mulPrimCoeffs.compBin u4 polyAvg)

private theorem coeffs_polynomialTransition4Fixed {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    (RF : FixedRecipe d hd V f) :
    (polynomialTransition4Fixed RF).inner.coeffs = poly4Coeffs RF.inner.coeffs := by
  unfold polynomialTransition4Fixed poly4Coeffs
  simp only [FixedRecipe.congrVal, FixedRecipe.coeffs_shiftClip, FixedRecipe.coeffs_mul,
    FixedRecipe.coeffs_pairAvg, FixedRecipe.coeffs_max, FixedRecipe.coeffs_min,
    FixedRecipe.coeffs_neg, FixedRecipe.coeffs_const]

private theorem sameCoeffs_polynomialTransition4Fixed {Op₁ : Type u} {Op₂ : Type u'}
    {Struct : Type v} {d₁ d₂ : ℕ} {hd₁ : 1 ≤ d₁} {hd₂ : 1 ≤ d₂}
    {V₁ : (Op₁ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {V₂ : (Op₂ → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f₁ : (Op₁ → ℝ) → (Struct → Bool) → ℝ}
    {f₂ : (Op₂ → ℝ) → (Struct → Bool) → ℝ}
    {F₁ : FixedRecipe d₁ hd₁ V₁ f₁} {F₂ : FixedRecipe d₂ hd₂ V₂ f₂}
    (h : F₁.sameCoeffs F₂) :
    (polynomialTransition4Fixed F₁).sameCoeffs (polynomialTransition4Fixed F₂) := by
  apply FixedRecipe.sameCoeffs_of_coeffs_eq
  dsimp only [FixedRecipe.coeffs]
  rw [coeffs_polynomialTransition4Fixed, coeffs_polynomialTransition4Fixed]
  exact congrArg poly4Coeffs (FixedRecipe.coeffs_eq_of_sameCoeffs h)

/-- Certified `UniformStreamRecipe` computing `Cslib.polynomialTransition4 (R.targetVal val sEnv)`
via normalized `[-1, 1]` stream additions, multiplications, and `shiftClip`. -/
@[expose] noncomputable def polynomialTransition4Recipe {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) : UniformStreamRecipe Op Struct :=
  (polynomialTransition4Fixed (FixedRecipe.ofRecipe R)).toRecipe

/-- `FixedRecipe` computing `dyadicSwitch r (2 ^ (m + 1) * max 0 (W.targetVal val sEnv))` for
`r ≤ m ≤ κ * W.slack`. -/
noncomputable def dyadicSwitchNormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) :
    FixedRecipe W.slack W.slack_pos W.ValidEnv
      (fun val sEnv => dyadicSwitch r ((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv))) :=
  let d := W.slack
  let hd := W.slack_pos
  let V := W.ValidEnv
  let WF := FixedRecipe.ofRecipe W
  let posW := ((FixedRecipe.const d hd V 0 (by norm_num)).max WF).congrVal
    (fun val sEnv => Max.max 0 (W.targetVal val sEnv))
    (fun _ => by push_cast; rfl)
  let s1 := posW.shiftClip ((m : ℤ) - (r : ℤ)) κ (by
    have hmZ : (m : ℤ) ≤ ((κ * d : ℕ) : ℤ) := by exact_mod_cast hm
    omega)
  let negHalfF := FixedRecipe.const d hd V (-1 / 2) (by norm_num)
  let s2 := (s1.pairAvg negHalfF).shiftClip 2 2
    (by exact_mod_cast Nat.le_mul_of_pos_right 2 hd)
  (polynomialTransition4Fixed s2).congrVal
    (fun val sEnv => dyadicSwitch r ((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)))
    (fun {env sEnv} _ => by
      set x := W.targetVal (fun op => streamVal (env op)) sEnv
      set w := (2 : ℝ) ^ (m + 1) * Max.max 0 x
      have hw0 : 0 ≤ w := mul_nonneg (by positivity) (le_max_left 0 x)
      have hw_div : Max.max 0 x = w / (2 : ℝ) ^ (m + 1) :=
        (mul_div_cancel_left₀ (Max.max 0 x) (by positivity)).symm
      rw [hw_div]
      push_cast
      exact (dyadicSwitch_eq_of_norm hr hw0).symm)

private def dyadicSwitchCoeffs (κ : ℕ) (w : RecipeCoeffs) : RecipeCoeffs :=
  let c0 := RecipeCoeffs.const 0
  let posW := maxPrimCoeffs.compBin c0 w
  let s1 := (shiftClipPrimCoeffs κ).comp posW
  let s2 := (shiftClipPrimCoeffs 2).comp (pairAvgPrimCoeffs.compBin s1 c0)
  poly4Coeffs s2

private def oneSubSwitchCoeffs (κ : ℕ) (w : RecipeCoeffs) : RecipeCoeffs :=
  (shiftClipPrimCoeffs 1).comp
    (pairAvgPrimCoeffs.compBin (RecipeCoeffs.const 0) (dyadicSwitchCoeffs κ w))

private def diffSwitchCoeffs (κ : ℕ) (w : RecipeCoeffs) : RecipeCoeffs :=
  let sw := dyadicSwitchCoeffs κ w
  (shiftClipPrimCoeffs 1).comp (pairAvgPrimCoeffs.compBin sw sw)

private theorem coeffs_dyadicSwitchNormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) :
    (dyadicSwitchNormFixed m κ W hm r hr).inner.coeffs = dyadicSwitchCoeffs κ W.coeffs := by
  unfold dyadicSwitchNormFixed dyadicSwitchCoeffs
  simp only [FixedRecipe.congrVal, FixedRecipe.ofRecipe, coeffs_polynomialTransition4Fixed,
    FixedRecipe.coeffs_shiftClip, FixedRecipe.coeffs_pairAvg, FixedRecipe.coeffs_max,
    FixedRecipe.coeffs_const]

private theorem sameCoeffs_dyadicSwitchNormFixed {Op : Type u} {Struct : Type v}
    {m₁ m₂ κ : ℕ} {W₁ W₂ : UniformStreamRecipe Op Struct}
    {hm₁ : m₁ ≤ κ * W₁.slack} {hm₂ : m₂ ≤ κ * W₂.slack}
    {r₁ r₂ : ℕ} {hr₁ : r₁ ≤ m₁} {hr₂ : r₂ ≤ m₂}
    (hW : sameCoeffs W₁ W₂) :
    (dyadicSwitchNormFixed m₁ κ W₁ hm₁ r₁ hr₁).sameCoeffs
      (dyadicSwitchNormFixed m₂ κ W₂ hm₂ r₂ hr₂) := by
  apply FixedRecipe.sameCoeffs_of_coeffs_eq
  dsimp only [FixedRecipe.coeffs]
  rw [coeffs_dyadicSwitchNormFixed, coeffs_dyadicSwitchNormFixed,
    UniformStreamRecipe.coeffs_eq_of_sameCoeffs hW]

/-- Certified `UniformStreamRecipe` computing
`dyadicSwitch r (2 ^ (m + 1) * max 0 (W.targetVal val sEnv))` from a normalized stream recipe `W`
when `r ≤ m ≤ κ * W.slack`. -/
@[expose] noncomputable def dyadicSwitchNormRecipe {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) : UniformStreamRecipe Op Struct :=
  (dyadicSwitchNormFixed m κ W hm r hr).toRecipe

/-- `FixedRecipe` computing the smooth dyadic partition-of-unity weight
`dyadicWeight m r (2 ^ (m + 1) * max 0 (W.targetVal val sEnv))`. -/
noncomputable def dyadicWeightNormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack) (r : ℕ) :
    FixedRecipe W.slack W.slack_pos W.ValidEnv
      (fun val sEnv => dyadicWeight m r ((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv))) :=
  let d := W.slack
  let hd := W.slack_pos
  let V := W.ValidEnv
  let raw :=
    FixedRecipe.dite (m = 0)
      (fun _ =>
        FixedRecipe.dite (r = 0)
          (fun _ => FixedRecipe.const d hd V 1 (by norm_num))
          (fun _ => FixedRecipe.const d hd V 0 (by norm_num)))
      (fun hm0 =>
        FixedRecipe.dite (r = 0)
          (fun _ =>
            let sw0 := dyadicSwitchNormFixed m κ W hm 0 (Nat.zero_le m)
            ((FixedRecipe.const d hd V 1 (by norm_num)).pairAvg sw0.neg).shiftClip 1 1
              (by exact_mod_cast Nat.le_mul_of_pos_right 1 hd))
          (fun hr0 =>
            FixedRecipe.dite (r < m)
              (fun hrm =>
                let swPrev := dyadicSwitchNormFixed m κ W hm (r - 1) (by omega)
                let swCurr := dyadicSwitchNormFixed m κ W hm r hrm.le
                (swPrev.pairAvg swCurr.neg).shiftClip 1 1
                  (by exact_mod_cast Nat.le_mul_of_pos_right 1 hd))
              (fun _ =>
                FixedRecipe.dite (r = m)
                  (fun _ => dyadicSwitchNormFixed m κ W hm (m - 1) (by omega))
                  (fun _ => FixedRecipe.const d hd V 0 (by norm_num)))))
  raw.congrVal
    (fun val sEnv => dyadicWeight m r ((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)))
    (fun {env sEnv} _ => by
      set w := (2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal (fun op => streamVal (env op)) sEnv)
      have hsw0 : ∀ k, 0 ≤ dyadicSwitch k w := fun _ => Cslib.polynomialTransition4_nonneg _
      have hsw1 : ∀ k, dyadicSwitch k w ≤ 1 := fun _ => Cslib.polynomialTransition4_le_one _
      dsimp only [dyadicWeight]
      by_cases hm0 : m = 0
      · simp only [hm0, ↓reduceDIte, ↓reduceIte]
        by_cases hr0 : r = 0 <;> simp [hr0]
      · simp only [hm0, ↓reduceDIte, ↓reduceIte]
        by_cases hr0 : r = 0
        · simp only [hr0, ↓reduceDIte, ↓reduceIte]
          push_cast
          exact shiftClipVal_sub_of_mem_unit zero_le_one le_rfl (hsw0 0) (hsw1 0)
        · simp only [hr0, ↓reduceDIte, ↓reduceIte]
          by_cases hrm : r < m
          · simp only [hrm, ↓reduceDIte, ↓reduceIte]
            exact shiftClipVal_sub_of_mem_unit (hsw0 _) (hsw1 _) (hsw0 _) (hsw1 _)
          · simp only [hrm, ↓reduceDIte, ↓reduceIte]
            by_cases hreq : r = m <;> simp [hreq])

private theorem coeffs_dyadicWeightNormFixed_cases {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack) (r : ℕ) :
    (dyadicWeightNormFixed m κ W hm r).coeffs = RecipeCoeffs.const 0 ∨
      (dyadicWeightNormFixed m κ W hm r).coeffs = dyadicSwitchCoeffs κ W.coeffs ∨
      (dyadicWeightNormFixed m κ W hm r).coeffs = oneSubSwitchCoeffs κ W.coeffs ∨
      (dyadicWeightNormFixed m κ W hm r).coeffs = diffSwitchCoeffs κ W.coeffs := by
  unfold dyadicWeightNormFixed
  dsimp only [FixedRecipe.coeffs, FixedRecipe.congrVal]
  by_cases hm0 : m = 0
  · simp only [FixedRecipe.dite, FixedRecipe.congrVal, hm0, ↓reduceDIte]
    by_cases hr0 : r = 0 <;>
      · simp only [hr0, ↓reduceDIte]
        left
        exact FixedRecipe.coeffs_const ..
  · simp only [FixedRecipe.dite, FixedRecipe.congrVal, hm0, ↓reduceDIte]
    by_cases hr0 : r = 0
    · simp only [hr0, ↓reduceDIte]
      right; right; left
      unfold oneSubSwitchCoeffs
      simp only [FixedRecipe.coeffs_shiftClip, FixedRecipe.coeffs_pairAvg,
        FixedRecipe.coeffs_neg, FixedRecipe.coeffs_const, coeffs_dyadicSwitchNormFixed]
    · simp only [hr0, ↓reduceDIte]
      by_cases hrm : r < m
      · simp only [hrm, ↓reduceDIte]
        right; right; right
        unfold diffSwitchCoeffs
        simp only [FixedRecipe.coeffs_shiftClip, FixedRecipe.coeffs_pairAvg,
          FixedRecipe.coeffs_neg, coeffs_dyadicSwitchNormFixed]
      · simp only [hrm, ↓reduceDIte]
        by_cases hreq : r = m
        · simp only [hreq, ↓reduceDIte]
          right; left
          exact coeffs_dyadicSwitchNormFixed ..
        · simp only [hreq, ↓reduceDIte]
          left
          exact FixedRecipe.coeffs_const ..

/-- Certified `UniformStreamRecipe` computing
`dyadicWeight m r (2 ^ (m + 1) * max 0 (W.targetVal val sEnv))` for any scale index `r : ℕ` when
`m ≤ κ * W.slack`. -/
@[expose] noncomputable def dyadicWeightNormRecipe {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack) (r : ℕ) :
    UniformStreamRecipe Op Struct :=
  (dyadicWeightNormFixed m κ W hm r).toRecipe

end ClippedAtomAndPolynomialSwitch

section RationalRampRecipe

private theorem quarter_clamped_mem_Icc (y : ℝ) :
    Max.max (1 / 4 : ℝ) (Min.min 1 y) ∈ Set.Icc (1 / 4 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem shiftClipVal_inv64_scaled (r : ℕ) {c : ℝ}
    (hc : c ∈ Set.Icc (1 / 4 : ℝ) 1) :
    shiftClipVal (4 - (r : ℤ)) (1 / (64 * c)) =
      (1 / 2) * ((1 / (2 : ℝ) ^ (r + 1)) * (1 / c)) := by
  have hr_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have h4rc : 1 ≤ 4 * (2 : ℝ) ^ r * c := by nlinarith [hc.1]
  have hval_eq : (2 : ℝ) ^ (4 - (r : ℤ)) * (1 / (64 * c)) = 1 / (4 * (2 : ℝ) ^ r * c) := by
    rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_neg, zpow_natCast]
    norm_num
    field_simp
    ring
  have hrhs_eq : 1 / (4 * (2 : ℝ) ^ r * c) =
      (1 / 2) * ((1 / (2 : ℝ) ^ (r + 1)) * (1 / c)) := by
    have hp : (2 : ℝ) ^ (r + 1) = 2 * (2 : ℝ) ^ r := by ring
    rw [hp]
    field_simp
    ring
  unfold shiftClipVal
  have hle1 : 1 / (4 * (2 : ℝ) ^ r * c) ≤ 1 := (div_le_one (by positivity)).mpr h4rc
  have hge_neg1 : -1 ≤ 1 / (4 * (2 : ℝ) ^ r * c) := by
    have h0 : 0 ≤ 1 / (4 * (2 : ℝ) ^ r * c) := by positivity
    linarith
  rw [hval_eq, min_eq_right hle1, max_eq_right hge_neg1, hrhs_eq]

/-- `FixedRecipe` computing the `r`-th clamped dyadic reciprocal term `(1 / 2) * (1 / 2 ^ (r + 1)) /
max (1 / 4) (min 1 (w / 2 ^ (r + 1)))` for `w = 2 ^ (m + 1) * max 0 (W.targetVal val sEnv)`. -/
noncomputable def invScaledNormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) :
    FixedRecipe W.slack W.slack_pos W.ValidEnv
      (fun val sEnv =>
        let w := (2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)
        (1 / 2) * ((1 / (2 : ℝ) ^ (r + 1)) *
          (1 / Max.max (1 / 4) (Min.min 1 (w / (2 : ℝ) ^ (r + 1)))))) :=
  let d := W.slack
  let hd := W.slack_pos
  let V := W.ValidEnv
  let WF := FixedRecipe.ofRecipe W
  let posW := ((FixedRecipe.const d hd V 0 (by norm_num)).max WF).congrVal
    (fun val sEnv => Max.max 0 (W.targetVal val sEnv))
    (fun _ => by push_cast; rfl)
  let scaledF := (posW.shiftClip ((m : ℤ) - (r : ℤ)) κ (by
      have hmZ : (m : ℤ) ≤ ((κ * d : ℕ) : ℤ) := by exact_mod_cast hm
      omega)).congrVal
    (fun val sEnv =>
      Min.min 1 (((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)) / (2 : ℝ) ^ (r + 1)))
    (fun {env sEnv} _ => by
      set x := W.targetVal (fun op => streamVal (env op)) sEnv
      set w := (2 : ℝ) ^ (m + 1) * Max.max 0 x
      have hw0 : 0 ≤ w := mul_nonneg (by positivity) (le_max_left 0 x)
      have hw_div : Max.max 0 x = w / (2 : ℝ) ^ (m + 1) :=
        (mul_div_cancel_left₀ (Max.max 0 x) (by positivity)).symm
      have hscale : (2 : ℝ) ^ ((m : ℤ) - (r : ℤ)) * (w / (2 : ℝ) ^ (m + 1)) =
          w / (2 : ℝ) ^ (r + 1) := by
        have hm1 : (m + 1 : ℕ) = (m - r) + (r + 1) := by omega
        have hsub : ((m : ℤ) - (r : ℤ)) = ((m - r : ℕ) : ℤ) := by omega
        rw [hsub, zpow_natCast, hm1, pow_add]
        field_simp
      rw [hw_div]
      unfold shiftClipVal
      have hq0 : 0 ≤ w / (2 : ℝ) ^ (r + 1) := by positivity
      rw [hscale, max_eq_right (le_min (by norm_num) (by linarith))])
  let cQuarter := FixedRecipe.const d hd V (1 / 4) (by norm_num)
  let cOne := FixedRecipe.const d hd V 1 (by norm_num)
  let clampedF := (cQuarter.max (cOne.min scaledF)).congrVal
    (fun val sEnv =>
      Max.max (1 / 4)
        (Min.min 1 (((2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)) / (2 : ℝ) ^ (r + 1))))
    (fun _ => by
      push_cast
      rw [← min_assoc, min_self])
  let inv64F := clampedF.recip64 (fun _ => quarter_clamped_mem_Icc _)
  let shiftedF := inv64F.shiftClip (4 - (r : ℤ)) 4 (by
    have h4 : (4 : ℤ) ≤ ((4 * d : ℕ) : ℤ) := by
      exact_mod_cast Nat.le_mul_of_pos_right 4 hd
    omega)
  shiftedF.congrVal
    (fun val sEnv =>
      let w := (2 : ℝ) ^ (m + 1) * Max.max 0 (W.targetVal val sEnv)
      (1 / 2) * ((1 / (2 : ℝ) ^ (r + 1)) *
        (1 / Max.max (1 / 4) (Min.min 1 (w / (2 : ℝ) ^ (r + 1))))))
    (fun _ => shiftClipVal_inv64_scaled r (quarter_clamped_mem_Icc _))

private noncomputable def invScaledCoeffs (κ : ℕ) (w : RecipeCoeffs) : RecipeCoeffs :=
  let c0 := RecipeCoeffs.const 0
  let posW := maxPrimCoeffs.compBin c0 w
  let scaled := (shiftClipPrimCoeffs κ).comp posW
  let clamped := maxPrimCoeffs.compBin c0 (minPrimCoeffs.compBin c0 scaled)
  (shiftClipPrimCoeffs 4).comp (recip64PrimCoeffs.comp clamped)

private theorem coeffs_invScaledNormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) :
    (invScaledNormFixed m κ W hm r hr).inner.coeffs = invScaledCoeffs κ W.coeffs := by
  unfold invScaledNormFixed invScaledCoeffs
  simp only [FixedRecipe.congrVal, FixedRecipe.ofRecipe, FixedRecipe.recip64,
    FixedRecipe.coeffs_toRecipe, UniformStreamRecipe.coeffs_recip64,
    FixedRecipe.coeffs_shiftClip, FixedRecipe.coeffs_max, FixedRecipe.coeffs_min,
    FixedRecipe.coeffs_const]

private theorem sameCoeffs_invScaledNormFixed {Op : Type u} {Struct : Type v}
    {m₁ m₂ κ : ℕ} {W₁ W₂ : UniformStreamRecipe Op Struct}
    {hm₁ : m₁ ≤ κ * W₁.slack} {hm₂ : m₂ ≤ κ * W₂.slack}
    {r₁ r₂ : ℕ} {hr₁ : r₁ ≤ m₁} {hr₂ : r₂ ≤ m₂}
    (hW : sameCoeffs W₁ W₂) :
    (invScaledNormFixed m₁ κ W₁ hm₁ r₁ hr₁).sameCoeffs
      (invScaledNormFixed m₂ κ W₂ hm₂ r₂ hr₂) := by
  apply FixedRecipe.sameCoeffs_of_coeffs_eq
  dsimp only [FixedRecipe.coeffs]
  rw [coeffs_invScaledNormFixed, coeffs_invScaledNormFixed,
    UniformStreamRecipe.coeffs_eq_of_sameCoeffs hW]

/-- Leaf reciprocal factor `(1 / 2) * (1 / 2 ^ (r + 1)) * (1 / max (1 / 4) (min 1 (w / 2 ^ (r+1))))`
for scale `r ≤ m` in the smooth dyadic reciprocal decomposition. -/
@[expose] noncomputable def invScaledNormRecipe {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (W : UniformStreamRecipe Op Struct) (hm : m ≤ κ * W.slack)
    (r : ℕ) (hr : r ≤ m) : UniformStreamRecipe Op Struct :=
  (invScaledNormFixed m κ W hm r hr).toRecipe

private theorem mul_coeffs_le_of_bounds {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {fA fB fT : (Op → ℝ) → (Struct → Bool) → ℝ}
    {A : FixedRecipe d hd V fA} {B : FixedRecipe d hd V fB} {T : FixedRecipe d hd V fT}
    {wA wB wC wI : ℕ}
    (hwA : A.toRecipe.coeffA ≤ wA) (hwB : A.toRecipe.coeffB ≤ wB)
    (hwC : A.toRecipe.coeffC ≤ wC) (hwI : A.toRecipe.intrinsicCoeff ≤ wI)
    (hBT : B.sameCoeffs T) :
    let mulP := mulPrim (Struct := Struct) d hd
    let tR := T.toRecipe
    let leafB := max mulP.coeffB (max (max wB tR.coeffB) (max wI tR.intrinsicCoeff))
    let leafA1 := mulP.coeffA + (leafB - mulP.coeffB) * mulP.coeffC
    let leafA2 := max wA tR.coeffA + leafB * max wC tR.coeffC
    (A.mul B).toRecipe.coeffA ≤ leafA1 + leafA2 + 4 ∧
      (A.mul B).toRecipe.coeffB ≤ leafB ∧
      (A.mul B).toRecipe.coeffC ≤ mulP.coeffC + max wC tR.coeffC ∧
      (A.mul B).toRecipe.intrinsicCoeff ≤
        max 8 (max mulP.intrinsicCoeff (max (leafA1 + 4 + max wI tR.intrinsicCoeff) leafB)) := by
  obtain ⟨hBa, hBb, hBc, hBi⟩ := FixedRecipe.sameCoeffs_toRecipe hBT
  intro mulP tR leafB leafA1 leafA2
  dsimp only [FixedRecipe.mul, FixedRecipe.toRecipe, UniformStreamRecipe.mul, composeBinPrim,
    UniformStreamRecipe.congrTarget, UniformStreamRecipe.weakenValid, UniformStreamRecipe.comp]
  dsimp only [FixedRecipe.toRecipe] at hwA hwB hwC hwI hBa hBb hBc hBi
  dsimp only [tR, FixedRecipe.toRecipe] at leafB leafA1 leafA2 ⊢
  rw [hBa, hBb, hBc, hBi]
  have hB_le : max mulP.coeffB
      (max (max A.inner.coeffB T.inner.coeffB)
        (max A.inner.intrinsicCoeff T.inner.intrinsicCoeff)) ≤
      leafB :=
    max_le_max le_rfl (max_le_max (max_le_max hwB le_rfl) (max_le_max hwI le_rfl))
  have hA1_le := Nat.add_le_add_left
    (Nat.mul_le_mul_right mulP.coeffC (Nat.sub_le_sub_right hB_le mulP.coeffB)) mulP.coeffA
  have hA2_le := Nat.add_le_add (max_le_max hwA (le_refl T.inner.coeffA))
    (Nat.mul_le_mul hB_le (max_le_max hwC (le_refl T.inner.coeffC)))
  have hMid := Nat.add_le_add (Nat.add_le_add_right hA1_le 4)
    (max_le_max hwI (le_refl T.inner.intrinsicCoeff))
  exact ⟨Nat.add_le_add_right (Nat.add_le_add hA1_le hA2_le) 4,
    hB_le,
    Nat.add_le_add_left (max_le_max hwC (le_refl T.inner.coeffC)) mulP.coeffC,
    (max_le_max le_rfl (max_le_max hMid hB_le)).trans (le_max_right 8 _)⟩

private theorem coeffs_le_of_eq {Op : Type u} {Struct : Type v}
    {d : ℕ} {hd : 1 ≤ d} {V : (Op → ℕ → ℤ) → (Struct → Bool) → Prop}
    {f : (Op → ℝ) → (Struct → Bool) → ℝ}
    {F : FixedRecipe d hd V f} {c : RecipeCoeffs} {mA mB mC mI : ℕ}
    (hEq : F.coeffs = c)
    (hA : c.coeffA ≤ mA) (hB : c.coeffB ≤ mB)
    (hC : c.coeffC ≤ mC) (hI : c.intrinsicCoeff ≤ mI) :
    F.toRecipe.coeffA ≤ mA ∧ F.toRecipe.coeffB ≤ mB ∧
      F.toRecipe.coeffC ≤ mC ∧ F.toRecipe.intrinsicCoeff ≤ mI := by
  subst hEq
  exact ⟨hA, hB, hC, hI⟩

private theorem sum_fin_two_pow_prefix {m : ℕ} (f : ℕ → ℝ) :
    (∑ i : Fin (2 ^ (m + 1)), if i.val ≤ m then f i.val else 0) =
      ∑ r ∈ range (m + 1), f r := by
  have hm_lt : m + 1 ≤ 2 ^ (m + 1) := (Nat.lt_two_pow_self (n := m + 1)).le
  rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ m then f k else 0), ← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_range]
  omega

/-- `FixedRecipe` computing `1 / (1 + max 0 (2 ^ m * R.targetVal val sEnv))` via the smooth dyadic
partition of unity over `r ∈ {0, ..., m}`. -/
noncomputable def invOneAddScaledFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (R : UniformStreamRecipe Op Struct) (hm : m ≤ κ * R.slack) :
    FixedRecipe R.slack R.slack_pos R.ValidEnv
      (fun val sEnv => 1 / (1 + Max.max 0 ((2 : ℝ) ^ m * R.targetVal val sEnv))) :=
  let d := R.slack
  let hd := R.slack_pos
  let V := R.ValidEnv
  let RF := FixedRecipe.ofRecipe R
  let posQ := ((FixedRecipe.const d hd V 0 (by norm_num)).max RF).congrVal
    (fun val sEnv => Max.max 0 (R.targetVal val sEnv))
    (fun _ => by push_cast; rfl)
  have h2pow_abs : |(1 / (2 : ℚ) ^ m : ℚ)| ≤ 1 := by
    have hge1 : (1 : ℚ) ≤ (2 : ℚ) ^ m := one_le_pow₀ (by norm_num)
    have hnonneg : (0 : ℚ) ≤ 1 / (2 : ℚ) ^ m := by positivity
    rw [abs_of_nonneg hnonneg]
    exact (div_le_one (by positivity)).mpr hge1
  let twoPowInvF := FixedRecipe.const d hd V (1 / (2 : ℚ) ^ m) h2pow_abs κ
  let wNormF := twoPowInvF.pairAvg posQ
  let wNormR := wNormF.toRecipe
  let swC := dyadicSwitchCoeffs κ wNormR.coeffs
  let oneSubC := oneSubSwitchCoeffs κ wNormR.coeffs
  let diffSwC := diffSwitchCoeffs κ wNormR.coeffs
  let invTpl := invScaledNormFixed 0 κ wNormR (Nat.zero_le _) 0 le_rfl
  let invTplR := invTpl.toRecipe
  let wgtMaxA := max swC.coeffA (max oneSubC.coeffA diffSwC.coeffA)
  let wgtMaxB := max swC.coeffB (max oneSubC.coeffB diffSwC.coeffB)
  let wgtMaxC := max swC.coeffC (max oneSubC.coeffC diffSwC.coeffC)
  let wgtMaxInt :=
    max 8 (max swC.intrinsicCoeff (max oneSubC.intrinsicCoeff diffSwC.intrinsicCoeff))
  let mulPrimR := mulPrim (Struct := Struct) d hd
  let leafB := max mulPrimR.coeffB
    (max (max wgtMaxB invTplR.coeffB) (max wgtMaxInt invTplR.intrinsicCoeff))
  let leafA1 := mulPrimR.coeffA + (leafB - mulPrimR.coeffB) * mulPrimR.coeffC
  let leafA2 := max wgtMaxA invTplR.coeffA + leafB * max wgtMaxC invTplR.coeffC
  let cA := leafA1 + leafA2 + 4
  let cB := leafB
  let cC := mulPrimR.coeffC + max wgtMaxC invTplR.coeffC
  let cInt := max 8 (max mulPrimR.intrinsicCoeff
    (max (leafA1 + 4 + max wgtMaxInt invTplR.intrinsicCoeff) leafB))
  have hWgtBounds : ∀ r,
      (dyadicWeightNormFixed m κ wNormR hm r).toRecipe.coeffA ≤ wgtMaxA ∧
        (dyadicWeightNormFixed m κ wNormR hm r).toRecipe.coeffB ≤ wgtMaxB ∧
        (dyadicWeightNormFixed m κ wNormR hm r).toRecipe.coeffC ≤ wgtMaxC ∧
        (dyadicWeightNormFixed m κ wNormR hm r).toRecipe.intrinsicCoeff ≤ wgtMaxInt := by
    intro r
    rcases coeffs_dyadicWeightNormFixed_cases m κ wNormR hm r with h | h | h | h
    · exact coeffs_le_of_eq h (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (le_max_left 8 _)
    · exact coeffs_le_of_eq h (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
        ((le_max_left _ _).trans (le_max_right 8 _))
    · exact coeffs_le_of_eq h
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _))
        (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right 8 _))
    · exact coeffs_le_of_eq h
        ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))
        ((le_max_right _ _).trans (le_max_right _ _))
        (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right 8 _))
  let children : Fin (2 ^ (m + 1)) → UniformStreamRecipe Op Struct := fun i =>
    if hi : i.val ≤ m then
      ((dyadicWeightNormFixed m κ wNormR hm i.val).mul
        (invScaledNormFixed m κ wNormR hm i.val hi)).toRecipe
    else
      (FixedRecipe.const d hd V 0 (by norm_num)).toRecipe
  have hChildBounds : ∀ i : Fin (2 ^ (m + 1)),
      (children i).coeffA ≤ cA ∧ (children i).coeffB ≤ cB ∧
        (children i).coeffC ≤ cC ∧ (children i).intrinsicCoeff ≤ cInt := by
    intro i
    dsimp only [children]
    split_ifs with hi
    · obtain ⟨hwA, hwB, hwC, hwI⟩ := hWgtBounds i.val
      exact mul_coeffs_le_of_bounds (T := invTpl) hwA hwB hwC hwI
        (sameCoeffs_invScaledNormFixed ⟨rfl, rfl, rfl, rfl⟩)
    · exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, le_max_left 8 _⟩
  have hTree : m + 1 ≤ (κ + 1) * d := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add hm hd
  let avgRaw := balancedAvgRecipe d hd (m + 1) (κ + 1) hTree children cA cB cC cInt
    (fun i => by dsimp only [children]; split_ifs <;> rfl)
    (fun i => by obtain ⟨ha, _, _, _⟩ := hChildBounds i; exact ha)
    (fun i => by obtain ⟨_, hb, _, _⟩ := hChildBounds i; exact hb)
    (fun i => by obtain ⟨_, _, hc, _⟩ := hChildBounds i; exact hc)
    (fun i => by obtain ⟨_, _, _, hi⟩ := hChildBounds i; exact hi)
  let avgF : FixedRecipe d hd V avgRaw.targetVal :=
    (FixedRecipe.ofRecipe avgRaw).weaken (fun hR i => by
      dsimp only [children]
      split_ifs <;> exact hR)
  let shiftedF := avgF.shiftClip ((m : ℤ) + 2) (κ + 2) (by
    have h2 : 2 ≤ 2 * d := Nat.le_mul_of_pos_right 2 hd
    have hm2 : m + 2 ≤ (κ + 2) * d := by
      rw [Nat.add_mul]
      exact Nat.add_le_add hm h2
    exact_mod_cast hm2)
  shiftedF.congrVal
    (fun val sEnv => 1 / (1 + Max.max 0 ((2 : ℝ) ^ m * R.targetVal val sEnv)))
    (fun {env sEnv} hR => by
      set q := R.targetVal (fun op => streamVal (env op)) sEnv
      have hq_hi : q ≤ 1 := (abs_le.mp (R.abs_targetVal_le_one hR)).2
      have hmax_mul : Max.max (0 : ℝ) ((2 : ℝ) ^ m * q) = (2 : ℝ) ^ m * Max.max 0 q := by
        rw [mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 ^ m), mul_zero]
      set w := 1 + Max.max (0 : ℝ) ((2 : ℝ) ^ m * q)
      have hw_lo : 1 ≤ w := by
        dsimp only [w]
        linarith [le_max_left (0 : ℝ) ((2 : ℝ) ^ m * q)]
      have hw_hi : w ≤ (2 : ℝ) ^ (m + 1) := by
        have hmax_le1 : Max.max (0 : ℝ) q ≤ 1 := max_le zero_le_one hq_hi
        have hu_le : Max.max (0 : ℝ) ((2 : ℝ) ^ m * q) ≤ (2 : ℝ) ^ m := by
          rw [hmax_mul]
          exact (mul_le_mul_of_nonneg_left hmax_le1 (by positivity)).trans
            (by ring_nf; exact le_rfl)
        have h1_le : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        have hp : (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ m + (2 : ℝ) ^ m := by ring
        dsimp only [w]
        linarith
      have hwNorm : wNormR.targetVal (fun op => streamVal (env op)) sEnv =
          w / (2 : ℝ) ^ (m + 1) := by
        change (((1 / (2 : ℚ) ^ m : ℚ) : ℝ) + Max.max 0 q) / 2 = w / (2 : ℝ) ^ (m + 1)
        push_cast
        dsimp only [w]
        rw [hmax_mul]
        have hp : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by ring
        rw [hp]
        field_simp
      have hwNorm_nonneg : 0 ≤ wNormR.targetVal (fun op => streamVal (env op)) sEnv := by
        rw [hwNorm]
        positivity
      have hw_rec : (2 : ℝ) ^ (m + 1) *
          Max.max 0 (wNormR.targetVal (fun op => streamVal (env op)) sEnv) = w := by
        rw [max_eq_right hwNorm_nonneg, hwNorm]
        exact mul_div_cancel₀ w (by positivity)
      have hchild_val : ∀ i : Fin (2 ^ (m + 1)),
          (children i).targetVal (fun op => streamVal (env op)) sEnv =
            if i.val ≤ m then
              (1 / 2) * (dyadicWeight m i.val w *
                ((1 / (2 : ℝ) ^ (i.val + 1)) *
                  (1 / Max.max (1 / 4) (Min.min 1 (w / (2 : ℝ) ^ (i.val + 1))))))
            else 0 := by
        intro i
        dsimp only [children]
        by_cases hi : i.val ≤ m
        · simp only [hi, ↓reduceDIte, ↓reduceIte, FixedRecipe.toRecipe]
          rw [hw_rec]
          ring
        · simp [hi, FixedRecipe.toRecipe]
      have havg_val : avgRaw.targetVal (fun op => streamVal (env op)) sEnv =
          (1 / (2 : ℝ) ^ (m + 2)) * (1 / w) := by
        change (∑ i : Fin (2 ^ (m + 1)),
            (children i).targetVal (fun op => streamVal (env op)) sEnv) /
          (2 : ℝ) ^ (m + 1) = _
        simp_rw [hchild_val]
        rw [sum_fin_two_pow_prefix (fun r => (1 / 2) * (dyadicWeight m r w *
          ((1 / (2 : ℝ) ^ (r + 1)) *
            (1 / Max.max (1 / 4) (Min.min 1 (w / (2 : ℝ) ^ (r + 1))))))),
          ← mul_sum, ← inv_eq_sum_dyadicWeight ⟨hw_lo, hw_hi⟩]
        have hp : (2 : ℝ) ^ (m + 2) = 2 * (2 : ℝ) ^ (m + 1) := by ring
        rw [hp]
        field_simp
      rw [havg_val]
      unfold shiftClipVal
      have hscale : (2 : ℝ) ^ ((m : ℤ) + 2) * ((1 / (2 : ℝ) ^ (m + 2)) * (1 / w)) = 1 / w := by
        have hz : ((m : ℤ) + 2) = ((m + 2 : ℕ) : ℤ) := by omega
        rw [hz, zpow_natCast]
        field_simp
      have hw_inv_le1 : 1 / w ≤ 1 := (div_le_one (by linarith)).mpr hw_lo
      have hw_inv_ge : -1 ≤ 1 / w := by
        have h0 : 0 ≤ 1 / w := by positivity
        linarith
      rw [hscale, min_eq_right hw_inv_le1, max_eq_right hw_inv_ge])

/-- Certified `UniformStreamRecipe` computing `1 / (1 + max 0 (2 ^ m * R.targetVal val sEnv))`
for `m ≤ κ * R.slack` via an `(m + 1)`-level balanced binary-tree average over dyadic partition-of-
unity terms. -/
@[expose] noncomputable def invOneAddScaledRecipe {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (R : UniformStreamRecipe Op Struct) (hm : m ≤ κ * R.slack) :
    UniformStreamRecipe Op Struct :=
  (invOneAddScaledFixed m κ R hm).toRecipe

/-- `FixedRecipe` computing `Cslib.rationalRamp4Unit (2 ^ m * R.targetVal val sEnv) / 2 ^ m`
[OpenAI2026LogSpace, Section 4.1]. -/
noncomputable def rationalRamp4NormFixed {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (R : UniformStreamRecipe Op Struct) (hm : m ≤ κ * R.slack) :
    FixedRecipe R.slack R.slack_pos R.ValidEnv
      (fun val sEnv =>
        Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * R.targetVal val sEnv) / (2 : ℝ) ^ m) :=
  let d := R.slack
  let hd := R.slack_pos
  let V := R.ValidEnv
  let RF := FixedRecipe.ofRecipe R
  let posQ := ((FixedRecipe.const d hd V 0 (by norm_num)).max RF).congrVal
    (fun val sEnv => Max.max 0 (R.targetVal val sEnv))
    (fun _ => by push_cast; rfl)
  let sF := invOneAddScaledFixed m κ R hm
  let s2F := sF.mul sF
  let s3F := s2F.mul sF
  let cNeg3_4 := FixedRecipe.const d hd V (-3 / 4) (by norm_num)
  let c3_4 := FixedRecipe.const d hd V (3 / 4) (by norm_num)
  let c1_16 := FixedRecipe.const d hd V (1 / 16) (by norm_num)
  let c1_4 := FixedRecipe.const d hd V (1 / 4) (by norm_num)
  let pA := cNeg3_4.pairAvg (c3_4.mul sF)
  let pB := (c3_4.mul sF).pairAvg s2F.neg
  let pAB := pA.pairAvg pB
  let p32 := (pAB.pairAvg (c1_16.mul s3F)).congrVal
    (fun val sEnv =>
      let s := 1 / (1 + Max.max 0 ((2 : ℝ) ^ m * R.targetVal val sEnv))
      (-3 + 6 * s - 4 * s ^ 2 + s ^ 3) / 32)
    (fun _ => by push_cast; ring)
  let pScaled := (p32.shiftClip (3 - (m : ℤ)) 3 (by
      have h3 : (3 : ℤ) ≤ ((3 * d : ℕ) : ℤ) := by
        exact_mod_cast Nat.le_mul_of_pos_right 3 hd
      omega)).congrVal
    (fun val sEnv =>
      let s := 1 / (1 + Max.max 0 ((2 : ℝ) ^ m * R.targetVal val sEnv))
      (-3 + 6 * s - 4 * s ^ 2 + s ^ 3) / (4 * (2 : ℝ) ^ m))
    (fun {env sEnv} _ => by
      set q := R.targetVal (fun op => streamVal (env op)) sEnv
      set u := Max.max (0 : ℝ) ((2 : ℝ) ^ m * q)
      set s := 1 / (1 + u)
      have hu0 : 0 ≤ u := le_max_left 0 _
      have hs0 : 0 ≤ s := by dsimp only [s]; positivity
      have hs1 : s ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      set P := -3 + 6 * s - 4 * s ^ 2 + s ^ 3
      have hP_lo : -3 ≤ P := by dsimp only [P]; nlinarith [sq_nonneg (s - 2)]
      have hP_hi : P ≤ 0 := by dsimp only [P]; nlinarith [sq_nonneg (s - 3 / 2)]
      unfold shiftClipVal
      have hmul : (2 : ℝ) ^ (3 - (m : ℤ)) * (P / 32) = P / (4 * (2 : ℝ) ^ m) := by
        rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_neg, zpow_natCast]
        norm_num
        field_simp
        ring
      have h2m_ge1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      have hle1 : P / (4 * (2 : ℝ) ^ m) ≤ 1 := by
        have hnonpos : P / (4 * (2 : ℝ) ^ m) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg hP_hi (by positivity)
        linarith
      have hge_neg1 : -1 ≤ P / (4 * (2 : ℝ) ^ m) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      rw [hmul, min_eq_right hle1, max_eq_right hge_neg1])
  let avgRamp := (c1_4.mul posQ).pairAvg pScaled
  let raw := avgRamp.shiftClip 3 3 (by exact_mod_cast Nat.le_mul_of_pos_right 3 hd)
  raw.congrVal
    (fun val sEnv => Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * R.targetVal val sEnv) / (2 : ℝ) ^ m)
    (fun {env sEnv} hR => by
      set q := R.targetVal (fun op => streamVal (env op)) sEnv
      have hq_hi : q ≤ 1 := (abs_le.mp (R.abs_targetVal_le_one hR)).2
      have hmax_mul : Max.max (0 : ℝ) ((2 : ℝ) ^ m * q) = (2 : ℝ) ^ m * Max.max 0 q := by
        rw [mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 2 ^ m), mul_zero]
      set u := Max.max (0 : ℝ) ((2 : ℝ) ^ m * q)
      set s := 1 / (1 + u)
      set P := -3 + 6 * s - 4 * s ^ 2 + s ^ 3
      have hramp_eq : Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m =
          Max.max 0 q + P / (2 : ℝ) ^ m := by
        have hdec := rationalRamp4Unit_eq_poly_add_inv ((2 : ℝ) ^ m * q)
        have hdec' : Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) = u + P := by grind
        rw [hdec', add_div, hmax_mul, mul_div_cancel_left₀ _ (by positivity)]
      have havg_eq :
          (((1 / 4 : ℚ) : ℝ) * Max.max 0 q + P / (4 * (2 : ℝ) ^ m)) / 2 =
            (Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m) / 8 := by
        rw [hramp_eq]
        push_cast
        field_simp
        ring
      change shiftClipVal 3 ((((1 / 4 : ℚ) : ℝ) * Max.max 0 q + P / (4 * (2 : ℝ) ^ m)) / 2) = _
      rw [havg_eq]
      unfold shiftClipVal
      have hmul8 : (2 : ℝ) ^ (3 : ℤ) *
          ((Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m) / 8) =
          Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m := by
        norm_num
        ring
      have hramp_lo : 0 ≤ Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m :=
        div_nonneg (Cslib.rationalRamp4Unit_nonneg _) (by positivity)
      have hramp_hi : Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) / (2 : ℝ) ^ m ≤ 1 := by
        refine (div_le_one (by positivity)).mpr ?_
        have hle_u : Cslib.rationalRamp4Unit ((2 : ℝ) ^ m * q) ≤ u :=
          Cslib.rationalRamp4Unit_le _
        have hmax_le1 : Max.max (0 : ℝ) q ≤ 1 := max_le zero_le_one hq_hi
        have hu_le : u ≤ (2 : ℝ) ^ m := by
          rw [hmax_mul]
          exact (mul_le_mul_of_nonneg_left hmax_le1 (by positivity)).trans
            (by ring_nf; exact le_rfl)
        exact hle_u.trans hu_le
      rw [hmul8, min_eq_right hramp_hi, max_eq_right (by linarith)])

/-- Certified `UniformStreamRecipe` computing the normalized rational correction ramp
`Cslib.rationalRamp4Unit (2 ^ m * R.targetVal val sEnv) / 2 ^ m` whenever `m ≤ κ * R.slack`. -/
@[expose] noncomputable def rationalRamp4NormRecipe {Op : Type u} {Struct : Type v}
    (m κ : ℕ) (R : UniformStreamRecipe Op Struct) (hm : m ≤ κ * R.slack) :
    UniformStreamRecipe Op Struct :=
  (rationalRamp4NormFixed m κ R hm).toRecipe

end RationalRampRecipe

section RowCompressionRecipes

/-- Operand stream index for a single step of two-coordinate row compression
(`Cslib.RowCompression`). -/
inductive RowStreamIdx (ι : Type u) where
  | floor : RowStreamIdx ι
  | oldDefault : RowStreamIdx ι
  | entry (x : ι) (μ : Fin 2) : RowStreamIdx ι
  deriving DecidableEq

/-- Normalized signed-stream environment precondition on `.floor`, `.oldDefault`, and all active
support coordinates `x ∈ items`. -/
structure RowSupportValidEnv {ι : Type u} (items : List ι)
    (env : RowStreamIdx ι → ℕ → ℤ) : Prop where
  floor_norm : IsNormSignedStream (env .floor)
  oldDefault_norm : IsNormSignedStream (env .oldDefault)
  entry_norm : ∀ x ∈ items, ∀ μ, IsNormSignedStream (env (.entry x μ))

/-- Normalized signed-stream environment precondition for `Cslib.RowCompression.update` at
coordinate `y`. -/
structure RowUpdateValidEnv {ι : Type u} (items : List ι) (y : ι)
    (env : RowStreamIdx ι → ℕ → ℤ) : Prop extends RowSupportValidEnv items env where
  target_norm : ∀ μ, IsNormSignedStream (env (.entry y μ))

private theorem threshold_mem_unit {ι : Type u} {s : Finset ι} {n : ℕ} {ρ z : ℝ}
    {w : ι → Fin 2 → ℝ} (hρ : |ρ| ≤ 1) (hz : |z| ≤ 1)
    (hw : ∀ x ∈ s, ∀ μ, |w x μ| ≤ 1) :
    Cslib.RowCompression.threshold s n ρ z w ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Cslib.RowCompression.threshold_nonneg, ?_⟩
  unfold Cslib.RowCompression.threshold
  refine max_le (abs_le.mp hz).2 (max_le (abs_le.mp hρ).2 ?_)
  exact kthLargest_le zero_le_one fun x hx => max_le (hw x hx 0) (hw x hx 1)

private theorem newDefault_mem_unit {ι : Type u} {s : Finset ι} {n K : ℕ} {ρ z : ℝ}
    {w : ι → Fin 2 → ℝ} (hρ : |ρ| ≤ 1) (hz : |z| ≤ 1)
    (hw : ∀ x ∈ s, ∀ μ, |w x μ| ≤ 1) :
    Cslib.RowCompression.newDefault s n K ρ z w ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨Cslib.RowCompression.newDefault_nonneg, ?_⟩
  have hu := (threshold_mem_unit (n := n) hρ hz hw).2
  unfold Cslib.RowCompression.newDefault
  refine max_le hu ((min_le_left _ _).trans (max_le (abs_le.mp hz).2 ?_))
  exact kthLargest_le zero_le_one fun x hx => (abs_le.mp (hw x hx 0)).2

/-- `FixedRecipe` computing the row-compression threshold `Cslib.RowCompression.threshold` via
`zeroPaddedRankListRecipe` [OpenAI2026LogSpace, Section 8.2, Lemmas 10.6--10.7]. -/
noncomputable def rowCompressionThresholdFixed {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n : ℕ) :
    FixedRecipe d hd (fun (env : RowStreamIdx ι → ℕ → ℤ) (_ : Struct → Bool) =>
        RowSupportValidEnv items env)
      (fun val _ =>
        Cslib.RowCompression.threshold items.toFinset n
          (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))) :=
  let V : (RowStreamIdx ι → ℕ → ℤ) → (Struct → Bool) → Prop :=
    fun env _ => RowSupportValidEnv items env
  let sizeTpl :=
    ((FixedRecipe.var (Struct := Struct) d hd V .floor (fun h => h.floor_norm)).abs).max
      ((FixedRecipe.var (Struct := Struct) d hd V .floor (fun h => h.floor_norm)).abs)
  let sizeTplR := sizeTpl.toRecipe
  let sizeChild : ι → UniformStreamRecipe (RowStreamIdx ι) Struct := fun x =>
    if hx : x ∈ items then
      (((FixedRecipe.var (Struct := Struct) d hd V (.entry x 0)
            (fun h => h.entry_norm x hx 0)).abs).max
        ((FixedRecipe.var (Struct := Struct) d hd V (.entry x 1)
            (fun h => h.entry_norm x hx 1)).abs)).toRecipe
    else
      (FixedRecipe.const (Struct := Struct) d hd V 0 (by norm_num)).toRecipe
  have hSizeCoeffs : ∀ x, (hx : x ∈ items) →
      sameCoeffs (sizeChild x) sizeTplR := by
    intro x hx
    simp only [sizeChild, hx, ↓reduceDIte]
    apply sameCoeffs_of_coeffs_eq
    simp only [sizeTplR, sizeTpl, FixedRecipe.coeffs_toRecipe, FixedRecipe.coeffs_max,
      FixedRecipe.coeffs_abs, FixedRecipe.coeffs_var]
  let rankSizeRaw := (zeroPaddedRankListRecipe (Struct := Struct) d hd n items hNodup κ hLen).comp
    sizeChild sizeTplR.coeffA sizeTplR.coeffB sizeTplR.coeffC (max 8 sizeTplR.intrinsicCoeff)
    (fun x => by dsimp only [sizeChild]; split_ifs <;> rfl)
    (fun x => by
      by_cases hx : x ∈ items
      · obtain ⟨ha, _, _, _⟩ := hSizeCoeffs x hx; rw [ha]
      · simp only [sizeChild, hx, ↓reduceDIte]; exact Nat.zero_le _)
    (fun x => by
      by_cases hx : x ∈ items
      · obtain ⟨_, hb, _, _⟩ := hSizeCoeffs x hx; rw [hb]
      · simp only [sizeChild, hx, ↓reduceDIte]; exact Nat.zero_le _)
    (fun x => by
      by_cases hx : x ∈ items
      · obtain ⟨_, _, hc, _⟩ := hSizeCoeffs x hx; rw [hc]
      · simp only [sizeChild, hx, ↓reduceDIte]; exact Nat.zero_le _)
    (fun x => by
      by_cases hx : x ∈ items
      · obtain ⟨_, _, _, hi⟩ := hSizeCoeffs x hx; rw [hi]; exact le_max_right 8 _
      · simp only [sizeChild, hx, ↓reduceDIte]; exact le_max_left 8 _)
  let rankSizeF := (FixedRecipe.ofRecipe rankSizeRaw).weaken (V₂ := V) (fun {env sEnv} hV => by
    have hCh : ∀ x, (sizeChild x).ValidEnv env sEnv := by
      intro x
      dsimp only [sizeChild]
      split_ifs <;> exact hV
    refine ⟨hCh, fun x _ => ⟨(sizeChild x).emits_signed (hCh x), ?_⟩⟩
    rw [(sizeChild x).emits_exact (hCh x)]
    exact (sizeChild x).abs_targetVal_le_one (hCh x))
  let floorF := FixedRecipe.var (Struct := Struct) d hd V .floor (fun h => h.floor_norm)
  let oldDefF := FixedRecipe.var (Struct := Struct) d hd V .oldDefault (fun h => h.oldDefault_norm)
  let raw := oldDefF.max (floorF.max rankSizeF)
  raw.congrVal
    (fun val _ =>
      Cslib.RowCompression.threshold items.toFinset n
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ)))
    (fun _ => by
      unfold Cslib.RowCompression.threshold
      congr 2
      exact kthLargest_congr fun x hx => by
        have hmem : x ∈ items := List.mem_toFinset.mp hx
        simp only [sizeChild, hmem, ↓reduceDIte]
        rfl)

/-- Certified primitive recipe over `RowStreamIdx ι` computing
`Cslib.RowCompression.threshold items.toFinset n` for any duplicate-free support list `items` of
length `≤ 2 ^ (κ * d)`. -/
@[expose] noncomputable def rowCompressionThresholdPrim {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n : ℕ) :
    UniformStreamRecipe (RowStreamIdx ι) Struct :=
  (rowCompressionThresholdFixed d hd items hNodup κ hLen n).toRecipe

/-- `FixedRecipe` computing `Cslib.RowCompression.newDefault` via `rowCompressionThresholdFixed` and
`zeroPaddedRankListRecipe` [OpenAI2026LogSpace, Section 8.2]. -/
noncomputable def rowCompressionNewDefaultFixed {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ) :
    FixedRecipe d hd (fun (env : RowStreamIdx ι → ℕ → ℤ) (_ : Struct → Bool) =>
        RowSupportValidEnv items env)
      (fun val _ =>
        Cslib.RowCompression.newDefault items.toFinset n K
          (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))) :=
  let V : (RowStreamIdx ι → ℕ → ℤ) → (Struct → Bool) → Prop :=
    fun env _ => RowSupportValidEnv items env
  let uF := rowCompressionThresholdFixed (Struct := Struct) d hd items hNodup κ hLen n
  let firstChild : ι → UniformStreamRecipe (RowStreamIdx ι) Struct := fun x =>
    if hx : x ∈ items then
      (FixedRecipe.var (Struct := Struct) d hd V (.entry x 0)
        (fun h => h.entry_norm x hx 0)).toRecipe
    else
      (FixedRecipe.const (Struct := Struct) d hd V 0 (by norm_num)).toRecipe
  let rankFirstRaw := (zeroPaddedRankListRecipe (Struct := Struct) d hd K items hNodup κ hLen).comp
    firstChild 4 0 0 8
    (fun x => by dsimp only [firstChild]; split_ifs <;> rfl)
    (fun x => by
      dsimp only [firstChild]
      split_ifs <;>
        · dsimp only [FixedRecipe.toRecipe, FixedRecipe.var, FixedRecipe.const, varRecipe,
            ratRecipe]
          omega)
    (fun x => by
      dsimp only [firstChild]
      split_ifs <;>
        · dsimp only [FixedRecipe.toRecipe, FixedRecipe.var, FixedRecipe.const, varRecipe,
            ratRecipe]
          omega)
    (fun x => by
      dsimp only [firstChild]
      split_ifs <;>
        · dsimp only [FixedRecipe.toRecipe, FixedRecipe.var, FixedRecipe.const, varRecipe,
            ratRecipe]
          omega)
    (fun x => by
      dsimp only [firstChild]
      split_ifs <;>
        · dsimp only [FixedRecipe.toRecipe, FixedRecipe.var, FixedRecipe.const, varRecipe,
            ratRecipe]
          omega)
  let rankFirstF := ((FixedRecipe.ofRecipe rankFirstRaw).weaken (V₂ := V) (fun {env sEnv} hV => by
      have hCh : ∀ x, (firstChild x).ValidEnv env sEnv := by
        intro x
        dsimp only [firstChild]
        split_ifs <;> exact hV
      refine ⟨hCh, fun x _ => ⟨(firstChild x).emits_signed (hCh x), ?_⟩⟩
      rw [(firstChild x).emits_exact (hCh x)]
      exact (firstChild x).abs_targetVal_le_one (hCh x))).congrVal
    (fun val _ => kthLargest K items.toFinset (fun x => val (.entry x 0)))
    (fun _ =>
      kthLargest_congr fun x hx => by
        have hmem : x ∈ items := List.mem_toFinset.mp hx
        simp only [firstChild, hmem, ↓reduceDIte]
        rfl)
  let oldDefF := FixedRecipe.var (Struct := Struct) d hd V .oldDefault (fun h => h.oldDefault_norm)
  let c1_4 := FixedRecipe.const (Struct := Struct) d hd V (1 / 4) (by norm_num)
  let c3_4 := FixedRecipe.const (Struct := Struct) d hd V (3 / 4) (by norm_num)
  let maxFirst := oldDefF.max rankFirstF
  let quarterNewDef := (c1_4.mul uF).max ((c1_4.mul maxFirst).min (c3_4.mul uF))
  let raw := quarterNewDef.shiftClip 2 2 (by exact_mod_cast Nat.le_mul_of_pos_right 2 hd)
  raw.congrVal
    (fun val _ =>
      Cslib.RowCompression.newDefault items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ)))
    (fun {env _} hV => by
      set ρ := streamVal (env .floor)
      set z := streamVal (env .oldDefault)
      set w : ι → Fin 2 → ℝ := fun x μ => streamVal (env (.entry x μ))
      set u := Cslib.RowCompression.threshold items.toFinset n ρ z w
      have hquarter :
          Max.max (((1 / 4 : ℚ) : ℝ) * u)
              (Min.min (((1 / 4 : ℚ) : ℝ) * Max.max z (kthLargest K items.toFinset fun x => w x 0))
                (((3 / 4 : ℚ) : ℝ) * u)) =
            (1 / 4 : ℝ) * Cslib.RowCompression.newDefault items.toFinset n K ρ z w := by
        push_cast
        dsimp only [u]
        have hpos4 : (0 : ℝ) ≤ 1 / 4 := by norm_num
        conv_rhs =>
          rw [Cslib.RowCompression.newDefault, mul_max_of_nonneg _ _ hpos4,
            mul_min_of_nonneg _ _ hpos4]
        have h34 : (1 / 4 : ℝ) * (3 * Cslib.RowCompression.threshold items.toFinset n ρ z w) =
            (3 / 4) * Cslib.RowCompression.threshold items.toFinset n ρ z w := by ring
        rw [h34]
      change shiftClipVal 2
          (Max.max (((1 / 4 : ℚ) : ℝ) * u)
            (Min.min (((1 / 4 : ℚ) : ℝ) * Max.max z (kthLargest K items.toFinset fun x => w x 0))
              (((3 / 4 : ℚ) : ℝ) * u))) = _
      rw [hquarter]
      have hz_mem := newDefault_mem_unit (s := items.toFinset) (n := n) (K := K)
        hV.floor_norm.2 hV.oldDefault_norm.2
        (fun x hx μ => (hV.entry_norm x (List.mem_toFinset.mp hx) μ).2)
      unfold shiftClipVal
      have hmul4 : (2 : ℝ) ^ (2 : ℤ) *
          ((1 / 4 : ℝ) * Cslib.RowCompression.newDefault items.toFinset n K ρ z w) =
          Cslib.RowCompression.newDefault items.toFinset n K ρ z w := by
        norm_num
        ring
      rw [hmul4, min_eq_right hz_mem.2, max_eq_right (by linarith [hz_mem.1])])

/-- Certified primitive recipe over `RowStreamIdx ι` computing
`Cslib.RowCompression.newDefault items.toFinset n K` [OpenAI2026LogSpace, (8.5)]. -/
@[expose] noncomputable def rowCompressionNewDefaultPrim {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ) :
    UniformStreamRecipe (RowStreamIdx ι) Struct :=
  (rowCompressionNewDefaultFixed d hd items hNodup κ hLen n K).toRecipe

/-- `FixedRecipe` computing `Cslib.RowCompression.update` for entry `(y, ν)` via
`rowCompressionThresholdFixed` and `rowCompressionNewDefaultFixed` [OpenAI2026LogSpace,
Section 8.2]. -/
noncomputable def rowCompressionUpdateFixed {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ) (y : ι) (ν : Fin 2) :
    FixedRecipe d hd (fun (env : RowStreamIdx ι → ℕ → ℤ) (_ : Struct → Bool) =>
        RowUpdateValidEnv items y env)
      (fun val _ =>
        Cslib.RowCompression.update items.toFinset n K
          (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ)) y ν) :=
  let V : (RowStreamIdx ι → ℕ → ℤ) → (Struct → Bool) → Prop :=
    fun env _ => RowUpdateValidEnv items y env
  let uF := (rowCompressionThresholdFixed (Struct := Struct) d hd items hNodup κ hLen n).weaken
    (V₂ := V) (fun hV => hV.toRowSupportValidEnv)
  let newDefF :=
    (rowCompressionNewDefaultFixed (Struct := Struct) d hd items hNodup κ hLen n K).weaken
      (V₂ := V) (fun hV => hV.toRowSupportValidEnv)
  let wy0 := FixedRecipe.var (Struct := Struct) d hd V (.entry y 0) (fun hV => hV.target_norm 0)
  let wy1 := FixedRecipe.var (Struct := Struct) d hd V (.entry y 1) (fun hV => hV.target_norm 1)
  let wyNu := FixedRecipe.var (Struct := Struct) d hd V (.entry y ν) (fun hV => hV.target_norm ν)
  let entrySizeY := wy0.abs.max wy1.abs
  let c0 := FixedRecipe.const (Struct := Struct) d hd V 0 (by norm_num)
  let c1_2 := FixedRecipe.const (Struct := Struct) d hd V (1 / 2) (by norm_num)
  let c7_8 := FixedRecipe.const (Struct := Struct) d hd V (7 / 8) (by norm_num)
  let c1_16 := FixedRecipe.const (Struct := Struct) d hd V (1 / 16) (by norm_num)
  let c1_32 := FixedRecipe.const (Struct := Struct) d hd V (1 / 32) (by norm_num)
  let excess4 := ((c1_2.mul entrySizeY).pairAvg uF.neg).max c0
  let rad32 := (c7_8.mul excess4).congrVal
    (fun val _ =>
      let u := Cslib.RowCompression.threshold items.toFinset n
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))
      Cslib.RowCompression.radius u (fun μ => val (.entry y μ)) / 32)
    (fun {env _} _ => by
      push_cast
      unfold Cslib.RowCompression.radius Cslib.RowCompression.entrySize
      set sY := Max.max |streamVal (env (.entry y 0))| |streamVal (env (.entry y 1))|
      set u := Cslib.RowCompression.threshold items.toFinset n
        (streamVal (env .floor)) (streamVal (env .oldDefault))
        (fun x μ => streamVal (env (.entry x μ)))
      have hpos4 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      have hinner : ((1 / 2 : ℝ) * sY + -u) / 2 = (1 / 4) * (sY - 2 * u) := by ring
      have hmax : Max.max ((1 / 4 : ℝ) * (sY - 2 * u)) 0 = (1 / 4) * Max.max (sY - 2 * u) 0 := by
        rw [mul_max_of_nonneg _ 0 hpos4, mul_zero]
      rw [hinner, hmax]
      ring)
  let def16 := (FixedRecipe.dite (ν = 0)
      (fun _ => c1_16.mul newDefF)
      (fun _ => c0)).congrVal
    (fun val _ =>
      let z' := Cslib.RowCompression.newDefault items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))
      Cslib.RowCompression.defaultEntry z' ν / 16)
    (fun _ => by
      unfold Cslib.RowCompression.defaultEntry
      by_cases hν : ν = 0
      · simp only [hν, ↓reduceDIte, ↓reduceIte]
        push_cast
        ring
      · simp [hν])
  let def32 := (FixedRecipe.dite (ν = 0)
      (fun _ => c1_32.mul newDefF)
      (fun _ => c0)).congrVal
    (fun val _ =>
      let z' := Cslib.RowCompression.newDefault items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))
      Cslib.RowCompression.defaultEntry z' ν / 32)
    (fun _ => by
      unfold Cslib.RowCompression.defaultEntry
      by_cases hν : ν = 0
      · simp only [hν, ↓reduceDIte, ↓reduceIte]
        push_cast
        ring
      · simp [hν])
  let diff32 := ((c1_16.mul wyNu).pairAvg def16.neg).congrVal
    (fun val _ =>
      let z' := Cslib.RowCompression.newDefault items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ))
      (val (.entry y ν) - Cslib.RowCompression.defaultEntry z' ν) / 32)
    (fun _ => by push_cast; ring)
  let clip32 := rad32.neg.max (diff32.min rad32)
  let upd64 := (clip32.pairAvg def32).congrVal
    (fun val _ =>
      Cslib.RowCompression.update items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ)) y ν / 64)
    (fun {env _} _ => by
      set ρ := streamVal (env .floor)
      set z := streamVal (env .oldDefault)
      set w : ι → Fin 2 → ℝ := fun x μ => streamVal (env (.entry x μ))
      set u := Cslib.RowCompression.threshold items.toFinset n ρ z w
      set z' := Cslib.RowCompression.newDefault items.toFinset n K ρ z w
      change (Max.max (-(Cslib.RowCompression.radius u (w y) / 32))
          (Min.min ((w y ν - Cslib.RowCompression.defaultEntry z' ν) / 32)
            (Cslib.RowCompression.radius u (w y) / 32)) +
        Cslib.RowCompression.defaultEntry z' ν / 32) / 2 = _
      unfold Cslib.RowCompression.update Cslib.RowCompression.updateEntry
      have hpos32 : (0 : ℝ) ≤ 1 / 32 := by norm_num
      have h1 : -(Cslib.RowCompression.radius u (w y) / 32) =
          (1 / 32) * (-Cslib.RowCompression.radius u (w y)) := by ring
      have h2 : (w y ν - Cslib.RowCompression.defaultEntry z' ν) / 32 =
          (1 / 32) * (w y ν - Cslib.RowCompression.defaultEntry z' ν) := by ring
      have h3 : Cslib.RowCompression.radius u (w y) / 32 =
          (1 / 32) * Cslib.RowCompression.radius u (w y) := by ring
      rw [h1, h2, h3, ← mul_min_of_nonneg _ _ hpos32, ← mul_max_of_nonneg _ _ hpos32]
      ring)
  let raw := upd64.shiftClip 6 6 (by exact_mod_cast Nat.le_mul_of_pos_right 6 hd)
  raw.congrVal
    (fun val _ =>
      Cslib.RowCompression.update items.toFinset n K
        (val .floor) (val .oldDefault) (fun x μ => val (.entry x μ)) y ν)
    (fun {env _} hV => by
      set ρ := streamVal (env .floor)
      set z := streamVal (env .oldDefault)
      set w : ι → Fin 2 → ℝ := fun x μ => streamVal (env (.entry x μ))
      set z' := Cslib.RowCompression.newDefault items.toFinset n K ρ z w
      unfold shiftClipVal
      have hmul64 : (2 : ℝ) ^ (6 : ℤ) *
          (Cslib.RowCompression.update items.toFinset n K ρ z w y ν / 64) =
          Cslib.RowCompression.update items.toFinset n K ρ z w y ν := by
        norm_num
        ring
      have hz'_mem := newDefault_mem_unit (s := items.toFinset) (n := n) (K := K)
        hV.floor_norm.2 hV.oldDefault_norm.2
        (fun x hx μ => (hV.entry_norm x (List.mem_toFinset.mp hx) μ).2)
      have hdef_mem : Cslib.RowCompression.defaultEntry z' ν ∈ Set.Icc (-1 : ℝ) 1 := by
        unfold Cslib.RowCompression.defaultEntry
        split_ifs
        · exact ⟨by linarith [hz'_mem.1], hz'_mem.2⟩
        · exact ⟨by norm_num, by norm_num⟩
      have hwy_mem := abs_le.mp (hV.target_norm ν).2
      have hupd_mem := Cslib.RowCompression.update_mem_Icc
        (s := items.toFinset) (n := n) (K := K) (ρ := ρ) (z := z) (w := w) y ν
      have hupd_lo : -1 ≤ Cslib.RowCompression.update items.toFinset n K ρ z w y ν :=
        (le_min hwy_mem.1 hdef_mem.1).trans hupd_mem.1
      have hupd_hi : Cslib.RowCompression.update items.toFinset n K ρ z w y ν ≤ 1 :=
        hupd_mem.2.trans (max_le hwy_mem.2 hdef_mem.2)
      rw [hmul64, min_eq_right hupd_hi, max_eq_right hupd_lo])

/-- Certified primitive recipe over `RowStreamIdx ι` computing coordinate `(y, ν)` of the
compressed row `Cslib.RowCompression.update items.toFinset n K` [OpenAI2026LogSpace, (8.6)]. -/
@[expose] noncomputable def rowCompressionUpdatePrim {ι : Type u} [DecidableEq ι]
    {Struct : Type v} (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ) (y : ι) (ν : Fin 2) :
    UniformStreamRecipe (RowStreamIdx ι) Struct :=
  (rowCompressionUpdateFixed d hd items hNodup κ hLen n K y ν).toRecipe

/-- Compose `rowCompressionNewDefaultPrim` with arbitrary certified child recipes for the floor,
old default, and active support entries. -/
@[expose] noncomputable def rowCompressionNewDefaultRecipe {ι : Type u} [DecidableEq ι]
    {Op : Type u'} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ)
    (floorR oldDefaultR : UniformStreamRecipe Op Struct)
    (entryR : ι → Fin 2 → UniformStreamRecipe Op Struct)
    (cA cB cC cInt : ℕ)
    (hSlackFloor : floorR.slack = d) (hSlackDef : oldDefaultR.slack = d)
    (hSlackEntry : ∀ x ∈ items, ∀ μ, (entryR x μ).slack = d)
    (hAFloor : floorR.coeffA ≤ cA) (hADef : oldDefaultR.coeffA ≤ cA)
    (hAEntry : ∀ x ∈ items, ∀ μ, (entryR x μ).coeffA ≤ cA)
    (hBFloor : floorR.coeffB ≤ cB) (hBDef : oldDefaultR.coeffB ≤ cB)
    (hBEntry : ∀ x ∈ items, ∀ μ, (entryR x μ).coeffB ≤ cB)
    (hCFloor : floorR.coeffC ≤ cC) (hCDef : oldDefaultR.coeffC ≤ cC)
    (hCEntry : ∀ x ∈ items, ∀ μ, (entryR x μ).coeffC ≤ cC)
    (hIntFloor : floorR.intrinsicCoeff ≤ cInt) (hIntDef : oldDefaultR.intrinsicCoeff ≤ cInt)
    (hIntEntry : ∀ x ∈ items, ∀ μ, (entryR x μ).intrinsicCoeff ≤ cInt) :
    UniformStreamRecipe Op Struct :=
  let child : RowStreamIdx ι → UniformStreamRecipe Op Struct
    | .floor => floorR
    | .oldDefault => oldDefaultR
    | .entry x μ => if x ∈ items then entryR x μ else ratRecipe d hd 0 (by norm_num)
  -- Each per-child slack, coefficient and validity fact holds for the floor, old-default and
  -- listed entry recipes by hypothesis, and for the zero filler recipe directly.
  have hchild (P : UniformStreamRecipe Op Struct → Prop) (hF : P floorR) (hD : P oldDefaultR)
      (hE : ∀ x ∈ items, ∀ μ, P (entryR x μ)) (hZ : P (ratRecipe d hd 0 (by norm_num))) :
      ∀ idx, P (child idx) := by
    intro idx
    cases idx with
    | floor => exact hF
    | oldDefault => exact hD
    | entry x μ =>
        dsimp only [child]
        split_ifs with hx
        · exact hE x hx μ
        · exact hZ
  let raw := (rowCompressionNewDefaultPrim (Struct := Struct) d hd items hNodup κ hLen n K).comp
    child cA cB cC (max 8 cInt)
    (hchild (·.slack = d) hSlackFloor hSlackDef hSlackEntry rfl)
    (hchild (·.coeffA ≤ cA) hAFloor hADef hAEntry (Nat.zero_le _))
    (hchild (·.coeffB ≤ cB) hBFloor hBDef hBEntry (Nat.zero_le _))
    (hchild (·.coeffC ≤ cC) hCFloor hCDef hCEntry (Nat.zero_le _))
    (hchild (·.intrinsicCoeff ≤ max 8 cInt) (hIntFloor.trans (le_max_right 8 _))
      (hIntDef.trans (le_max_right 8 _))
      (fun x hx μ => (hIntEntry x hx μ).trans (le_max_right 8 _)) (le_max_left 8 _))
  (raw.weakenValid
    (fun env sEnv =>
      floorR.ValidEnv env sEnv ∧ oldDefaultR.ValidEnv env sEnv ∧
        ∀ x ∈ items, ∀ μ, (entryR x μ).ValidEnv env sEnv)
    (fun {env sEnv} ⟨hFl, hDf, hEn⟩ => by
      have hCh : ∀ idx, (child idx).ValidEnv env sEnv :=
        hchild (·.ValidEnv env sEnv) hFl hDf hEn trivial
      have hNorm : ∀ idx, IsNormSignedStream (fun u => ((child idx).digitProg u).eval env sEnv) :=
        fun idx => ⟨(child idx).emits_signed (hCh idx), by
          rw [(child idx).emits_exact (hCh idx)]
          exact (child idx).abs_targetVal_le_one (hCh idx)⟩
      exact ⟨hCh, ⟨hNorm .floor, hNorm .oldDefault, fun x _ μ => hNorm (.entry x μ)⟩⟩)).congrTarget
    (fun val sEnv =>
      Cslib.RowCompression.newDefault items.toFinset n K
        (floorR.targetVal val sEnv) (oldDefaultR.targetVal val sEnv)
        (fun x μ => (entryR x μ).targetVal val sEnv))
    (fun _ =>
      Cslib.RowCompression.newDefault_congr_on fun x hx μ => by
        have hmem : x ∈ items := List.mem_toFinset.mp hx
        dsimp only [child]
        simp only [hmem, ↓reduceIte])

/-- Compose `rowCompressionUpdatePrim` with arbitrary certified child recipes for the floor, old
default, and row entries. -/
@[expose] noncomputable def rowCompressionUpdateRecipe {ι : Type u} [DecidableEq ι]
    {Op : Type u'} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (items : List ι) (hNodup : items.Nodup)
    (κ : ℕ) (hLen : items.length ≤ 2 ^ (κ * d)) (n K : ℕ) (y : ι) (ν : Fin 2)
    (floorR oldDefaultR : UniformStreamRecipe Op Struct)
    (entryR : ι → Fin 2 → UniformStreamRecipe Op Struct)
    (cA cB cC cInt : ℕ)
    (hSlackFloor : floorR.slack = d) (hSlackDef : oldDefaultR.slack = d)
    (hSlackEntry : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, (entryR x μ).slack = d)
    (hAFloor : floorR.coeffA ≤ cA) (hADef : oldDefaultR.coeffA ≤ cA)
    (hAEntry : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, (entryR x μ).coeffA ≤ cA)
    (hBFloor : floorR.coeffB ≤ cB) (hBDef : oldDefaultR.coeffB ≤ cB)
    (hBEntry : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, (entryR x μ).coeffB ≤ cB)
    (hCFloor : floorR.coeffC ≤ cC) (hCDef : oldDefaultR.coeffC ≤ cC)
    (hCEntry : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, (entryR x μ).coeffC ≤ cC)
    (hIntFloor : floorR.intrinsicCoeff ≤ cInt) (hIntDef : oldDefaultR.intrinsicCoeff ≤ cInt)
    (hIntEntry : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, (entryR x μ).intrinsicCoeff ≤ cInt) :
    UniformStreamRecipe Op Struct :=
  let child : RowStreamIdx ι → UniformStreamRecipe Op Struct
    | .floor => floorR
    | .oldDefault => oldDefaultR
    | .entry x μ => if x = y ∨ x ∈ items then entryR x μ else ratRecipe d hd 0 (by norm_num)
  -- Each per-child slack, coefficient and validity fact holds for the floor, old-default and
  -- updated or listed entry recipes by hypothesis, and for the zero filler recipe directly.
  have hchild (P : UniformStreamRecipe Op Struct → Prop) (hF : P floorR) (hD : P oldDefaultR)
      (hE : ∀ x, (x = y ∨ x ∈ items) → ∀ μ, P (entryR x μ))
      (hZ : P (ratRecipe d hd 0 (by norm_num))) : ∀ idx, P (child idx) := by
    intro idx
    cases idx with
    | floor => exact hF
    | oldDefault => exact hD
    | entry x μ =>
        dsimp only [child]
        split_ifs with hx
        · exact hE x hx μ
        · exact hZ
  let raw := (rowCompressionUpdatePrim (Struct := Struct) d hd items hNodup κ hLen n K y ν).comp
    child cA cB cC (max 8 cInt)
    (hchild (·.slack = d) hSlackFloor hSlackDef hSlackEntry rfl)
    (hchild (·.coeffA ≤ cA) hAFloor hADef hAEntry (Nat.zero_le _))
    (hchild (·.coeffB ≤ cB) hBFloor hBDef hBEntry (Nat.zero_le _))
    (hchild (·.coeffC ≤ cC) hCFloor hCDef hCEntry (Nat.zero_le _))
    (hchild (·.intrinsicCoeff ≤ max 8 cInt) (hIntFloor.trans (le_max_right 8 _))
      (hIntDef.trans (le_max_right 8 _))
      (fun x hx μ => (hIntEntry x hx μ).trans (le_max_right 8 _)) (le_max_left 8 _))
  (raw.weakenValid
    (fun env sEnv =>
      floorR.ValidEnv env sEnv ∧ oldDefaultR.ValidEnv env sEnv ∧
        (∀ μ, (entryR y μ).ValidEnv env sEnv) ∧
        ∀ x ∈ items, ∀ μ, (entryR x μ).ValidEnv env sEnv)
    (fun {env sEnv} ⟨hFl, hDf, hY, hEn⟩ => by
      have hCh : ∀ idx, (child idx).ValidEnv env sEnv :=
        hchild (·.ValidEnv env sEnv) hFl hDf
          (fun x hx μ => hx.elim (fun h => h ▸ hY μ) (fun hmem => hEn x hmem μ)) trivial
      have hNorm : ∀ idx, IsNormSignedStream (fun u => ((child idx).digitProg u).eval env sEnv) :=
        fun idx => ⟨(child idx).emits_signed (hCh idx), by
          rw [(child idx).emits_exact (hCh idx)]
          exact (child idx).abs_targetVal_le_one (hCh idx)⟩
      exact ⟨hCh, ⟨⟨hNorm .floor, hNorm .oldDefault, fun x _ μ => hNorm (.entry x μ)⟩,
        fun μ => hNorm (.entry y μ)⟩⟩)).congrTarget
    (fun val sEnv =>
      Cslib.RowCompression.update items.toFinset n K
        (floorR.targetVal val sEnv) (oldDefaultR.targetVal val sEnv)
        (fun x μ => (entryR x μ).targetVal val sEnv) y ν)
    (fun {env sEnv} _ => by
      have hw_on : ∀ x ∈ items.toFinset, ∀ μ,
          (child (.entry x μ)).targetVal (fun op => streamVal (env op)) sEnv =
            (entryR x μ).targetVal (fun op => streamVal (env op)) sEnv := by
        intro x hx μ
        have hcond : x = y ∨ x ∈ items := Or.inr (List.mem_toFinset.mp hx)
        dsimp only [child]
        simp only [hcond, ↓reduceIte]
      have hwy : ∀ μ,
          (child (.entry y μ)).targetVal (fun op => streamVal (env op)) sEnv =
            (entryR y μ).targetVal (fun op => streamVal (env op)) sEnv := by
        intro μ
        dsimp only [child]
        simp only [true_or, ↓reduceIte]
      change Cslib.RowCompression.update items.toFinset n K _ _
          (fun x μ => (child (.entry x μ)).targetVal (fun op => streamVal (env op)) sEnv) y ν = _
      unfold Cslib.RowCompression.update
      dsimp only [child]
      rw [Cslib.RowCompression.threshold_congr_on hw_on,
        Cslib.RowCompression.newDefault_congr_on hw_on]
      have hfun : (fun μ => (child (.entry y μ)).targetVal (fun op => streamVal (env op)) sEnv) =
          fun μ => (entryR y μ).targetVal (fun op => streamVal (env op)) sEnv := by
        ext μ
        exact hwy μ
      rw [hfun])

end RowCompressionRecipes

end Cslib.StreamArithmetic
