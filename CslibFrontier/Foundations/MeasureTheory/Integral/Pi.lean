/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Integral/Pi.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrals of products of functions of the coordinates

The lower Lebesgue integral of a product `∏ i, f i (x i)` of measurable functions of the
coordinates against a product of σ-finite measures is the product of the integrals
(`MeasureTheory.lintegral_fintype_prod_eq_prod`, Tonelli's theorem), the `ℝ≥0∞` version of
Mathlib's `integral_fintype_prod_eq_prod`.

Under a product of probability measures, a product `∏ i ∈ S, f i (x i)` over a subset `S` of the
coordinates is integrable when each factor is (`MeasureTheory.Integrable.finset_prod_pi`), and its
integral is the product of the integrals of the factors
(`MeasureTheory.integral_finset_prod_pi_eq_prod`). These are the `Finset` versions of Mathlib's
`Integrable.fintype_prod_dep` and `integral_fintype_prod_eq_prod`: the coordinates outside `S`
contribute factors `1`.

## Main results

* `MeasureTheory.lintegral_fin_nat_prod_eq_prod`, `MeasureTheory.lintegral_fintype_prod_eq_prod`:
  Tonelli's theorem for a product of functions of the coordinates.
* `MeasureTheory.Integrable.finset_prod_pi`: integrability of a product over a subset.
* `MeasureTheory.integral_finset_prod_pi_eq_prod`: Fubini's theorem for a product over a subset.
-/

public section

namespace MeasureTheory

open scoped ENNReal

section Lintegral

-- As in Mathlib's `integral_fin_nat_prod_eq_prod`: after `simp_rw`, the `MeasurableSpace`
-- instance on `(j : Fin n) → E (Fin.succAbove 0 j)` must unify with the one on `E j.succ`.
set_option backward.isDefEq.respectTransparency false in
/-- **Tonelli's theorem** for a product of functions of the coordinates, in `n` variables for a
natural number `n`: the `ℝ≥0∞` version of `integral_fin_nat_prod_eq_prod`, whose proof this
ports to lower Lebesgue integrals. -/
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : Fin n) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ
        = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi fun i => μ i.succ)) := by
          rw [← (measurePreserving_piFinSuccAbove μ 0).symm.lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
          rw [← ih fun i : Fin n => hf i.succ]
          exact lintegral_prod_mul (hf 0).aemeasurable
            (Finset.measurable_prod _ fun (i : Fin n) _ =>
              (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂μ i := by rw [Fin.prod_univ_succ]

/-- **Tonelli's theorem** for a product of functions of the coordinates: for σ-finite measures and
measurable `f i`, `∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i`. The `ℝ≥0∞` version
of `integral_fintype_prod_eq_prod`. -/
theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    {f : (i : ι) → E i → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_nat_prod_eq_prod fun i => hf (e i)

end Lintegral

variable {ι : Type*} [Fintype ι] {E : ι → Type*} {mE : ∀ i, MeasurableSpace (E i)}
  {μ : (i : ι) → Measure (E i)} [∀ i, IsProbabilityMeasure (μ i)]

/-- A product `∏ i ∈ S, f i (x i)` of integrable factors over a subset `S` of the coordinates is
integrable under a product of probability measures; the `Finset` version of
`Integrable.fintype_prod_dep`. -/
theorem Integrable.finset_prod_pi {𝕜 : Type*} [RCLike 𝕜] {f : (i : ι) → E i → 𝕜}
    (S : Finset ι) (hf : ∀ i ∈ S, Integrable (f i) (μ i)) :
    Integrable (fun x => ∏ i ∈ S, f i (x i)) (Measure.pi μ) := by
  classical
  simp only [← Fintype.prod_ite_mem S]
  exact Integrable.fintype_prod_dep (f := fun i t => if i ∈ S then f i t else 1)
    fun i => by split_ifs with h; exacts [hf i h, integrable_const _]

/-- **Fubini's theorem** for a product `∏ i ∈ S, f i (x i)` over a subset `S` of the coordinates,
under a product of probability measures; the `Finset` version of
`integral_fintype_prod_eq_prod`. -/
theorem integral_finset_prod_pi_eq_prod {𝕜 : Type*} [RCLike 𝕜] (f : (i : ι) → E i → 𝕜)
    (S : Finset ι) :
    ∫ x, ∏ i ∈ S, f i (x i) ∂Measure.pi μ = ∏ i ∈ S, ∫ t, f i t ∂μ i := by
  classical
  simp only [← Fintype.prod_ite_mem S]
  rw [integral_fintype_prod_eq_prod (f := fun i t => if i ∈ S then f i t else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

end MeasureTheory
