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
# Integrals of products over a subset of the coordinates

Under a product of probability measures, a product `∏ i ∈ S, f i (x i)` over a subset `S` of the
coordinates is integrable when each factor is (`MeasureTheory.Integrable.finset_prod_pi`), and its
integral is the product of the integrals of the factors
(`MeasureTheory.integral_finset_prod_pi_eq_prod`). These are the `Finset` versions of Mathlib's
`Integrable.fintype_prod_dep` and `integral_fintype_prod_eq_prod`: the coordinates outside `S`
contribute factors `1`.

## Main results

* `MeasureTheory.Integrable.finset_prod_pi`: integrability of a product over a subset.
* `MeasureTheory.integral_finset_prod_pi_eq_prod`: Fubini's theorem for a product over a subset.
-/

public section

namespace MeasureTheory

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
