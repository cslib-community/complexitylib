/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Function/L2Space.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Inner products of `L²` classes of functions

The inner product in `L²(μ)` of the classes of two square-integrable functions `f` and `g` is
`∫ conj (f a) * g a dμ` (`MeasureTheory.L2.inner_toLp_toLp`). Mathlib states this only for
continuous and bounded continuous functions (`ContinuousMap.inner_toLp`,
`BoundedContinuousFunction.inner_toLp`).

Consequently a family `v k` of real `L²(μ)` functions spans a dense subspace as soon as every
`f ∈ L²(μ)` with `∫ f (v k) dμ = 0` for all `k` vanishes almost everywhere
(`MeasureTheory.L2.topologicalClosure_span_toLp_eq_top`).

## Main results

* `MeasureTheory.L2.inner_toLp_toLp`: the inner product of `hf.toLp f` and `hg.toLp g`.
* `MeasureTheory.L2.topologicalClosure_span_toLp_eq_top`: density of the span of a family whose
  orthogonal complement is trivial.
-/

public section

open scoped InnerProductSpace

namespace MeasureTheory.L2

variable {α 𝕜 : Type*} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α}

/-- The inner product of the `L²` classes of `f` and `g` is `∫ conj (f a) * g a dμ`. -/
theorem inner_toLp_toLp {f g : α → 𝕜} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ⟪hf.toLp f, hg.toLp g⟫_𝕜 = ∫ a, (starRingEnd 𝕜) (f a) * g a ∂μ := by
  rw [inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z hfz hgz
  rw [hfz, hgz, RCLike.inner_apply, mul_comm]

/-- A family `v k` of real `L²(μ)` functions spans a dense subspace of `L²(μ)` if every
`f ∈ L²(μ)` orthogonal to all of them, `∫ f (v k) dμ = 0`, vanishes almost everywhere. -/
theorem topologicalClosure_span_toLp_eq_top {κ : Type*} {v : κ → α → ℝ}
    (hv : ∀ k, MemLp (v k) 2 μ)
    (h : ∀ f : α → ℝ, MemLp f 2 μ → (∀ k, ∫ a, f a * v k a ∂μ = 0) → f =ᵐ[μ] 0) :
    (Submodule.span ℝ (Set.range fun k => (hv k).toLp (v k))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro F hF
  rw [Submodule.mem_orthogonal] at hF
  refine Lp.eq_zero_iff_ae_eq_zero.2 (h _ (Lp.memLp F) fun k => ?_)
  refine Eq.trans ?_ (hF _ (Submodule.subset_span ⟨k, rfl⟩))
  rw [← Lp.toLp_coeFn F (Lp.memLp F), inner_toLp_toLp, Lp.toLp_coeFn]
  simp only [conj_trivial, mul_comm]

end MeasureTheory.L2
