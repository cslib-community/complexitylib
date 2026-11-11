/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQuery
import CslibFrontier.Foundations.Quantum.Measurement.Overlap
import CslibFrontier.Foundations.Quantum.Measurement.ReadoutOverlap

/-!
# Ambainis's quantum adversary method for non-Boolean input alphabets

This module proves [Ambainis2002], Theorem 6 (Section 6.1 of `arXiv:quant-ph/0002066v1`) in the
quantum value-query model (`Cslib.Quantum.ValueState`, `Cslib.Quantum.valueOracle`,
`Cslib.Quantum.runValue`) over an arbitrary finite query index type `ι`, arbitrary input alphabet
`α`, finite value register `V`, and finite workspace `W`, for **any** unitary oracle family
`step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V)`.

Let `querySlice i ψ : EuclideanSpace ℂ (V × W)` be the amplitudes of `ψ : ValueState ι V W` on query
index `i : ι`. Because `valueOracle step x` applies the linear isometry equivalence `step (x i)` on
each `(i, w)` fiber:

* `∑ i : ι, ‖querySlice i ψ‖ ^ 2 = ‖ψ‖ ^ 2` (`Cslib.Quantum.sum_sq_norm_querySlice`);
* `‖querySlice i (valueOracle step x ψ)‖ = ‖querySlice i ψ‖`
  (`Cslib.Quantum.norm_querySlice_valueOracle`);
* when `x i = y i`, `inner ℂ (querySlice i (valueOracle step x ψ))
    (querySlice i (valueOracle step y φ)) = inner ℂ (querySlice i ψ) (querySlice i φ)`
  (`Cslib.Quantum.inner_querySlice_valueOracle_of_eq`);
* therefore one value query lowers `‖inner ℂ ψ φ‖` by at most
  `2 ∑_{i : x i ≠ y i} ‖querySlice i ψ‖ * ‖querySlice i φ‖`
  (`Cslib.Quantum.norm_inner_valueOracle_valueOracle_ge`), with the same constant `2` as the binary
  phase oracle (`Cslib.Quantum.norm_inner_phaseOracle_phaseOracle_ge`), without paying any two-value
  diagonalization overhead.

Bounding each step's drop in `valueWeightedProgress` gives `(1 - δ) √(m m') ≤ 2 T √L`
(`Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value`). Combining with multi-outcome Lemma 1
(`Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_readout_ne` and
`Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_measureOut_ne`) yields the multi-outcome bounds
`Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value` and
`Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value_measureOut`.

## Main definitions

* `Cslib.Quantum.querySlice`: slice of a `ValueState ι V W` at query index `i : ι`.
* `Cslib.Quantum.valueWeightedProgress`: weighted sum of state overlaps of `runValue` over `R`.

## Main results

* `Cslib.Quantum.norm_inner_valueOracle_valueOracle_ge`: one-step overlap loss bound for
  `valueOracle`.
* `Cslib.Quantum.one_sub_mul_sum_le_of_sq_le_value`: weighted adversary inequality for `runValue`.
* `Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value`: [Ambainis2002], Theorem 6 (overlap
  form) for non-Boolean value queries.
* `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value` and
  `Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value_measureOut`:
  [Ambainis2002], Theorem 6 for multi-outcome classical readouts.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002], Section 6.1, Theorem 6
  (`arXiv:quant-ph/0002066v1`).
-/

public section

namespace Cslib.Quantum

open Finset

section QuerySlice

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]

/-- The amplitudes of a value-query state `ψ : ValueState ι V W` on query index `i : ι`. -/
@[expose] def querySlice (i : ι) (ψ : ValueState ι V W) : EuclideanSpace ℂ (V × W) :=
  WithLp.toLp 2 fun (v, w) => ψ.ofLp (i, v, w)

omit [Fintype ι] [Fintype V] [Fintype W] in
/-- Coordinate evaluation of `querySlice i ψ`. -/
@[simp] theorem querySlice_apply (i : ι) (ψ : ValueState ι V W) (v : V) (w : W) :
    (querySlice i ψ).ofLp (v, w) = ψ.ofLp (i, v, w) :=
  rfl

private def fiberSlice (i : ι) (w : W) (ψ : ValueState ι V W) : EuclideanSpace ℂ V :=
  WithLp.toLp 2 fun v => ψ.ofLp (i, v, w)

private theorem fiberSlice_valueOracle
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : ValueState ι V W) (i : ι) (w : W) :
    fiberSlice i w (valueOracle step x ψ) = step (x i) (fiberSlice i w ψ) := by
  ext v
  simp [fiberSlice, valueOracle_apply]

omit [Fintype ι] in
private theorem inner_querySlice_eq_sum_fiberSlice (i : ι) (ψ φ : ValueState ι V W) :
    inner ℂ (querySlice i ψ) (querySlice i φ) =
      ∑ w : W, inner ℂ (fiberSlice i w ψ) (fiberSlice i w φ) := by
  simp only [PiLp.inner_apply]
  rw [Fintype.sum_prod_type, sum_comm]
  rfl

omit [Fintype ι] in
private theorem norm_querySlice_sq_eq_sum_fiberSlice (i : ι) (ψ : ValueState ι V W) :
    ‖querySlice i ψ‖ ^ 2 = ∑ w : W, ‖fiberSlice i w ψ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq]
  rw [Fintype.sum_prod_type, sum_comm]
  rfl

/-- Decomposition of the inner product on `ValueState ι V W` across query indices `i : ι`. -/
theorem inner_eq_sum_inner_querySlice (ψ φ : ValueState ι V W) :
    inner ℂ ψ φ = ∑ i : ι, inner ℂ (querySlice i ψ) (querySlice i φ) := by
  simp only [PiLp.inner_apply]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => sum_congr rfl fun ⟨v, w⟩ _ => rfl

/-- Parseval identity across query indices: `∑_i ‖querySlice i ψ‖² = ‖ψ‖²`. -/
theorem sum_sq_norm_querySlice (ψ : ValueState ι V W) :
    ∑ i : ι, ‖querySlice i ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  exact sum_congr rfl fun ⟨v, w⟩ _ => rfl

/-- On each query index `i`, `valueOracle step x` acts as a linear isometry on `querySlice i`. -/
@[simp] theorem norm_querySlice_valueOracle
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x : ι → α) (ψ : ValueState ι V W) (i : ι) :
    ‖querySlice i (valueOracle step x ψ)‖ = ‖querySlice i ψ‖ := by
  have hsq : ‖querySlice i (valueOracle step x ψ)‖ ^ 2 = ‖querySlice i ψ‖ ^ 2 := by
    rw [norm_querySlice_sq_eq_sum_fiberSlice, norm_querySlice_sq_eq_sum_fiberSlice]
    refine sum_congr rfl fun w _ => ?_
    rw [fiberSlice_valueOracle, LinearIsometryEquiv.norm_map]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- When two inputs `x` and `y` agree at `i`, `valueOracle` preserves the `i`-slice overlap. -/
theorem inner_querySlice_valueOracle_of_eq
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    {x y : ι → α} {i : ι} (hxy : x i = y i) (ψ φ : ValueState ι V W) :
    inner ℂ (querySlice i (valueOracle step x ψ)) (querySlice i (valueOracle step y φ)) =
      inner ℂ (querySlice i ψ) (querySlice i φ) := by
  rw [inner_querySlice_eq_sum_fiberSlice, inner_querySlice_eq_sum_fiberSlice]
  refine sum_congr rfl fun w _ => ?_
  rw [fiberSlice_valueOracle, fiberSlice_valueOracle, hxy, LinearIsometryEquiv.inner_map_map]

/-- **Per-query overlap loss bound for `valueOracle`**: one value query lowers `‖inner ℂ ψ φ‖` by at
most `2 ∑_{i : x i ≠ y i} ‖querySlice i ψ‖ * ‖querySlice i φ‖`. -/
theorem norm_inner_valueOracle_valueOracle_ge [DecidableEq α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (x y : ι → α) (ψ φ : ValueState ι V W) :
    ‖inner ℂ ψ φ‖ - 2 * ∑ i with x i ≠ y i, ‖querySlice i ψ‖ * ‖querySlice i φ‖ ≤
      ‖inner ℂ (valueOracle step x ψ) (valueOracle step y φ)‖ := by
  have hdiff : inner ℂ ψ φ - inner ℂ (valueOracle step x ψ) (valueOracle step y φ) =
      ∑ i with x i ≠ y i, (inner ℂ (querySlice i ψ) (querySlice i φ) -
        inner ℂ (querySlice i (valueOracle step x ψ)) (querySlice i (valueOracle step y φ))) := by
    rw [inner_eq_sum_inner_querySlice ψ φ,
      inner_eq_sum_inner_querySlice (valueOracle step x ψ) (valueOracle step y φ),
      ← sum_sub_distrib]
    symm
    refine sum_subset (subset_univ _) fun i _ hi => ?_
    simp only [mem_filter, mem_univ, true_and, not_not] at hi
    rw [inner_querySlice_valueOracle_of_eq step hi, sub_self]
  have hnorm : ‖inner ℂ ψ φ - inner ℂ (valueOracle step x ψ) (valueOracle step y φ)‖ ≤
      2 * ∑ i with x i ≠ y i, ‖querySlice i ψ‖ * ‖querySlice i φ‖ := by
    rw [hdiff, mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
    have h₁ : ‖inner ℂ (querySlice i ψ) (querySlice i φ)‖ ≤
        ‖querySlice i ψ‖ * ‖querySlice i φ‖ := norm_inner_le_norm _ _
    have h₂ : ‖inner ℂ (querySlice i (valueOracle step x ψ))
        (querySlice i (valueOracle step y φ))‖ ≤
        ‖querySlice i ψ‖ * ‖querySlice i φ‖ := by
      simpa only [norm_querySlice_valueOracle] using
        norm_inner_le_norm (querySlice i (valueOracle step x ψ))
          (querySlice i (valueOracle step y φ))
    have htri := norm_sub_le (inner ℂ (querySlice i ψ) (querySlice i φ))
      (inner ℂ (querySlice i (valueOracle step x ψ)) (querySlice i (valueOracle step y φ)))
    linarith
  have hsub := norm_sub_norm_le (inner ℂ ψ φ)
    (inner ℂ (valueOracle step x ψ) (valueOracle step y φ))
  linarith

end QuerySlice

section AdversaryBounds

variable {ι V W α : Type*} [Fintype ι] [Fintype V] [Fintype W]

/-- Weighted progress measure of a value-query algorithm over an input relation `R` after `t`
queries. -/
@[expose] noncomputable def valueWeightedProgress
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    (ψ₀ : ValueState ι V W)
    (R : Finset ((ι → α) × (ι → α))) (γ : (ι → α) × (ι → α) → ℝ) (t : ℕ) : ℝ :=
  ∑ p ∈ R, γ p * ‖inner ℂ (runValue step U ψ₀ p.1 t) (runValue step U ψ₀ p.2 t)‖

/-- Before any query, all states agree, so `valueWeightedProgress` equals `∑ p ∈ R, γ p`. -/
theorem valueWeightedProgress_zero
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset ((ι → α) × (ι → α))) (γ : (ι → α) × (ι → α) → ℝ) :
    valueWeightedProgress step U ψ₀ R γ 0 = ∑ p ∈ R, γ p := by
  have h : ‖inner ℂ (U 0 ψ₀) (U 0 ψ₀)‖ = 1 := by
    rw [LinearIsometry.inner_map_map, inner_self_eq_norm_sq_to_K, hψ₀]
    simp
  simp only [valueWeightedProgress, runValue, h, mul_one]

private theorem sum_endpoint_querySlice_sq_le [DecidableEq α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1)
    (R : Finset ((ι → α) × (ι → α))) (k : (ι → α) × (ι → α) → (ι → α))
    (w : (ι → α) × (ι → α) → ι → ℝ) (α_b : (ι → α) → ℝ)
    (hα : ∀ x ∈ R.image k, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i ≤ α_b x)
    (t : ℕ) :
    ∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i,
        w p i * ‖querySlice i (runValue step U ψ₀ (k p) t)‖ ^ 2 ≤
      ∑ x ∈ R.image k, α_b x := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := R) (g := k) (t := R.image k)
    fun _ h => mem_image_of_mem k h]
  refine sum_le_sum fun x hx => ?_
  have hswap :
      ∑ p ∈ R with k p = x, ∑ i with p.1 i ≠ p.2 i,
          w p i * ‖querySlice i (runValue step U ψ₀ (k p) t)‖ ^ 2 =
        ∑ i, (∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i) *
          ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2 := by
    calc
      ∑ p ∈ R with k p = x, ∑ i with p.1 i ≠ p.2 i,
          w p i * ‖querySlice i (runValue step U ψ₀ (k p) t)‖ ^ 2
          = ∑ p ∈ R, ∑ i,
              if p.1 i ≠ p.2 i ∧ k p = x then
                w p i * ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2
              else 0 := by
              simp only [sum_filter]
              refine sum_congr rfl fun p _ => ?_
              by_cases hkx : k p = x <;> simp [hkx]
      _ = ∑ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x,
            w p i * ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2 := by
            rw [sum_comm]
            simp only [sum_filter]
      _ = ∑ i, (∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i) *
            ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2 := by
            simp only [sum_mul]
  rw [hswap]
  calc
    ∑ i, (∑ p ∈ R with p.1 i ≠ p.2 i ∧ k p = x, w p i) *
        ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2
        ≤ ∑ i, α_b x * ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2 :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hα x hx i) (sq_nonneg _)
    _ = α_b x * ∑ i, ‖querySlice i (runValue step U ψ₀ x t)‖ ^ 2 := (mul_sum ..).symm
    _ = α_b x := by
          rw [sum_sq_norm_querySlice, norm_runValue, hψ₀, one_pow, mul_one]

/-- **Weighted quantum adversary inequality for value-query algorithms**: if after `T` value queries
the states on every pair in `R` have overlap at most `δ`, and nonnegative step weights `a, b`
satisfy `γ(p)² ≤ a(p, i) b(p, i)` whenever `p.1 i ≠ p.2 i` with coordinatewise fiber budgets
`α_b` and `β_b`, then
`(1 - δ) ∑_{p ∈ R} γ p ≤ T (∑_{x ∈ fst(R)} α_b x + ∑_{y ∈ snd(R)} β_b y)`. -/
theorem one_sub_mul_sum_le_of_sq_le_value [DecidableEq α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (R : Finset ((ι → α) × (ι → α))) (γ : (ι → α) × (ι → α) → ℝ)
    {δ : ℝ}
    (hδ : ∀ p ∈ R, ‖inner ℂ (runValue step U ψ₀ p.1 T) (runValue step U ψ₀ p.2 T)‖ ≤ δ)
    (a b : (ι → α) × (ι → α) → ι → ℝ) (α_b β_b : (ι → α) → ℝ)
    (hγ : ∀ p ∈ R, 0 ≤ γ p)
    (ha : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ a p i)
    (hb : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → 0 ≤ b p i)
    (hγsq : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i → γ p ^ 2 ≤ a p i * b p i)
    (hα : ∀ x ∈ R.image Prod.fst, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.1 = x, a p i ≤ α_b x)
    (hβ : ∀ y ∈ R.image Prod.snd, ∀ i, ∑ p ∈ R with p.1 i ≠ p.2 i ∧ p.2 = y, b p i ≤ β_b y) :
    (1 - δ) * ∑ p ∈ R, γ p ≤
      T * (∑ x ∈ R.image Prod.fst, α_b x + ∑ y ∈ R.image Prod.snd, β_b y) := by
  have hstep : ∀ t : ℕ,
      valueWeightedProgress step U ψ₀ R γ t - valueWeightedProgress step U ψ₀ R γ (t + 1) ≤
        ∑ x ∈ R.image Prod.fst, α_b x + ∑ y ∈ R.image Prod.snd, β_b y := fun t => by
    have hp : valueWeightedProgress step U ψ₀ R γ t -
          valueWeightedProgress step U ψ₀ R γ (t + 1) ≤
        (∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i,
            a p i * ‖querySlice i (runValue step U ψ₀ p.1 t)‖ ^ 2) +
          ∑ p ∈ R, ∑ i with p.1 i ≠ p.2 i,
            b p i * ‖querySlice i (runValue step U ψ₀ p.2 t)‖ ^ 2 := by
      simp only [valueWeightedProgress, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_le_sum fun p hp => ?_
      have horacle := norm_inner_valueOracle_valueOracle_ge step p.1 p.2
        (runValue step U ψ₀ p.1 t) (runValue step U ψ₀ p.2 t)
      change γ p * ‖inner ℂ (runValue step U ψ₀ p.1 t) (runValue step U ψ₀ p.2 t)‖ -
          γ p * ‖inner ℂ (U (t + 1) (valueOracle step p.1 (runValue step U ψ₀ p.1 t)))
            (U (t + 1) (valueOracle step p.2 (runValue step U ψ₀ p.2 t)))‖ ≤ _
      rw [LinearIsometry.inner_map_map]
      have hmul := mul_le_mul_of_nonneg_left horacle (hγ p hp)
      rw [mul_sub, ← mul_assoc, mul_comm (γ p) 2, mul_sum] at hmul
      have h1 : γ p * ‖inner ℂ (runValue step U ψ₀ p.1 t) (runValue step U ψ₀ p.2 t)‖ -
            γ p * ‖inner ℂ (valueOracle step p.1 (runValue step U ψ₀ p.1 t))
              (valueOracle step p.2 (runValue step U ψ₀ p.2 t))‖ ≤
          ∑ i with p.1 i ≠ p.2 i,
            2 * γ p * (‖querySlice i (runValue step U ψ₀ p.1 t)‖ *
              ‖querySlice i (runValue step U ψ₀ p.2 t)‖) := by
        linarith
      refine h1.trans (sum_le_sum fun i hi => ?_)
      have hi' := (mem_filter.1 hi).2
      exact two_mul_mul_le_of_sq_le_mul (norm_nonneg _) (norm_nonneg _)
        (ha p hp i hi') (hb p hp i hi') (hγsq p hp i hi')
    have hX := sum_endpoint_querySlice_sq_le step U hψ₀ R Prod.fst a α_b hα t
    have hY := sum_endpoint_querySlice_sq_le step U hψ₀ R Prod.snd b β_b hβ t
    linarith
  have htel (t : ℕ) : valueWeightedProgress step U ψ₀ R γ 0 -
      valueWeightedProgress step U ψ₀ R γ t ≤
        t * (∑ x ∈ R.image Prod.fst, α_b x + ∑ y ∈ R.image Prod.snd, β_b y) := by
    induction t with
    | zero => simp
    | succ t ih =>
      have hs := hstep t
      push_cast
      linarith
  have htelT := htel T
  have hend : valueWeightedProgress step U ψ₀ R γ T ≤ δ * ∑ p ∈ R, γ p := by
    rw [valueWeightedProgress, mul_sum]
    refine sum_le_sum fun p hp => ?_
    rw [mul_comm δ]
    exact mul_le_mul_of_nonneg_left (hδ p hp) (hγ p hp)
  rw [valueWeightedProgress_zero step U hψ₀ R γ] at htelT
  linarith

/-- **Ambainis's adversary bound for non-Boolean input alphabets** ([Ambainis2002], Section 6.1,
Theorem 6, overlap form): let `R` be a nonempty set of pairs of inputs `x, y : ι → α` on which a
`T`-query value-query algorithm `(step, U, ψ₀)` with `‖ψ₀‖ = 1` ends in states with overlap at most
`δ`. If every first input of `R` lies in at least `m` pairs of `R` and every second input in at
least `m'`, and `l_{x,i} l_{y,i} ≤ L` whenever `(x, y) ∈ R` and `x i ≠ y i`, then
`(1 - δ) √(m m') ≤ 2 T √L`. -/
theorem one_sub_mul_sqrt_le_two_mul_mul_sqrt_value [DecidableEq α]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    {R : Finset ((ι → α) × (ι → α))} (hR : R.Nonempty) {δ : ℝ}
    (hδ : ∀ p ∈ R, ‖inner ℂ (runValue step U ψ₀ p.1 T) (runValue step U ψ₀ p.2 T)‖ ≤ δ)
    {m m' L : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1})
    (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    (1 - δ) * √(m * m') ≤ 2 * T * √L := by
  rcases le_or_gt 1 δ with h1 | h1
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg _)).trans (by positivity)
  set X := R.image Prod.fst
  set Y := R.image Prod.snd
  have hX : (0 : ℝ) < #X := Nat.cast_pos.2 (card_pos.2 (hR.image _))
  have hY : (0 : ℝ) < #Y := Nat.cast_pos.2 (card_pos.2 (hR.image _))
  have hRX : (m : ℝ) * #X ≤ #R := by
    have : m * #X ≤ #R := by
      rw [card_eq_sum_card_image Prod.fst R, mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      exact hm p hp
    exact_mod_cast this
  have hRY : (m' : ℝ) * #Y ≤ #R := by
    have : m' * #Y ≤ #R := by
      rw [card_eq_sum_card_image Prod.snd R, mul_comm, ← smul_eq_mul, ← sum_const]
      refine sum_le_sum fun y hy => ?_
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
      exact hm' p hp
    exact_mod_cast this
  set wXY : ℝ := (#X : ℝ) * (#Y : ℝ)
  have hwXY : 0 < wXY := mul_pos hX hY
  have htel := one_sub_mul_sum_le_of_sq_le_value step U hψ₀ T R (fun _ => √wXY) hδ
    (fun p i => (#Y : ℝ) * √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1})
    (fun p i => (#X : ℝ) * √L / #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2})
    (fun _ => (#Y : ℝ) * √L) (fun _ => (#X : ℝ) * √L)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun _ _ _ _ => by positivity) (fun _ _ _ _ => by positivity)
    (fun p hp i hi => by
      have hl₁ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} :=
        Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
      have hl₂ : (0 : ℝ) < #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} :=
        Nat.cast_pos.2 (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hi, rfl⟩⟩)
      have hll : (#{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} : ℝ) *
          #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L := by exact_mod_cast hL p hp i hi
      rw [Real.sq_sqrt hwXY.le, div_mul_div_comm, le_div_iff₀ (mul_pos hl₁ hl₂)]
      calc
        wXY * ((#{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} : ℝ) *
            #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2})
            ≤ wXY * L := mul_le_mul_of_nonneg_left hll hwXY.le
        _ = wXY * (√L * √L) := by rw [Real.mul_self_sqrt (Nat.cast_nonneg L)]
        _ = (#Y : ℝ) * √L * ((#X : ℝ) * √L) := by dsimp only [wXY]; ring)
    (fun z _ i => by
      let S := R.filter fun p => p.1 i ≠ p.2 i ∧ p.1 = z
      rw [sum_congr rfl (g := fun _ => (#Y : ℝ) * √L / (#S : ℝ)) fun p hp => by
        simp only [S, (mem_filter.1 hp).2.2], sum_const, nsmul_eq_mul]
      by_cases h0 : #S = 0
      · rw [h0, Nat.cast_zero, zero_mul]
        exact mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · exact (mul_div_cancel₀ _ (by exact_mod_cast h0)).le)
    (fun z _ i => by
      let S := R.filter fun p => p.1 i ≠ p.2 i ∧ p.2 = z
      rw [sum_congr rfl (g := fun _ => (#X : ℝ) * √L / (#S : ℝ)) fun p hp => by
        simp only [S, (mem_filter.1 hp).2.2], sum_const, nsmul_eq_mul]
      by_cases h0 : #S = 0
      · rw [h0, Nat.cast_zero, zero_mul]
        exact mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      · exact (mul_div_cancel₀ _ (by exact_mod_cast h0)).le)
  simp only [sum_const, nsmul_eq_mul] at htel
  have hR' : √(m * m') * √wXY ≤ #R := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    dsimp only [wXY]
    nlinarith [mul_le_mul hRX hRY (by positivity) (by positivity)]
  refine le_of_mul_le_mul_right ?_ hwXY
  calc
    (1 - δ) * √(m * m') * wXY
        = (1 - δ) * √(m * m') * (√wXY * √wXY) := by rw [Real.mul_self_sqrt hwXY.le]
    _ = (1 - δ) * (√(m * m') * √wXY) * √wXY := by ring
    _ ≤ (1 - δ) * #R * √wXY :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR' (by linarith))
            (Real.sqrt_nonneg _)
    _ = (1 - δ) * ((#R : ℝ) * √wXY) := by ring
    _ ≤ T * ((#X : ℝ) * ((#Y : ℝ) * √L) + (#Y : ℝ) * ((#X : ℝ) * √L)) := htel
    _ = 2 * T * √L * wXY := by dsimp only [wXY]; ring

/-- **Ambainis's adversary bound for non-Boolean inputs and multi-outcome outputs** ([Ambainis2002],
Section 6.1, Theorem 6): let `f : (ι → α) → β` be a target function with `f p.1 ≠ f p.2` for all
`p ∈ R`, and suppose a `T`-query value-query algorithm `(step, U, ψ₀)` with classical readout
`out : ι × V × W → β` outputs `f x` with probability at least `1 - ε` (`2 * ε ≤ 1`) on every first
and second input of `R`. Then `(1 - 2√(ε(1-ε))) √(m m') ≤ 2 T √L`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value [DecidableEq α]
    {β : Type*} [DecidableEq β]
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → β) (f : (ι → α) → β)
    {R : Finset ((ι → α) × (ι → α))} (hR : R.Nonempty)
    (hne : ∀ p ∈ R, f p.1 ≠ f p.2) {ε : ℝ}
    (h₁ : ∀ p ∈ R, 1 - ε ≤ measureProb (runValue step U ψ₀ p.1 T) {q | out q = f p.1})
    (h₂ : ∀ p ∈ R, 1 - ε ≤ measureProb (runValue step U ψ₀ p.2 T) {q | out q = f p.2})
    (hε : 2 * ε ≤ 1) {m m' L : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1})
    (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T * √L :=
  one_sub_mul_sqrt_le_two_mul_mul_sqrt_value step U hψ₀ T hR
    (fun p hp => norm_inner_le_two_mul_sqrt_of_readout_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out (hne p hp) (h₁ p hp) (h₂ p hp) hε)
    hm hm' hL

/-- `PMF` (`measureOut`) form of `one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value`, not
requiring `[DecidableEq β]`. -/
theorem one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value_measureOut [DecidableEq α]
    {β : Type*}
    (step : α → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (U : ℕ → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W)
    {ψ₀ : ValueState ι V W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (out : ι × V × W → β) (f : (ι → α) → β)
    {R : Finset ((ι → α) × (ι → α))} (hR : R.Nonempty)
    (hne : ∀ p ∈ R, f p.1 ≠ f p.2) {ε : ℝ}
    (h₁ : ∀ p ∈ R, ENNReal.ofReal (1 - ε) ≤
      measureOut (runValue step U ψ₀ p.1 T) (by rw [norm_runValue, hψ₀]) out (f p.1))
    (h₂ : ∀ p ∈ R, ENNReal.ofReal (1 - ε) ≤
      measureOut (runValue step U ψ₀ p.2 T) (by rw [norm_runValue, hψ₀]) out (f p.2))
    (hε : 2 * ε ≤ 1) {m m' L : ℕ}
    (hm : ∀ p ∈ R, m ≤ #{q ∈ R | q.1 = p.1})
    (hm' : ∀ p ∈ R, m' ≤ #{q ∈ R | q.2 = p.2})
    (hL : ∀ p ∈ R, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ R | q.1 i ≠ q.2 i ∧ q.1 = p.1} * #{q ∈ R | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ L) :
    (1 - 2 * √(ε * (1 - ε))) * √(m * m') ≤ 2 * T * √L :=
  one_sub_mul_sqrt_le_two_mul_mul_sqrt_value step U hψ₀ T hR
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureOut_ne
      (by rw [norm_runValue, hψ₀]) (by rw [norm_runValue, hψ₀])
      out (hne p hp) (h₁ p hp) (h₂ p hp) hε)
    hm hm' hL

end AdversaryBounds

end Cslib.Quantum
