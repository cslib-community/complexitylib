/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Uniform
public import Complexity.Probability.PMF.Uniform
public import Mathlib.Data.Fintype.Pi

/-!
# Uniform random linear combinations over finite fields

A nonzero linear functional on uniformly sampled field vectors is uniform. This shared API
supports polynomial-evaluation batching, Ligero row consistency and VOLE constraint batching.

## Main definitions

* `linearCombAddHom`: the additive homomorphism `r ↦ ∑ i, r i * d i`.

## Main results

* `uniformOfFintype_map_linearComb`: a nonzero functional maps the uniform law to the uniform law.
* `toOuterMeasure_uniform_linearComb_eq`: each field element has probability exactly `1 / |F|`.
-/

public section

namespace Cslib.Probability

open scoped BigOperators ENNReal

section LinearComb

variable {ι F : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The additive homomorphism `r ↦ ∑ i, r i * d i`. -/
def linearCombAddHom [Semiring F] (d : ι → F) : (ι → F) →+ F where
  toFun r := ∑ i, r i * d i
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

omit [DecidableEq ι] in
@[simp]
theorem linearCombAddHom_apply [Semiring F] (d r : ι → F) :
    linearCombAddHom d r = ∑ i, r i * d i := by
  rfl

omit [DecidableEq ι] in
/-- If `d i₀ ≠ 0` for some coordinate `i₀`, the linear functional `r ↦ ∑ i, r i * d i` is
surjective. -/
theorem linearCombAddHom_surjective [Field F] {d : ι → F} {i₀ : ι} (hd : d i₀ ≠ 0) :
    Function.Surjective (linearCombAddHom d) := by
  classical
  intro v
  refine ⟨Pi.single i₀ (v * (d i₀)⁻¹), ?_⟩
  simp only [linearCombAddHom_apply]
  rw [Finset.sum_eq_single i₀]
  · simp [inv_mul_cancel_right₀ hd]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact (h (Finset.mem_univ i₀)).elim

/-- **Uniformity of a random linear combination**: if `d i₀ ≠ 0`, then for a uniformly random vector
`r : ι → F` over a finite field, `∑ i, r i * d i` is uniformly distributed on `F`. -/
theorem uniformOfFintype_map_linearComb [Field F] [Fintype F] {d : ι → F} {i₀ : ι}
    (hd : d i₀ ≠ 0) :
    (PMF.uniformOfFintype (ι → F)).map (fun r => ∑ i, r i * d i) = PMF.uniformOfFintype F := by
  exact Cslib.Probability.PMF.uniformOfFintype_map_addHom (linearCombAddHom d)
    (linearCombAddHom_surjective hd)

/-- If `d i₀ ≠ 0`, a uniform random linear combination `∑ i, r i * d i` hits any fixed target
`t : F` with probability *exactly* `1 / |F|`. -/
theorem toOuterMeasure_uniform_linearComb_eq [Field F] [Fintype F] {d : ι → F} {i₀ : ι}
    (hd : d i₀ ≠ 0) (t : F) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure {r | ∑ i, r i * d i = t} =
      1 / (Fintype.card F : ℝ≥0∞) := by
  have hpre : {r : ι → F | ∑ i, r i * d i = t} = (fun r : ι → F => ∑ i, r i * d i) ⁻¹' {t} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, uniformOfFintype_map_linearComb hd,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, one_div]

/-- If `d i₀ ≠ 0`, a uniform random linear combination `∑ i, r i * d i` vanishes with probability
*exactly* `1 / |F|`. -/
theorem toOuterMeasure_uniform_linearComb_eq_zero [Field F] [Fintype F] {d : ι → F} {i₀ : ι}
    (hd : d i₀ ≠ 0) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure {r | ∑ i, r i * d i = 0} =
      1 / (Fintype.card F : ℝ≥0∞) :=
  toOuterMeasure_uniform_linearComb_eq hd 0

end LinearComb

end Cslib.Probability
