/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Measurement of finite-dimensional quantum states

A pure state of a finite-dimensional quantum system with computational basis `ι` is a unit vector
of the Euclidean space `ℂ^ι`, with basis states `|x⟩` (`Cslib.Quantum.ket`). Measuring a unit
state `ψ` in the computational basis gives outcome `y` with probability `|ψ_y|²`
(`Cslib.Quantum.measure`); the probability of an outcome in a set `S` is
`∑_{y ∈ S} |ψ_y|²` (`Cslib.Quantum.measureProb`) [Arora, Barak][AroraBarak09], Chapter 10.

Both quantum models of the library measure through this API: the circuit model on
`ι = Fin n → Bool` (`CslibFrontier/Computability/Circuit/Quantum/Basic.lean`), and the query model,
whose register probability `Cslib.Quantum.regProb` is `measureProb` of the outcomes with a given
query index (`CslibFrontier/Computability/QueryComplexity/Quantum/Search.lean`).

## Main definitions

* `Cslib.Quantum.ket`: the computational basis state `|x⟩`.
* `Cslib.Quantum.measureProb`: the probability of measuring an outcome in a set.
* `Cslib.Quantum.measure`: the outcome distribution of measuring a unit state.

## Main results

* `Cslib.Quantum.measureProb_univ`: the outcome probabilities sum to `‖ψ‖²`.
* `Cslib.Quantum.measureProb_compl`: the outcomes outside a set have the remaining probability.
* `Cslib.Quantum.measureProb_ket`: a basis state is measured with certainty.
* `Cslib.Quantum.measureProb_map_sum_orthonormal`: measuring an isometric image of a
  superposition of orthonormal states each measured in `S` with probability `0` or `1`.
* `Cslib.Quantum.measure_toOuterMeasure_apply`: the measurement probabilities are `measureProb`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset

variable {ι : Type*}

/-- The computational basis state `|x⟩`. -/
noncomputable def ket [DecidableEq ι] (x : ι) : EuclideanSpace ℂ ι := EuclideanSpace.single x 1

@[simp] theorem ket_apply [DecidableEq ι] (x y : ι) : (ket x).ofLp y = if y = x then 1 else 0 := by
  simp [ket]

@[simp] theorem norm_ket [Fintype ι] [DecidableEq ι] (x : ι) : ‖ket x‖ = 1 := by
  simp [ket, PiLp.norm_single]

/-- The probability `∑_{y ∈ S} |ψ_y|²` that measuring `ψ` in the computational basis gives an
outcome in `S`. -/
noncomputable def measureProb (ψ : EuclideanSpace ℂ ι) (S : Finset ι) : ℝ :=
  ∑ y ∈ S, ‖ψ.ofLp y‖ ^ 2

theorem measureProb_nonneg (ψ : EuclideanSpace ℂ ι) (S : Finset ι) : 0 ≤ measureProb ψ S :=
  sum_nonneg fun _ _ => by positivity

/-- The outcome probabilities of a state sum to its squared norm. -/
theorem measureProb_univ [Fintype ι] (ψ : EuclideanSpace ℂ ι) : measureProb ψ univ = ‖ψ‖ ^ 2 :=
  (EuclideanSpace.norm_sq_eq ψ).symm

/-- Measuring a basis state `|x⟩` gives outcome `x` with certainty. -/
theorem measureProb_ket [DecidableEq ι] (x : ι) (S : Finset ι) :
    measureProb (ket x) S = if x ∈ S then 1 else 0 := by
  simp [measureProb, apply_ite]

theorem measureProb_le_measureProb_univ [Fintype ι] (ψ : EuclideanSpace ℂ ι) (S : Finset ι) :
    measureProb ψ S ≤ measureProb ψ univ :=
  sum_le_sum_of_subset_of_nonneg (subset_univ S) fun _ _ _ => by positivity

theorem measureProb_mono (ψ : EuclideanSpace ℂ ι) {S T : Finset ι} (h : S ⊆ T) :
    measureProb ψ S ≤ measureProb ψ T :=
  sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

/-- The outcomes outside `S` have the remaining probability. -/
theorem measureProb_compl [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) (S : Finset ι) :
    measureProb ψ Sᶜ = ‖ψ‖ ^ 2 - measureProb ψ S := by
  have h := sum_add_sum_compl S fun y => ‖ψ.ofLp y‖ ^ 2
  rw [← measureProb_univ]
  simp only [measureProb] at h ⊢
  linarith

/-- Outcome probabilities scale with the squared modulus of a scalar. -/
theorem measureProb_smul (c : ℂ) (ψ : EuclideanSpace ℂ ι) (S : Finset ι) :
    measureProb (c • ψ) S = ‖c‖ ^ 2 * measureProb ψ S := by
  simp only [measureProb, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    mul_sum]

/-- A state is the sum of the basis states weighted by its amplitudes. -/
theorem sum_smul_ket [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    ∑ x, ψ.ofLp x • ket x = ψ := by
  ext y
  simp [Finset.sum_apply]

/-- A state measured in `S` with probability zero has no amplitude in `S`. -/
theorem ofLp_eq_zero_of_measureProb_eq_zero {ψ : EuclideanSpace ℂ ι} {S : Finset ι}
    (h : measureProb ψ S = 0) {y : ι} (hy : y ∈ S) : ψ.ofLp y = 0 := by
  rw [measureProb] at h
  have := (sum_eq_zero_iff_of_nonneg fun y _ => by positivity).mp h y hy
  simpa using this

/-- A unit state measured in `S` with certainty has no amplitude outside `S`. -/
theorem ofLp_eq_zero_of_measureProb_eq_one [Fintype ι] {ψ : EuclideanSpace ℂ ι}
    {S : Finset ι} (hψ : ‖ψ‖ = 1) (h : measureProb ψ S = 1) {y : ι} (hy : y ∉ S) :
    ψ.ofLp y = 0 := by
  classical
  have h' := measureProb_compl ψ S
  rw [h, hψ, one_pow, sub_self] at h'
  exact ofLp_eq_zero_of_measureProb_eq_zero h' (mem_compl.mpr hy)

/-- **Measuring an isometric image of a superposition of orthonormal states, each measured in `S`
with probability `0` or `1`**: the probability of `S` is the total squared weight of the states
measured in `S` with certainty, as the images of the others have no amplitude in `S`. -/
theorem measureProb_map_sum_orthonormal [Fintype ι] {κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (U : E →ₗᵢ[ℂ] EuclideanSpace ℂ ι)
    {v : κ → E} (hv : Orthonormal ℂ v) (c : κ → ℂ) (S : Finset ι) (A : κ → Prop)
    [DecidablePred A] (h₁ : ∀ k, A k → measureProb (U (v k)) S = 1)
    (h₀ : ∀ k, ¬ A k → measureProb (U (v k)) S = 0) :
    measureProb (U (∑ k, c k • v k)) S = ∑ k ∈ univ.filter A, ‖c k‖ ^ 2 := by
  have hn (k : κ) : ‖U (v k)‖ = 1 := by rw [U.norm_map, hv.1 k]
  set w := ∑ k ∈ univ.filter A, c k • v k
  have hS {y : ι} (hy : y ∈ S) : (U (∑ k, c k • v k)).ofLp y = (U w).ofLp y := by
    rw [← sum_filter_add_sum_filter_not univ A, map_add, WithLp.ofLp_add, Pi.add_apply,
      add_eq_left, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    refine sum_eq_zero fun k hk => ?_
    rw [map_smul, WithLp.ofLp_smul, Pi.smul_apply,
      ofLp_eq_zero_of_measureProb_eq_zero (h₀ k (mem_filter.mp hk).2) hy, smul_zero]
  have hSc {y : ι} (hy : y ∉ S) : (U w).ofLp y = 0 := by
    rw [map_sum, WithLp.ofLp_sum, Finset.sum_apply]
    refine sum_eq_zero fun k hk => ?_
    rw [map_smul, WithLp.ofLp_smul, Pi.smul_apply,
      ofLp_eq_zero_of_measureProb_eq_one (hn k) (h₁ k (mem_filter.mp hk).2) hy, smul_zero]
  have hw : ‖w‖ ^ 2 = ∑ k ∈ univ.filter A, ‖c k‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, Orthonormal.inner_sum hv, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  rw [measureProb, sum_congr rfl fun y hy => by rw [hS hy], ← hw, ← U.norm_map,
    ← measureProb_univ, measureProb]
  refine sum_subset (subset_univ S) fun y _ hy => ?_
  rw [hSc hy, norm_zero, zero_pow two_ne_zero]

/-- **Measurement in the computational basis**: a unit state `ψ` gives outcome `y` with
probability `|ψ_y|²`. -/
noncomputable def measure [Fintype ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : PMF ι :=
  PMF.ofFintype (fun y => ENNReal.ofReal (‖ψ.ofLp y‖ ^ 2)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← EuclideanSpace.norm_sq_eq, hψ,
      one_pow, ENNReal.ofReal_one]

@[simp] theorem measure_apply [Fintype ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (y : ι) :
    measure ψ hψ y = ENNReal.ofReal (‖ψ.ofLp y‖ ^ 2) :=
  rfl

/-- The measurement gives an outcome in `S` with probability `measureProb ψ S`. -/
theorem measure_toOuterMeasure_apply [Fintype ι] (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1)
    (S : Finset ι) :
    (measure ψ hψ).toOuterMeasure ↑S = ENNReal.ofReal (measureProb ψ S) := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype, measureProb,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity, ← sum_indicator_subset _ (subset_univ S)]
  refine sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ S <;> simp [Set.indicator, hy]

end Cslib.Quantum
