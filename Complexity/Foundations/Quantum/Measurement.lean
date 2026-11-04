/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
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
`ι = Fin n → Bool` (`Complexity/Computability/Circuit/Quantum/Basic.lean`), and the query model,
whose register probability `Cslib.Quantum.regProb` is `measureProb` of the outcomes with a given
query index (`Complexity/Computability/QueryComplexity/Quantum/Search.lean`).

## Main definitions

* `Cslib.Quantum.ket`: the computational basis state `|x⟩`.
* `Cslib.Quantum.measureProb`: the probability of measuring an outcome in a set.
* `Cslib.Quantum.measure`: the outcome distribution of measuring a unit state.

## Main results

* `Cslib.Quantum.measureProb_univ`: the outcome probabilities sum to `‖ψ‖²`.
* `Cslib.Quantum.measureProb_ket`: a basis state is measured with certainty.
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
