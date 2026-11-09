/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Cslib.MachineLearning.PACLearning.Defs
public import Cslib.Probability.PMF
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF

/-!
# Learning from uniform random examples

A concept over the cube is a Boolean function `f : (ι → Bool) → Bool`, and a concept class is a
`PACLearning.ConceptClass (ι → Bool) Bool`. A deterministic learner from `m` examples is a
`PACLearning.Learner (ι → Bool) Bool m`: it maps a `PACLearning.LabeledSample` of `m` labelled
points to a hypothesis. Here the examples of the unknown target `f` are labelled at independent
uniformly random points (`UniformLearning.examples`, `UniformLearning.uniformExamples`), and the
error of a hypothesis `h` is the fraction of the points where it differs from `f`
(`UniformLearning.uniformError`): the probability that `h` misclassifies a fresh uniform point. A
learner *learns* a class with error `ε` and confidence `1 - δ` under the uniform distribution
(`UniformLearning.Learns`) if, for every target in the class, the hypothesis has error above `ε`
with probability at most `δ` over the examples. This is learning from random examples under the
uniform distribution, the setting of the low-degree algorithm of Linial, Mansour and Nisan
[LinialMansourNisan1993] [O'Donnell, Definition 3.27][ODonnell2014].

Valiant's model of probably approximately correct learning, `PACLearning.IsPACLearnerFor`
[Valiant1984], is distribution-free, and in its computational form asks for learners running in
polynomial time. Learning under the uniform distribution is the special case of the realizable
family of the uniform distribution labelled by a concept (`UniformLearning.uniformRealizable`): a
learner that learns `C` under the uniform distribution is a PAC learner for `C` over that family
(`UniformLearning.Learns.isPACLearnerFor`). The definitions here are information-theoretic: they
bound the number of examples, not the running time of the learner.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.examples`,
  `Cslib.MachineLearning.UniformLearning.uniformExamples`: the examples of a concept at given
  points, and at independent uniform points.
* `Cslib.MachineLearning.UniformLearning.uniformError`: the error of a hypothesis under the uniform
  distribution.
* `Cslib.MachineLearning.UniformLearning.Learns`: learning a concept class from uniform random
  examples.
* `Cslib.MachineLearning.UniformLearning.uniformRealizable`: the uniform distribution labelled by
  the concepts of a class, as a family of distributions on labelled points.

## Main results

* `Cslib.MachineLearning.UniformLearning.uniformExamples_eq_pi`: the examples are independent.
* `Cslib.MachineLearning.UniformLearning.learns_iff`: learning in terms of uniform samples of
  points.
* `Cslib.MachineLearning.UniformLearning.mem_uniformRealizable_iff`: the uniform realizable family
  as pushforwards along the graphs of concepts.
* `Cslib.MachineLearning.UniformLearning.Learns.isPACLearnerFor`: learning under the uniform
  distribution is PAC learning over the uniform realizable family.

## References

* [L. G. Valiant, *A theory of the learnable*][Valiant1984]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open MeasureTheory PACLearning Cslib.Probability
open scoped ENNReal NNReal

variable {ι : Type*} {m : ℕ}

/-- The examples of `f` at the points `x j`: the labelled pairs `(x j, f (x j))`. -/
def examples (f : (ι → Bool) → Bool) (x : Fin m → ι → Bool) : LabeledSample (ι → Bool) Bool m :=
  fun j => (x j, f (x j))

@[simp] theorem examples_apply (f : (ι → Bool) → Bool) (x : Fin m → ι → Bool) (j : Fin m) :
    examples f x j = (x j, f (x j)) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- `m` labelled examples of `f` at independent uniformly random points. -/
noncomputable def uniformExamples (f : (ι → Bool) → Bool) (m : ℕ) :
    PMF (LabeledSample (ι → Bool) Bool m) :=
  (PMF.uniformOfFintype (Fin m → ι → Bool)).map (examples f)

/-- The examples are independent, each a uniform point labelled by `f`. -/
theorem uniformExamples_eq_pi (f : (ι → Bool) → Bool) (m : ℕ) :
    uniformExamples f m =
      PMF.pi fun _ : Fin m => (PMF.uniformOfFintype (ι → Bool)).map fun x => (x, f x) := by
  rw [PMF.pi_map, PMF.pi_uniformOfFintype]
  rfl

/-- The error of a hypothesis `h` for the target `f` under the uniform distribution: the fraction
of the points where `h` and `f` differ. -/
noncomputable def uniformError (f h : (ι → Bool) → Bool) : ℝ :=
  hammingDist h f / 2 ^ Fintype.card ι

theorem uniformError_nonneg (f h : (ι → Bool) → Bool) : 0 ≤ uniformError f h := by
  unfold uniformError
  positivity

@[simp] theorem uniformError_self (f : (ι → Bool) → Bool) : uniformError f f = 0 := by
  simp [uniformError]

/-- The error of a hypothesis is at most one. -/
theorem uniformError_le_one (f h : (ι → Bool) → Bool) : uniformError f h ≤ 1 := by
  rw [uniformError, div_le_one (by positivity)]
  have := hammingDist_le_card_fintype (x := h) (y := f)
  rw [Fintype.card_fun, Fintype.card_bool] at this
  exact_mod_cast this

/-- The error is the probability that a uniform point is misclassified. -/
theorem toOuterMeasure_uniformOfFintype_ne (f h : (ι → Bool) → Bool) :
    (PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {x | h x ≠ f x} =
      ENNReal.ofReal (uniformError f h) := by
  rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _), PMF.toOuterMeasure_apply_toReal]
  congr 1
  simp only [Set.mem_ofPred_eq, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, uniformError,
    hammingDist, div_eq_mul_inv]

/-- The learner `A` *learns* the concept class `C` from `m` uniform random examples with error `ε`
and confidence `1 - δ`: for every target `f ∈ C`, the hypothesis output by `A` on `m` examples of
`f` at independent uniform points has error above `ε` with probability at most `δ`. -/
def Learns (A : Learner (ι → Bool) Bool m) (C : ConceptClass (ι → Bool) Bool) (ε δ : ℝ) :
    Prop :=
  ∀ f ∈ C, (uniformExamples f m).toOuterMeasure {S | ε < uniformError f (A S)} ≤ ENNReal.ofReal δ

/-- A learner learns `C` exactly when, for every target `f ∈ C`, the uniform samples of `m` points
whose examples lead to a hypothesis of error above `ε` have probability at most `δ`. -/
theorem learns_iff {A : Learner (ι → Bool) Bool m} {C : ConceptClass (ι → Bool) Bool}
    {ε δ : ℝ} :
    Learns A C ε δ ↔ ∀ f ∈ C,
      (PMF.uniformOfFintype (Fin m → ι → Bool)).toOuterMeasure
        {x | ε < uniformError f (A (examples f x))} ≤ ENNReal.ofReal δ := by
  refine forall₂_congr fun f _ => ?_
  rw [uniformExamples, PMF.toOuterMeasure_map_apply]
  rfl

/-- Learning is monotone: a smaller class, a larger error and a smaller confidence. -/
theorem Learns.mono {A : Learner (ι → Bool) Bool m} {C C' : ConceptClass (ι → Bool) Bool}
    {ε ε' δ δ' : ℝ} (hA : Learns A C ε δ) (hC : C' ⊆ C) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    Learns A C' ε' δ' :=
  fun f hf => (((uniformExamples f m).toOuterMeasure.mono fun _ hh =>
    hε.trans_lt hh).trans ((hA f (hC hf)).trans (ENNReal.ofReal_le_ofReal hδ)))

/-! ### The uniform realizable family -/

/-- The *uniform realizable family* of a concept class `C`: the distributions of a uniform point
labelled by a concept of `C`. -/
def uniformRealizable (C : ConceptClass (ι → Bool) Bool) :
    Set (Measure ((ι → Bool) × Bool)) :=
  {D | ∃ f ∈ C, D = ((PMF.uniformOfFintype (ι → Bool)).map fun x => (x, f x)).toMeasure}

/-- The uniform realizable family consists of the pushforwards of the uniform distribution along
the graphs `x ↦ (x, c x)` of the concepts `c ∈ C`: the realizable distributions of
`PACLearning` with the uniform distribution on points. -/
theorem mem_uniformRealizable_iff {C : ConceptClass (ι → Bool) Bool}
    {D : Measure ((ι → Bool) × Bool)} :
    D ∈ uniformRealizable C ↔
      ∃ c ∈ C, D = (PMF.uniformOfFintype (ι → Bool)).toMeasure.map fun x => (x, c x) := by
  refine exists_congr fun c => and_congr_right fun _ => ?_
  rw [PMF.toMeasure_map (hf := measurable_of_countable fun x : ι → Bool => (x, c x))]

/-- Under the uniform distribution labelled by `f`, the error of `h` is its uniform error. -/
theorem error_map_eq_ofReal_uniformError (f h : (ι → Bool) → Bool) :
    error ((PMF.uniformOfFintype (ι → Bool)).map fun x => (x, f x)).toMeasure h =
      ENNReal.ofReal (uniformError f h) := by
  rw [error, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ((Set.to_countable _).measurableSet),
    PMF.toOuterMeasure_map_apply]
  exact toOuterMeasure_uniformOfFintype_ne f h

/-- **Learning under the uniform distribution is PAC learning** over the uniform realizable
family: a learner that learns `C` from `m` uniform random examples with error `ε` and confidence
`1 - δ` witnesses `PACLearning.IsPACLearnerFor m ε δ C (uniformRealizable C)`. -/
theorem Learns.isPACLearnerFor {A : Learner (ι → Bool) Bool m}
    {C : ConceptClass (ι → Bool) Bool} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hA : Learns A C ε.val δ.val) : IsPACLearnerFor m ε δ C (uniformRealizable C) := by
  refine ⟨A, fun D _ hD => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hD
  set q := (PMF.uniformOfFintype (ι → Bool)).map fun x => (x, f x)
  have herr (h : (ι → Bool) → Bool) : error q.toMeasure h = ENNReal.ofReal (uniformError f h) :=
    error_map_eq_ofReal_uniformError f h
  have hopt : optimalError q.toMeasure C = 0 :=
    le_antisymm ((iInf₂_le f hf).trans (by rw [herr, uniformError_self, ENNReal.ofReal_zero]))
      zero_le
  have hpi : Measure.pi (fun _ : Fin m => q.toMeasure) = (uniformExamples f m).toMeasure := by
    rw [uniformExamples_eq_pi, PMF.toMeasure_pi]
  rw [hpi, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ((Set.to_countable _).measurableSet)]
  refine ((uniformExamples f m).toOuterMeasure.mono fun S hS => ?_).trans
    ((hA f hf).trans_eq (ENNReal.ofReal_coe_nnreal))
  simp only [Set.mem_ofPred_eq, hopt, zero_add, herr, ← ENNReal.ofReal_coe_nnreal] at hS ⊢
  exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hS).1)

end Cslib.MachineLearning.UniformLearning
