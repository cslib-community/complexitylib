/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.MachineLearning.UniformLearning.Basic
public import Mathlib.Data.Finset.Density
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform

/-!
# Learning with membership queries

A learner with *membership queries* may ask for the value `f x` of the unknown target `f` at any
point `x` of its choice [Angluin1988]. With its random choices fixed, it is a decision tree whose
variables are the points of the cube: run on the truth table of `f`, the query of the variable `x`
returns `f x`, and the leaf it reaches is the hypothesis. So a randomized membership-query learner
is a family of such decision trees indexed by random seeds drawn from a distribution
(`UniformLearning.QueryLearner`), and the depth of the trees bounds the number of queries on every
run (`UniformLearning.QueryLearner.QueriesAtMost`). It *learns* a concept class with error `ε` and
confidence `1 - δ` (`UniformLearning.QueryLearner.Learns`) if, for every target in the class, the
hypothesis has error above `ε` under the uniform distribution (`UniformLearning.uniformError`) with
probability at most `δ` over the seed. Membership queries subsume random examples: querying
uniformly random points simulates a learner from uniform random examples, which learns exactly
the same classes (`UniformLearning.QueryLearner.learns_ofLearner_iff`). This is learning under the
uniform distribution with queries
[O'Donnell, Definition 3.27][ODonnell2014]; the query model has no counterpart in `PACLearning`,
whose learners see only labelled samples.

A *non-adaptive* learner chooses its query points from the seed alone, and then computes its
hypothesis from the answers (`UniformLearning.QueryLearner.ofNonadaptive`); it makes as many
queries as it lists points (`UniformLearning.QueryLearner.depth_ofNonadaptive_le`).

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner`: a randomized learner with membership
  queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.QueriesAtMost`: a bound on the number of
  queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.Learns`: learning a concept class with
  membership queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.ofNonadaptive`: the learner querying given
  points.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.ofLearner`: the query learner simulating a
  learner from random examples.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.eval_ofNonadaptive`,
  `Cslib.MachineLearning.UniformLearning.QueryLearner.depth_ofNonadaptive_le`: the hypothesis and
  the query count of a non-adaptive learner.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_ofLearner_iff`: membership queries
  subsume random examples.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_uniformOfFintype_of_le_dens`: with
  uniform seeds from a finite type, learning follows from a lower bound on the density of the
  good seeds.

## References

* [D. Angluin, *Queries and concept learning*][Angluin1988]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open PACLearning Cslib.Probability
open scoped ENNReal

variable {ι Ω : Type*}

variable (ι Ω) in
/-- A learner with membership queries on the cube `ι → Bool`, with random seeds in `Ω`: for each
seed, a decision tree whose variables are the points of the cube and whose leaves are hypotheses.
Run on the truth table of the target `f`, the query of the point `x` returns `f x`. -/
abbrev QueryLearner : Type _ :=
  Ω → DecisionTree (ι → Bool) ((ι → Bool) → Bool)

namespace QueryLearner

/-- The learner `A` makes at most `q` membership queries on every seed and every target. -/
def QueriesAtMost (A : QueryLearner ι Ω) (q : ℕ) : Prop :=
  ∀ ω, (A ω).depth ≤ q

section Learns

variable [Fintype ι] [DecidableEq ι]

/-- The learner `A` *learns* the concept class `C` with membership queries, with seeds drawn from
`μ`, error `ε` and confidence `1 - δ`: for every target `f ∈ C`, the hypothesis output by `A` on
`f` has error above `ε` with probability at most `δ`. -/
def Learns (A : QueryLearner ι Ω) (μ : PMF Ω) (C : ConceptClass (ι → Bool) Bool) (ε δ : ℝ) :
    Prop :=
  ∀ f ∈ C, (μ.map fun ω => (A ω).eval f).toOuterMeasure {h | ε < uniformError f h} ≤
    ENNReal.ofReal δ

/-- Learning is monotone: a smaller class, a larger error and a smaller confidence. -/
theorem Learns.mono {A : QueryLearner ι Ω} {μ : PMF Ω} {C C' : ConceptClass (ι → Bool) Bool}
    {ε ε' δ δ' : ℝ} (hA : A.Learns μ C ε δ) (hC : C' ⊆ C) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    A.Learns μ C' ε' δ' :=
  fun f hf => (((μ.map fun ω => (A ω).eval f).toOuterMeasure.mono fun _ hh =>
    hε.trans_lt hh).trans ((hA f (hC hf)).trans (ENNReal.ofReal_le_ofReal hδ)))

/-- A learner learns `C` when, for every target `f ∈ C`, the seeds on which it outputs a
hypothesis of error above `ε` have probability at most `δ`. -/
theorem learns_iff {A : QueryLearner ι Ω} {μ : PMF Ω} {C : ConceptClass (ι → Bool) Bool} {ε δ : ℝ} :
    A.Learns μ C ε δ ↔
      ∀ f ∈ C, μ.toOuterMeasure {ω | ε < uniformError f ((A ω).eval f)} ≤ ENNReal.ofReal δ := by
  refine forall₂_congr fun f _ => ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- **Learning from a density bound.** With uniform seeds from a finite type, a learner learns `C`
with error `ε` and confidence `p` if, for every target in `C`, the seeds on which its hypothesis
has error at most `ε` make up at least a `p` fraction of all seeds. -/
theorem learns_uniformOfFintype_of_le_dens [Fintype Ω] [Nonempty Ω] {A : QueryLearner ι Ω}
    {C : ConceptClass (ι → Bool) Bool} {ε p : ℝ}
    (h : ∀ f ∈ C, p ≤ (Finset.dens {ω | uniformError f ((A ω).eval f) ≤ ε} : ℝ)) :
    A.Learns (PMF.uniformOfFintype Ω) C ε (1 - p) := by
  refine learns_iff.2 fun f hf => ?_
  have hsplit := Finset.dens_filter_add_dens_filter_not_eq_dens (s := (Finset.univ : Finset Ω))
    fun ω => uniformError f ((A ω).eval f) ≤ ε
  simp only [Finset.dens_univ, not_le] at hsplit
  have hcast : (Finset.dens {ω | uniformError f ((A ω).eval f) ≤ ε} : ℝ) +
      Finset.dens {ω | ε < uniformError f ((A ω).eval f)} = 1 := mod_cast hsplit
  rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _),
    PMF.toOuterMeasure_uniformOfFintype_toReal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbad : ((Finset.univ.filter (· ∈ {ω | ε < uniformError f ((A ω).eval f)})).card : ℝ) /
      Fintype.card Ω = Finset.dens {ω | ε < uniformError f ((A ω).eval f)} := by
    rw [Finset.nnratCast_dens]
    rfl
  rw [hbad]
  linarith [h f hf]

end Learns

variable [Fintype ι]

/-- The non-adaptive learner that queries the points `points ω` and outputs `hyp g ω`, computed
from the answers `g` at those points. -/
def ofNonadaptive (points : Ω → List (ι → Bool))
    (hyp : ((ι → Bool) → Bool) → Ω → (ι → Bool) → Bool) : QueryLearner ι Ω :=
  fun ω => DecisionTree.queryAll (fun g => hyp g ω) (points ω) fun _ => false

/-- If the hypothesis depends only on the answers at the queried points, the non-adaptive learner
run on `f` outputs `hyp f ω`. -/
theorem eval_ofNonadaptive {points : Ω → List (ι → Bool)}
    {hyp : ((ι → Bool) → Bool) → Ω → (ι → Bool) → Bool}
    (hhyp : ∀ ω g g', (∀ x ∈ points ω, g x = g' x) → hyp g ω = hyp g' ω)
    (f : (ι → Bool) → Bool) (ω : Ω) :
    (ofNonadaptive points hyp ω).eval f = hyp f ω := by
  rw [ofNonadaptive, DecisionTree.eval_queryAll]
  exact hhyp ω _ _ fun x hx => ite_eq_left_iff.2 fun h => absurd hx h

/-- The non-adaptive learner makes at most as many queries as it lists points. -/
theorem depth_ofNonadaptive_le (points : Ω → List (ι → Bool))
    (hyp : ((ι → Bool) → Bool) → Ω → (ι → Bool) → Bool) (ω : Ω) :
    (ofNonadaptive points hyp ω).depth ≤ (points ω).length :=
  DecisionTree.depth_queryAll_le _ _ _

section OfLearner

variable {m : ℕ}

/-- The membership-query learner simulating the learner `A` from random examples: it queries the
target at `m` uniformly random points and runs `A` on the resulting examples. -/
def ofLearner (A : Learner (ι → Bool) Bool m) : QueryLearner ι (Fin m → ι → Bool) :=
  ofNonadaptive (fun x => List.ofFn x) fun g x => A (examples g x)

/-- Run on the target `f`, the simulating learner outputs the hypothesis of `A` on the examples
of `f` at its seed. -/
theorem eval_ofLearner (A : Learner (ι → Bool) Bool m) (f : (ι → Bool) → Bool)
    (x : Fin m → ι → Bool) : (ofLearner A x).eval f = A (examples f x) :=
  eval_ofNonadaptive (fun x _ _ h => congrArg A (funext fun j => by
    rw [examples_apply, examples_apply, h (x j) (List.mem_ofFn.2 ⟨j, rfl⟩)])) f x

/-- The simulating learner makes `m` queries. -/
theorem queriesAtMost_ofLearner (A : Learner (ι → Bool) Bool m) : (ofLearner A).QueriesAtMost m :=
  fun x => (depth_ofNonadaptive_le _ _ x).trans_eq List.length_ofFn

/-- **Membership queries subsume random examples**: with uniform seeds, the learner simulating `A`
learns exactly the classes that `A` learns from uniform random examples. -/
theorem learns_ofLearner_iff [DecidableEq ι] {A : Learner (ι → Bool) Bool m}
    {C : ConceptClass (ι → Bool) Bool} {ε δ : ℝ} :
    (ofLearner A).Learns (PMF.uniformOfFintype (Fin m → ι → Bool)) C ε δ ↔
      UniformLearning.Learns A C ε δ := by
  rw [learns_iff, UniformLearning.learns_iff]
  simp only [eval_ofLearner]

end OfLearner

end QueryLearner

end Cslib.MachineLearning.UniformLearning
