/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Composition
public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery
import CslibFrontier.Computability.DecisionTree.Cost
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Black-box reductions between membership-query learners

To learn a class `C` from a learner `A` for the transformed class `amp '' C`, run `A`, answer
each of its queries `amp f y` by a decision tree `s y` that queries `f`, and post-process the
hypothesis of `A` with an extra seed (`UniformLearning.QueryLearner.reduce`). Run on `f`, the
reduction outputs the post-processed hypothesis of `A` run on `amp f`
(`UniformLearning.QueryLearner.eval_reduce`). If `A` makes at most `q` queries and every `s y`
has depth at most `d`, the reduction makes at most `q * d`
(`UniformLearning.QueryLearner.queriesAtMost_reduce`).

The extra seed is uniform on a finite type and independent of the seed of `A`
(`UniformLearning.QueryLearner.reduceSeed`). Suppose `A` learns `amp '' C` with error `ε'` and
success probability `p`. Suppose also that, for every `f ∈ C`, post-processing turns every
hypothesis with error at most `ε'` against `amp f` into one with error at most `ε` against `f`
for a `ρ` fraction of the extra seeds. Then the reduction learns `C` with error `ε` and success
probability `p * ρ` (`UniformLearning.QueryLearner.learns_reduce`).

This is the shape of the reconstruction property of black-box amplification
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Definition 3.4, pp. 10:10–10:11]
[CarmosinoImpagliazzoKabanetsKolokolova2016]. There, a circuit approximating `Amp(f)` and
oracle access to `f` give a circuit approximating `f`. Here the circuit is the hypothesis of
`A`, and the oracle access is through the trees `s y`. As for the other query learners, only
the number of queries is certified, not running time.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.reduce`: substitute query trees into a
  learner and post-process its hypothesis.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.reduceSeed`: a seed of the learner together
  with an independent uniform extra seed.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.eval_reduce`: the output of the reduction.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.queriesAtMost_reduce`: at most `q * d`
  queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_reduce`: success probabilities
  multiply.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open PACLearning Cslib.Probability
open scoped ENNReal

variable {ι κ Ω T : Type*}

/-- **A black-box reduction.** Run `A`, answering each of its queries at a point `y` by the
decision tree `s y` over the new domain, and post-process the hypothesis `h` of `A` with the
extra seed `τ` into `post h τ`. -/
def reduce (A : QueryLearner ι Ω) (s : (ι → Bool) → DecisionTree (κ → Bool) Bool)
    (post : ((ι → Bool) → Bool) → T → (κ → Bool) → Bool) : QueryLearner κ (Ω × T) :=
  fun ω => ((A ω.1).substitute s).map fun h => post h ω.2

/-- Run on `f`, the reduction outputs the post-processed hypothesis of `A` run on the function
`g` that the query trees compute. -/
theorem eval_reduce (A : QueryLearner ι Ω) {s : (ι → Bool) → DecisionTree (κ → Bool) Bool}
    (post : ((ι → Bool) → Bool) → T → (κ → Bool) → Bool) {f : (κ → Bool) → Bool}
    {g : (ι → Bool) → Bool} (hs : ∀ y, (s y).eval f = g y) (ω : Ω × T) :
    (reduce A s post ω).eval f = post ((A ω.1).eval g) ω.2 := by
  simp only [reduce, DecisionTree.eval_map, DecisionTree.eval_substitute, hs]

/-- If `A` makes at most `q` queries and every query tree has depth at most `d`, the reduction
makes at most `q * d` queries. -/
theorem queriesAtMost_reduce {A : QueryLearner ι Ω} {s : (ι → Bool) → DecisionTree (κ → Bool) Bool}
    (post : ((ι → Bool) → Bool) → T → (κ → Bool) → Bool) {q d : ℕ} (hA : A.QueriesAtMost q)
    (hs : ∀ y, (s y).depth ≤ d) : (reduce A s post).QueriesAtMost (q * d) := fun ω => by
  simp only [reduce, DecisionTree.depth_map]
  exact ((A ω.1).depth_substitute_le s).trans
    (((A ω.1).weightedDepth_le_depth_mul hs).trans (Nat.mul_le_mul_right d (hA ω.1)))

/-- The seed distribution of `reduce`: a seed of the learner drawn from `μ`, and an independent
uniform extra seed. -/
noncomputable def reduceSeed (μ : PMF Ω) (T : Type*) [Fintype T] [Nonempty T] : PMF (Ω × T) :=
  μ.bind fun ω => (PMF.uniformOfFintype T).map (ω, ·)

/-- **Success probabilities of a reduction multiply.** Suppose the query trees compute `amp f`
for every `f ∈ C`, and `A` learns `amp '' C` with error `ε'` and success probability `p`.
Suppose also that, for every `f ∈ C`, every hypothesis with error at most `ε'` against `amp f`
post-processes to error at most `ε` against `f` on a `ρ` fraction of the extra seeds. Then the
reduction learns `C` with error `ε` and success probability `p * ρ`. -/
theorem learns_reduce [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype T]
    [Nonempty T] {A : QueryLearner ι Ω} {μ : PMF Ω}
    {s : (ι → Bool) → DecisionTree (κ → Bool) Bool}
    {post : ((ι → Bool) → Bool) → T → (κ → Bool) → Bool}
    {amp : ((κ → Bool) → Bool) → (ι → Bool) → Bool} {C : ConceptClass (κ → Bool) Bool}
    {ε' ε p ρ : ℝ} (hs : ∀ f ∈ C, ∀ y, (s y).eval f = amp f y)
    (hA : A.Learns μ (amp '' C) ε' (1 - p)) (hp : p ≤ 1) (hρ : 0 ≤ ρ)
    (hpost : ∀ f ∈ C, ∀ h, uniformError (amp f) h ≤ ε' →
      ρ ≤ (Finset.dens {τ : T | uniformError f (post h τ) ≤ ε} : ℝ)) :
    (reduce A s post).Learns (reduceSeed μ T) C ε (1 - p * ρ) := by
  classical
  rw [learns_iff]
  intro f hf
  set good : Set Ω := {ω | uniformError (amp f) ((A ω).eval (amp f)) ≤ ε'}
  set ok : Set (Ω × T) := {ω | uniformError f ((reduce A s post ω).eval f) ≤ ε}
  -- the first stage succeeds with probability at least `p`
  have hgood : p ≤ (μ.toOuterMeasure good).toReal := by
    have hsum := PMF.toOuterMeasure_toReal_add_compl μ good
    have hc : goodᶜ = {ω | ε' < uniformError (amp f) ((A ω).eval (amp f))} := by
      ext ω
      simp [good]
    have hbad : (μ.toOuterMeasure goodᶜ).toReal ≤ 1 - p := by
      rw [hc]
      exact ENNReal.toReal_le_of_le_ofReal (by linarith) (learns_iff.1 hA (amp f) ⟨f, hf, rfl⟩)
    linarith
  -- from a good first stage, the post-processing succeeds with probability at least `ρ`
  have hstep : ∀ ω ∈ μ.support, ω ∈ good →
      ρ ≤ (((PMF.uniformOfFintype T).map (ω, ·)).toOuterMeasure ok).toReal := by
    intro ω _ hω
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFintype_toReal]
    have hpre : ∀ τ : T, (τ ∈ (ω, ·) ⁻¹' ok) ↔
        uniformError f (post ((A ω).eval (amp f)) τ) ≤ ε := fun τ => by
      simp only [Set.mem_preimage, ok, Set.mem_ofPred_eq, eval_reduce A post (hs f hf)]
    refine (hpost f hf _ hω).trans_eq ?_
    rw [Finset.nnratCast_dens]
    congr 3
    exact Finset.filter_congr fun τ _ => (hpre τ).symm
  have hmul := PMF.toOuterMeasure_bind_ge_mul μ _ good ok hρ hgood hstep
  have hsum := PMF.toOuterMeasure_toReal_add_compl (reduceSeed μ T) ok
  have hc : okᶜ = {ω | ε < uniformError f ((reduce A s post ω).eval f)} := by
    ext ω
    simp [ok]
  rw [← hc, ← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold reduceSeed at hsum ⊢
  linarith

end Cslib.MachineLearning.UniformLearning.QueryLearner
