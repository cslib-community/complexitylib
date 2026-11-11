/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Composition
public import CslibFrontier.MachineLearning.UniformLearning.MembershipQuery
public import CslibFrontier.Probability.IID
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.IID.Event
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Best-of-`k` selection for membership-query learners

A learner whose hypothesis is good only with small probability `p` becomes a learner with
confidence `1 - η` by the standard repetition-and-selection argument: run it on `k` independent
seeds, estimate the agreement of each of the `k` hypotheses with the target on `t` fresh uniform
points by membership queries, and output a hypothesis of largest empirical agreement
(`UniformLearning.QueryLearner.bestOf`). This is the confidence boosting step of
[Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 2.11, p. 10:9]
[CarmosinoImpagliazzoKabanetsKolokolova2016], which applies it to the Nisan–Wigderson
reconstruction learner.

The hypotheses are fixed before the estimation queries, so the combined learner makes at most
`k * q + t` queries when each run makes at most `q`
(`UniformLearning.QueryLearner.queriesAtMost_bestOf`), and its output is the hypothesis of one of
the runs (`UniformLearning.QueryLearner.exists_eval_bestOf_eq`). Any bound on the hypotheses of
all runs, such as their circuit or formula complexity, therefore bounds the output
(`UniformLearning.QueryLearner.le_sup_eval_bestOf`).

The seeds of the combined learner are `k` independent seeds of the given learner together with
`t` independent uniform points (`UniformLearning.QueryLearner.bestOfSeed`). If the given learner
has error above `ε` with probability at most `δ`, the combined learner has error above `ε + 2θ`
with probability at most `δ ^ k + 2 k exp (-2 t θ²)`: every run fails with probability `δ ^ k`,
and otherwise some agreement estimate is off by `t θ` with probability at most
`2 k exp (-2 t θ²)` by Hoeffding's inequality and a union bound
(`UniformLearning.QueryLearner.learns_bestOf`). For a learner with error at most `ε` with
probability at least `p`, taking `k ≥ log (2/η) / p` and `t ≥ log (4k/η) / (2θ²)` gives error at
most `ε + 2θ` with probability at least `1 - η`
(`UniformLearning.QueryLearner.learns_bestOf_of_success`). For a weak learner, with agreement at
least `1/2 + γ` with probability at least `p`, taking `θ = γ/4` gives agreement at least
`1/2 + γ/2` with probability at least `1 - η` once `t ≥ 8 log (4k/η) / γ²`
(`UniformLearning.QueryLearner.learns_bestOf_of_weak`).

As for the other query learners here, only the number of queries is certified; running time is
not. Selection compares exact integer agreement counts; ties go to the first maximizing run.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.QueryLearner.agreeCount`: the number of sample points
  where a hypothesis agrees with the target.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.selectBest`: the index of a hypothesis of
  largest agreement count.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.bestOf`: run `k` times, estimate and select.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.bestOfSeed`: the seed distribution of
  `bestOf`.

## Main results

* `Cslib.MachineLearning.UniformLearning.QueryLearner.eval_bestOf`: the output of `bestOf` is the
  hypothesis of the selected run.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.queriesAtMost_bestOf`: `bestOf` makes at
  most `k * q + t` queries.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.le_sup_eval_bestOf`: hypothesis complexity
  is at most the largest among the runs.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_bestOf`: the confidence of `bestOf`.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_bestOf_of_success`: a learner that
  succeeds with probability `p` becomes one with confidence `1 - η`, at error `ε + 2θ`.
* `Cslib.MachineLearning.UniformLearning.QueryLearner.learns_bestOf_of_weak`: weak learners
  become learners with confidence `1 - η`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning.QueryLearner

open Cslib.Probability MeasureTheory
open scoped ENNReal

variable {ι Ω : Type*} {k t : ℕ}

section Selection

/-- The number of the sample points `x i` at which the hypothesis `h` agrees with the target
`g`. -/
def agreeCount (g h : (ι → Bool) → Bool) (x : Fin t → ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => h (x i) = g (x i)).card

/-- The index of a hypothesis among `hs` with the largest agreement count with `g` on the sample
`x`; the first such index. -/
def selectBest [NeZero k] (g : (ι → Bool) → Bool) (hs : Fin k → (ι → Bool) → Bool)
    (x : Fin t → ι → Bool) : Fin k :=
  ((List.finRange k).argmax fun j => agreeCount g (hs j) x).getD 0

/-- The selected hypothesis has the largest agreement count. -/
theorem agreeCount_le_selectBest [NeZero k] (g : (ι → Bool) → Bool)
    (hs : Fin k → (ι → Bool) → Bool) (x : Fin t → ι → Bool) (j : Fin k) :
    agreeCount g (hs j) x ≤ agreeCount g (hs (selectBest g hs x)) x := by
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.1
    (mt List.argmax_eq_none.1 (List.ne_nil_of_mem (List.mem_finRange j)) :
      (List.finRange k).argmax (fun j => agreeCount g (hs j) x) ≠ none)
  rw [selectBest, hm, Option.getD_some]
  exact List.le_of_mem_argmax (List.mem_finRange j) hm

/-- Selection reads the target only at the sample points. -/
theorem selectBest_congr [NeZero k] {g g' : (ι → Bool) → Bool} (hs : Fin k → (ι → Bool) → Bool)
    (x : Fin t → ι → Bool) (h : ∀ i, g (x i) = g' (x i)) :
    selectBest g hs x = selectBest g' hs x := by
  simp only [selectBest, agreeCount, h]

/-- The number of agreements at the sample points, as a sum of indicators. -/
private theorem sum_agree_eq (f h : (ι → Bool) → Bool) (x : Fin t → ι → Bool) :
    (∑ i, if h (x i) = f (x i) then (1 : ℝ) else 0) = agreeCount f h x := by
  rw [agreeCount, Finset.natCast_card_filter]

end Selection

variable [Fintype ι]

/-- **Best-of-`k` selection**: run `A` on the seeds `ω 0, …, ω (k - 1)`, query the target at the
sample points `x 0, …, x (t - 1)`, and output a hypothesis of a run with the largest number of
agreements with the target at those points. -/
def bestOf (A : QueryLearner ι Ω) (k t : ℕ) [NeZero k] :
    QueryLearner ι ((Fin k → Ω) × (Fin t → ι → Bool)) := fun s =>
  (DecisionTree.seqFin fun j => A (s.1 j)).bind fun hs =>
    DecisionTree.queryAll (fun g => hs (selectBest g hs s.2)) (List.ofFn s.2) fun _ => false

/-- Run on the target `f`, `bestOf` outputs the hypothesis of the run selected by its agreement
with `f` on the sample. -/
theorem eval_bestOf (A : QueryLearner ι Ω) (k t : ℕ) [NeZero k] (f : (ι → Bool) → Bool)
    (ω : Fin k → Ω) (x : Fin t → ι → Bool) :
    (bestOf A k t (ω, x)).eval f =
      (A (ω (selectBest f (fun j => (A (ω j)).eval f) x))).eval f := by
  simp only [bestOf, DecisionTree.eval_bind, DecisionTree.eval_seqFin,
    DecisionTree.eval_queryAll]
  rw [selectBest_congr _ _ fun i => ite_eq_left (List.mem_ofFn.2 ⟨i, rfl⟩)]

/-- The output of `bestOf` is the hypothesis of one of the runs. -/
theorem exists_eval_bestOf_eq (A : QueryLearner ι Ω) (k t : ℕ) [NeZero k]
    (f : (ι → Bool) → Bool) (ω : Fin k → Ω) (x : Fin t → ι → Bool) :
    ∃ j, (bestOf A k t (ω, x)).eval f = (A (ω j)).eval f :=
  ⟨_, eval_bestOf A k t f ω x⟩

/-- Any measure `c` of the output hypothesis, such as its circuit complexity, is at most the
largest value of `c` on the hypotheses of the runs. -/
theorem le_sup_eval_bestOf (A : QueryLearner ι Ω) (k t : ℕ) [NeZero k] (f : (ι → Bool) → Bool)
    (ω : Fin k → Ω) (x : Fin t → ι → Bool) (c : ((ι → Bool) → Bool) → ℕ) :
    c ((bestOf A k t (ω, x)).eval f) ≤ Finset.univ.sup fun j => c ((A (ω j)).eval f) := by
  obtain ⟨j, hj⟩ := exists_eval_bestOf_eq A k t f ω x
  rw [hj]
  exact Finset.le_sup (f := fun j => c ((A (ω j)).eval f)) (Finset.mem_univ j)

/-- If every run makes at most `q` queries, `bestOf` makes at most `k * q + t`: `k * q` for the
runs and `t` for the agreement estimates. -/
theorem queriesAtMost_bestOf [NeZero k] {A : QueryLearner ι Ω} {q : ℕ}
    (hA : A.QueriesAtMost q) : (bestOf A k t).QueriesAtMost (k * q + t) := fun _ =>
  (DecisionTree.depth_bind_le _ _ fun _ =>
    (DecisionTree.depth_queryAll_le _ _ _).trans_eq List.length_ofFn).trans
      (Nat.add_le_add_right (DecisionTree.depth_seqFin_le _ fun _ => hA _) t)

variable [DecidableEq ι]

/-- The seed distribution of `bestOf`: `k` independent seeds drawn from `μ` and `t` independent
uniform sample points. -/
noncomputable def bestOfSeed (μ : PMF Ω) (k t : ℕ) : PMF ((Fin k → Ω) × (Fin t → ι → Bool)) :=
  (PMF.iid μ k).bind fun ω => (PMF.uniformOfFintype (Fin t → ι → Bool)).map (ω, ·)

/-- A uniform point is classified correctly with probability `1 - uniformError f h`. -/
private theorem sum_uniform_agree (f h : (ι → Bool) → Bool) :
    ∑ a, ((PMF.uniformOfFintype (ι → Bool)) a).toReal * (if h a = f a then 1 else 0) =
      1 - uniformError f h := by
  have h2 := PMF.toOuterMeasure_toReal_add_compl (PMF.uniformOfFintype (ι → Bool))
    {a | h a = f a}
  have hc : ({a | h a = f a}ᶜ : Set (ι → Bool)) = {a | h a ≠ f a} := rfl
  rw [hc, toOuterMeasure_uniformOfFintype_ne, ENNReal.toReal_ofReal (uniformError_nonneg f h)]
    at h2
  have h4 : ∑ a, ((PMF.uniformOfFintype (ι → Bool)) a).toReal * (if h a = f a then 1 else 0) =
      ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {a | h a = f a}).toReal := by
    rw [PMF.toOuterMeasure_apply_toReal]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp_all
  linarith

/-- **Confidence of best-of-`k` selection.** If `A` has error above `ε` with probability at most
`δ`, then `bestOf A k t` has error above `ε + 2θ` with probability at most
`δ ^ k + 2 k exp (-2 t θ²)`. -/
theorem learns_bestOf [NeZero k] {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε δ θ : ℝ} (hA : A.Learns μ C ε δ)
    (hδ : 0 ≤ δ) (hθ : 0 ≤ θ) :
    (bestOf A k t).Learns (bestOfSeed μ k t) C (ε + 2 * θ)
      (δ ^ k + 2 * k * Real.exp (-2 * t * θ ^ 2)) := by
  rw [learns_iff]
  intro f hf
  -- the seeds on which some run has error at most `ε`
  let pre : Set (Fin k → Ω) := {ω | ∃ j, uniformError f ((A (ω j)).eval f) ≤ ε}
  have hpre : (PMF.iid μ k).toOuterMeasure preᶜ ≤ ENNReal.ofReal (δ ^ k) := by
    have hc : preᶜ = {ω : Fin k → Ω | ∀ i, ω i ∈ {a | ε < uniformError f ((A a).eval f)}} := by
      ext ω
      simp [pre]
    rw [hc, PMF.toOuterMeasure_iid_forall, ENNReal.ofReal_pow hδ]
    gcongr
    exact learns_iff.1 hA f hf
  have hstep : ∀ ω ∈ (PMF.iid μ k).support, ω ∈ pre →
      ((PMF.uniformOfFintype (Fin t → ι → Bool)).map (ω, ·)).toOuterMeasure
        {s | ε + 2 * θ < uniformError f ((bestOf A k t s).eval f)} ≤
        ENNReal.ofReal (2 * k * Real.exp (-2 * t * θ ^ 2)) := by
    rintro ω - ⟨j₀, hj₀⟩
    -- the samples on which the agreement estimate of run `j` is off by at least `t θ`
    let E : Fin k → Set (Fin t → ι → Bool) := fun j => {x | (t : ℝ) * θ ≤
      |(∑ i, if (A (ω j)).eval f (x i) = f (x i) then (1 : ℝ) else 0) -
        ∑ _i : Fin t, ∑ a, ((PMF.uniformOfFintype (ι → Bool)) a).toReal *
          (if (A (ω j)).eval f a = f a then 1 else 0)|}
    have hmean (j : Fin k) : (∑ _i : Fin t, ∑ a, ((PMF.uniformOfFintype (ι → Bool)) a).toReal *
        (if (A (ω j)).eval f a = f a then 1 else 0)) =
          t * (1 - uniformError f ((A (ω j)).eval f)) := by
      simp only [sum_uniform_agree, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
    have hsub : (fun x => (ω, x)) ⁻¹'
        {s | ε + 2 * θ < uniformError f ((bestOf A k t s).eval f)} ⊆ ⋃ j, E j := by
      intro x hx
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_bestOf] at hx
      by_contra hnot
      simp only [Set.mem_iUnion, not_exists, E, Set.mem_ofPred_eq, not_le, hmean,
        sum_agree_eq] at hnot
      have h1 := abs_lt.1 (hnot (selectBest f (fun j => (A (ω j)).eval f) x))
      have h2 := abs_lt.1 (hnot j₀)
      have hle : (agreeCount f ((A (ω j₀)).eval f) x : ℝ) ≤
          agreeCount f ((A (ω (selectBest f (fun j => (A (ω j)).eval f) x))).eval f) x := by
        exact_mod_cast agreeCount_le_selectBest f (fun j => (A (ω j)).eval f) x j₀
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have h3 := mul_le_mul_of_nonneg_left hj₀ ht
      have h4 : (t : ℝ) *
          uniformError f ((A (ω (selectBest f (fun j => (A (ω j)).eval f) x))).eval f) <
            t * (ε + 2 * θ) := by
        linarith
      linarith [lt_of_mul_lt_mul_left h4 ht]
    have hE (j : Fin k) : (PMF.uniformOfFintype (Fin t → ι → Bool)).toOuterMeasure (E j) ≤
        ENNReal.ofReal (2 * Real.exp (-2 * t * θ ^ 2)) := by
      rw [← PMF.pi_uniformOfFintype (ι := Fin t) (α := fun _ => ι → Bool)]
      have hH := PMF.pi_sum_abs_sub_mean_ge_card_mul
        (fun _ : Fin t => PMF.uniformOfFintype (ι → Bool))
        (fun _ a => if (A (ω j)).eval f a = f a then (1 : ℝ) else 0)
        (fun _ a _ => by by_cases h : (A (ω j)).eval f a = f a <;> simp [h]) hθ
      rw [Fintype.card_fin] at hH
      exact (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _)
        (by positivity)).2 hH
    rw [PMF.toOuterMeasure_map_apply]
    calc _ ≤ (PMF.uniformOfFintype (Fin t → ι → Bool)).toOuterMeasure (⋃ j, E j) :=
          measure_mono hsub
      _ ≤ ∑ j, (PMF.uniformOfFintype (Fin t → ι → Bool)).toOuterMeasure (E j) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _j : Fin k, ENNReal.ofReal (2 * Real.exp (-2 * t * θ ^ 2)) :=
          Finset.sum_le_sum fun j _ => hE j
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
        congr 1
        ring
  calc _ ≤ (PMF.iid μ k).toOuterMeasure preᶜ +
        ENNReal.ofReal (2 * k * Real.exp (-2 * t * θ ^ 2)) :=
        PMF.toOuterMeasure_bind_failure_le _ _ pre _ _ hstep
    _ ≤ ENNReal.ofReal (δ ^ k) + ENNReal.ofReal (2 * k * Real.exp (-2 * t * θ ^ 2)) := by
        gcongr
    _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm

/-- **Boosting the confidence.** If `A` has error at most `ε` with probability at least `p`, then
`bestOf A k t` with `k ≥ log (2/η) / p` runs and `t ≥ log (4k/η) / (2θ²)` sample points has error at
most `ε + 2θ` with probability at least `1 - η`: all runs fail with probability at most `η / 2`, and
some agreement estimate is off by `tθ` with probability at most `η / 2`. -/
theorem learns_bestOf_of_success [NeZero k] {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {ε p θ η : ℝ}
    (hA : A.Learns μ C ε (1 - p)) (hp : p ≤ 1) (hθ : 0 ≤ θ) (hη : 0 < η)
    (hk : Real.log (2 / η) ≤ p * k) (ht : Real.log (4 * k / η) ≤ 2 * t * θ ^ 2) :
    (bestOf A k t).Learns (bestOfSeed μ k t) C (ε + 2 * θ) η := by
  refine (learns_bestOf hA (by linarith) hθ).mono le_rfl le_rfl ?_
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne k))
  -- all `k` runs fail with probability at most `η / 2`
  have h1 : (1 - p) ^ k ≤ η / 2 := by
    calc (1 - p) ^ k ≤ Real.exp (-Real.log (2 / η)) :=
          Real.one_sub_pow_le_exp hp (by linarith)
      _ = η / 2 := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  -- some agreement estimate is off by `t θ` with probability at most `η / 2`
  have h2 : Real.exp (-2 * t * θ ^ 2) ≤ η / (4 * k) := by
    calc Real.exp (-2 * t * θ ^ 2) ≤ Real.exp (-Real.log (4 * k / η)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = η / (4 * k) := by
          rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have h3 : 2 * k * Real.exp (-2 * t * θ ^ 2) ≤ η / 2 := by
    calc 2 * k * Real.exp (-2 * t * θ ^ 2) ≤ 2 * k * (η / (4 * k)) := by gcongr
      _ = η / 2 := by field_simp; ring
  linarith

/-- **From weak to confident learning.** If `A` outputs a hypothesis with agreement at least
`1/2 + γ` (error at most `1/2 - γ`) with probability at least `p`, then `bestOf A k t` with
`k ≥ log (2/η) / p` runs and `t ≥ 8 log (4k/η) / γ²` sample points outputs a hypothesis with
agreement at least `1/2 + γ/2` with probability at least `1 - η`. This is
`learns_bestOf_of_success` with `θ = γ / 4`. -/
theorem learns_bestOf_of_weak [NeZero k] {A : QueryLearner ι Ω} {μ : PMF Ω}
    {C : PACLearning.ConceptClass (ι → Bool) Bool} {γ p η : ℝ}
    (hA : A.Learns μ C (1 / 2 - γ) (1 - p)) (hγ : 0 < γ) (hp : p ≤ 1) (hη : 0 < η)
    (hk : Real.log (2 / η) ≤ p * k) (ht : 8 * Real.log (4 * k / η) ≤ t * γ ^ 2) :
    (bestOf A k t).Learns (bestOfSeed μ k t) C (1 / 2 - γ / 2) η :=
  (learns_bestOf_of_success hA hp (by linarith : (0 : ℝ) ≤ γ / 4) hη hk
    (by nlinarith)).mono le_rfl (by linarith) le_rfl

end Cslib.MachineLearning.UniformLearning.QueryLearner
