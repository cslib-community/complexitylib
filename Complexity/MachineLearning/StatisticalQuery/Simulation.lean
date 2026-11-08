/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.StatisticalQuery.Basic
public import Complexity.Probability.Product
import Complexity.Probability.Concentration
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF
import Complexity.Probability.Product.Reindex

/-!
# Simulating statistical queries from examples

A statistical query learner can be run on random labelled examples: answer each query `φ` by the
empirical mean of `φ` on a fresh block of `m` examples (`StatisticalQuery.simulate`). By
Hoeffding's inequality an empirical mean is within the tolerance `τ` of the expectation except
with probability `2 exp (-m τ² / 2)`, and by a union bound over the at most `q` queries of the run,
all answers are within tolerance except with probability `2 q exp (-m τ² / 2)`. The run is then a
run of the learner against an oracle answering within tolerance, so the hypothesis has error at
most `ε` whenever the learner learns with tolerance `τ` and error `ε`
(`StatisticalQuery.Learns.toOuterMeasure_lt_disagreement_simulate_le`). With
`m ≥ 2 log (2 q / δ) / τ²` this is a PAC learner from `q m` examples for the family of the
distributions of a `D`-random point labelled by a concept of the class
(`StatisticalQuery.Learns.isPACLearnerFor`): learnability from statistical queries implies PAC
learnability [Kearns1998, Theorem 1].

The learner may choose its queries adaptively; the union bound runs along the tree of its calls
(`StatisticalQuery.toOuterMeasure_simulate_notMem_le`): each query of the run is answered from a
block of examples independent of the blocks used before, whatever the earlier answers were. This
is the block form of the simulation in [Reyzin, Section 2.1][Reyzin2020], with `m` examples per
query. Kearns's Theorem 1 also covers the case of a finite query space answered from a single
sample; that form is not formalized here.

## Main definitions

* `Cslib.MachineLearning.StatisticalQuery.empirical`: the empirical mean of a query on a block of
  labelled examples.
* `Cslib.MachineLearning.StatisticalQuery.simulate`: running a learner on blocks of examples.
* `Cslib.MachineLearning.StatisticalQuery.labelled`: the distribution of a labelled example.
* `Cslib.MachineLearning.StatisticalQuery.realizable`: the distributions of a `D`-random point
  labelled by a concept of a class.
* `Cslib.MachineLearning.StatisticalQuery.simulateLearner`: the PAC learner from `q m` examples.

## Main results

* `Cslib.MachineLearning.StatisticalQuery.toOuterMeasure_simulate_notMem_le`: the union bound along
  an adaptive run.
* `Cslib.MachineLearning.StatisticalQuery.toOuterMeasure_empirical_notMem_valid_le`: an empirical
  mean of `m` examples is within tolerance except with probability `2 exp (-m τ² / 2)`.
* `Cslib.MachineLearning.StatisticalQuery.Learns.toOuterMeasure_lt_disagreement_simulate_le`: the
  simulated learner fails with probability at most `2 q exp (-m τ² / 2)`.
* `Cslib.MachineLearning.StatisticalQuery.Learns.isPACLearnerFor`: learning from statistical queries
  gives PAC learning from `q m` examples.

## References

* [M. Kearns, *Efficient noise-tolerant learning from statistical queries*][Kearns1998]
* [L. Reyzin, *Statistical queries and statistical algorithms: foundations and
  applications*][Reyzin2020]
-/

@[expose] public section

namespace Cslib.MachineLearning.StatisticalQuery

open Finset MeasureTheory PACLearning Cslib.Probability
open scoped ENNReal NNReal

variable {X : Type}

/-- The empirical mean of the query `φ` on a block `s` of `m` labelled examples. -/
noncomputable def empirical {m : ℕ} (φ : Query X) (s : Fin m → X × Bool) : ℝ :=
  (∑ k, φ (s k).1 (s k).2) / m

/-- Run the statistical query program `A` on blocks of labelled examples: its `i`-th call `φ` is
answered by the empirical mean of `φ` on the `i`-th block. Once the blocks run out, the remaining
calls are answered by `0`. -/
noncomputable def simulate {m : ℕ} {α : Type} :
    (n : ℕ) → (Fin n → Fin m → X × Bool) → OracleComp (spec X) α → α
  | _, _, .pure a => a
  | 0, _, .liftBind _ next => OracleComp.interpret (m := Id) (fun _ => (0 : ℝ)) (next 0)
  | n + 1, blocks, .liftBind φ next => simulate n (Fin.tail blocks) (next (empirical φ (blocks 0)))

@[simp] theorem simulate_pure {m : ℕ} {α : Type} (n : ℕ) (blocks : Fin n → Fin m → X × Bool)
    (a : α) : simulate n blocks (pure a : OracleComp (spec X) α) = a := by
  cases n <;> rfl

@[simp] theorem simulate_query_bind {m : ℕ} {α : Type} (n : ℕ)
    (blocks : Fin (n + 1) → Fin m → X × Bool) (φ : Query X) (next : ℝ → OracleComp (spec X) α) :
    simulate (n + 1) blocks (OracleComp.query φ >>= next) =
      simulate n (Fin.tail blocks) (next (empirical φ (blocks 0))) :=
  rfl

/-- **The union bound along an adaptive run.** Let the program `A` make at most `n` calls, and let
its results be in `good` whenever each call `φ` is answered by an element of `possible φ`. If the
empirical mean of each query on a sample of `P` is outside `possible φ` with probability at most
`β`, then running `A` on `n` independent samples of `P` gives a result outside `good` with
probability at most `n β`. -/
theorem toOuterMeasure_simulate_notMem_le [Finite X] {m : ℕ} {α : Type}
    {A : OracleComp (spec X) α} {n : ℕ} (hA : OracleComp.IsQueryBounded A n)
    {possible : Query X → Set ℝ} {good : Set α}
    (hgood : OracleComp.supportWith possible A ⊆ good) (P : PMF (Fin m → X × Bool)) {β : ℝ≥0∞}
    (hP : ∀ φ, P.toOuterMeasure {s | empirical φ s ∉ possible φ} ≤ β) :
    (PMF.pi fun _ : Fin n => P).toOuterMeasure {b | simulate n b A ∉ good} ≤ n * β := by
  induction hA generalizing good with
  | pure a n =>
    have hb : {b : Fin n → Fin m → X × Bool |
        simulate n b (pure a : OracleComp (spec X) α) ∉ good} = ∅ := by
      ext b
      simp only [simulate_pure, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hgood rfl
    rw [hb, measure_empty]
    exact zero_le
  | liftBind φ next n _ ih =>
    rw [PMF.pi_fin_succ]
    refine (PMF.toOuterMeasure_bind_failure_le _ _ {s | empirical φ s ∈ possible φ} _
      (↑n * β) fun s _ hs => ?_).trans ?_
    · rw [PMF.toOuterMeasure_map_apply]
      exact ih (empirical φ s) (good := good)
        (fun h hh => hgood (Set.mem_biUnion hs hh))
    · rw [Set.compl_ofPred]
      calc P.toOuterMeasure {s | empirical φ s ∉ possible φ} + ↑n * β ≤ β + ↑n * β :=
            add_le_add (hP φ) le_rfl
        _ = ↑(n + 1) * β := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

variable [Fintype X]

/-- The distribution of an example: a `D`-random point labelled by the target `c`. -/
noncomputable def labelled (D : PMF X) (c : X → Bool) : PMF (X × Bool) :=
  D.map fun x => (x, c x)

/-- **Estimating a statistical query.** The empirical mean of the query `φ` on `m` independent
examples of the target `c` under `D` is outside the tolerance `τ ≥ 0` of its expectation with
probability at most `2 exp (-m τ² / 2)`, by Hoeffding's inequality. -/
theorem toOuterMeasure_empirical_notMem_valid_le (D : PMF X) (c : X → Bool) (m : ℕ) (φ : Query X)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (PMF.pi fun _ : Fin m => labelled D c).toOuterMeasure {s | empirical φ s ∉ valid D c τ φ} ≤
      ENNReal.ofReal (2 * Real.exp (-(m * τ ^ 2) / 2)) := by
  have hexpect : ∑ p, (labelled D c p).toReal * φ p.1 p.2 = expect D c φ := by
    rw [labelled, PMF.sum_map_mul]
    rfl
  refine (measure_mono fun s hs => ?_).trans
    (PMF.pi_abs_sum_div_sub_sum_mul_ge_le (labelled D c) (fun p => φ p.1 p.2)
      (fun p => φ.abs_le_one p.1 p.2) hτ)
  simp only [valid, empirical, Set.mem_ofPred_eq, not_le] at hs
  rw [Set.mem_ofPred_eq, hexpect]
  exact hs.le

/-- **Statistical queries from examples** [Kearns1998, Theorem 1] [Reyzin, Section 2.1]
[Reyzin2020]. If `A` learns `C` under `D` from statistical queries of tolerance `τ ≥ 0` with error
`ε`, using at most `q` queries, then running `A` on `q` independent blocks of `m` examples of a
target `c ∈ C`, each query answered by the empirical mean on its own block, gives a hypothesis of
error above `ε` with probability at most `2 q exp (-m τ² / 2)`. -/
theorem Learns.toOuterMeasure_lt_disagreement_simulate_le {A : Algorithm X} {D : PMF X}
    {C : ConceptClass X Bool} {τ ε : ℝ} (hA : Learns A D C τ ε) {q : ℕ}
    (hq : OracleComp.IsQueryBounded A q) (hτ : 0 ≤ τ) {c : X → Bool} (hc : c ∈ C) (m : ℕ) :
    (PMF.pi fun _ : Fin q => PMF.pi fun _ : Fin m => labelled D c).toOuterMeasure
      {b | ε < disagreement D c (simulate q b A)} ≤
        q * ENNReal.ofReal (2 * Real.exp (-(m * τ ^ 2) / 2)) := by
  have h := toOuterMeasure_simulate_notMem_le hq (good := {h | disagreement D c h ≤ ε})
    (hA c hc) _ fun φ => toOuterMeasure_empirical_notMem_valid_le D c m φ hτ
  simpa only [Set.mem_ofPred_eq, not_le] using h

/-! ### PAC learning -/

/-- The distributions of a `D`-random point labelled by a concept of `C`: the family over which
learning under `D` is PAC learning. -/
def realizable [MeasurableSpace X] (D : PMF X) (C : ConceptClass X Bool) :
    Set (Measure (X × Bool)) :=
  {μ | ∃ c ∈ C, μ = (labelled D c).toMeasure}

/-- The PAC learner from `q m` examples that runs `A` on `q` blocks of `m` examples, the block `j`
consisting of the examples `finProdFinEquiv (j, k)`. -/
noncomputable def simulateLearner (A : Algorithm X) (q m : ℕ) : Learner X Bool (q * m) :=
  fun S => simulate q (fun j k => S (finProdFinEquiv (j, k))) A

/-- Under a `D`-random point labelled by `c`, the error of `h` is its disagreement with `c`. -/
theorem error_labelled [MeasurableSpace X] [MeasurableSingletonClass X] (D : PMF X)
    (c h : X → Bool) :
    error (labelled D c).toMeasure h = ENNReal.ofReal (disagreement D c h) := by
  rw [error, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ((Set.to_countable _).measurableSet),
    labelled, PMF.toOuterMeasure_map_apply,
    ← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _), PMF.toOuterMeasure_apply_toReal]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : c x = h x
  · simp [hx]
  · simp [hx, Ne.symm hx]

/-- **Learning from statistical queries gives PAC learning** [Kearns1998, Theorem 1]
[Reyzin, Section 2.1][Reyzin2020]. If `A` learns `C` under `D` from statistical queries of
tolerance `τ ≥ 0` with error `ε`, using at most `q` queries, and `2 q exp (-m τ² / 2) ≤ δ`, then
running `A` on `q` blocks of `m` examples is a PAC learner with error `ε` and confidence `1 - δ`
from `q m` examples, for the distributions of a `D`-random point labelled by a concept of `C`. -/
theorem Learns.isPACLearnerFor [MeasurableSpace X] [MeasurableSingletonClass X] {A : Algorithm X}
    {D : PMF X} {C : ConceptClass X Bool} {τ : ℝ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hA : Learns A D C τ ε.val) {q : ℕ} (hq : OracleComp.IsQueryBounded A q) (hτ : 0 ≤ τ)
    {m : ℕ} (hm : q * (2 * Real.exp (-(m * τ ^ 2) / 2)) ≤ δ.val) :
    IsPACLearnerFor (q * m) ε δ C (realizable D C) := by
  refine ⟨simulateLearner A q m, fun μ _ hμ => ?_⟩
  obtain ⟨c, hc, rfl⟩ := hμ
  have hopt : optimalError (labelled D c).toMeasure C = 0 := by
    refine le_antisymm ((iInf₂_le c hc).trans ?_) zero_le
    rw [error_labelled]
    simp [disagreement]
  have hpi : Measure.pi (fun _ : Fin (q * m) => (labelled D c).toMeasure) =
      (PMF.pi fun _ : Fin (q * m) => labelled D c).toMeasure := by
    rw [PMF.toMeasure_pi]
  rw [hpi, PMF.toMeasure_apply_eq_toOuterMeasure_apply _ ((Set.to_countable _).measurableSet)]
  calc (PMF.pi fun _ : Fin (q * m) => labelled D c).toOuterMeasure
        {S | optimalError (labelled D c).toMeasure C + ε <
          error (labelled D c).toMeasure (simulateLearner A q m S)}
      ≤ (PMF.pi fun _ : Fin (q * m) => labelled D c).toOuterMeasure
          ((fun S j k => S (finProdFinEquiv (j, k))) ⁻¹'
            {b | (ε.val : ℝ) < disagreement D c (simulate q b A)}) := by
        refine measure_mono fun S hS => ?_
        simp only [Set.mem_ofPred_eq, hopt, zero_add, error_labelled] at hS
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [← ENNReal.ofReal_coe_nnreal] at hS
        exact (ENNReal.ofReal_lt_ofReal_iff'.1 hS).1
    _ = (PMF.pi fun _ : Fin q => PMF.pi fun _ : Fin m => labelled D c).toOuterMeasure
          {b | (ε.val : ℝ) < disagreement D c (simulate q b A)} := by
        rw [← PMF.toOuterMeasure_map_apply, PMF.pi_map_finProdFinEquiv]
    _ ≤ q * ENNReal.ofReal (2 * Real.exp (-(m * τ ^ 2) / 2)) :=
        hA.toOuterMeasure_lt_disagreement_simulate_le hq hτ hc m
    _ ≤ δ := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hm

end Cslib.MachineLearning.StatisticalQuery
