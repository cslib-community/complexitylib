/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Languages.Probabilistic.Semantics
public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal

/-!
# Replicable sample algorithms with a shared seed

A randomized sample algorithm of sample size `m` over domain `X` with shared seed space `Ω` and
output type `α` consists of a distribution `seed : PMF Ω` for the shared randomness and a
sample-to-output kernel `run : (Fin m → X) → Ω → PMF α` (`Algorithm`)
[ImpagliazzoLeiPitassiSorrell2022]. When the algorithm is deterministic given the sample and seed,
`Algorithm.deterministic` lifts a map `(Fin m → X) → Ω → α` into `Algorithm`.

`Program` packages a `ProbComp`-backed seed generator `seed : ProbComp Ω` and sample runner
`run : (Fin m → X) → Ω → ProbComp α`, together with single-run `Program.exec` and two-sample
shared-seed `Program.coupledExec`, interpreted semantically into `Algorithm` via `ProbComp.eval`
(`Program.toAlgorithm`). Note that `Program` fixes probabilistic control over `ProbComp` without
providing finite-precision real representations or native resource bounds.

Running `A` twice on independent i.i.d. samples `S₁, S₂ ~ D^m` with the same shared seed `r ~ seed`
induces the joint output distribution `Algorithm.pairedOutput A D` on `α × α`. The disagreement
probability `Algorithm.disagreeProb A D` is `Pr[y₁ ≠ y₂]` under this coupling, and
`Algorithm.agreeProb A D = 1 - Algorithm.disagreeProb A D` is `Pr[y₁ = y₂]`.

* **Weak (distribution-family) `ρ`-replicability** (`IsReplicableFor A 𝒟 ρ`, and
  single-distribution `IsReplicableOn A D ρ`): `Algorithm.disagreeProb A D ≤ ρ` for every `D ∈ 𝒟`.
* **Strong (all-distributions) `ρ`-replicability** (`IsReplicable A ρ`):
  `IsReplicableFor A Set.univ ρ`.
* **Accuracy** (`IsAccurateFor A 𝒟 good β`, `IsAccurate A good β`): under a single sample
  `S ~ D^m`, the marginal output misses `good D` with probability at most `β`.
* **Estimation accuracy** (`EstimatesFor A 𝒟 target ε β`, `Estimates A target ε β`): for real-valued
  outputs, `|y - target D| ≤ ε` fails with probability at most `β`.

## Main definitions

* `Cslib.MachineLearning.Replicable.Algorithm`: semantic shared-seed sample algorithms.
* `Cslib.MachineLearning.Replicable.Program`: `ProbComp`-backed shared-seed sample programs.
* `Cslib.MachineLearning.Replicable.Algorithm.output`,
  `Cslib.MachineLearning.Replicable.Algorithm.marginal`,
  `Cslib.MachineLearning.Replicable.Algorithm.pairedOutput`: single-run and paired shared-seed laws.
* `Cslib.MachineLearning.Replicable.Algorithm.disagreeProb`,
  `Cslib.MachineLearning.Replicable.Algorithm.agreeProb`: disagreement and agreement probabilities.
* `Cslib.MachineLearning.Replicable.IsReplicableFor`,
  `Cslib.MachineLearning.Replicable.IsReplicableOn`,
  `Cslib.MachineLearning.Replicable.IsReplicable`: weak and strong `ρ`-replicability.
* `Cslib.MachineLearning.Replicable.IsAccurateFor`,
  `Cslib.MachineLearning.Replicable.IsAccurateOn`,
  `Cslib.MachineLearning.Replicable.IsAccurate`,
  `Cslib.MachineLearning.Replicable.EstimatesFor`,
  `Cslib.MachineLearning.Replicable.Estimates`: accuracy predicates.

## Main results

* `Cslib.MachineLearning.Replicable.Algorithm.agreeProb_add_disagreeProb`: agreement and
  disagreement sum to `1`.
* `Cslib.MachineLearning.Replicable.Algorithm.disagreeProb_deterministic`: simplified disagreement
  probability for algorithms deterministic given the sample and seed.
* `Cslib.MachineLearning.Replicable.IsReplicableFor.map`,
  `Cslib.MachineLearning.Replicable.IsReplicableFor.mapWithSeed`: deterministic and seed-dependent
  post-processing preserve replicability.
* `Cslib.MachineLearning.Replicable.IsReplicable.toIsReplicableFor`,
  `Cslib.MachineLearning.Replicable.IsReplicableFor.mono`,
  `Cslib.MachineLearning.Replicable.IsReplicableFor.antitone`: monotonicity and family restriction.

## References

* [ImpagliazzoLeiPitassiSorrell2022]
-/

public section

namespace Cslib.MachineLearning.Replicable

open Cslib.Probability
open scoped ENNReal

universe u v w z

/-- A semantic randomized sample algorithm of sample size `m` over domain `X` with shared seed
distribution `seed : PMF Ω` and output type `α`. Given sample `S` and shared seed `r`,
`run S r : PMF α` is the conditional output distribution (which is pure when all randomness lies
in the shared seed). -/
structure Algorithm (X : Type u) (Ω : Type v) (α : Type w) (m : ℕ) where
  /-- Distribution of the shared random seed. -/
  seed : PMF Ω
  /-- Conditional output distribution given the sample and shared seed. -/
  run : (Fin m → X) → Ω → PMF α

namespace Algorithm

variable {X : Type u} {Ω : Type v} {α : Type w} {γ : Type z} {m : ℕ}

/-- Construct an `Algorithm` whose randomness lies entirely in the shared seed. -/
@[expose] noncomputable def deterministic (seed : PMF Ω) (f : (Fin m → X) → Ω → α) :
    Algorithm X Ω α m where
  seed := seed
  run S r := PMF.pure (f S r)

/-- Single-execution marginal output distribution on a fixed sample `S`. -/
@[expose] noncomputable def output (A : Algorithm X Ω α m) (S : Fin m → X) : PMF α :=
  A.seed.bind (A.run S)

/-- Single-execution marginal output distribution on `m` i.i.d. samples from `D`. -/
@[expose] noncomputable def marginal (A : Algorithm X Ω α m) (D : PMF X) : PMF α :=
  (Probability.PMF.iid D m).bind A.output

/-- Two-sample shared-seed joint output distribution on `α × α` when `S₁, S₂ ~ iid D m` are
drawn independently and executed with the same shared seed `r ~ A.seed`. -/
@[expose] noncomputable def pairedOutput (A : Algorithm X Ω α m) (D : PMF X) : PMF (α × α) :=
  A.seed.bind fun r =>
    (Probability.PMF.iid D m).bind fun S₁ =>
      (Probability.PMF.iid D m).bind fun S₂ =>
        (A.run S₁ r).bind fun y₁ =>
          (A.run S₂ r).map fun y₂ => (y₁, y₂)

/-- The single-execution marginal equals drawing the shared seed first, then the sample. -/
theorem marginal_eq_seed_bind (A : Algorithm X Ω α m) (D : PMF X) :
    A.marginal D = A.seed.bind fun r => (Probability.PMF.iid D m).bind fun S => A.run S r :=
  PMF.bind_comm (Probability.PMF.iid D m) A.seed (fun S r => A.run S r)

/-- Probability that two independent i.i.d. samples sharing a seed yield different outputs. -/
@[expose] noncomputable def disagreeProb (A : Algorithm X Ω α m) (D : PMF X) : ℝ :=
  ((A.pairedOutput D).toOuterMeasure {p : α × α | p.1 ≠ p.2}).toReal

/-- Probability that two independent i.i.d. samples sharing a seed yield the same output. -/
@[expose] noncomputable def agreeProb (A : Algorithm X Ω α m) (D : PMF X) : ℝ :=
  ((A.pairedOutput D).toOuterMeasure {p : α × α | p.1 = p.2}).toReal

theorem disagreeProb_nonneg (A : Algorithm X Ω α m) (D : PMF X) : 0 ≤ A.disagreeProb D :=
  ENNReal.toReal_nonneg

theorem agreeProb_nonneg (A : Algorithm X Ω α m) (D : PMF X) : 0 ≤ A.agreeProb D :=
  ENNReal.toReal_nonneg

theorem disagreeProb_le_one (A : Algorithm X Ω α m) (D : PMF X) : A.disagreeProb D ≤ 1 :=
  Probability.PMF.toOuterMeasure_toReal_le_one _ _

theorem agreeProb_le_one (A : Algorithm X Ω α m) (D : PMF X) : A.agreeProb D ≤ 1 :=
  Probability.PMF.toOuterMeasure_toReal_le_one _ _

/-- Agreement and disagreement probabilities sum to `1`. -/
theorem agreeProb_add_disagreeProb (A : Algorithm X Ω α m) (D : PMF X) :
    A.agreeProb D + A.disagreeProb D = 1 := by
  simpa only [agreeProb, disagreeProb, Set.compl_ofPred, not_not] using
    Probability.PMF.toOuterMeasure_toReal_add_compl (A.pairedOutput D) {p : α × α | p.1 = p.2}

theorem agreeProb_eq_one_sub_disagreeProb (A : Algorithm X Ω α m) (D : PMF X) :
    A.agreeProb D = 1 - A.disagreeProb D :=
  eq_sub_of_add_eq (agreeProb_add_disagreeProb A D)

theorem disagreeProb_eq_one_sub_agreeProb (A : Algorithm X Ω α m) (D : PMF X) :
    A.disagreeProb D = 1 - A.agreeProb D :=
  eq_sub_of_add_eq' (agreeProb_add_disagreeProb A D)

/-- Paired output distribution for an algorithm that is deterministic given sample and seed. -/
theorem pairedOutput_deterministic (seed : PMF Ω) (f : (Fin m → X) → Ω → α) (D : PMF X) :
    (deterministic seed f).pairedOutput D =
      seed.bind fun r =>
        (Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).map fun S₂ => (f S₁ r, f S₂ r) := by
  simp only [pairedOutput, deterministic, PMF.pure_bind, PMF.pure_map]
  rfl

/-- Disagreement probability for an algorithm that is deterministic given sample and seed, expressed
by integrating the per-pair seed disagreement probability over independent samples. -/
theorem disagreeProb_deterministic (seed : PMF Ω) (f : (Fin m → X) → Ω → α) (D : PMF X) :
    (deterministic seed f).disagreeProb D =
      ((seed.bind fun r =>
        (Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).map fun S₂ => (f S₁ r, f S₂ r)).toOuterMeasure
        {p : α × α | p.1 ≠ p.2}).toReal := by
  rw [disagreeProb, pairedOutput_deterministic]

/-- Disagreement probability of a deterministic-given-seed algorithm expressed as a `tsum` over
the shared seed of the conditional pair-disagreement probability. -/
theorem disagreeProb_deterministic_eq_tsum_seed (seed : PMF Ω) (f : (Fin m → X) → Ω → α)
    (D : PMF X) :
    (deterministic seed f).disagreeProb D =
      ∑' r : Ω, (seed r).toReal *
        (((Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).map fun S₂ => (f S₁ r, f S₂ r)).toOuterMeasure
          {p : α × α | p.1 ≠ p.2}).toReal := by
  rw [disagreeProb_deterministic, PMF.toOuterMeasure_bind_apply,
    ENNReal.tsum_toReal_eq (fun r => ENNReal.mul_ne_top (seed.apply_ne_top r)
      (Probability.PMF.toOuterMeasure_ne_top _ _))]
  refine tsum_congr fun r => ?_
  rw [ENNReal.toReal_mul]

/-- Disagreement probability of a deterministic-given-seed algorithm expressed by drawing the two
independent samples first, then the shared seed. -/
theorem disagreeProb_deterministic_eq_tsum_samples (seed : PMF Ω) (f : (Fin m → X) → Ω → α)
    (D : PMF X) :
    (deterministic seed f).disagreeProb D =
      ∑' S₁ : Fin m → X, (Probability.PMF.iid D m S₁).toReal *
        ∑' S₂ : Fin m → X, (Probability.PMF.iid D m S₂).toReal *
          (seed.toOuterMeasure {r | f S₁ r ≠ f S₂ r}).toReal := by
  have hcomm :
      (deterministic seed f).pairedOutput D =
        (Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).bind fun S₂ =>
            seed.map fun r => (f S₁ r, f S₂ r) := by
    rw [pairedOutput_deterministic, PMF.bind_comm]
    refine PMF.bind_congr_on_support _ _ _ fun S₁ _ => ?_
    simp only [PMF.map]
    exact PMF.bind_comm seed (Probability.PMF.iid D m)
      (fun r S₂ => PMF.pure (f S₁ r, f S₂ r))
  rw [disagreeProb, hcomm, PMF.toOuterMeasure_bind_apply,
    ENNReal.tsum_toReal_eq (fun S₁ => ENNReal.mul_ne_top ((Probability.PMF.iid D m).apply_ne_top S₁)
      (Probability.PMF.toOuterMeasure_ne_top _ _))]
  refine tsum_congr fun S₁ => ?_
  rw [ENNReal.toReal_mul, PMF.toOuterMeasure_bind_apply,
    ENNReal.tsum_toReal_eq (fun S₂ => ENNReal.mul_ne_top ((Probability.PMF.iid D m).apply_ne_top S₂)
      (Probability.PMF.toOuterMeasure_ne_top _ _))]
  congr 1
  refine tsum_congr fun S₂ => ?_
  rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply]
  rfl

/-- Deterministic post-processing of an algorithm's output. -/
@[expose] noncomputable def map (A : Algorithm X Ω α m) (f : α → γ) : Algorithm X Ω γ m where
  seed := A.seed
  run S r := (A.run S r).map f

/-- Post-processing with access to the shared seed `r`. -/
@[expose] noncomputable def mapWithSeed (A : Algorithm X Ω α m) (f : Ω → α → γ) :
    Algorithm X Ω γ m where
  seed := A.seed
  run S r := (A.run S r).map (f r)

theorem marginal_map (A : Algorithm X Ω α m) (f : α → γ) (D : PMF X) :
    (A.map f).marginal D = (A.marginal D).map f := by
  simp only [marginal, output, map, PMF.map_bind]
  rfl

theorem disagreeProb_mapWithSeed_le (A : Algorithm X Ω α m) (f : Ω → α → γ) (D : PMF X) :
    (A.mapWithSeed f).disagreeProb D ≤ A.disagreeProb D := by
  simp only [disagreeProb, pairedOutput, mapWithSeed]
  have hstep (r : Ω) (S₁ S₂ : Fin m → X) :
      (((A.run S₁ r).map (f r)).bind fun y₁ =>
        ((A.run S₂ r).map (f r)).map fun y₂ => (y₁, y₂)).toOuterMeasure {p : γ × γ | p.1 ≠ p.2} ≤
      ((A.run S₁ r).bind fun y₁ =>
        (A.run S₂ r).map fun y₂ => (y₁, y₂)).toOuterMeasure {p : α × α | p.1 ≠ p.2} := by
    have hmap :
        ((A.run S₁ r).map (f r)).bind (fun y₁ =>
          ((A.run S₂ r).map (f r)).map fun y₂ => (y₁, y₂)) =
        ((A.run S₁ r).bind fun y₁ =>
          (A.run S₂ r).map fun y₂ => (y₁, y₂)).map (Prod.map (f r) (f r)) := by
      simp only [PMF.map_bind, PMF.bind_map, PMF.map_comp, Function.comp_def, Prod.map_apply]
    rw [hmap, PMF.toOuterMeasure_map_apply]
    exact MeasureTheory.measure_mono fun p hp hEq => hp (congrArg (f r) hEq)
  have hle :
      (A.seed.bind fun r => (Probability.PMF.iid D m).bind fun S₁ =>
        (Probability.PMF.iid D m).bind fun S₂ =>
          ((A.run S₁ r).map (f r)).bind fun y₁ =>
            ((A.run S₂ r).map (f r)).map fun y₂ => (y₁, y₂)).toOuterMeasure
        {p : γ × γ | p.1 ≠ p.2} ≤
      (A.pairedOutput D).toOuterMeasure {p : α × α | p.1 ≠ p.2} := by
    rw [pairedOutput, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun S₁ => mul_le_mul_of_nonneg_left ?_ zero_le
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    exact tsum_le_tsum fun S₂ => mul_le_mul_of_nonneg_left (hstep r S₁ S₂) zero_le
  exact ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _) hle

theorem disagreeProb_map_le (A : Algorithm X Ω α m) (f : α → γ) (D : PMF X) :
    (A.map f).disagreeProb D ≤ A.disagreeProb D :=
  disagreeProb_mapWithSeed_le A (fun _ => f) D

end Algorithm

/-! ### `ProbComp`-backed shared-seed programs -/

/-- A `ProbComp`-backed randomized sample algorithm: `seed` samples the shared randomness using
finite uniform choices, and `run S r` represents the sample-and-seed step as a `ProbComp`
computation interpreted via `Program.toAlgorithm` (allowing noncomputable real-arithmetic maps). -/
structure Program (X Ω α : Type) (m : ℕ) where
  /-- Program sampling the shared random seed. -/
  seed : ProbComp Ω
  /-- Program executed on the sample and shared seed. -/
  run : (Fin m → X) → Ω → ProbComp α

namespace Program

variable {X Ω α γ : Type} {m : ℕ}

/-- Construct a `Program` whose execution is deterministic once the shared seed is sampled. -/
@[expose] def deterministic (seed : ProbComp Ω) (f : (Fin m → X) → Ω → α) :
    Program X Ω α m where
  seed := seed
  run S r := pure (f S r)

/-- Single execution of `P` on sample `S` as a `ProbComp` program. -/
@[expose] def exec (P : Program X Ω α m) (S : Fin m → X) : ProbComp α := do
  let r ← P.seed
  P.run S r

/-- Paired execution of `P` on two samples `S₁, S₂` sharing one draw of `P.seed`. -/
@[expose] def coupledExec (P : Program X Ω α m) (S₁ S₂ : Fin m → X) : ProbComp (α × α) := do
  let r ← P.seed
  let y₁ ← P.run S₁ r
  let y₂ ← P.run S₂ r
  return (y₁, y₂)

/-- Semantic `Algorithm` obtained by interpreting `P.seed` and `P.run` via `ProbComp.eval`. -/
@[expose] noncomputable def toAlgorithm (P : Program X Ω α m) : Algorithm X Ω α m where
  seed := ProbComp.eval P.seed
  run S r := ProbComp.eval (P.run S r)

theorem eval_exec (P : Program X Ω α m) (S : Fin m → X) :
    ProbComp.eval (P.exec S) = P.toAlgorithm.output S := by
  simp only [exec, ProbComp.eval_bind, toAlgorithm, Algorithm.output]

theorem eval_coupledExec (P : Program X Ω α m) (S₁ S₂ : Fin m → X) :
    ProbComp.eval (P.coupledExec S₁ S₂) =
      (ProbComp.eval P.seed).bind fun r =>
        (ProbComp.eval (P.run S₁ r)).bind fun y₁ =>
          (ProbComp.eval (P.run S₂ r)).map fun y₂ => (y₁, y₂) := by
  simp only [coupledExec, ProbComp.eval_bind, ProbComp.eval_pure]
  rfl

/-- Evaluating the paired `ProbComp` execution over independent samples agrees with
`Algorithm.pairedOutput`. -/
theorem pairedOutput_toAlgorithm (P : Program X Ω α m) (D : PMF X) :
    P.toAlgorithm.pairedOutput D =
      (Probability.PMF.iid D m).bind fun S₁ =>
        (Probability.PMF.iid D m).bind fun S₂ =>
          ProbComp.eval (P.coupledExec S₁ S₂) := by
  simp only [toAlgorithm, Algorithm.pairedOutput, eval_coupledExec]
  rw [PMF.bind_comm]
  refine PMF.bind_congr_on_support _ _ _ fun S₁ _ => ?_
  exact PMF.bind_comm _ _ _

@[simp] theorem toAlgorithm_deterministic (seed : ProbComp Ω) (f : (Fin m → X) → Ω → α) :
    (deterministic seed f).toAlgorithm = Algorithm.deterministic (ProbComp.eval seed) f :=
  rfl

/-- Deterministic post-processing of a `Program`. -/
@[expose] def map (P : Program X Ω α m) (f : α → γ) : Program X Ω γ m where
  seed := P.seed
  run S r := f <$> P.run S r

@[simp] theorem toAlgorithm_map (P : Program X Ω α m) (f : α → γ) :
    (P.map f).toAlgorithm = P.toAlgorithm.map f := by
  simp only [map, toAlgorithm, Algorithm.map, ProbComp.eval_map]

end Program

/-! ### Replicability and accuracy predicates -/

section Replicability

variable {X : Type u} {Ω : Type v} {α : Type w} {γ : Type z} {m : ℕ}

/-- **Weak (distribution-family) `ρ`-replicability**: `A` is `ρ`-replicable over the distribution
family `𝒟` if for every `D ∈ 𝒟`, two runs on independent `m`-samples from `D` sharing `A.seed`
disagree with probability at most `ρ` [ImpagliazzoLeiPitassiSorrell2022]. -/
@[expose] def IsReplicableFor (A : Algorithm X Ω α m) (𝒟 : Set (PMF X)) (ρ : ℝ) : Prop :=
  ∀ D ∈ 𝒟, A.disagreeProb D ≤ ρ

/-- Single-distribution `ρ`-replicability. -/
abbrev IsReplicableOn (A : Algorithm X Ω α m) (D : PMF X) (ρ : ℝ) : Prop :=
  A.disagreeProb D ≤ ρ

/-- **Strong (distribution-free) `ρ`-replicability**: `A` is `ρ`-replicable under all
distributions `D : PMF X` [ImpagliazzoLeiPitassiSorrell2022]. -/
abbrev IsReplicable (A : Algorithm X Ω α m) (ρ : ℝ) : Prop :=
  IsReplicableFor A Set.univ ρ

theorem isReplicableFor_iff_agreeProb {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ} :
    IsReplicableFor A 𝒟 ρ ↔ ∀ D ∈ 𝒟, 1 - ρ ≤ A.agreeProb D := by
  refine forall_congr' fun D => forall_congr' fun _ => ?_
  rw [Algorithm.agreeProb_eq_one_sub_disagreeProb]
  constructor <;> intro h <;> linarith

theorem isReplicable_iff {A : Algorithm X Ω α m} {ρ : ℝ} :
    IsReplicable A ρ ↔ ∀ D : PMF X, A.disagreeProb D ≤ ρ :=
  ⟨fun h D => h D (Set.mem_univ D), fun h D _ => h D⟩

theorem IsReplicableFor.mono {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ ρ' : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (hρ : ρ ≤ ρ') : IsReplicableFor A 𝒟 ρ' :=
  fun D hD => (h D hD).trans hρ

theorem IsReplicableFor.antitone {A : Algorithm X Ω α m} {𝒟 𝒟' : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (h𝒟 : 𝒟' ⊆ 𝒟) : IsReplicableFor A 𝒟' ρ :=
  fun D hD => h D (h𝒟 hD)

theorem IsReplicable.toIsReplicableFor {A : Algorithm X Ω α m} {ρ : ℝ}
    (h : IsReplicable A ρ) (𝒟 : Set (PMF X)) : IsReplicableFor A 𝒟 ρ :=
  h.antitone (Set.subset_univ 𝒟)

theorem IsReplicableFor.toIsReplicableOn {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) {D : PMF X} (hD : D ∈ 𝒟) : IsReplicableOn A D ρ :=
  h D hD

theorem IsReplicableFor.mapWithSeed {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (f : Ω → α → γ) :
    IsReplicableFor (A.mapWithSeed f) 𝒟 ρ :=
  fun D hD => (Algorithm.disagreeProb_mapWithSeed_le A f D).trans (h D hD)

theorem IsReplicableFor.map {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (f : α → γ) :
    IsReplicableFor (A.map f) 𝒟 ρ :=
  fun D hD => (Algorithm.disagreeProb_map_le A f D).trans (h D hD)

/-- **Accuracy over a distribution family**: under `D ∈ 𝒟`, the single-run marginal output fails
the acceptable set `good D` with probability at most `β`. -/
@[expose] def IsAccurateFor (A : Algorithm X Ω α m) (𝒟 : Set (PMF X))
    (good : PMF X → Set α) (β : ℝ) : Prop :=
  ∀ D ∈ 𝒟, ((A.marginal D).toOuterMeasure (good D)ᶜ).toReal ≤ β

/-- Single-distribution accuracy against an acceptable output set `S`. -/
abbrev IsAccurateOn (A : Algorithm X Ω α m) (D : PMF X) (S : Set α) (β : ℝ) : Prop :=
  ((A.marginal D).toOuterMeasure Sᶜ).toReal ≤ β

/-- Strong (distribution-free) accuracy over all distributions. -/
abbrev IsAccurate (A : Algorithm X Ω α m) (good : PMF X → Set α) (β : ℝ) : Prop :=
  IsAccurateFor A Set.univ good β

/-- **`(ε, β)`-estimation accuracy** for real-valued outputs: under every `D ∈ 𝒟`, the output is
within `ε` of `target D` except with probability at most `β`. -/
abbrev EstimatesFor (A : Algorithm X Ω ℝ m) (𝒟 : Set (PMF X)) (target : PMF X → ℝ)
    (ε β : ℝ) : Prop :=
  IsAccurateFor A 𝒟 (fun D => {y | |y - target D| ≤ ε}) β

/-- Strong `(ε, β)`-estimation accuracy over all distributions. -/
abbrev Estimates (A : Algorithm X Ω ℝ m) (target : PMF X → ℝ) (ε β : ℝ) : Prop :=
  EstimatesFor A Set.univ target ε β

theorem isAccurateFor_iff_prob_good {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)}
    {good : PMF X → Set α} {β : ℝ} :
    IsAccurateFor A 𝒟 good β ↔
      ∀ D ∈ 𝒟, 1 - β ≤ ((A.marginal D).toOuterMeasure (good D)).toReal := by
  refine forall_congr' fun D => forall_congr' fun _ => ?_
  have hsum := Probability.PMF.toOuterMeasure_toReal_add_compl (A.marginal D) (good D)
  constructor <;> intro h <;> linarith

theorem IsAccurateFor.mono {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)} {good : PMF X → Set α}
    {β β' : ℝ} (h : IsAccurateFor A 𝒟 good β) (hβ : β ≤ β') : IsAccurateFor A 𝒟 good β' :=
  fun D hD => (h D hD).trans hβ

theorem IsAccurateFor.antitone {A : Algorithm X Ω α m} {𝒟 𝒟' : Set (PMF X)} {good : PMF X → Set α}
    {β : ℝ} (h : IsAccurateFor A 𝒟 good β) (h𝒟 : 𝒟' ⊆ 𝒟) : IsAccurateFor A 𝒟' good β :=
  fun D hD => h D (h𝒟 hD)

theorem IsAccurateFor.map {A : Algorithm X Ω α m} {𝒟 : Set (PMF X)}
    {good : PMF X → Set α} {good' : PMF X → Set γ} {β : ℝ} (f : α → γ)
    (h : IsAccurateFor A 𝒟 good β)
    (hgood : ∀ D ∈ 𝒟, ∀ y ∈ good D, f y ∈ good' D) :
    IsAccurateFor (A.map f) 𝒟 good' β := by
  intro D hD
  rw [Algorithm.marginal_map, PMF.toOuterMeasure_map_apply]
  have hsub : f ⁻¹' (good' D)ᶜ ⊆ (good D)ᶜ := fun y hy hmem => hy (hgood D hD y hmem)
  exact (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((A.marginal D).toOuterMeasure.mono hsub)).trans (h D hD)

theorem EstimatesFor.mono {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)} {target : PMF X → ℝ}
    {ε ε' β β' : ℝ} (h : EstimatesFor A 𝒟 target ε β) (hε : ε ≤ ε') (hβ : β ≤ β') :
    EstimatesFor A 𝒟 target ε' β' := by
  intro D hD
  have hsub : {y | |y - target D| ≤ ε'}ᶜ ⊆ {y | |y - target D| ≤ ε}ᶜ := fun y hy hle =>
    hy (hle.trans hε)
  exact (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    ((A.marginal D).toOuterMeasure.mono hsub)).trans ((h D hD).trans hβ)

theorem EstimatesFor.antitone {A : Algorithm X Ω ℝ m} {𝒟 𝒟' : Set (PMF X)} {target : PMF X → ℝ}
    {ε β : ℝ} (h : EstimatesFor A 𝒟 target ε β) (h𝒟 : 𝒟' ⊆ 𝒟) :
    EstimatesFor A 𝒟' target ε β :=
  IsAccurateFor.antitone h h𝒟

end Replicability

end Cslib.MachineLearning.Replicable
