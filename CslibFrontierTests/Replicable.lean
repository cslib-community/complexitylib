/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.Replicable.Amplification
import CslibFrontier.MachineLearning.Replicable.Basic
import CslibFrontier.MachineLearning.Replicable.BiasEstimation
import CslibFrontier.MachineLearning.Replicable.Composition
import CslibFrontier.MachineLearning.Replicable.Rounding
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Uniform

/-! Nonvacuous checks and counterexamples for replicable learning algorithms:
* exact disagreement `1 / 2` and non-replicability of a naive single-coin sampler on a fair coin;
* weak (distribution-family) vs strong (distribution-free) replicability separation;
* composition of replicability under `seqPair`, `seqBind`, and `replicate`;
* discrete (`Fin 4`, `Fin 8`) and continuous (`[0, 1)`) randomized-threshold and grid rounding;
* replicable coin-bias and bounded-mean estimation (`replicableBiasProg`, `replicableMeanProg`);
* confidence amplification (`majorityVote`, `medianOfRuns`), finite-domain heavy-hitter
  amplification (`amplifyFinite`) turning a non-replicable sampler into a strongly replicable one,
  and general-domain collision-threshold amplification (`amplifyReplicability`) on `ℤ`. -/

namespace CslibFrontierTests.Replicable

open Cslib.MachineLearning.Replicable
open scoped ENNReal

section CounterexampleAndSeparation

/-- A fair Boolean coin distribution. -/
noncomputable def fairCoin : PMF Bool :=
  Cslib.Probability.PMF.uniformOfFintype Bool

private theorem fairCoin_apply (b : Bool) : fairCoin b = (2⁻¹ : ℝ≥0∞) := by
  simp [fairCoin, Cslib.Probability.PMF.uniformOfFintype]

/-- Naive algorithm that ignores its shared seed and returns its first sample bit. -/
noncomputable def sampleFirstAlg : Algorithm Bool Unit Bool 1 where
  seed := PMF.pure ()
  run S _ := PMF.pure (S 0)

private theorem marginal_sampleFirstAlg (D : PMF Bool) : sampleFirstAlg.marginal D = D := by
  rw [Algorithm.marginal_eq_seed_bind]
  simp only [sampleFirstAlg, PMF.pure_bind]
  have hiid : Cslib.Probability.PMF.iid D 1 = PMF.map (fun x : Bool => fun _ : Fin 1 => x) D := by
    ext S
    rw [Cslib.Probability.PMF.iid_apply, Fin.prod_univ_one]
    rw [PMF.map_apply, tsum_eq_single (S 0)]
    · simp only [funext_iff, Fin.forall_fin_one, ↓reduceIte]
    · intro x hx
      have hne : S ≠ (fun _ : Fin 1 => x) := by
        intro h
        exact hx (by simpa using (congrFun h 0).symm)
      simp [hne]
  rw [hiid, PMF.bind_map]
  exact PMF.map_id D

/-- Exact disagreement probability `1 / 2` of `sampleFirstAlg` on `fairCoin`. -/
theorem disagreeProb_sampleFirstAlg_fairCoin :
    sampleFirstAlg.disagreeProb fairCoin = 1 / 2 := by
  rw [Algorithm.disagreeProb]
  have hpair : sampleFirstAlg.pairedOutput fairCoin =
      fairCoin.bind fun b₁ => fairCoin.map fun b₂ => (b₁, b₂) := by
    simp only [Algorithm.pairedOutput, sampleFirstAlg, PMF.pure_bind]
    have hrun : ∀ D : PMF Bool,
        ((Cslib.Probability.PMF.iid D 1).bind fun S => PMF.pure (S 0)) = D := by
      intro D
      have h := marginal_sampleFirstAlg D
      simpa [Algorithm.marginal_eq_seed_bind, sampleFirstAlg, PMF.pure_bind] using h
    have hinner : ∀ b₁ : Bool,
        ((Cslib.Probability.PMF.iid fairCoin 1).bind fun S₂ => PMF.map (fun b₂ => (b₁, b₂))
          (PMF.pure (S₂ 0))) = fairCoin.map fun b₂ => (b₁, b₂) := by
      intro b₁
      calc ((Cslib.Probability.PMF.iid fairCoin 1).bind fun S₂ =>
              PMF.map (fun b₂ => (b₁, b₂)) (PMF.pure (S₂ 0)))
          = PMF.map (fun b₂ => (b₁, b₂))
              ((Cslib.Probability.PMF.iid fairCoin 1).bind fun S₂ => PMF.pure (S₂ 0)) := by
            rw [PMF.map_bind]
        _ = fairCoin.map fun b₂ => (b₁, b₂) := by rw [hrun fairCoin]
    calc ((Cslib.Probability.PMF.iid fairCoin 1).bind fun S₁ =>
            (Cslib.Probability.PMF.iid fairCoin 1).bind fun S₂ =>
              PMF.map (fun b₂ => (S₁ 0, b₂)) (PMF.pure (S₂ 0)))
        = (Cslib.Probability.PMF.iid fairCoin 1).bind fun S₁ =>
            fairCoin.map fun b₂ => (S₁ 0, b₂) := by
          refine congrArg (PMF.bind (Cslib.Probability.PMF.iid fairCoin 1)) (funext fun S₁ => ?_)
          exact hinner (S₁ 0)
      _ = ((Cslib.Probability.PMF.iid fairCoin 1).bind fun S₁ => PMF.pure (S₁ 0)).bind fun b₁ =>
            fairCoin.map fun b₂ => (b₁, b₂) := by
          rw [PMF.bind_bind]
          simp only [PMF.pure_bind]
      _ = fairCoin.bind fun b₁ => fairCoin.map fun b₂ => (b₁, b₂) := by rw [hrun fairCoin]
  rw [hpair, PMF.toOuterMeasure_apply, tsum_fintype]
  have hdiag : ∀ b₁ b₂ : Bool,
      (fairCoin.bind fun x₁ => fairCoin.map fun x₂ => (x₁, x₂)) (b₁, b₂) =
        fairCoin b₁ * fairCoin b₂ := by
    intro b₁ b₂
    rw [PMF.bind_apply, tsum_eq_single b₁]
    · rw [PMF.map_apply, tsum_eq_single b₂]
      · simp
      · intro x hx
        have hneq : (b₁, b₂) ≠ (b₁, x) := by simp [Ne.symm hx]
        simp [hneq]
    · intro x hx
      have hzero : (fairCoin.map fun x₂ => (x, x₂)) (b₁, b₂) = 0 := by
        rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_zero]
        intro x₂ _
        have hneq : (b₁, b₂) ≠ (x, x₂) := by simp [Ne.symm hx]
        simp [hneq]
      simp [hzero]
  rw [ENNReal.toReal_sum fun p _ => by
    rcases p with ⟨b₁, b₂⟩
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top]
  rw [Fintype.sum_prod_type]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hdiag, fairCoin_apply, Fintype.sum_bool]
  norm_num

/-- Counterexample: `sampleFirstAlg` fails `1 / 4`-replicability even on `{fairCoin}`, and hence
fails strong `1 / 4`-replicability. -/
theorem not_replicable_sampleFirstAlg :
    ¬ IsReplicableFor sampleFirstAlg {fairCoin} (1 / 4) ∧
    ¬ IsReplicable sampleFirstAlg (1 / 4) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hle := h fairCoin rfl
    rw [disagreeProb_sampleFirstAlg_fairCoin] at hle
    norm_num at hle
  · intro h
    have hle := h fairCoin trivial
    rw [disagreeProb_sampleFirstAlg_fairCoin] at hle
    norm_num at hle

/-- Weak vs strong replicability separation: `sampleFirstAlg` is `0`-replicable on point-mass
coins `{PMF.pure true, PMF.pure false}`, yet not strongly `1 / 4`-replicable. -/
theorem weak_vs_strong_separation :
    IsReplicableFor sampleFirstAlg {PMF.pure true, PMF.pure false} 0 ∧
    ¬ IsReplicable sampleFirstAlg (1 / 4) := by
  refine ⟨?_, not_replicable_sampleFirstAlg.2⟩
  intro D hD
  have hpure : ∀ b : Bool, sampleFirstAlg.disagreeProb (PMF.pure b) ≤ 0 := by
    intro b
    rw [Algorithm.disagreeProb]
    have hpair : sampleFirstAlg.pairedOutput (PMF.pure b) = PMF.pure (b, b) := by
      have hiid : Cslib.Probability.PMF.iid (PMF.pure b) 1 = PMF.pure (fun _ : Fin 1 => b) := by
        ext S
        rw [Cslib.Probability.PMF.iid_apply, Fin.prod_univ_one, PMF.pure_apply, PMF.pure_apply]
        by_cases hS : S = fun _ => b
        · simp [hS]
        · have h0 : S 0 ≠ b := fun hb => hS (funext fun i => by fin_cases i; exact hb)
          simp [hS, h0]
      simp only [Algorithm.pairedOutput, sampleFirstAlg, hiid, PMF.pure_bind, PMF.pure_map]
    rw [hpair, PMF.toOuterMeasure_apply, tsum_eq_single (b, b)]
    · simp
    · intro p hp
      have h0 : (PMF.pure (b, b)) p = 0 := by
        simp [PMF.pure_apply, hp]
      simp [h0]
  rcases hD with rfl | rfl <;> exact hpure _

end CounterexampleAndSeparation

section RoundingAndComposition

/-- Exact disagreement probability `1 / 4` of `thresholdRound 0 1 4` between `3 / 8` and `5 / 8`,
together with the general bound `thresholdRound_disagree_le`. -/
theorem thresholdRound_concrete_example :
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).toOuterMeasure
      {i : Fin 4 | thresholdRound 0 1 4 i (3 / 8) ≠ thresholdRound 0 1 4 i (5 / 8)}).toReal =
      1 / 4 ∧
    ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).toOuterMeasure
      {i : Fin 4 | thresholdRound 0 1 4 i (3 / 8) ≠ thresholdRound 0 1 4 i (5 / 8)}).toReal ≤
      2 * (1 / 4 : ℝ) / (1 - 0) + 1 / 4 := by
  have hexact : ((Cslib.Probability.PMF.uniformOfFintype (Fin 4)).toOuterMeasure
      {i : Fin 4 | thresholdRound 0 1 4 i (3 / 8) ≠ thresholdRound 0 1 4 i (5 / 8)}).toReal =
      1 / 4 := by
    rw [Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
    have hfilter : (Finset.univ.filter fun x : Fin 4 =>
        x ∈ ({i : Fin 4 | thresholdRound 0 1 4 i (3 / 8) ≠
          thresholdRound 0 1 4 i (5 / 8)} : Set (Fin 4))) = {2} := by
      ext i
      fin_cases i <;> simp [thresholdRound, thresholdValue] <;> norm_num
    rw [hfilter, Finset.card_singleton]
    norm_num
  exact ⟨hexact, by
    refine (thresholdRound_disagree_le (by norm_num : (0 : ℝ) < 1) (3 / 8) (5 / 8)).trans ?_
    norm_num⟩

/-- Continuous `[0, 1)` Lebesgue rounding bound instantiated at `(3 / 8, 5 / 8)`. -/
theorem continuousThresholdRound_concrete :
    (MeasureTheory.volume
      {u : ℝ | u ∈ Set.Ico (0 : ℝ) 1 ∧
        continuousThresholdRound 0 1 u (3 / 8) ≠ continuousThresholdRound 0 1 u (5 / 8)}).toReal ≤
      1 / 4 := by
  have hvol := volume_thresholdRound_ne_le (by norm_num : (0 : ℝ) < 1) (3 / 8) (5 / 8)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rw [ENNReal.toReal_ofReal (by norm_num)] at hreal
  refine hreal.trans ?_
  norm_num

/-- Grid rounding accuracy, `seqPair` composition, and `replicate` composition. -/
theorem roundGrid_concrete_and_composition :
    (∀ i : Fin 8, ∀ x : ℝ, |roundGrid 1 8 i x - x| ≤ 1 / 2) ∧
    IsReplicable
      ((roundGridProg (1 : ℝ) 8 (fun _ : Fin 4 → Bool => (0 : ℝ))).toAlgorithm.seqPair
        (roundGridProg (1 : ℝ) 8 (fun _ : Fin 4 → Bool => (0 : ℝ))).toAlgorithm.seed
        (fun a => (roundGridProg (1 : ℝ) 8 (fun _ : Fin 4 → Bool => a)).toAlgorithm.run))
      (1 / 4) ∧
    IsReplicable
      ((roundGridProg (1 : ℝ) 8 (fun _ : Fin 4 → Bool => (0 : ℝ))).toAlgorithm.replicate 3)
      (3 / 8) := by
  have hconc : ∀ a : ℝ,
      IsReplicable (roundGridProg (1 : ℝ) 8 (fun _ : Fin 4 → Bool => a)).toAlgorithm (1 / 8) := by
    intro a
    refine (isReplicableFor_roundGridProg_of_concentrates (δ := (0 : ℝ)) (β := (0 : ℝ))
      (by norm_num : (0 : ℝ) < 1) 8 (fun _ : Fin 4 → Bool => a) Set.univ (fun _ => a)
      le_rfl le_rfl fun D _ => by simp).mono (by norm_num)
  have h1 := hconc 0
  refine ⟨fun i x => (abs_roundGrid_sub_le (by norm_num : (0 : ℝ) < 1) 8 i x).trans (by norm_num),
    ?_, ?_⟩
  · have hcomp := h1.seqPair (by norm_num : (0 : ℝ) ≤ 1 / 8) fun a D _ => by
      exact hconc a D trivial
    intro D hD
    exact (hcomp D hD).trans (by norm_num)
  · have hrep := h1.replicate (k := 3)
    intro D hD
    exact (hrep D hD).trans (by norm_num)

end RoundingAndComposition

section BiasEstimationTests

/-- Concrete nonvacuous coin bias estimation client with `w = 1 / 4`, `N = 8`, `m = 200`. -/
theorem concrete_replicableBiasProg_check :
    IsReplicable (replicableBiasProg (1 / 4) 8 200).toAlgorithm
      (2 * (1 / 16 : ℝ) / (1 / 4) + 1 / 8 +
        2 * (2 * Real.exp (-2 * (200 : ℝ) * (1 / 16 : ℝ) ^ 2))) ∧
    Estimates (replicableBiasProg (1 / 4) 8 200).toAlgorithm coinBias
      (1 / 4 / 2 + 1 / 16) (2 * Real.exp (-2 * (200 : ℝ) * (1 / 16 : ℝ) ^ 2)) :=
  ⟨isReplicable_replicableBiasProg (by norm_num) (by norm_num) 8 200,
   estimates_replicableBiasProg (by norm_num) (by norm_num) 8 200⟩

/-- Existential parameter synthesis for `replicableBiasProg` at `(ε, ρ, β) = (1/10, 1/10, 1/10)`. -/
theorem exists_replicableBiasProg_concrete :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableBiasProg w N m).toAlgorithm (1 / 10) ∧
      Estimates (replicableBiasProg w N m).toAlgorithm coinBias (1 / 10) (1 / 10) :=
  exists_replicableBiasProg (by norm_num) (by norm_num) (by norm_num)

/-- Existential parameter synthesis for bounded-mean estimation on `Fin 3` at `(1/5, 1/5, 1/5)`. -/
theorem exists_replicableMeanProg_fin3 :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableMeanProg (fun i : Fin 3 => (i : ℝ) / 2) w N m).toAlgorithm (1 / 5) ∧
      Estimates (replicableMeanProg (fun i : Fin 3 => (i : ℝ) / 2) w N m).toAlgorithm
        (fun D => distExpectation D (fun i : Fin 3 => (i : ℝ) / 2)) (1 / 5) (1 / 5) :=
  exists_replicableMeanProg (a := (0 : ℝ)) (b := (1 : ℝ)) (fun i : Fin 3 => (i : ℝ) / 2)
    (fun i => ⟨by positivity, by
      have hi : (i : ℝ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp i.isLt
      linarith⟩)
    (by norm_num) (by norm_num) (by norm_num)

end BiasEstimationTests

section AmplificationTests

/-- Boolean majority confidence amplification reduces error `1 / 4` to `≤ 1 / 100`. -/
theorem majorityVote_concrete_check :
    IsAccurateFor (majorityVote sampleFirstAlg 5)
      {D : PMF Bool | (D.toOuterMeasure ({true} : Set Bool)ᶜ).toReal ≤ 1 / 4}
      (fun _ => {true}) (1 / 4) ∧
    ∃ r : ℕ, IsAccurateFor (majorityVote sampleFirstAlg r)
      {D : PMF Bool | (D.toOuterMeasure ({true} : Set Bool)ᶜ).toReal ≤ 1 / 4}
      (fun _ => {true}) (1 / 100) := by
  have hbase : IsAccurateFor sampleFirstAlg
      {D : PMF Bool | (D.toOuterMeasure ({true} : Set Bool)ᶜ).toReal ≤ 1 / 4}
      (fun _ => {true}) (1 / 4) := by
    intro D hD
    rw [marginal_sampleFirstAlg]
    exact hD
  refine ⟨?_, exists_majorityVote hbase (by norm_num) (by norm_num) (by norm_num)⟩
  exact (majorityVote_accurate hbase (by norm_num) 5).mono (by norm_num)

/-- Real median-of-runs confidence amplification reduces failure `1 / 4` to `≤ 1 / 100`. -/
theorem medianOfRuns_concrete_check {X Ω : Type} {m : ℕ} (A : Algorithm X Ω ℝ m)
    {𝒟 : Set (PMF X)} {target : PMF X → ℝ}
    (hA : EstimatesFor A 𝒟 target (1 / 2) (1 / 4)) :
    EstimatesFor (medianOfRuns A 5) 𝒟 target (1 / 2) (1 / 4) ∧
    ∃ r : ℕ, EstimatesFor (medianOfRuns A r) 𝒟 target (1 / 2) (1 / 100) :=
  ⟨(medianOfRuns_accurate hA (by norm_num) 5).mono le_rfl (by norm_num),
   exists_medianOfRuns hA (by norm_num) (by norm_num) (by norm_num)⟩

/-- Finite-domain heavy-hitter amplification turns the unreplicable `sampleFirstAlg` (which has
disagreement `1 / 2` on `fairCoin`) into a **strongly** `1 / 10`-replicable and `(1 / 10)`-accurate
algorithm on biased coins `D true ≥ 7 / 8` (where `β₀ = 1 / 8 < 1 / (|Bool| + 1) = 1 / 3`). -/
theorem amplifyFinite_from_unreplicable :
    ∃ (a b : ℝ) (k N : ℕ) (_ : NeZero k) (_ : NeZero N),
      IsReplicable (amplifyFinite sampleFirstAlg a b k N) (1 / 10) ∧
      IsAccurateFor (amplifyFinite sampleFirstAlg a b k N)
        {D : PMF Bool | (D.toOuterMeasure ({true} : Set Bool)ᶜ).toReal ≤ 1 / 8}
        (fun _ => {true}) (1 / 10) := by
  have hbase : IsAccurateFor sampleFirstAlg
      {D : PMF Bool | (D.toOuterMeasure ({true} : Set Bool)ᶜ).toReal ≤ 1 / 8}
      (fun _ => {true}) (1 / 8) := by
    intro D hD
    rw [marginal_sampleFirstAlg]
    exact hD
  exact exists_amplifyFinite sampleFirstAlg hbase (by norm_num)
    (by simp [Fintype.card_bool]; norm_num) (by norm_num) (by norm_num)

/-- General-domain amplification on infinite `[DecidableEq ℤ]` amplifies `1 / 10`-replicability
to `1 / 100`-replicability. -/
theorem amplifyReplicability_int_check {X Ω : Type} {m : ℕ} (A : Algorithm X Ω ℤ m)
    {𝒟 : Set (PMF X)} (hA : IsReplicableFor A 𝒟 (1 / 10)) :
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₂) (_ : NeZero N),
      IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 (1 / 100) :=
  exists_amplifyReplicability A hA (by norm_num) (by norm_num) (by norm_num)

end AmplificationTests

end CslibFrontierTests.Replicable
