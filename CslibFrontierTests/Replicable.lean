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

section

open Cslib.Probability.PMF

private noncomputable def sampleBoolThresholdProg : Program Bool (Fin 4) Bool 1 :=
  thresholdProg (3 / 8 : ℝ) (5 / 8 : ℝ) 4 fun S => if S 0 then 3 / 4 else 1 / 4

/-- `thresholdProg` executes deterministically via `Program.exec` outside the interval and obeys
`thresholdRound_disagree_le` inside `(3 / 8, 5 / 8)`. -/
theorem thresholdProg_concrete_check :
    (sampleBoolThresholdProg.exec (fun _ => true)).eval = PMF.pure true ∧
    (sampleBoolThresholdProg.exec (fun _ => false)).eval = PMF.pure false ∧
    ((uniformOfFintype (Fin 4)).toOuterMeasure
        {i | thresholdRound (3 / 8) (5 / 8) 4 i (7 / 16) ≠
          thresholdRound (3 / 8) (5 / 8) 4 i (9 / 16)}).toReal ≤ 3 / 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Program.eval_exec, Algorithm.output, sampleBoolThresholdProg, thresholdProg,
      Program.toAlgorithm_deterministic]
    simp only [Algorithm.deterministic, ite_true]
    have hconst : ∀ i : Fin 4, thresholdRound (3 / 8) (5 / 8) 4 i (3 / 4) = true :=
      fun i => thresholdRound_true_of_right_le (by norm_num) i (by norm_num)
    simp only [hconst, PMF.bind_const]
  · rw [Program.eval_exec, Algorithm.output, sampleBoolThresholdProg, thresholdProg,
      Program.toAlgorithm_deterministic]
    simp only [Algorithm.deterministic, Bool.false_eq_true, ↓reduceIte]
    have hconst : ∀ i : Fin 4, thresholdRound (3 / 8) (5 / 8) 4 i (1 / 4) = false :=
      fun i => thresholdRound_false_of_lt_left (by norm_num) i (by norm_num)
    simp only [hconst, PMF.bind_const]
  · have h := thresholdRound_disagree_le (a := (3 / 8 : ℝ)) (b := 5 / 8)
      (by norm_num) (N := 4) (7 / 16) (9 / 16)
    linarith [h]

/-- `continuousRoundGrid` stays within half a bin width and separates `7 / 16` from `1 / 2` on
a measurable set of `[0, 1)` of Lebesgue measure at most `1 / 4`. -/
theorem continuousRoundGrid_concrete_check :
    (∀ u x : ℝ, |continuousRoundGrid (1 / 4) u x - x| ≤ (1 / 4 : ℝ) / 2) ∧
    continuousRoundGrid (1 / 4) (1 / 8) (7 / 16) ≠
      continuousRoundGrid (1 / 4) (1 / 8) (1 / 2) ∧
    MeasureTheory.volume
        {u | u ∈ Set.Ico 0 1 ∧
          continuousRoundGrid (1 / 4) u (7 / 16) ≠
            continuousRoundGrid (1 / 4) u (1 / 2)} ≤
      ENNReal.ofReal (1 / 4) := by
  refine ⟨fun u x => abs_continuousRoundGrid_sub_le (w := (1 / 4 : ℝ)) (by norm_num) u x, ?_, ?_⟩
  · simp only [continuousRoundGrid, continuousRoundGridBin]
    have hfl1 : (⌊(7 / 16 : ℝ) / (1 / 4) + 1 / 8⌋ : ℤ) = 1 := by
      rw [Int.floor_eq_iff]; norm_num
    have hfl2 : (⌊(1 / 2 : ℝ) / (1 / 4) + 1 / 8⌋ : ℤ) = 2 := by
      rw [Int.floor_eq_iff]; norm_num
    rw [hfl1, hfl2]
    norm_num
  · have h := volume_roundGrid_ne_le (w := (1 / 4 : ℝ)) (by norm_num) (7 / 16) (1 / 2)
    refine h.trans (ENNReal.ofReal_le_ofReal ?_)
    norm_num

private theorem uniformFin_bind_toOuterMeasure_le {α : Type} (K : ℕ) [NeZero K]
    (g : Fin K → PMF α) (s : Set α)
    (hzero : ∀ r : Fin K, r ≠ 0 → (g r).toOuterMeasure s = 0) :
    (((uniformOfFintype (Fin K)).bind g).toOuterMeasure s).toReal ≤ 1 / (K : ℝ) := by
  have hle : ((uniformOfFintype (Fin K)).bind g).toOuterMeasure s ≤ (K : ENNReal)⁻¹ := by
    rw [PMF.toOuterMeasure_bind_apply]
    calc
      ∑' r : Fin K, (uniformOfFintype (Fin K)) r * (g r).toOuterMeasure s
          ≤ ∑' r : Fin K, if r = 0 then (uniformOfFintype (Fin K)) 0 * 1 else 0 := by
            refine tsum_le_tsum fun r => ?_
            by_cases hr : r = 0
            · subst hr
              simp only [↓reduceIte]
              refine mul_le_mul_right ?_ _
              have hle1 : (g 0).toOuterMeasure s ≤ (g 0).toOuterMeasure Set.univ :=
                MeasureTheory.OuterMeasure.mono _ (Set.subset_univ _)
              simpa [PMF.toOuterMeasure_apply, PMF.tsum_coe] using hle1
            · simp only [hr, ↓reduceIte, hzero r hr, mul_zero, le_refl]
      _ = (K : ENNReal)⁻¹ := by
            rw [tsum_ite_eq, mul_one, uniformOfFintype_apply, Fintype.card_fin]
  have hreal := ENNReal.toReal_mono (by simp [NeZero.ne K]) hle
  simpa [one_div] using hreal

private noncomputable def constExceptZeroAlg {X α : Type} (K m : ℕ) [NeZero K]
    (d : α) (f : (Fin m → X) → α) : Algorithm X (Fin K) α m where
  seed := uniformOfFintype (Fin K)
  run S r := PMF.pure (if r.val = 0 then f S else d)

private theorem isReplicableFor_constExceptZeroAlg {X α : Type} (K m : ℕ) [NeZero K]
    (d : α) (f : (Fin m → X) → α) (𝒟 : Set (PMF X)) :
    IsReplicableFor (constExceptZeroAlg K m d f) 𝒟 (1 / (K : ℝ)) := by
  intro D _
  rw [Algorithm.disagreeProb]
  dsimp [Algorithm.pairedOutput, constExceptZeroAlg]
  refine uniformFin_bind_toOuterMeasure_le K _ {p : α × α | ¬p.1 = p.2} fun r hr => ?_
  have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
  simp only [hr0, ↓reduceIte, PMF.pure_bind, PMF.map, Function.comp_apply, PMF.bind_const]
  rw [PMF.toOuterMeasure_pure_apply]
  simp

private theorem isAccurateFor_constExceptZeroAlg {X α : Type} (K m : ℕ) [NeZero K]
    (d : α) (f : (Fin m → X) → α) (𝒟 : Set (PMF X)) :
    IsAccurateFor (constExceptZeroAlg K m d f) 𝒟 (fun _ => {d}) (1 / (K : ℝ)) := by
  intro D _
  rw [Algorithm.marginal_eq_seed_bind]
  dsimp [constExceptZeroAlg]
  refine uniformFin_bind_toOuterMeasure_le K _ ({d}ᶜ) fun r hr => ?_
  have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
  simp [hr0, PMF.bind_const, PMF.toOuterMeasure_apply]

/-- Composition operators `Algorithm.pad`, `Algorithm.seqBind`, and `Algorithm.pi` preserve
replicability, accuracy (for `pad`), and product marginal structure. -/
theorem composition_pad_seqBind_pi_check :
    let A : Algorithm Bool (Fin 8) Bool 1 := constExceptZeroAlg 8 1 true fun S => S 0
    let B : Algorithm Bool (Fin 8) Bool 1 := constExceptZeroAlg 8 1 false fun S => !S 0
    let F : Fin 2 → Algorithm Bool (Fin 8) Bool 1 := fun j => if j = (0 : Fin 2) then A else B
    IsReplicableFor (A.pad (by omega : 1 ≤ 3)) {fairCoin} (1 / 8) ∧
    IsAccurateFor (A.pad (by omega : 1 ≤ 3)) {fairCoin} (fun _ => {true}) (1 / 8) ∧
    (A.pad (by omega : 1 ≤ 3)).disagreeProb fairCoin = A.disagreeProb fairCoin ∧
    (A.pad (by omega : 1 ≤ 3)).marginal fairCoin = A.marginal fairCoin ∧
    IsReplicableFor (A.seqBind (uniformOfFintype (Fin 8)) fun a (S : Fin 1 → Bool) r =>
      PMF.pure (if r.val = 0 then a && S 0 else true)) {fairCoin} (1 / 4) ∧
    IsReplicableFor (Algorithm.pi F) {fairCoin} (1 / 4) ∧
    (Algorithm.pi F).marginal fairCoin =
      pmfPiFin fun j : Fin 2 => (F j).marginal fairCoin := by
  intro A B F
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isReplicableFor_constExceptZeroAlg 8 1 true (fun S => S 0) {fairCoin}).pad (by omega)
  · exact (isAccurateFor_constExceptZeroAlg 8 1 true (fun S => S 0) {fairCoin}).pad (by omega)
  · exact A.disagreeProb_pad (by omega) fairCoin
  · exact A.marginal_pad (by omega) fairCoin
  · have hA : IsReplicableFor A {fairCoin} (1 / 8) :=
      isReplicableFor_constExceptZeroAlg 8 1 true (fun S => S 0) {fairCoin}
    have h2 : ∀ a : Bool,
        IsReplicableFor
          ({ seed := uniformOfFintype (Fin 8),
             run := fun S r => PMF.pure (if r.val = 0 then a && S 0 else true) } :
            Algorithm Bool (Fin 8) Bool 1) {fairCoin} (1 / 8) :=
      fun a => isReplicableFor_constExceptZeroAlg 8 1 true (fun S => a && S 0) {fairCoin}
    have hbind := hA.seqBind (by norm_num : (0 : ℝ) ≤ 1 / 8) h2
    intro D' hD'
    exact (hbind D' hD').trans (by norm_num)
  · have hpi := IsReplicableFor.pi (A := F) (𝒟 := {fairCoin}) (ρ := fun _ => (1 / 8 : ℝ))
        fun j => by
      fin_cases j
      · simpa [F] using isReplicableFor_constExceptZeroAlg 8 1 true (fun S => S 0) {fairCoin}
      · simpa [F] using isReplicableFor_constExceptZeroAlg 8 1 false (fun S => !S 0) {fairCoin}
    intro D' hD'
    refine (hpi D' hD').trans ?_
    norm_num
  · exact Algorithm.marginal_pi F fairCoin

end

end RoundingAndComposition

section BiasEstimationTests

/-- Concrete nonvacuous coin bias estimation client with `w = 1 / 4`, `N = 8`, `m = 4096`
(yielding nontrivial strong `59 / 72`-replicability `< 1` and
`(5 / 32, 2 / 9)` estimation accuracy). -/
theorem concrete_replicableBiasProg_check :
    IsReplicable (replicableBiasProg (1 / 4) 8 4096).toAlgorithm (59 / 72 : ℝ) ∧
    Estimates (replicableBiasProg (1 / 4) 8 4096).toAlgorithm coinBias
      (5 / 32 : ℝ) (2 / 9 : ℝ) := by
  have hexp : Real.exp (-2 * (4096 : ℝ) * (1 / 32 : ℝ) ^ 2) ≤ 1 / 9 := by
    have hpow : (9 : ℝ) ≤ Real.exp 8 := by
      linarith [Real.add_one_le_exp (8 : ℝ)]
    have hnorm : (-2 * (4096 : ℝ) * (1 / 32 : ℝ) ^ 2) = -(8 : ℝ) := by norm_num
    rw [hnorm, Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hpow)
  have hrep := isReplicable_replicableBiasProg (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 32) 8 4096
  have hest := estimates_replicableBiasProg (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 1 / 32) 8 4096
  refine ⟨hrep.mono (by linarith), hest.mono (by norm_num) (by linarith)⟩

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
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N),
      IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 (1 / 100) :=
  exists_amplifyReplicability A hA (by norm_num) (by norm_num) (by norm_num)

section

open Cslib.Probability.PMF

private noncomputable def nontrivialIntAlg (K : ℕ) [NeZero K] : Algorithm Bool (Fin K) ℤ 1 :=
  constExceptZeroAlg K 1 (1 : ℤ) fun S => if S 0 then 1 else 2

private theorem pmf_bind_apply_ge {α β : Type} (p : PMF α) (f : α → PMF β) (a : α) (b : β) :
    p a * f a b ≤ (p.bind f) b := by
  rw [PMF.bind_apply]
  exact le_tsum (fun x => p x * f x b) a

private theorem disagreeProb_nontrivialIntAlg_pos (K : ℕ) [NeZero K] :
    0 < (nontrivialIntAlg K).disagreeProb fairCoin := by
  let A := nontrivialIntAlg K
  have h0 := pmf_bind_apply_ge A.seed
    (fun r => (iid fairCoin 1).bind fun S₁ => (iid fairCoin 1).bind fun S₂ =>
      (A.run S₁ r).bind fun y₁ => (A.run S₂ r).map fun y₂ => (y₁, y₂))
    (0 : Fin K) (1, 2)
  have h1 := pmf_bind_apply_ge (iid fairCoin 1)
    (fun S₁ => (iid fairCoin 1).bind fun S₂ =>
      (A.run S₁ 0).bind fun y₁ => (A.run S₂ 0).map fun y₂ => (y₁, y₂))
    (fun _ => true) (1, 2)
  have h2 := pmf_bind_apply_ge (iid fairCoin 1)
    (fun S₂ => (A.run (fun _ => true) 0).bind fun y₁ =>
      (A.run S₂ 0).map fun y₂ => (y₁, y₂))
    (fun _ => false) (1, 2)
  have hterm : ((A.run (fun _ => true) 0).bind fun y₁ =>
      (A.run (fun _ => false) 0).map fun y₂ => (y₁, y₂)) (1, 2) = 1 := by
    simp [A, nontrivialIntAlg, constExceptZeroAlg, PMF.pure_bind, PMF.map]
  have hS1 : (iid fairCoin 1) (fun _ => true) = (1 / 2 : ENNReal) := by
    rw [iid_apply, Fin.prod_univ_one]
    simp [fairCoin]
  have hS2 : (iid fairCoin 1) (fun _ => false) = (1 / 2 : ENNReal) := by
    rw [iid_apply, Fin.prod_univ_one]
    simp [fairCoin]
  have hK : A.seed 0 = (K : ENNReal)⁻¹ := by
    simp [A, nontrivialIntAlg, constExceptZeroAlg, uniformOfFintype_apply]
  have hlower : (K : ENNReal)⁻¹ * ((1 / 2 : ENNReal) * (1 / 2 : ENNReal)) ≤
      (A.pairedOutput fairCoin) (1, 2) := by
    rw [hterm, mul_one, hS2] at h2
    rw [hS1] at h1
    rw [hK] at h0
    calc (K : ENNReal)⁻¹ * ((1 / 2 : ENNReal) * (1 / 2 : ENNReal))
        ≤ (K : ENNReal)⁻¹ * ((1 / 2 : ENNReal) *
            ((iid fairCoin 1).bind fun S₂ =>
              (A.run (fun _ => true) 0).bind fun y₁ =>
                (A.run S₂ 0).map fun y₂ => (y₁, y₂)) (1, 2)) := by
          gcongr
      _ ≤ (K : ENNReal)⁻¹ *
            ((iid fairCoin 1).bind fun S₁ => (iid fairCoin 1).bind fun S₂ =>
              (A.run S₁ 0).bind fun y₁ => (A.run S₂ 0).map fun y₂ => (y₁, y₂)) (1, 2) := by
          gcongr
      _ ≤ (A.pairedOutput fairCoin) (1, 2) := h0
  have hpos : 0 < (A.pairedOutput fairCoin) (1, 2) := by
    refine lt_of_lt_of_le ?_ hlower
    refine ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top K)) ?_
    exact ne_of_gt (ENNReal.mul_pos (by norm_num) (by norm_num))
  have hle : (A.pairedOutput fairCoin) (1, 2) ≤
      (A.pairedOutput fairCoin).toOuterMeasure {p | p.1 ≠ p.2} := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    exact MeasureTheory.OuterMeasure.mono _ (Set.singleton_subset_iff.mpr (by norm_num))
  have hne : (A.pairedOutput fairCoin).toOuterMeasure {p | p.1 ≠ p.2} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (le_trans (MeasureTheory.OuterMeasure.mono _ (Set.subset_univ _))
        (by simp [PMF.toOuterMeasure_apply, PMF.tsum_coe]))
  rw [Algorithm.disagreeProb]
  exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le hpos hle)) hne

/-- Concrete nontrivial algorithm on infinite `[DecidableEq ℤ]` with strictly positive
disagreement probability simultaneously amplified to `1 / 100`-replicability and `1 / 100`-accuracy
for outputting `1`. -/
theorem amplifyReplicability_nontrivialInt_check :
    ∃ (K : ℕ) (_ : NeZero K) (a b : ℝ) (T k₁ k₂ N : ℕ)
      (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N),
      0 < (nontrivialIntAlg K).disagreeProb fairCoin ∧
      IsReplicableFor (amplifyReplicability (nontrivialIntAlg K) a b T k₁ k₂ N)
        {fairCoin} (1 / 100) ∧
      IsAccurateFor (amplifyReplicability (nontrivialIntAlg K) a b T k₁ k₂ N)
        {fairCoin} (fun _ => {1}) (1 / 100) := by
  obtain ⟨a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN, β₀_req, hβ₀_pos, hspec⟩ :=
    exists_amplifyReplicability_accurate (ρ₀ := (1 / 4 : ℝ)) (ρ := 1 / 100) (β := 1 / 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K₀, hK₀⟩ := exists_nat_one_div_lt hβ₀_pos
  let K := max 4 (K₀ + 1)
  have : NeZero K := ⟨by omega⟩
  have hK_ge4 : (4 : ℝ) ≤ K := by exact_mod_cast le_max_left 4 (K₀ + 1)
  have hK_inv : 1 / (K : ℝ) ≤ β₀_req := by
    have hle : (K₀ + 1 : ℝ) ≤ K := by exact_mod_cast le_max_right 4 (K₀ + 1)
    exact (one_div_le_one_div_of_le (by positivity) hle).trans hK₀.le
  have hrepA : IsReplicableFor (nontrivialIntAlg K) {fairCoin} (1 / 4) := by
    intro D hD
    exact (isReplicableFor_constExceptZeroAlg K 1 (1 : ℤ) _ _ D hD).trans
      (one_div_le_one_div_of_le (by norm_num) hK_ge4)
  have haccA : IsAccurateFor (nontrivialIntAlg K) {fairCoin} (fun _ => {1}) (1 / K) :=
    isAccurateFor_constExceptZeroAlg K 1 (1 : ℤ) _ _
  obtain ⟨hrepAmp, haccAmp⟩ := hspec (nontrivialIntAlg K) hrepA haccA hK_inv
  exact ⟨K, inferInstance, a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN,
    disagreeProb_nontrivialIntAlg_pos K, hrepAmp, haccAmp⟩

end

end AmplificationTests

end CslibFrontierTests.Replicable
