/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyInitialSecondNoise

/-!
# Sparse noise of literal initial preparation walks

The actual selected preparation has rank-sparse input support before its unchanged usage
walk. The resulting spectral scalar is intersected with the original range payment.
Successful preparation lists consume this minimum with the terminal rank and usage noise
masks kept distinct. This proves neither child availability nor a numerical field salary.

## Main results

* `initialSecondSignal_noise_allocated`: successful literal preparation walks pay the minimum.
* `compressedBin_secondNoise_allocated`: the compressed-bin execution supplies those walks.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability Cslib.RowCompression NormalizedMoments
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- Actual sparse-input spectral payment, intersected with the original range payment.
This scalar retains zeta, the original source normalization and computed step count. -/
@[expose] def initialSecondNoiseMoment (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ζ : ℝ) (j : ℕ) : ℝ :=
  min ((|ζ| * (2 : ℝ) ^ (-B.requestPrecision M r) *
    (1 / 64 : ℝ) ^ dyadicSlack (Nat.log2 M + 1) j) ^ 4)
    (ζ ^ 4 * (32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^
      (2 * B.steps M r (dyadicSlack (Nat.log2 M + 1) j)) * (16 * HP.K)))

/-- Both branches are nonnegative; no independence or mean-error hypothesis enters. -/
lemma initialSecondNoiseMoment_nonneg (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ζ : ℝ) (j : ℕ) :
    0 ≤ B.initialSecondNoiseMoment M r ζ j := by
  unfold initialSecondNoiseMoment
  apply le_min (by positivity)
  have hr : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4) := by norm_num
  positivity

/-- The actual completed preparation list consumes the sparse spectral scalar.
The rank mask is terminal, the noise mask is usage, and the first history is arbitrary. -/
theorem initialSecondSignal_noise_allocated (B : BudgetData HP P) (M bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (H : Horizon P) (ks ka ku : ℕ) (hks : ks ≤ H.maxExponent) (husage : ka ≤ ku)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (F : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (W : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ))
    (hW : (List.range (Nat.log2 M + 1)).mapM (fun i =>
      B.complete M r (B.binPreparation bin r (F (i + 1)))
        (dyadicSlack (Nat.log2 M + 1) i)) = some W)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ) (j : ℕ) (hj : j < Nat.log2 M + 1) :
    rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
        B.padding ss st ka G (firstSignalIncrement F ka
          (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
        (fun _ _ _ _ => 0) 1 j) ≤ B.initialSecondNoiseMoment M r ζ j := by
  apply le_min
  · apply B.initialSecondSignal_noise_moment M bin _ r R ks ku ss st hs hu F W hW ka G ζ j hj
    intro d
    rw [haux]
    exact ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩
  · let input := fun i => selectedPreparation HP B.padding R st ka (F i)
    let walks := fun i => conditionalWalk
      (retainedMask R.source (side P ks) B.padding ss)
      (retainedMask R.terminal (side P ku) B.padding st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P ku)
        (side_le P ks) (side_le P ku) (CopyPadding.identifier B.padding ss)
        (CopyPadding.identifier B.padding st))
      (fun _ _ => B.steps M r (dyadicSlack (Nat.log2 M + 1) (i - 1))) (input i)
    have he (σ : Environment P 3) (x y : ZMod P) :
        actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G (firstSignalIncrement F ka
            (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
          (fun _ _ _ _ => 0) 1 j σ x y =
        actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
          B.padding ss st ka G (firstSignalIncrement F ka (secondSignalIncrement walks ζ))
          (fun _ _ _ _ => 0) 1 j σ x y := by
      simp only [actualNoiseEntry, twoMaskMean, Fin.isValue, one_ne_zero, ↓reduceIte,
        div_one, actualPrefix_twoSignal_second, Nat.add_sub_cancel]
      have hw := B.preparationWalks_get M bin r R ks ku ss st hs hu F W hW j hj
      rw [B.binPreparation_eq_selected bin r R ka st ht haux] at hw
      have hw' : W[j]?.getD 0 = walks (j + 1) := by
        dsimp only [walks, input, Nat.add_sub_cancel]
        convert hw using 1; congr 8
      rw [hw']
    have heq := funext fun σ => funext fun x => funext fun y => he σ x y
    rw [heq]
    have hb := actualSelectedSecondSignal_noise_le HP
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) B.padding R H ks ka ku husage
      hks ss st F F (fun i => B.steps M r (dyadicSlack (Nat.log2 M + 1) (i - 1))) ζ G j
    simpa only [walks, input, hs, gridChannel, Nat.add_sub_cancel, Nat.cast_ofNat] using hb

/-- Successful computed compression supplies literal histories consumed by the new
scalar. This is conditional execution; no joint lower-budget availability is claimed.
In particular it demands no second-mean stability premise. -/
theorem compressedBin_secondNoise_allocated (B : BudgetData HP P) (M bin ka : ℕ)
    (ζ floor : ℝ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (R : RoleProfile 3)
    (H : Horizon P) (ks ku : ℕ) (hks : ks ≤ H.maxExponent) (husage : ka ≤ ku)
    (ss st : List (ZMod P))
    (hs : r.source = gridChannel R.source ks ss)
    (ht : r.terminal = gridChannel R.terminal ka st)
    (hu : r.usage = gridChannel R.terminal ku st)
    (haux : B.auxiliary bin = polynomialPrepCutoff4 HP.θ)
    (result : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hresult : B.compressedBin M bin ka ζ floor r = some result) :
    ∃ F W, B.initialPrefixes M r = some F ∧
      (List.range (Nat.log2 M + 1)).mapM (fun i =>
        B.complete M r (B.binPreparation bin r (F (i + 1)))
          (dyadicSlack (Nat.log2 M + 1) i)) = some W ∧
      ∀ j < Nat.log2 M + 1,
        rowNormPow 4 P r.source.rate (retainedMask R.source (side P ks) B.padding ss)
          (retainedMask R.terminal (side P ku) B.padding st)
          (actualNoiseEntry R.source R.terminal (side P ks) (side P ka) (side P ku)
            B.padding ss st ka B.base (firstSignalIncrement F ka
              (secondSignalIncrement (fun i σ x y => W[i - 1]?.getD 0 σ x y) ζ))
            (fun _ _ _ _ => 0) 1 j) ≤ B.initialSecondNoiseMoment M r ζ j := by
  have haux' (d : ℝ) : B.auxiliary bin d ∈ Set.Icc 0 1 := by
    rw [haux]
    exact ⟨polynomialPrepCutoff4_nonneg _ _, polynomialPrepCutoff4_le_one _ _⟩
  obtain ⟨F, W, hF, hW, _⟩ := B.compressedBin_secondNoise M bin ka haux' ζ floor
    r R ks ku ss st hs hu result hresult
  exact ⟨F, W, hF, hW, fun j hj => B.initialSecondSignal_noise_allocated M bin r R H
    ks ka ku hks husage ss st hs ht hu haux F W hW B.base ζ j hj⟩

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
