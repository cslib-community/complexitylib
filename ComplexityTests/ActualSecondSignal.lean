/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of actual preparatory second signals)

import Complexity.Foundations.Probability.NormalizedAtomRows.MeanBias
import Complexity.Foundations.Probability.NormalizedAtomRows.ActualMoment

/-! Finite raw-sample clients, completed-raw preparation wiring, and two-signal edges. -/
set_option linter.privateModule false

open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private lemma bigK (HP : FourthRootHierarchyParams 16 1 16 32 8) : 5 < HP.K := by
  have h := HP.gate
  have hnonneg : 0 ≤ 32 * (HP.k : ℝ) / HP.η := div_nonneg (by positivity) HP.η_pos.le
  have hh : (5 : ℝ) < HP.K := by linarith
  exact_mod_cast hh

private lemma rank_zero (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (f : ZMod 5 → ℝ) : kthLargest HP.K univ f = 0 := by
  have hc (v : ZMod 5) : ¬HP.K ≤ #{w : ZMod 5 | f v ≤ f w} := by
    have h := card_filter_le (univ : Finset (ZMod 5)) (fun w => f v ≤ f w)
    have hcard : Fintype.card (ZMod 5) = 5 := ZMod.card 5
    simp only [card_univ, hcard] at h
    have hk := bigK HP
    omega
  simp [kthLargest, hc]

private def child (b : Environment 5 3 → Bool) (σ : Environment 5 3)
    : Matrix (ZMod 5) (ZMod 5) ℝ := fun _x y => if b σ ∧ y = 0 then 1 else 0

private def prepChild (_σ : Environment 5 3) : Matrix (ZMod 5) (ZMod 5) ℝ :=
  fun _ _ => 1

private def selected (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Environment 5 3 → Bool) :=
  rawSamplePreparation HP 1 threeRoles 0 0 0 0 0 0 [1] [2] [3] 2 id
    (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child b)
    (fun _ => prepChild) (fun _ _ _ => 9)

private lemma raw_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Environment 5 3 → Bool) (σ : Environment 5 3) (x y : ZMod 5) :
    rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
      (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child b)
      (fun _ => prepChild) (fun _ _ _ => 9) σ x y = child b σ x y := by
  have had : Admissible (HierarchyTask.rawRequests (k := 0) (Role := Fin 3)
      (Symbol := ZMod 5) 0 0 .residual
      (gridChannel threeRoles.source 0 [1]) (gridChannel threeRoles.midpoint 0 [2])
      (gridChannel threeRoles.terminal 0 [3]) (rate 0)).direct := ⟨by decide, rfl, rfl⟩
  change rate 0 * _ * normalizedRequest 1 (id : ZMod 5 → ZMod 5) _ id HP.ρ HP.K
    (child b) prepChild σ x y + rate 0 * _ * _ * (∑ z : ZMod 5, (0 : ℝ) * _) -
      rate 0 * _ * (0 : ℝ) = child b σ x y
  simp only [zero_mul, sum_const_zero, mul_zero, sub_zero, add_zero]
  unfold normalizedRequest
  rw [dite_eq_left had]
  have hside : side 5 0 = 5 := by norm_num [side]
  simp only [HierarchyTask.rawRequests, threeRoles, min_self, DenseRowRecipe.normalized,
    coordinate, gridChannel, semanticSide_grid, hside,
    full_retains, ↓reduceIte, id_eq, rowGate, filter_true, rank_zero,
    HP.ρ_one 0 HP.η_pos.le, mul_one]
  have hsemantic : semanticSide 5 1 = 5 := by
    simpa [rate, hside] using semanticSide_grid 5 0
  norm_num [hsemantic, ZMod.val_lt, HierarchyTask.usageRatio,
    CorrectionRowTask.Channel.retains, channels,
    semanticSide_grid, rate, hside, full_retains, CorrectionRowRecipe.normalizer, prepChild]

private lemma selected_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Environment 5 3 → Bool) (σ : Environment 5 3) (x y : ZMod 5) :
    selected HP b σ x y = child b σ x y := by
  have hside : side 5 0 = 5 := by norm_num [side]
  have hprep : polynomialPrepCutoff4 HP.θ 1 = 1 := by
    apply HP.prep_full_on_Q
    have h := HP.le_Q 1
    have hh := HP.θ₂_lt
    norm_num at hh
    linarith
  simp only [selected, rawSamplePreparation, selectedPreparation,
    DenseRowRecipe.preparation, atomPrep,
    raw_eq, rowGate, retainedMask, hside, full_retains, filter_true, rank_zero,
    HP.ρ_one 0 HP.η_pos.le, mul_one]
  by_cases h : b σ ∧ y = 0
  · simp [child, h, rate, hprep]
  · have hzero := polynomialPrepCutoff4_eq_zero HP.θ_pos
      (show (0 : ℝ) ≤ HP.θ / 2 by linarith [HP.θ_pos])
    simp [child, h, rate, hzero]

-- Genuine selected preparation is nonzero at one endpoint and zero at another.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    selected HP (fun _ => true) σ 0 0 = 1 ∧ selected HP (fun _ => true) σ 0 1 = 0 := by
  simp [selected_eq, child]

private def fullGraph (x y : ZMod 5) : RotationMap
    (RetainedPairSlice (retainedMask (0 : Fin 3) 5 1 [1])
      (retainedMask 2 5 1 [3]) x y) Unit := ⟨id, fun _ => rfl⟩

private def walk (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Environment 5 3 → Bool) (_j : ℕ) :=
  conditionalWalk (retainedMask (0 : Fin 3) 5 1 [1]) (retainedMask 2 5 1 [3])
    fullGraph (fun _ _ => 0) (fun σ x y => selected HP b σ x y)

private lemma walk_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Environment 5 3 → Bool) (j : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    walk HP b j σ x y = child b σ x y := by
  have hs : retainedMask (0 : Fin 3) 5 1 [1] σ x := full_retains _ _
  have ht : retainedMask (2 : Fin 3) 5 1 [3] σ y := full_retains _ _
  simp [walk, conditionalWalk, hs, ht, selected_eq]

-- Actual two-signal prefix: genuine preparation, arbitrary nonzero first signal, ζ=3.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    actualPrefix (firstSignalIncrement (fun j _ _ _ => j + 7) 0
      (secondSignalIncrement (walk HP (fun _ => true)) 3)) (fun _ _ _ _ => 0)
      2 σ 0 0 1 = 3 ∧
    actualPrefix (firstSignalIncrement (fun j _ _ _ => j + 7) 0
      (secondSignalIncrement (walk HP (fun _ => true)) 3)) (fun _ _ _ _ => 0)
      2 σ 0 0 0 = 10 := by
  rw [actualPrefix_twoSignal_second, actualPrefix_twoSignal_first, walk_eq]
  norm_num [child, rate]

-- The whole genuine preparation and its prefixes vanish for zero dense children.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3)
    (i : ℕ) (x y : ZMod 5) :
    actualPrefix (firstSignalIncrement (fun _ _ _ _ => 7) 0
      (secondSignalIncrement (walk HP (fun _ => false)) 3)) (fun _ _ _ _ => 0)
      i σ x y 1 = 0 := by
  rw [actualPrefix_twoSignal_second, walk_eq]
  simp [child]

private def randomBit (σ : Environment 5 3) : Bool := decide ((σ 1).1 0 = 0)

-- Real frames exist; the regression varies a spectator's constant column on the same Ω.
private def baseFrame : Frame 5 4 1 := Classical.choice inferInstance
private def envLow : Environment 5 3 := fun _ => (0, baseFrame)
private def envHigh : Environment 5 3 := fun _ => (1, baseFrame)

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    selected HP randomBit envLow 0 0 = 1 ∧ selected HP randomBit envHigh 0 0 = 0 := by
  simp [selected_eq, child, randomBit, envLow, envHigh]

-- Without evaluating the enormous environment sum, at least one actual centered noise
-- is ≥3/2: the two genuine walk values differ by 1. The mean is the actual joint mean.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ σ : Environment 5 3,
      actualNoiseEntry (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 (fun _ _ => 0)
        (firstSignalIncrement (fun _ _ _ _ => 7) 0
          (secondSignalIncrement (walk HP randomBit) 3)) (fun _ _ _ _ => 0)
        1 0 σ 0 0 ≥ 3 / 2 := by
  have he (σ : Environment 5 3) := actualNoiseEntry_secondSignalIncrement
    (0 : Fin 3) 2 5 5 5 1 [1] [3] (fun _ => fullGraph) (fun _ _ _ => 0)
    (fun _ σ x y => selected HP randomBit σ x y) (fun _ _ _ _ => 7) 0 3
    (fun _ _ => 0) 0 σ 0 0
  change ∀ σ, actualNoiseEntry (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 (fun _ _ => 0)
    (firstSignalIncrement (fun _ _ _ _ => 7) 0 (secondSignalIncrement (walk HP randomBit) 3))
    (fun _ _ _ _ => 0) 1 0 σ 0 0 =
    |(3 : ℝ)| * |walk HP randomBit 1 σ 0 0 - rowSliceMean
      (retainedMask (0 : Fin 3) 5 1 [1]) (retainedMask 2 5 1 [3])
      (fun σ x y => selected HP randomBit σ x y) 0 0| at he
  change ∃ σ, _ ≥ (3 : ℝ) / 2
  by_contra hn
  push Not at hn
  have h0 := hn envLow
  have h1 := hn envHigh
  rw [he envLow] at h0
  rw [he envHigh] at h1
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at h0 h1
  change 3 * |walk HP randomBit 1 envLow 0 0 - _| < 3 / 2 at h0
  change 3 * |walk HP randomBit 1 envHigh 0 0 - _| < 3 / 2 at h1
  rw [walk_eq] at h0 h1
  simp only [child, randomBit, envLow, envHigh, Pi.zero_apply, Pi.one_apply,
    decide_true, and_self, ↓reduceIte, one_ne_zero, decide_false,
    Bool.false_eq_true, false_and] at h0 h1
  have htri := abs_sub_le (1 : ℝ)
    (rowSliceMean (retainedMask (0 : Fin 3) 5 1 [1]) (retainedMask 2 5 1 [3])
      (fun σ x y => selected HP randomBit σ x y) 0 0) 0
  rw [abs_sub_comm (0 : ℝ)] at h1
  norm_num only [sub_zero, abs_one] at htri h1
  linarith

-- Empty usage slices remain stationary without a fabricated conditional sample.
example (x y : Unit) :
    rowSliceMean (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => False)
      (conditionalWalk (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => False)
        (fun _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun _ _ => 2)
        (fun σ _ _ => if σ then 1 else 0)) x y = 0 := by
  rw [rowSliceMean_conditionalWalk]
  simp [rowSliceMean]

-- Empty usage is genuinely off-mask, even after three compression updates.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    let H := fun j => conditionalWalk (retainedMask (0 : Fin 3) 5 1 [1])
      (retainedMask 2 0 1 [3])
      (fun _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun _ _ => j)
      (fun τ x y => selected HP randomBit τ x y)
    (iterate univ (fun _ => 1) (fun _ => 1) (fun _ => 1)
      ((firstSignalIncrement (fun _ _ _ _ => 7) 0 (secondSignalIncrement H 3)) σ 0)
      ⟨0, fun _ _ => 0⟩ 3).row 0 1 = 0 := by
  dsimp only
  have hy : ¬retainedMask (2 : Fin 3) 0 1 [3] σ 0 := by
    intro hh
    have h := (mem_retentionBox.mp hh) 0
    omega
  exact (actualTwoSignal_zero_off (0 : Fin 3) 2 5 0 1 [1] [3]
    (fun _ _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun j _ _ => j)
    (fun _ τ x y => selected HP randomBit τ x y) (fun _ _ _ _ => 7) 0 3
    σ 0 0 hy).2 univ (fun _ => 1) (fun _ => 1) (fun _ => 1) 3

private def smallHorizon : Horizon 5 := ⟨0, 0, by decide, by decide⟩

-- A positive, nonconstant actual selected preparation pays the narrower kt=1 usage
-- moment while its rank cutoff stays at k=0; all children share the same environment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 1) 1 [3]) (selected HP randomBit) ≤ 16 * HP.K ∧
      selected HP randomBit envLow 0 0 = 1 ∧ selected HP randomBit envHigh 0 0 = 0 := by
  constructor
  · exact selectedPreparation_moment_le HP (by have := bigK HP; omega) 1 threeRoles
      smallHorizon 0 0 1 (by decide) (by decide) [1] [3]
      (rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
        (fun _ => child randomBit) (fun _ => prepChild) (fun _ _ _ => 9))
  · simp [selected_eq, child, randomBit, envLow, envHigh]

-- A nonempty suffix and degenerate D=0 still use the exact one-point frame marginal.
example : (∑ x : ZMod 5, (({σ : Environment 5 3 |
    retainedMask (0 : Fin 3) (side 5 0) 0 [1, 2] σ x} : Finset _).dens : ℝ)) = 5 := by
  rw [source_density_sum]
  norm_num [side]

-- This finite raw-sample i=2 second-prefix noise client uses the H4 graph and input
-- budget 3. Its first signal is nonzero, its children use the nonconstant spectator, and
-- the steps depend on the requested ε and dyadic slack rather than an assumed noise bound.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {ε : ℝ} (hε : 0 < ε) :
    let steps := fun j => spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4))
      ((3 : ℝ) ^ 4 * 512 * HP.K) ε (dyadicSlack 4 (j - 1))
    let T := fun (_j : ℕ) σ x y => rawSamplePreparation HP 1 threeRoles
      0 0 0 0 0 0 [1] [2] [3] 2 id
      (fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) => child randomBit)
      (fun _ => prepChild) (fun _ _ _ => 9) σ x y
    let H := fun j => conditionalWalk (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 0) 1 [3])
      (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 0)
        (side_le 5 0) (side_le 5 0) (fun x => CopyPadding.identifier 1 [1] x)
        (fun y => CopyPadding.identifier 1 [3] y)) (fun _ _ => steps j) (T j)
    rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 0) 1 [3])
      (actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 0) 1 [1] [3] 0
        (fun _ _ => 0) (firstSignalIncrement (fun j _ _ _ => j + 7) 0
          (secondSignalIncrement H 3)) (fun _ _ _ _ => 0) 1 2) ≤
      (ε * (64 : ℝ)⁻¹ ^ dyadicSlack 4 2) ^ 4 := by
  exact actualSelectedSecondSignal_noise_le_dyadic HP (by have := bigK HP; omega)
    1 threeRoles smallHorizon 0 0 0 (by decide) (by decide) [1] [3]
    (fun (_j : ℕ) σ => rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
      (fun (_ : HierarchyTask.Request HP.k (Fin 3) (ZMod 5)) => child randomBit)
      (fun _ => prepChild) (fun _ _ _ => 9) σ)
    (fun j _ _ _ => j + 7) _ 3 (fun _ _ => 0) 2 4 hε (by rfl)

-- Zero scaling gives exact zero actual noise, including the ε=0 boundary.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ)
    (σ : Environment 5 3) (x y : ZMod 5) :
    actualNoiseEntry (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 (fun _ _ => 0)
      (firstSignalIncrement (fun _ _ _ _ => 7) 0
        (secondSignalIncrement (walk HP randomBit) 0)) (fun _ _ _ _ => 0) 1 i σ x y = 0 := by
  simp [actualNoiseEntry, twoMaskMean, actualPrefix_twoSignal_second, rowSliceMean]

-- The logarithmic sufficient-length lemma permits zero capacity with arbitrary scaling.
example (ζ ε : ℝ) (slack : ℕ) :
    ζ ^ 4 * (32 * (1 - 1 / (155648 * ((3 : ℕ) + 1 : ℝ) * (4 : ℝ) ^ 4)) ^
      (2 * spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4))
        (ζ ^ 4 * 512 * 0) ε slack) * (16 * (0 : ℕ))) ≤
      (ε * (64 : ℝ)⁻¹ ^ slack) ^ 4 :=
  by
    simp only [Nat.cast_zero, mul_zero]
    positivity

-- At ε=0 a positive spectral upper bound never becomes exactly zero in finite time.
example (n : ℕ) : ¬((1 : ℝ) ^ 4 *
    (32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^ (2 * n) * (16 * 1)) ≤ 0) := by
  have h : (0 : ℝ) < (1 : ℝ) ^ 4 *
      (32 * (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4)) ^ (2 * n) * (16 * 1)) := by
    positivity
  exact not_le.mpr h


-- The actual target is a positive, nonconstant genuine preparation, on the same full Ω.
private def biasTruth : Matrix (ZMod 5) (ZMod 5) ℝ := fun _ y => if y = 0 then 1 else 0

private lemma genuine_bias_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 3) (x y : ZMod 5) :
    genuinePrep HP (2 : Fin 3) 1 [3] 0 biasTruth σ x y = biasTruth x y := by
  have hside : side 5 0 = 5 := by norm_num [side]
  have hone : polynomialPrepCutoff4 HP.θ 1 = 1 := by
    apply polynomialPrepCutoff4_eq_one HP.θ_pos
    have h := HP.θ₂_lt
    norm_num at h
    linarith [HP.θ_lt_θ₂]
  have hzero := polynomialPrepCutoff4_eq_zero HP.θ_pos
    (show (0 : ℝ) ≤ HP.θ / 2 by linarith [HP.θ_pos])
  simp only [genuinePrep, DenseRowRecipe.preparation, atomPrep, rowGate, hside,
    full_retains, filter_true, rank_zero, HP.ρ_one 0 HP.η_pos.le, mul_one]
  by_cases hy : y = 0 <;> simp [biasTruth, hy, rate, hone, hzero]

private lemma genuine_bias_mean (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (x y : ZMod 5) :
    genuineMean HP (0 : Fin 3) 2 5 5 (CopyPadding.identifier 1 [1] x) 1 [3]
      0 biasTruth x y = biasTruth x y := by
  simp only [genuineMean, rowSliceMean, genuine_bias_eq, full_retains, and_self,
    filter_true, Fintype.expect_const]

-- Stationarity does not remove preparation bias: deleting a nonzero actual child
-- residual gives second mean discrepancy one, even for an exact stationary walk.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) :
    actualClippedMean HP (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 biasTruth 3
      (firstSignalIncrement (fun _ _ _ _ => 7) 0
        (secondSignalIncrement (walk HP (fun _ => false)) 3))
      (fun _ _ _ _ => 0) 1 i 0 0 = 1 := by
  unfold walk
  rw [actualClippedMean_second_eq HP (0 : Fin 3) 2 5 5 5 1 [1] [3]
    (fun _ => fullGraph) (fun _ _ _ => 0)
    (fun _ σ x y => selected HP (fun _ => false) σ x y)
    (fun _ _ _ _ => 7) 0 3 biasTruth i 0 0]
  simp only [rowSliceMean, selected_eq, child, Bool.false_eq_true, false_and, ↓reduceIte,
    genuine_bias_mean, biasTruth]
  norm_num

-- Exact-zero residual perturbation gives exact-zero actual deterministic bias,
-- while the selected preparation and genuine target are positive at endpoint zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) :
    actualClippedMean HP (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 biasTruth 3
      (firstSignalIncrement (fun _ _ _ _ => 7) 0
        (secondSignalIncrement (walk HP (fun _ => true)) 3))
      (fun _ _ _ _ => 0) 1 i 0 0 = 0 := by
  unfold walk
  rw [actualClippedMean_second_eq HP (0 : Fin 3) 2 5 5 5 1 [1] [3]
    (fun _ => fullGraph) (fun _ _ _ => 0)
    (fun _ σ x y => selected HP (fun _ => true) σ x y)
    (fun _ _ _ _ => 7) 0 3 biasTruth i 0 0]
  simp only [rowSliceMean, selected_eq, child,
    retainedMask, full_retains, and_self, filter_true, genuine_bias_mean, biasTruth]
  norm_num

-- An empty usage slice has genuine mean and selected-input mean zero even with
-- nonzero residuals. No assumption that the conditional slice is inhabited is needed.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowSliceMean (retainedMask (0 : Fin 3) 5 1 [1]) (retainedMask 2 0 1 [3])
      (fun σ x y => selected HP (fun _ => true) σ x y) 0 0 -
    genuineMean HP (0 : Fin 3) 2 5 0 (CopyPadding.identifier 1 [1] 0) 1 [3]
      0 biasTruth 0 0 = 0 := by
  have hz (σ : Environment 5 3) (y : ZMod 5) : ¬retainedMask (2 : Fin 3) 0 1 [3] σ y := by
    intro hh
    have h := (mem_retentionBox.mp hh) 0
    omega
  have hz' (σ : Environment 5 3) : ¬frameRetains 5 4 0 (σ 2)
      (CopyPadding.identifier 1 [3] (0 : ZMod 5)) := hz σ 0
  simp only [rowSliceMean, genuineMean, hz, hz', and_false, filter_false, expect_empty, sub_self]


-- The real perturbed lower-child residual pays an explicit absolute envelope.
-- This does not use a relative error or a target bound inferred from row mass.
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {Lh Lρ : ℝ} (hLh : 0 ≤ Lh) (hLρ : 0 ≤ Lρ) (σ : Environment 5 3) :
    preparationError threeRoles 1 [3] 0 Lh Lρ
      (fun τ => rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
        (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
        (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child (fun _ => false))
        (fun _ => prepChild) (fun _ _ _ => 9) τ) biasTruth σ 0 0 ≤ Lh + Lρ := by
  have hb := preparationError_le threeRoles 1 [3] 0 hLh hLρ
    (fun τ => rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
      (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child (fun _ => false))
      (fun _ => prepChild) (fun _ _ _ => 9) τ) biasTruth σ 0 0
    (e := 1) (m := 1) (by norm_num)
    (by simp [raw_eq, child, biasTruth])
    (by intro w _; simp only [raw_eq, child, Bool.false_eq_true, false_and, ↓reduceIte,
                               biasTruth]; split_ifs <;> norm_num)
  simpa only [rate, pow_zero, one_pow, inv_one, mul_one, div_one] using hb

-- A real completed H4 raw child with seven smoothing steps, not an unaveraged cutoff.
private def completed (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Bool) (_j : ℕ) (σ : Environment 5 3) (x y : ZMod 5) : ℝ :=
  completedRawChild HP 1 threeRoles 0 0 0 0 0 0 [1] [2] [3] 2 id
    (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child (fun _ => b))
    (fun _ => prepChild) (fun _ _ _ => 9) 7 σ x y

set_option backward.isDefEq.respectTransparency false in
private lemma completed_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Bool) (j : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    completed HP b j σ x y = child (fun _ => b) σ x y := by
  have hs : ∀ τ : Environment 5 3,
      retainedMask threeRoles.source (side 5 0) 1 [1] τ x := by
    intro τ
    have he : side 5 0 = 5 := by norm_num [side]
    rw [he]
    exact full_retains _ _
  have ht : ∀ τ : Environment 5 3,
      retainedMask threeRoles.terminal (side 5 0) 1 [3] τ y := by
    intro τ
    have he : side 5 0 = 5 := by norm_num [side]
    rw [he]
    exact full_retains _ _
  simp only [completed, completedRawChild, conditionalWalk, hs, ht, and_self,
    mem_filter, mem_univ, ↓reduceDIte]
  simp only [raw_eq, child]
  exact congrFun (RotationMap.walk_pow_const _ _ _) _

private lemma completed_prep_eq (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (b : Bool) (j : ℕ) (σ : Environment 5 3) (x y : ZMod 5) :
    selectedPreparation HP 1 threeRoles [3] 0 (completed HP b j) σ x y =
      child (fun _ => b) σ x y := by
  have he : (fun τ => rawIncomingNormalized HP 1 id threeRoles 0 0 0 0 0 0 [1] [2] [3]
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff 2 id
      (fun (_ : HierarchyTask.Request 0 (Fin 3) (ZMod 5)) => child (fun _ => b))
      (fun _ => prepChild) (fun _ _ _ => 9) τ) = completed HP b j := by
    funext τ a z
    rw [raw_eq, completed_eq]
  rw [← he]
  exact selected_eq HP (fun _ => b) σ x y

-- Positive completed preparation, a zero child, and a nonconstant endpoint survive smoothing.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    selectedPreparation HP 1 threeRoles [3] 0 (completed HP true 3) σ 0 0 = 1 ∧
    selectedPreparation HP 1 threeRoles [3] 0 (completed HP true 3) σ 0 1 = 0 ∧
    selectedPreparation HP 1 threeRoles [3] 0 (completed HP false 3) σ 0 0 = 0 := by
  simp [completed_prep_eq, child]

-- The cutoff of the average is one, whereas the average of cutoffs is only one half.
-- These nonconstant raw values are in matrix units and share the same full rank slice.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    let raw := fun (b : Bool) (_τ : Environment 5 3) (_x y : ZMod 5) =>
      if b ∧ y = 0 then (2 : ℝ) else 0
    selectedPreparation HP 1 threeRoles [3] 0
      (fun τ x y => 𝔼 b : Bool, raw b τ x y) σ 0 0 = 1 ∧
    (𝔼 b : Bool, selectedPreparation HP 1 threeRoles [3] 0 (raw b) σ 0 0) = 1 / 2 := by
  have h1 : polynomialPrepCutoff4 HP.θ 1 = 1 := by
    apply polynomialPrepCutoff4_eq_one HP.θ_pos
    have h := HP.θ₂_lt
    norm_num at h
    linarith [HP.θ_lt_θ₂]
  have h2 : polynomialPrepCutoff4 HP.θ 2 = 1 := by
    apply polynomialPrepCutoff4_eq_one HP.θ_pos
    have h := HP.θ₂_lt
    norm_num at h
    linarith [HP.θ_lt_θ₂]
  have h0 := polynomialPrepCutoff4_eq_zero HP.θ_pos
    (show (0 : ℝ) ≤ HP.θ / 2 by linarith [HP.θ_pos])
  have hs : side 5 0 = 5 := by norm_num [side]
  simp only [selectedPreparation, DenseRowRecipe.preparation, atomPrep, rowGate,
    retainedMask, hs, full_retains, filter_true, rank_zero,
    HP.ρ_one 0 HP.η_pos.le, mul_one]
  simp only [Finset.expect_eq_sum_div_card, Fintype.sum_bool]
  norm_num [rate, smul_eq_mul, h1, h2, h0]

-- Actual seven-step raw prefixes and seven-step preparation prefixes have zero
-- deterministic bias for exact completed raw children; both coordinates start at zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (i : ℕ) :
    let A := completed HP true
    let T := fun j σ x y => selectedPreparation HP 1 threeRoles [3] 0 (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask (0 : Fin 3) 5 1 [1])
      (retainedMask 2 5 1 [3]) fullGraph (fun _ _ => 7) (T j)
    actualClippedMean HP (0 : Fin 3) 2 5 5 5 1 [1] [3] 0 biasTruth 3
      (firstSignalIncrement A 0 (secondSignalIncrement H 3))
      (fun _ _ _ _ => 0) 1 i 0 0 = 0 := by
  dsimp only
  rw [actualClippedMean_second_eq]
  simp only [rowSliceMean, completed_prep_eq, child,
    genuine_bias_mean, biasTruth, retainedMask, full_retains, and_self, filter_true,
    Fintype.expect_const, sub_self, abs_zero, mul_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

-- Empty usage stays zero even for the positive completed child.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    rowSliceMean (retainedMask (0 : Fin 3) 5 1 [1]) (fun _ _ => False)
      (fun σ x y => selectedPreparation HP 1 threeRoles [3] 0 (completed HP true 3) σ x y)
      0 0 = 0 := by
  simp [rowSliceMean]

-- Numerical second-prefix payment also consumes the completed seven-step raw H4 child.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {ε : ℝ} (hε : 0 < ε) :
    let A := completed HP true
    let steps := fun j => spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ) ^ 4))
      ((3 : ℝ) ^ 4 * 512 * HP.K) ε (dyadicSlack 4 (j - 1))
    let T := fun j σ x y => selectedPreparation HP 1 threeRoles [3] 0 (A j) σ x y
    let H := fun j => conditionalWalk (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 1) 1 [3])
      (graph (0 : Fin 3) 2 (by decide) (side 5 0) (side 5 1)
        (side_le 5 0) (side_le 5 1) (fun x => CopyPadding.identifier 1 [1] x)
        (fun y => CopyPadding.identifier 1 [3] y)) (fun _ _ => steps j) (T j)
    rowNormPow 4 5 (rate 0) (retainedMask (0 : Fin 3) (side 5 0) 1 [1])
      (retainedMask 2 (side 5 1) 1 [3])
      (actualNoiseEntry (0 : Fin 3) 2 (side 5 0) (side 5 0) (side 5 1) 1 [1] [3] 0
        biasTruth (firstSignalIncrement A 0 (secondSignalIncrement H 3))
        (fun _ _ _ _ => 0) 1 2) ≤ (ε * (64 : ℝ)⁻¹ ^ dyadicSlack 4 2) ^ 4 := by
  exact actualSelectedSecondSignal_noise_le_dyadic HP (by have := bigK HP; omega)
    1 threeRoles smallHorizon 0 0 1 (by decide) (by decide) [1] [3]
    (completed HP true) (completed HP true) _ 3 biasTruth 2 4 hε (by rfl)
