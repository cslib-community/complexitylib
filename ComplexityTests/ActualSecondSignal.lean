/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of actual preparatory second signals)

import Complexity.Foundations.Probability.NormalizedAtomRows.SecondSignal
import Complexity.Foundations.Probability.NormalizedAtomRows.ActualMoment

/-! Genuine selected preparation from zero-iteration residual children, and two-signal edges. -/
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
  selectedResidualPreparation HP 1 threeRoles 0 0 0 0 0 0 [1] [2] [3] 2 id
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
  simp only [selected, selectedResidualPreparation, DenseRowRecipe.preparation, atomPrep,
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
