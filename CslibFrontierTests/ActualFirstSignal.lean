/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of actual first-signal prefixes)

import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FirstSignal

/-! Nonconstant positive prefixes, literal zero inputs and empty-slice stationarity. -/

set_option linter.privateModule false

open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

noncomputable section
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private def fullGraph (x y : ZMod 5) : RotationMap
    (RetainedPairSlice (retainedMask (0 : Fin 2) 5 1 [1])
      (retainedMask 1 5 1 [2]) x y) Unit :=
  ⟨id, fun _ => rfl⟩

private def input (j : ℕ) (_σ : Environment 5 2) (_x y : ZMod 5) : ℝ :=
  (j + 1 : ℕ) * (y.val + 1 : ℕ)

private def pref (j : ℕ) := conditionalWalk (retainedMask (0 : Fin 2) 5 1 [1])
  (retainedMask 1 5 1 [2]) fullGraph (fun _ _ => 0) (input j)

private theorem pref_eq (j : ℕ) (σ : Environment 5 2) (x y : ZMod 5) :
    pref j σ x y = (j + 1 : ℕ) * (y.val + 1 : ℕ) := by
  have hs : retainedMask (0 : Fin 2) 5 1 [1] σ x := by
    exact full_retains _ _
  have ht : retainedMask (1 : Fin 2) 5 1 [2] σ y := by
    exact full_retains _ _
  simp [pref, conditionalWalk, hs, ht, input]

-- A nonconstant, nonzero actual prefix built from genuine walk differences and zero raw.
example (σ : Environment 5 2) :
    actualPrefix (firstSignalIncrement pref 0 (fun _ _ _ _ => 7)) (fun _ _ _ _ => 0)
      0 σ 0 0 0 = 2 ∧
    actualPrefix (firstSignalIncrement pref 0 (fun _ _ _ _ => 7)) (fun _ _ _ _ => 0)
      0 σ 0 1 0 = 4 ∧
    actualPrefix (firstSignalIncrement pref 0 (fun _ _ _ _ => 7)) (fun _ _ _ _ => 0)
      2 σ 0 1 0 = 8 := by
  simp only [actualPrefix_firstSignalIncrement pref 0 (fun _ _ _ _ => 7)
    (fun _ _ _ _ => 0) (by intros; rfl), pref_eq]
  norm_num [rate, ZMod.val_one_eq_one_mod]

-- The first channel really divides by the fourth-power sampling rate.
example (σ : Environment 5 2) :
    actualPrefix (firstSignalIncrement pref 1 (fun _ _ _ _ => 0)) (fun _ _ _ _ => 0)
      0 σ 0 1 0 = 64 := by
  rw [actualPrefix_firstSignalIncrement pref 1 _ _ (by intros; rfl), pref_eq]
  norm_num [rate, ZMod.val_one_eq_one_mod]

-- Zero first input is preserved even with nonzero arbitrary second increments.
example (σ : Environment 5 2) (x y : ZMod 5) (i k : ℕ) :
    actualPrefix (firstSignalIncrement (fun _ _ _ _ => 0) k (fun _ _ _ _ => 9))
      (fun _ _ _ _ => 0) i σ x y 0 = 0 := by
  rw [actualPrefix_firstSignalIncrement _ _ _ _ (by intros; rfl), zero_div]

-- Empty retained slices need no fabricated point or conditional probability.
example (x y : Unit) :
    rowSliceMean (fun (_ : Bool) (_ : Unit) => False) (fun _ _ => True)
      (conditionalWalk (fun (_ : Bool) (_ : Unit) => False) (fun _ _ => True)
        (fun _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun _ _ => 3)
        (fun σ _ _ => if σ then 2 else 7)) x y = 0 := by
  rw [rowSliceMean_conditionalWalk]
  simp [rowSliceMean]

-- Nonconstant randomness: the slice mean is 9/2 and centered row moment is 625/16.
example :
    rowSliceMean (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (conditionalWalk (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
        (fun _ _ => (⟨id, fun _ => rfl⟩ : RotationMap _ Unit)) (fun _ _ => 0)
        (fun σ _ _ => if σ then 2 else 7)) () () = 9 / 2 := by
  rw [rowSliceMean_conditionalWalk]
  norm_num [rowSliceMean, expect_eq_sum_div_card, Fintype.sum_bool]

example :
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun σ _ _ => (if σ then (2 : ℝ) else 7) - 9 / 2) = 625 / 16 := by
  norm_num [rowNormPow, expect_eq_sum_div_card, Fintype.sum_bool]
