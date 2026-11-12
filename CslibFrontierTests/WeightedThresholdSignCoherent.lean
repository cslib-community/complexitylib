/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevSignCoherent
import CslibFrontier.Foundations.Analysis.SpecialFunctions.FiberCount

/-!
Clients of the sign-coherent lower bound for Andreev's function: level-set counting, split cubes
of unate separable forms, the fiber-counting Jensen step, the cube restriction and Theorem 13.
-/

open Cslib Cslib.Circuits

namespace WeightedThresholdSignCoherentTests

open Boolean.WeightedThreshold Finset

-- A fixed weight vector on two bits has at most `3` nonconstant threshold shifts.
example (β : Fin 2 → ℝ) :
    #{g : BitString 2 → Bool | IsThresholdShift β g ∧ ∃ u v, g u ≠ g v} ≤ 3 := by
  simpa using card_isThresholdShift_nonconst_le β

-- Any real function on a finite type has at most `|X| + 1` upper level sets.
example (φ : Fin 5 → ℝ) : #{g : Fin 5 → Bool | IsUpperLevelSet φ g} ≤ 6 := by
  simpa using card_isUpperLevelSet_le φ

-- A unate separable form on the `3 × 3` grid of unit cubes splits at most `9 - 4 = 5` of them.
example (F : Fin 2 → ℕ → ℝ) (hF : ∀ i, Monotone (F i) ∨ Antitone (F i)) (θ : ℝ) :
    #{q : Fin 2 → Fin 3 | Cslib.Combinatorics.CubeSplits F θ q} ≤ 5 := by
  exact (Cslib.Combinatorics.card_cubeSplits_le F hF θ).trans_eq (by simp)

-- Along `s ↦ s₀ + s₁`, the threshold `3 / 2` splits the cube `(0, 1)` of the `2 × 2` grid: its
-- vertex sums run from `1` to `3`.
example : Cslib.Combinatorics.CubeSplits (m := 2) (fun _ s => (s : ℝ)) (3 / 2) ![0, 1] := by
  rw [Cslib.Combinatorics.cubeSplits_iff]
  exact ⟨![false, false], ![true, true], by simp [Fin.sum_univ_two]; norm_num,
    by simp [Fin.sum_univ_two]; norm_num⟩

-- At the cube point with block counts `s`, Andreev's function reads the table at `s mod 2`.
example (b m : ℕ) (x : BitString (2 ^ b)) (s : Fin b → ℕ) (hs : ∀ j, s j ≤ m) :
    Boolean.andreev b m (andreevCubePoint b m x s) =
      x (BitString.equivFin b fun j => decide (s j % 2 = 1)) :=
  andreev_andreevCubePoint x hs

-- Theorem 13 applies to every circuit of depth at most two, whose top gate may read inputs, once
-- its bottom gates are sign-coherent; at balance it gives `N (N - 3 b - 1) / (3 b ^ 3)` gates.
example (b m : ℕ) (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (Boolean.andreev b m)))
    (hcoh : ∀ k ∈ circuitBottomGates c 0,
      IsSignCoherent (Boolean.andreevBlockVar b m) (inputWeight c.program k))
    (hbal : b * m = 2 ^ b) :
    (2 : ℝ) ^ b * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 3) ≤ #(circuitBottomGates c 0) ∧
      (m : ℝ) * andreevCubeSplitBound b #(circuitBottomGates c 0) ≤
        b * #(circuitBottomGates c 0) :=
  ⟨le_card_circuitBottomGates_of_balanced c hd hcomp hcoh hbal,
    mul_andreevCubeSplitBound_le c hd hcomp hcoh⟩

-- Lemma 14 needs no sign condition: every depth-two circuit for `andreev b m` has many splitting
-- gates on every cube.
example (b m : ℕ) (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (Boolean.andreev b m)))
    (q : Fin b → Fin m) :
    (2 : ℝ) ^ 2 ^ b * andreevCubeSplitBound b #(circuitBottomGates c 0) ≤
      ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) :=
  two_pow_mul_andreevCubeSplitBound_le c hd hcomp q

end WeightedThresholdSignCoherentTests
