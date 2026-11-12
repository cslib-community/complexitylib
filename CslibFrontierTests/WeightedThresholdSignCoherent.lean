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

-- An antitone (reflected) form: along `s ↦ -(s₀ + s₁)` the threshold `-1 / 2` splits the corner
-- cube `(0, 0)` (vertex sums `0` down to `-2`) but not the cube `(1, 1)` (sums `-2` to `-4`).
example : Cslib.Combinatorics.CubeSplits (m := 2) (fun _ s => -(s : ℝ)) (-1 / 2) ![0, 0] := by
  rw [Cslib.Combinatorics.cubeSplits_iff]
  exact ⟨![true, true], ![false, false], by simp [Fin.sum_univ_two]; norm_num,
    by simp [Fin.sum_univ_two]; norm_num⟩

example : ¬ Cslib.Combinatorics.CubeSplits (m := 2) (fun _ s => -(s : ℝ)) (-1 / 2) ![1, 1] := by
  rw [Cslib.Combinatorics.cubeSplits_iff]
  rintro ⟨-, z', -, h⟩
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_one] at h
  push_cast at h
  have h₀ : (0 : ℝ) ≤ (z' 0).toNat := Nat.cast_nonneg _
  have h₁ : (0 : ℝ) ≤ (z' 1).toNat := Nat.cast_nonneg _
  linarith

-- At the cube point with block counts `s`, Andreev's function reads the table at `s mod 2`.
example (b m : ℕ) (x : BitString (2 ^ b)) (s : Fin b → ℕ) (hs : ∀ j, s j ≤ m) :
    Boolean.andreev b m (andreevCubePoint b m x s) =
      x (BitString.equivFin b fun j => decide (s j % 2 = 1)) :=
  andreev_andreevCubePoint x hs

-- Theorem 13 applies to every circuit of depth at most two, whose top gate may read inputs, once
-- its bottom gates are sign-coherent; at balance it gives `N (N - 3 b - 1) / (3 b ^ 3)` gates.
example (b m : ℕ) (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (Boolean.andreev b m)))
    (hcoh : ∀ k ∈ outputBottomGates c 0,
      IsSignCoherent (Boolean.andreevBlockVar b m) (inputWeight c.program k))
    (hbal : b * m = 2 ^ b) :
    (2 : ℝ) ^ b * ((2 : ℝ) ^ b - 3 * b - 1) / (3 * (b : ℝ) ^ 3) ≤ #(outputBottomGates c 0) ∧
      (m : ℝ) * andreevCubeSplitBound b #(outputBottomGates c 0) ≤
        b * #(outputBottomGates c 0) :=
  ⟨le_card_outputBottomGates_of_balanced c hd hcomp hcoh hbal,
    mul_andreevCubeSplitBound_le c hd hcomp hcoh⟩

-- Lemma 14 needs no sign condition: every depth-two circuit for `andreev b m` has many splitting
-- gates on every cube.
example (b m : ℕ) (c : Circuit signature (2 ^ b + b * m) 1)
    (hd : c.depth ≤ 2) (hcomp : c.Computes interpretation (single (Boolean.andreev b m)))
    (q : Fin b → Fin m) :
    (2 : ℝ) ^ 2 ^ b * andreevCubeSplitBound b #(outputBottomGates c 0) ≤
      ∑ x : BitString (2 ^ b), (andreevCubeSplitCount c q x : ℝ) :=
  two_pow_mul_andreevCubeSplitBound_le c hd hcomp q

/-! ### A concrete circuit: `andreev 1 1` with two bottom gates

Inputs `x 0, x 1` are the table and `x 2` the single address bit, so `andreev 1 1 x` is `x 1` if
`x 2` and `x 0` otherwise. The bottom gates are `x 1 ∧ x 2` (`x 1 + x 2 ≥ 2`) and `x 0 ∧ ¬x 2`
(`x 0 - x 2 ≥ 1`), and the top gate is their disjunction. -/

/-- A depth-two circuit for `andreev 1 1` with two bottom gates. -/
noncomputable def andreevOneOne : Circuit signature (2 ^ 1 + 1 * 1) 1 :=
  depthTwoInputs (G := 2) (fun j => ⟨2, ![![1, 1], ![1, -1]] j, ![2, 1] j⟩)
    (fun j => ![![1, 2], ![0, 2]] j) ![1, 1] 0 1

theorem andreev_one_one (x : BitString (2 ^ 1 + 1 * 1)) :
    Boolean.andreev 1 1 x = if x 2 then x 1 else x 0 := by
  rw [andreev_eq_table_parities]
  have hp : andreevParities 1 1 x = fun _ => x 2 := by
    funext j
    fin_cases j
    have huniv : (univ : Finset (Fin 1)) = {0} := rfl
    simp only [andreevParities, parity, huniv, parityOn_singleton]
    rfl
  rw [hp]
  cases x 2 <;> rfl

theorem andreevOneOne_computes :
    andreevOneOne.Computes interpretation (single (Boolean.andreev 1 1)) := by
  intro x
  funext o
  fin_cases o
  change andreevOneOne.eval interpretation x 0 = Boolean.andreev 1 1 x
  rw [andreevOneOne, eval_depthTwoInputs, andreev_one_one]
  simp only [interpretation, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.zero_apply, zero_mul, sum_const_zero, add_zero]
  have key (a b c : Bool) :
      decide ((1 : ℝ) ≤ 1 * ((decide ((2 : ℝ) ≤ 1 * (b.toNat : ℝ) + 1 * (c.toNat : ℝ))).toNat : ℝ)
        + 1 * ((decide ((1 : ℝ) ≤ 1 * (a.toNat : ℝ) + -1 * (c.toNat : ℝ))).toNat : ℝ)) =
        if c = true then b else a := by
    cases a <;> cases b <;> cases c <;> norm_num
  exact key (x 0) (x 1) (x 2)

-- With one bit per block every weight vector is sign-coherent; Theorem 13's coherence hypothesis
-- for the general circuit is discharged through `isSignCoherent_inputWeight_depthTwoInputs`.
theorem andreevOneOne_coherent (j : Fin 2) :
    IsSignCoherent (Boolean.andreevBlockVar 1 1)
      (argWeight (⟨2, ![![(1 : ℝ), 1], ![1, -1]] j, ![(2 : ℝ), 1] j⟩ : Op)
        (![![(1 : Fin (2 ^ 1 + 1 * 1)), 2], ![0, 2]] j)) := by
  intro i
  rcases le_total 0 (argWeight _ _ (Boolean.andreevBlockVar 1 1 i 0)) with h | h
  · exact Or.inl fun t => by fin_cases t; exact h
  · exact Or.inr fun t => by fin_cases t; exact h

example : ∀ k ∈ outputBottomGates andreevOneOne 0,
    IsSignCoherent (Boolean.andreevBlockVar 1 1) (inputWeight andreevOneOne.program k) := by
  obtain ⟨top, htop⟩ : ∃ top, andreevOneOne.outputs 0 = .gate top := ⟨_, rfl⟩
  intro k hk
  rw [outputBottomGates_of_gate htop] at hk
  exact isSignCoherent_inputWeight_depthTwoInputs _ _ _ _ _ andreevOneOne_coherent htop hk

-- Theorem 13 applied to the concrete circuit, with `G = 2` bottom gates.
example : ((1 : ℕ) : ℝ) ^ 1 * andreevCubeSplitBound 1 2 ≤
    ((1 ^ 1 - (1 - 1) ^ 1 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) :=
  pow_mul_andreevCubeSplitBound_le_of_depthTwoInputs _ _ _ _ _ andreevOneOne_computes
    andreevOneOne_coherent

end WeightedThresholdSignCoherentTests
