/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Stability
import Mathlib.Tactic.FinCases

/-! A genuinely unsparse scalar instance of Lemma 3.2 and the full stability theorem. -/

open Cslib.LeastSquares Matrix

namespace FullRounding1326

/-- Six nonzero scalar design rows, hence general position in dimension one. -/
public def x : Fin 6 → Fin 1 → ℝ := fun _ _ => 1
/-- Four negative and two large positive responses. -/
public def y : Fin 6 → ℝ := fun i => if i < 4 then -1 else 4
/-- Four half-retained observations; both positive responses are removed. -/
public noncomputable def w : Fin 6 → ℝ := fun i => if i < 4 then 1 / 2 else 0

private theorem gp : GeneralPosition x := by
  classical
  intro s hs
  obtain ⟨hunique⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp
    (show Fintype.card s = 1 by simpa using hs)
  let := hunique
  apply linearIndependent_unique_iff.mpr
  intro h
  have := congrFun h 0
  norm_num [x] at this

private theorem weights : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1 := by
  intro i
  fin_cases i <;> norm_num [w]

private theorem mass : (∑ i, w i) = 2 := by
  norm_num [w, Fin.sum_univ_succ]

private theorem feasible : Feasible x y (fun _ => 1) 0 w := by
  refine ⟨weights, gp.weightedGram_posDef x w weights (by rw [mass]; norm_num), ?_⟩
  norm_num [weightedEstimate, weightedGram, weightedResponse, x, y, w,
    Fin.sum_univ_succ, Matrix.inv_def, Matrix.det_fin_one, Matrix.adjugate_fin_one,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec]

/-- Four fractional coordinates exceed the one-dimensional sparse bound. -/
public theorem input_is_unsparse :
    (Finset.univ.filter fun i => 0 < w i ∧ w i < 1).card = 4 := by
  have heq : (Finset.univ.filter fun i => 0 < w i ∧ w i < 1) = {0, 1, 2, 3} := by
    ext i
    fin_cases i <;> norm_num [w]
  rw [heq]
  decide

/-- The original target is violated, so the feasible witness represents a real audit. -/
public theorem full_data_positive :
    0 < (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ weightedEstimate 0 0 Finset.univ x y (fun _ => 1) := by
  norm_num [weightedEstimate, weightedGram, weightedResponse, x, y,
    Fin.sum_univ_succ, Matrix.inv_def, Matrix.det_fin_one, Matrix.adjugate_fin_one,
    Matrix.mulVec, dotProduct, Matrix.vecMulVec]

/-- Sparsification preserves the actual estimate of the unsparse witness and its mass. -/
public theorem sparse_output :
    ∃ u : Fin 6 → ℝ, (∀ i, u i ∈ Set.Icc (0 : ℝ) 1) ∧
      2 ≤ ∑ i, u i ∧
      (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ 1 ∧
      weightedEstimate 0 0 Finset.univ x y u = weightedEstimate 0 0 Finset.univ x y w ∧
      (weightedGram 0 Finset.univ x u).PosDef := by
  simpa only [mass, Fintype.card_fin] using
    exists_sparse_weights x gp y w weights (by rw [mass]; norm_num)

open Classical in
/-- Full rounding starts with four fractional coordinates and preserves feasibility. -/
public theorem rounded_subset :
    ∃ s : Finset (Fin 6), Feasible x y (fun _ => 1) 0 (fun i => if i ∈ s then 1 else 0) ∧
      2 - (s.card : ℝ) < 1 := by
  classical
  obtain ⟨s, hs, hm⟩ := exists_round_subset x gp y (fun _ => 1) 0 w feasible
    (by rw [mass]; norm_num)
  refine ⟨s, ?_, ?_⟩
  · convert hs using 2
    split_ifs <;> rfl
  · simpa only [mass, Fintype.card_fin, Nat.cast_one] using hm

/-- The one-dimensional endpoint applies to an actual nontrivial audit with unsparse input. -/
public theorem exact_ceiling :
    integralStability x y (fun _ => 1) 0 = ⌈fractionalStability x y (fun _ => 1) 0⌉₊ :=
  integralStability_eq_ceil_of_card_eq_one x gp (by decide) y (fun _ => 1) 0 w feasible
    (by rw [mass]; norm_num)

end FullRounding1326
