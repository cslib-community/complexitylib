/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.FixedSize
import Complexity.Statistics.LeastSquares.SimpleMatrix
import Complexity.Statistics.LeastSquares.SharpGap
import Complexity.Statistics.LeastSquares.FixedEffects.FixedColumns
public import ComplexityTests.PaperEndpoints.LeastSquaresRadon1326
import all ComplexityTests.PaperEndpoints.LeastSquaresRadon1326
import Mathlib.Tactic

/-! Complete clients for convex-hull relaxation, scalar attainment and the
model boundary between refitted and fixed-column group dummies. -/

open Cslib.LeastSquares Matrix

namespace LeastSquaresRelaxation

private theorem sharp_injective : Function.Injective SharpGap.x := by
  intro i j he
  apply SharpGap.general_position i j
  change ((SharpGap.point i).1 : ℝ) = ((SharpGap.point j).1 : ℝ) at he
  exact_mod_cast he

private theorem sharp_feasible : Simple.SignFeasible SharpGap.x SharpGap.y
    (Simple.realVector SharpGap.witness) := by
  have hw := SharpGap.witness_feasible
  have hm : Simple.mass (Simple.realVector SharpGap.witness) = 10 - 4899/5000 := by
    rw [Simple.mass_realVector]
    rw [show Simple.mass SharpGap.witness = (10 - 4899/5000 : ℚ) by
      linarith [SharpGap.fractional_certificate.2.1]]
    norm_num
  exact ⟨hw.1, by rw [hm]; norm_num, hw.2.1,
    (Simple.slope_nonpos_iff _ _ _ hw.2.1).mp hw.2.2⟩

-- Attainment and actual inverse-OLS semantics on the paper's strict-gap instance.
example : ∃ u, Simple.MassOptimal SharpGap.x SharpGap.y u ∧
    fractionalStability (Simple.design SharpGap.x) SharpGap.y Simple.slopeTarget 0 =
      10 - Simple.mass u ∧
    (Finset.univ.filter fun i => 0 < u i ∧ u i < 1).card ≤ 2 := by
  simpa using Simple.exists_sparse_massOptimal _ _ _ sharp_injective sharp_feasible (by
    rw [Simple.mass_realVector]
    have hm := SharpGap.fractional_certificate.2.1
    exact_mod_cast (show (1 : ℚ) < Simple.mass SharpGap.witness by linarith))

open Classical in
example : ∃ S : Finset (Fin 10), Simple.SignFeasible SharpGap.x SharpGap.y
    (fun i => if i ∈ S then 1 else 0) ∧
    Simple.mass (Simple.realVector SharpGap.witness) - S.card < 2 := by
  have hmass : 4 ≤ Simple.mass (Simple.realVector SharpGap.witness) := by
    rw [Simple.mass_realVector]
    have hm := SharpGap.fractional_certificate.2.1
    exact_mod_cast (show (4 : ℚ) ≤ Simple.mass SharpGap.witness by linarith)
  obtain ⟨S, hs, hl⟩ := Simple.exists_round_sign_subset _ _ _ sharp_injective sharp_feasible hmass
  refine ⟨S, ?_, hl⟩
  convert hs using 1; (funext i; split_ifs <;> rfl)

-- The full Proposition 5.3 construction starts from the same feasible weights,
-- rather than assuming existence of an optimizer.
example : ∃ u, Simple.MassOptimal SharpGap.x SharpGap.y u ∧
    Simple.crossNumerator SharpGap.x SharpGap.y u = 0 := by
  have hmass : 4 ≤ Simple.mass (Simple.realVector SharpGap.witness) := by
    rw [Simple.mass_realVector]
    have hm := SharpGap.fractional_certificate.2.1
    exact_mod_cast (show (4 : ℚ) ≤ Simple.mass SharpGap.witness by linarith)
  have hfull : 0 < Simple.crossNumerator SharpGap.x SharpGap.y (fun _ => 1) := by
    norm_num [Simple.crossNumerator, Simple.mass, SharpGap.x, SharpGap.y,
      Simple.realVector, SharpGap.point, Fin.sum_univ_succ]
  obtain ⟨u, hu, _, hz, _⟩ := Simple.exists_sparse_self_centered _ _ _
    sharp_injective sharp_feasible hmass hfull
  exact ⟨u, hu, hz⟩

-- A constant regressor is rejected by the actual generic design, too.
example : ¬ Feasible (Simple.design (fun _ : Fin 3 => (1 : ℝ)))
    (fun _ => 0) Simple.slopeTarget 0 (fun _ => 1) := by
  rw [← Simple.signFeasible_iff]
  intro h
  have hv := h.2.2.1
  norm_num [Simple.xNumerator, Simple.crossNumerator, Simple.mass, Fin.sum_univ_succ] at hv

-- The exact six-point counterexample rules out the tight branch of Proposition 5.2.
private theorem no_tight_lower : ¬ ∃ S : Finset (Fin 6), S.card = 4 ∧
    Geometry.IsLowerRange LeastSquaresRadon1326.point S ∧
    Geometry.PolytopeMinimum LeastSquaresRadon1326.point 4
      (Geometry.subsetSum LeastSquaresRadon1326.point S) := by
  rintro ⟨S, hS, hlow, hmin⟩
  have hT : NonRange.retained.card = 4 := by decide
  have hmem : Geometry.subsetSum LeastSquaresRadon1326.point NonRange.retained ∈
      Geometry.setPolytope LeastSquaresRadon1326.point 4 := by
    rw [Geometry.setPolytope_eq_image]
    refine ⟨fun i => if i ∈ NonRange.retained then 1 else 0, ⟨?_, ?_⟩, ?_⟩
    · intro i; dsimp only; split_ifs <;> norm_num
    · simp [hT]
    · unfold Geometry.subsetSum
      congr 1
      funext i
      split_ifs <;> rfl
  have hle := hmin.2 _ hmem
  rw [← hS, Geometry.saddleObjective_subsetSum, hS, ← hT,
    Geometry.saddleObjective_subsetSum] at hle
  have he : S = NonRange.retained := by
    by_contra hn
    have hlt := LeastSquaresRadon1326.minimum S (hS.trans hT.symm) hn
    linarith
  obtain ⟨c, _, hc, hd⟩ := hlow
  apply LeastSquaresRadon1326.nonrange
  exact ⟨c, he ▸ hc, he ▸ hd⟩

-- Every actual polytope minimizer of this source instance lies strictly inside
-- a lower edge. This test cannot pass by choosing the integral branch.
public theorem fractional_lower_edge :
    ∃ v, Geometry.PolytopeMinimum LeastSquaresRadon1326.point 4 v ∧
    ∃ (R : Finset (Fin 6)) (i j : Fin 6) (t : ℝ),
      R.card = 3 ∧ 0 < t ∧ t < 1 ∧ Geometry.IsLowerSwap LeastSquaresRadon1326.point R i j ∧
      ((LeastSquaresRadon1326.point i).1 - (LeastSquaresRadon1326.point j).1) *
        ((LeastSquaresRadon1326.point i).2 - (LeastSquaresRadon1326.point j).2) < 0 ∧
      v = (1 - t) • Geometry.subsetSum LeastSquaresRadon1326.point (insert i R) +
        t • Geometry.subsetSum LeastSquaresRadon1326.point (insert j R) := by
  obtain ⟨⟨v, hv⟩, h | h⟩ := Geometry.fixedSize_relaxation LeastSquaresRadon1326.point 4
    (by norm_num) (by decide) LeastSquaresRadon1326.general_position
  · exact (no_tight_lower h).elim
  · obtain ⟨R, i, j, t, _, _, _, hcard, ht, ht1, hlow, _, _, _, hpair, he⟩ := h v hv
    refine ⟨v, hv, R, i, j, t, by omega, ht, ht1, hlow, hpair, ?_⟩
    convert he using 1; (congr 3 <;> ext k <;> simp)

namespace Groups

open FixedEffects.MatrixModel

private def x (_ : Fin 2) (i : Fin 3) : ℝ := i
private def y (g : Fin 2) (i : Fin 3) : ℝ := -x g i
private def full : Finset (Sigma fun _ : Fin 2 => Fin 3) := Finset.univ

private theorem full_feasible : Feasible (FixedEffects.MatrixModel.row x) (fun p => y p.1 p.2)
    (Pi.single none 1) 0 (fun p => if p ∈ full then 1 else 0) := by
  have hv : 0 < scatter x := by
    norm_num [scatter, cross, x, Fin.sum_univ_succ]
  have hc : cross x y ≤ 0 := by
    norm_num [cross, x, y, Fin.sum_univ_succ]
  have hg : weightedGram 0 Finset.univ (FixedEffects.MatrixModel.row x)
      (fun p => if p ∈ full then 1 else 0) =
      gram x := by simp [full, weightedGram, gram]
  have he : weightedEstimate 0 0 Finset.univ (FixedEffects.MatrixModel.row x) (fun p => y p.1 p.2)
      (fun p => if p ∈ full then 1 else 0) = (gram x)⁻¹ *ᵥ response x y := by
    simp [full, weightedEstimate, weightedGram, weightedResponse, gram, response]
  refine ⟨fun p => by simp [full], hg ▸ (gram_posDef_iff x).mpr hv, ?_⟩
  rw [he, single_dotProduct, one_mul]
  exact (inverse_slope_nonpos_iff x y hv).mpr hc

-- A genuine nonsingular group-preserving inverse fit instantiates equality of
-- the two stability values under the derived small-deletion condition.
example : integralStability (FixedEffects.MatrixModel.row x)
    (fun p => y p.1 p.2) (Pi.single none 1) 0 = 0 := by
  have hp : PreservesGroups full := by intro g; exact ⟨0, Finset.mem_univ _⟩
  have hs := (feasible_iff x y full hp).mp full_feasible
  have hz : subsetStability x y = 0 := by
    apply Nat.eq_zero_of_le_zero
    have hh : subsetStability x y ≤ Fintype.card (Sigma fun _ : Fin 2 => Fin 3) - full.card :=
      Nat.sInf_le ⟨full, hs, rfl⟩
    simpa [full] using hh
  rw [integralStability_eq_subsetStability x y ⟨full, hs⟩ (by intro g; rw [hz]; decide), hz]

-- The cardinality criterion also applies to a genuine positive deletion count.
example : PreservesGroups ((Finset.univ : Finset (Sigma fun _ : Fin 2 => Fin 3)).erase ⟨0, 0⟩) := by
  apply preservesGroups_of_deletions_lt
  intro g
  norm_num

-- Erasing one entire group fails fixed-column feasibility, regardless of sign.
example : ¬ Feasible (FixedEffects.MatrixModel.row x) (fun p => y p.1 p.2) (Pi.single none 1) 0
    (fun p => if p ∈ (Finset.univ.filter fun p => p.1 = (0 : Fin 2)) then 1 else 0) := by
  intro h
  have hp := preservesGroups_of_posDef x
    (Finset.univ.filter fun p : Sigma fun _ : Fin 2 => Fin 3 => p.1 = (0 : Fin 2)) h.2.1
  obtain ⟨i, hi⟩ := hp 1
  norm_num at hi

end Groups
end LeastSquaresRelaxation
