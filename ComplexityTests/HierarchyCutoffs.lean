/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of selected hierarchy cutoffs)

public import Complexity.Computability.LogSpaceDerandomization.HierarchyRankCutoffs

/-! Boundary, support, positive-output and actual H4 sampling regressions. -/

set_option linter.privateModule false

open Finset Cslib Matrix Matrix.FourthRootHierarchyParams
open scoped BigOperators
namespace CutoffRegression
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable (P : FourthRootHierarchyParams 16 1 16 32 8)

/-- Both closed boundaries and both full boundaries of the actual incoming gate. -/
example : P.incomingCutoff P.τ₀ = 1 ∧ P.incomingCutoff P.τ₁ = 0 ∧
    P.incomingCutoff 0 = 1 ∧ P.incomingCutoff 1 = 0 := by
  exact ⟨P.incomingCutoff_one le_rfl, P.incomingCutoff_zero le_rfl,
    P.incomingCutoff_one (by rw [P.τ₀_eq]; norm_num),
    P.incomingCutoff_zero (by rw [P.τ₁_eq]; norm_num)⟩

example : polynomialAuxCutoff4 P.θ (P.θ / 8) 0 = 0 ∧
    polynomialAuxCutoff4 P.θ (P.θ / 4) (P.θ / 100) = 1 ∧
    polynomialAuxCutoff4 P.θ P.θ (P.θ / 50) = 0 :=
  ⟨polynomialAuxCutoff4_eq_zero_of_entry_le P.θ_pos le_rfl,
    polynomialAuxCutoff4_eq_one P.θ_pos le_rfl le_rfl,
    polynomialAuxCutoff4_eq_zero_of_rank_ge P.θ_pos le_rfl⟩

public lemma Q_one_pos : 0 < P.Q 1 := by
  have h := P.le_Q 1
  have hsmall := P.θ₂_lt
  norm_num at hsmall
  linarith

/-- Nonempty true Q/rho support, for the chosen actual hierarchy parameters. -/
example : polynomialAuxCutoff4 P.θ 1 0 = 1 ∧
    polynomialPrepCutoff4 P.θ 1 = 1 ∧ P.ρ 0 = 1 := by
  have hr := P.ρ_one 0 P.η_pos.le
  exact ⟨P.aux_full_on_Q_rho (ne_of_gt (Q_one_pos P)) (by rw [hr]; norm_num),
    P.prep_full_on_Q (ne_of_gt (Q_one_pos P)), hr⟩

lemma singleton_rank (g : Unit → ℝ) : kthLargest 2 (univ : Finset Unit) g = 0 := by
  simp [kthLargest]

/-- A retained singleton produces a nonzero actual normalized correction recipe.
This checks the entire product, clipped normalizer and raw ranks, not just scalar identities. -/
theorem singleton_normalized :
    CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ
      P.toHierarchyParams.atomCutoff P.γ 2 2 1
      (fun (_ : Unit) (_ : Unit) => True) (fun (_ : Unit) (_ : Unit) => True)
      (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => 1)
      (fun (_ : Unit × Unit) _ _ => 1) (fun _ => 0) ((), ()) () () = P.Q 1 := by
  have hcap := P.toHierarchyParams.atomCutoff_eq (by norm_num : (0:ℝ) ≤ 1)
    (by have := Nat.cast_nonneg (α := ℝ) P.k; linarith)
  simp only [CorrectionRowRecipe.normalized, ↓reduceIte, div_one, rowGate,
    filter_true, singleton_rank, P.ρ_one 0 P.η_pos.le, incomingGate,
    P.incomingCutoff_one (by rw [P.τ₀_eq]; norm_num : (0:ℝ) ≤ P.τ₀),
    mul_one, CorrectionRowRecipe.normalizer, hcap,
    P.γ_one 0 (by norm_num)]
  norm_num [expect_eq_sum_div_card]

example : 0 < CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ)
    P.incomingCutoff P.ρ P.toHierarchyParams.atomCutoff P.γ 2 2 1
    (fun (_ : Unit) (_ : Unit) => True) (fun (_ : Unit) (_ : Unit) => True)
    (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => 1)
    (fun (_ : Unit × Unit) _ _ => 1) (fun _ => 0) ((), ()) () () := by
  rw [singleton_normalized]
  exact Q_one_pos P

/-- At one full auxiliary source with Kc=1, the actual incoming gate closes the whole column. -/
theorem singleton_closed :
    CorrectionRowRecipe.normalized (polynomialAuxCutoff4 P.θ) P.incomingCutoff P.ρ
      P.toHierarchyParams.atomCutoff P.γ 2 1 1
      (fun (_ : Unit) (_ : Unit) => True) (fun (_ : Unit) (_ : Unit) => True)
      (fun (_ : Unit) (_ : Unit) => True) (fun _ _ => 1)
      (fun (_ : Unit × Unit) _ _ => 1) (fun _ => 0) ((), ()) () () = 0 := by
  have haux : polynomialAuxCutoff4 P.θ 1 0 = 1 :=
    P.aux_full_on_Q_rho (ne_of_gt (Q_one_pos P))
      (by rw [P.ρ_one 0 P.η_pos.le]; norm_num)
  have hrank : kthLargest 1 (univ : Finset Unit) (fun _ => (1:ℝ)) = 1 := by
    simp [kthLargest]
  simp only [CorrectionRowRecipe.normalized, ↓reduceIte, div_one, rowGate,
    filter_true, singleton_rank, P.ρ_one 0 P.η_pos.le, incomingGate, auxScore,
    haux, hrank, P.incomingCutoff_zero (by rw [P.τ₁_eq]; norm_num : P.τ₁ ≤ (1:ℝ)),
    mul_zero, zero_div, zero_mul]

private noncomputable def frameParams : FourthRootHierarchyParams 16 1 16 32 8 :=
  Classical.choice (nonempty (by norm_num) (by norm_num))

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A checked nonempty H=4/P=5 instance of the actual pilot constructor, at horizon zero,
with a positive singleton substochastic input. This is not a claimed unbounded horizon. -/
noncomputable def concretePilot :=
  Matrix.HierarchyParams.H4RankEnvironment.selectedPilotSampling (P := 5) frameParams (0 : Fin 2) (1
      : Fin 2)
    (fun (_ : Unit) => (0 : ZMod 5)) (fun (_ : Unit) => (0 : ZMod 5))
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
    (Matrix.HierarchyParams.H4RankEnvironment.zeroHorizon (P := 5)) (k := 0) (by decide)
    (C := fun _ _ => (1 : ℝ)) (by intros; norm_num)
    (by intro x; norm_num [Matrix.mulVec, dotProduct]) frameParams.k_pos

/-- The same actual positive input also instantiates final-pilot correction sampling laws. -/
noncomputable def concreteCorrection :=
  Matrix.HierarchyParams.H4RankEnvironment.selectedCorrectionSampling (P := 5) frameParams (0 : Fin
      2) (1 : Fin 2)
    (fun (_ : Unit) => (0 : ZMod 5)) (fun (_ : Unit) => (0 : ZMod 5))
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)
    (Matrix.HierarchyParams.H4RankEnvironment.zeroHorizon (P := 5)) (k := 0) (by decide)
    (C := fun _ _ => (1 : ℝ)) (by intros; norm_num)
    (by intro x; norm_num [Matrix.mulVec, dotProduct]) frameParams.k_pos

end
end CutoffRegression
