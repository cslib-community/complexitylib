/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Expander.LowerBound
import CslibFrontier.Foundations.Combinatorics.Sunflower.LowerBound
import CslibFrontier.Probability.LoomisWhitney

/-!
Regression clients for the trace lower bound on spectral expansion, the Erdős–Rado lower bound
for the sunflower lemma, and the discrete Loomis–Whitney inequality.
-/

namespace CslibFrontierTests.CombinatorialBounds

open Cslib Finset

/-! ### Spectral expansion -/

-- A `2`-regular multigraph on four vertices has `λ ^ 2 ≥ (4 - 2) / (2 · 3) = 1 / 3`.
example (G : RotationMap (Fin 4) (Fin 2)) : 1 / 3 ≤ G.spectralExpansion ^ 2 := by
  refine le_trans (le_of_eq ?_) (G.div_le_sq_spectralExpansion (by simp))
  simp only [Fintype.card_fin]
  norm_num

example (G : RotationMap (Fin 3) (Fin 2)) : 0 < G.spectralExpansion :=
  G.spectralExpansion_pos (by simp)

-- A `2`-regular multigraph on eight vertices has `λ ≥ 1 / √4 = 1 / 2`.
example (G : RotationMap (Fin 8) (Fin 2)) : 1 / 2 ≤ G.spectralExpansion := by
  have h := G.one_div_sqrt_two_mul_le_spectralExpansion (by simp)
  rwa [Fintype.card_fin, Nat.cast_ofNat, Real.sqrt_mul_self zero_le_two] at h

-- Degree equal to the number of vertices allows `λ = 0`.
example : (RotationMap.complete (Fin 5)).spectralExpansion = 0 :=
  RotationMap.spectralExpansion_complete

/-! ### Sunflowers -/

example : #(Sunflower.graphFamily (Fin 3) Bool) = 8 := by simp [Sunflower.card_graphFamily]

-- Eight sets of size three without a sunflower with three petals.
example : ¬ ContainsSunflower 3 (Sunflower.graphFamily (Fin 3) Bool) := by
  simpa using Sunflower.not_containsSunflower_graphFamily (ι := Fin 3) (β := Bool)

example : ∃ F : Finset (Finset (Fin 2 × Fin 2)),
    #F = 4 ∧ (∀ s ∈ F, #s = 2) ∧ ¬ ContainsSunflower 3 F :=
  exists_card_eq_pow_not_containsSunflower 3 2 (by decide)

example : ContainsSunflower 2 ({{0}, {1}} : Finset (Finset (Fin 3))) :=
  (containsSunflower_iff_le_card (by decide) 2).2 (by decide)

example : ¬ ContainsSunflower 3 ({{0}, {1}} : Finset (Finset (Fin 3))) := by
  rw [containsSunflower_iff_le_card (by decide)]
  decide

example : #Sunflower.twoTriangles = 6 ∧ ¬ ContainsSunflower 3 Sunflower.twoTriangles :=
  ⟨Sunflower.card_twoTriangles, Sunflower.not_containsSunflower_twoTriangles⟩

/-! ### Loomis–Whitney -/

-- In three dimensions: `|A| ^ 2` is at most the product of the sizes of the three projections.
example (A : Finset (Fin 3 → Bool)) :
    #A ^ 2 ≤ ∏ i, #(A.image (univ.erase i).restrict) := by
  have h := Cslib.Finset.card_pow_le_prod_card_image_restrict_erase (α := fun _ => Bool)
    (by simp) A
  rwa [Fintype.card_fin] at h

end CslibFrontierTests.CombinatorialBounds
