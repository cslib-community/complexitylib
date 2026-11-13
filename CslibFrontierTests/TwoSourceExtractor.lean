/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.Extractor.TwoSource

/-! Two-source extractors: the Chor–Goldreich bound on concrete sources, the necessity of the
entropy threshold, and weighted Lindsey. -/

namespace CslibFrontierTests.TwoSourceExtractor

open Cslib Cslib.Probability Cslib.Probability.PMF

/-- The inner product of 4-bit strings is a two-source extractor for min-entropies `3` and `3`
with error `2 ^ ((4 - 3 - 3) / 2) / 2 = 1 / 4`. -/
theorem dotProduct_four :
    IsStrongTwoSourceExtractor (fun x y : Fin 4 → Bool => x ⬝ᵥ y) 3 3 (1 / 4) := by
  have h := isStrongTwoSourceExtractor_dotProduct (ι := Fin 4) 3 3
  rw [Fintype.card_fin] at h
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  rw [show ((4 : ℕ) : ℝ) - 3 - 3 = -2 by norm_num, show (-2 : ℝ) / 2 = -1 by norm_num,
    Real.rpow_neg_one]
  norm_num

private theorem three_le_minEntropy_uniform :
    (3 : ℝ) ≤ minEntropy (PMF.uniformOfFintype (Fin 4 → Bool)) := by
  rw [minEntropy_uniformOfFintype, BitString.logb_card]
  norm_num

-- The entropy hypotheses are satisfiable: two independent uniform 4-bit sources.
example :
    dist ((PMF.uniformOfFintype (Fin 4 → Bool)).bind fun x =>
        (PMF.uniformOfFintype (Fin 4 → Bool)).map fun y => x ⬝ᵥ y)
      (PMF.uniformOfFintype Bool) ≤ 1 / 4 :=
  dotProduct_four.isTwoSourceExtractor _ _ three_le_minEntropy_uniform
    three_le_minEntropy_uniform

-- At `k₁ + k₂ = n` the inner product fails: strings on the first two coordinates are orthogonal
-- to strings on the last two.
example : ¬ IsTwoSourceExtractor (fun x y : Fin 4 → Bool => x ⬝ᵥ y) 2 2 (1 / 4) := by
  have h := not_isTwoSourceExtractor_dotProduct (ι := Fin 4) {0, 1} (ε := 1 / 4) (by norm_num)
  have hS : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have hSc : ({0, 1} : Finset (Fin 4))ᶜ.card = 2 := by decide
  rw [hS, hSc] at h
  exact_mod_cast h

-- Weighted Lindsey on 3-bit strings: a uniform weight against a point mass.
example :
    (∑ x : Fin 3 → Bool, ∑ y : Fin 3 → Bool, (1 / 8 : ℝ) * (if y = 0 then 1 else 0) *
      BitString.signVal (x ⬝ᵥ y)) ^ 2 ≤
      2 ^ 3 * (∑ _x : Fin 3 → Bool, (1 / 8 : ℝ) ^ 2) *
        ∑ y : Fin 3 → Bool, (if y = 0 then (1 : ℝ) else 0) ^ 2 := by
  have h := BitString.sq_sum_mul_signVal_dotProduct_le (ι := Fin 3) (fun _ => (1 / 8 : ℝ))
    (fun y => if y = 0 then (1 : ℝ) else 0)
  simpa only [Fintype.card_fin] using h

end CslibFrontierTests.TwoSourceExtractor
