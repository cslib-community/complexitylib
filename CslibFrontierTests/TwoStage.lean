/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Probability.TwoStage

/-! Checks of two-stage sampling (`Cslib.Probability.mul_le_card_filter_product` and
`Cslib.Probability.mul_le_dens_filter_prod`) on small concrete products. -/

namespace CslibFrontierTests.TwoStage

/-- Half of the first coordinates are even, and for each of them half of the second coordinates
are below `2`: so a quarter of the pairs are both. -/
example : (1 / 2 : ℝ) * (1 / 2) ≤ (Finset.dens {ab : Fin 4 × Fin 4 |
    ab.1.val % 2 = 0 ∧ ab.2.val < 2} : ℝ) :=
  Cslib.Probability.mul_le_dens_filter_prod (fun a : Fin 4 => a.val % 2 = 0)
    (fun a (b : Fin 4) => a.val % 2 = 0 ∧ b.val < 2) (by norm_num)
    (by
      rw [Finset.dens, show Finset.card {a : Fin 4 | a.val % 2 = 0} = 2 by decide]
      norm_num)
    fun a ha => by
      simp only [ha, true_and]
      rw [Finset.dens, show Finset.card {b : Fin 4 | b.val < 2} = 2 by decide]
      norm_num

/-- The count form ranges over finsets: two of `0, 1, 2, 3` are even, and each has two partners
below `2` in `0, 1, 2`, so at least four pairs of `range 4 ×ˢ range 3` are both. -/
example : (2 : ℝ) * 2 ≤ Finset.card {ab ∈ Finset.range 4 ×ˢ Finset.range 3 |
    ab.1 % 2 = 0 ∧ ab.2 < 2} :=
  Cslib.Probability.mul_le_card_filter_product (Finset.range 4) (Finset.range 3)
    (fun a => a % 2 = 0) (fun a b => a % 2 = 0 ∧ b < 2) (by norm_num)
    (by rw [show Finset.card {a ∈ Finset.range 4 | a % 2 = 0} = 2 by decide]; norm_num)
    fun a _ ha => by
      simp only [ha, true_and]
      rw [show Finset.card {b ∈ Finset.range 3 | b < 2} = 2 by decide]
      norm_num

end CslibFrontierTests.TwoStage
