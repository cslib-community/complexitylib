/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.PairShearTranslation
import Complexity.Foundations.Probability.EfronStein

/-!
# Shears and translations of coordinate pairs

Concrete pair moves on `ZMod 2 × (Fin 3 → ZMod 5)`, a concrete instance of the Efron–Stein
inequality, and a client of the pair bound: a function invariant under the moves of the pairs
`(i, i + 1)` of `Fin 3` depends only on the spectator, for every modulus `L` and every action on
the spectator.
-/

namespace ComplexityTests.PairShearTranslation

open Cslib Cslib.RotationMap Finset Function
open scoped BigOperators

-- The shear `w ↦ w + w 1 • e 0` acts on the spectator by `ρ`; the translation `w ↦ w + e 2` does
-- not.
example : pairShearTranslationMove (L := 5) (Equiv.addRight (1 : ZMod 2)) (Equiv.refl _) 0 1 0
    (0, ![1, 2, 3]) = (1, ![3, 2, 3]) := by decide
example : pairShearTranslationMove (L := 5) (Equiv.addRight (1 : ZMod 2)) (Equiv.refl _) 2 0 1
    (0, ![1, 2, 4]) = (0, ![0, 2, 4]) := by decide
example : pairShearTranslationMove (L := 5) (Equiv.addRight (1 : ZMod 2)) (Equiv.refl _) 1 2 3
    (0, ![1, 2, 4]) = (0, ![1, 2, 0]) := by decide

/-- The indicator that the two coordinates of a uniform `w : Fin 2 → Bool` agree. -/
noncomputable def eqInd (p : Unit × (Fin 2 → Bool)) : ℝ := if p.2 0 = p.2 1 then 1 else 0

/-- **Efron–Stein on a concrete function**: the second moment of `eqInd` about its average is
`1 / 4`, and the sum of the single-coordinate terms is `1 / 2`. -/
example : 𝔼 p, (eqInd p - 𝔼 w, eqInd (p.1, w)) ^ 2 = 1 / 4 ∧
    ∑ i, 𝔼 p, (eqInd p - 𝔼 a, eqInd (p.1, update p.2 i a)) ^ 2 = 1 / 2 := by
  constructor
  · simp only [Fintype.expect_prod_type, Fin.expect_univ_cons, Fintype.expect_bool,
      Fintype.expect_unique]
    norm_num [eqInd]
  · simp only [Fin.sum_univ_two, Fintype.expect_prod_type, Fin.expect_univ_cons,
      Fintype.expect_bool, Fintype.expect_unique]
    norm_num [eqInd, update_apply]

example : 𝔼 p, (eqInd p - 𝔼 w, eqInd (p.1, w)) ^ 2 ≤
    ∑ i, 𝔼 p, (eqInd p - 𝔼 a, eqInd (p.1, update p.2 i a)) ^ 2 :=
  Fintype.expect_sq_sub_expect_le_sum_expect_sq_sub_update eqInd

/-- **A client**: on `Y × (Fin 3 → ZMod L)`, a real function invariant under the moves of the
pairs `(i, i + 1)` depends only on the spectator, whatever the actions `ρ` on `Y`. -/
example {Y : Type} [Fintype Y] (L : ℕ) [NeZero L] (ρ : Fin 3 → Fin 3 → Equiv.Perm Y)
    (f : Y × (Fin 3 → ZMod L) → ℝ)
    (hf : ∀ i j k p, f (pairShearTranslationMove (ρ i j) (ρ j i) i j k p) = f p)
    (p : Y × (Fin 3 → ZMod L)) :
    f p = 𝔼 w, f (p.1, w) := by
  have h := expect_sq_sub_expect_le_pairShearTranslation ρ (fun i ↦ i + 1) (by decide) f
  simp only [hf, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    expect_const_zero, sum_const_zero, mul_zero] at h
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg fun q ↦ sq_nonneg
    (f q - 𝔼 w, f (q.1, w))).1 (le_antisymm h (expect_nonneg fun _ _ ↦ sq_nonneg _))
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h0 p))

end ComplexityTests.PairShearTranslation
