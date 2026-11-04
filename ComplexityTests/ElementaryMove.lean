/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.ElementaryMove

/-!
# Elementary moves on the nonzero vectors of `(ZMod P) ^ H`

A concrete elementary move, and a client of the Poincaré inequality: for every prime `P`, a real
function on `(ZMod P) ^ 3` invariant under the six elementary moves is constant on the nonzero
vectors.
-/

namespace ComplexityTests.ElementaryMove

open Cslib Cslib.RotationMap Finset
open scoped BigOperators

-- `F ↦ F + F 2 • e 0` on `(ZMod 5) ^ 3`.
example : elementaryMove (P := 5) 0 2 ![1, 2, 3] = ![4, 2, 3] := by decide
-- It wraps around.
example : elementaryMove (P := 5) 1 0 ![4, 3, 0] = ![4, 2, 0] := by decide

/-- **A client**: for every prime `P`, a function on `(ZMod P) ^ 3` invariant under the elementary
moves takes one value on all nonzero vectors. -/
example (P : ℕ) [Fact P.Prime] (g : (Fin 3 → ZMod P) → ℝ)
    (hg : ∀ a b F, a ≠ b → g (elementaryMove a b F) = g F) (F F' : Fin 3 → ZMod P)
    (hF : F ≠ 0) (hF' : F' ≠ 0) : g F = g F' := by
  obtain ⟨m, hm⟩ := exists_expect_sq_sub_le_elementaryMove le_rfl g
  have hzero : ∑ a, ∑ b ∈ univ.erase a, 𝔼 F, (g (elementaryMove a b F) - g F) ^ 2 = 0 :=
    sum_eq_zero fun a _ ↦ sum_eq_zero fun b hb ↦ by
      simp [hg a b _ (mem_erase.1 hb).1.symm]
  rw [hzero, mul_zero] at hm
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg fun G ↦ by
    split_ifs
    · exact le_rfl
    · exact sq_nonneg (g G - m)).1 (le_antisymm hm (expect_nonneg fun G _ ↦ by
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _))
  have e (G : Fin 3 → ZMod P) (hG : G ≠ 0) : g G = m := by
    have := congrFun h0 G
    simp only [hG, ite_false, Pi.zero_apply] at this
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  rw [e F hF, e F' hF']

end ComplexityTests.ElementaryMove
