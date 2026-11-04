/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Foundations.Combinatorics.Expander.RelativeShearTranslation

/-!
# The relative Poincaré inequality for shears and translations

Concrete moves with a spectator, the transform of a constant, and a client of the relative
Poincaré inequality: a function invariant under the four moves is constant on every fiber
`{x} × (ZMod n × ZMod n)`, for every `n` and every pair of spectator permutations.
-/

namespace ComplexityTests.RelativeShearTranslation

open Cslib Cslib.RotationMap Finset
open scoped BigOperators

-- The shears move the spectator; the translations do not.
example : twistedShearTranslationMove (Equiv.addRight (1 : ZMod 3)) (Equiv.refl _) 5 0
    (0, (1, 2)) = (1, (3, 2)) := by decide
example : twistedShearTranslationMove (Equiv.addRight (1 : ZMod 3)) (Equiv.refl _) 5 1
    (0, (1, 2)) = (0, (1, 3)) := by decide
example : twistedShearTranslationMove (Equiv.addRight (1 : ZMod 3)) (Equiv.refl _) 5 2
    (2, (4, 2)) = (2, (0, 2)) := by decide

-- A constant has no nonzero frequencies.
example : ZMod.dftProd (N := 4) (fun _ ↦ (7 : ℂ)) (1, 3) = 0 :=
  ZMod.dftProd_const_of_ne_zero 7 (by decide)

/-- **A client**: a real function on `X × (ZMod n × ZMod n)` invariant under the four moves is
constant on every fiber, whatever the spectator permutations. -/
example {X : Type*} [Fintype X] (n : ℕ) [NeZero n] (π₁ π₂ : Equiv.Perm X)
    (f : X × (ZMod n × ZMod n) → ℝ)
    (hf : ∀ k p, f (twistedShearTranslationMove π₁ π₂ n k p) = f p) (p : X × (ZMod n × ZMod n)) :
    f p = 𝔼 w, f (p.1, w) := by
  have h := expect_sq_sub_expect_fiber_le_twistedShearTranslation π₁ π₂ f
  simp only [hf, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    expect_const_zero, sum_const_zero, mul_zero] at h
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg fun q ↦ sq_nonneg
    (f q - 𝔼 w, f (q.1, w))).1 (le_antisymm h (expect_nonneg fun _ _ ↦ sq_nonneg _))
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h0 p))

end ComplexityTests.RelativeShearTranslation
