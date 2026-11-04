/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Uniform expectations of one coordinate

A coordinate of a uniform finite product has the uniform marginal, including when
conditioning on an event of that coordinate. All other coordinates remain spectators.
The conditional identity includes empty events, whose finite expectation is zero.
-/

public section
open Finset
open scoped BigOperators

namespace Finset

/-- Averaging a function of one coordinate integrates out all spectator coordinates. -/
theorem expect_pi_eval {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [Nonempty A] (j : R) (F : A → ℝ) :
    (𝔼 σ : R → A, F (σ j)) = 𝔼 a, F a := by
  classical
  calc
    _ = 𝔼 p : A × ({r : R // r ≠ j} → A), F p.1 :=
      Fintype.expect_equiv (Equiv.piSplitAt j (fun _ : R => A)) _ _ (fun _ => rfl)
    _ = _ := by rw [← univ_product_univ, expect_product]; simp

/-- A conditional coordinate average retains the actual event and all spectators.
No nonemptiness premise is needed, and no independent copy of the product is introduced. -/
theorem expect_pi_eval_filter {R A : Type*} [Fintype R] [DecidableEq R]
    [Fintype A] [Nonempty A] (j : R) (p : A → Prop) [DecidablePred p]
    (F : A → ℝ) :
    (𝔼 σ ∈ ({σ : R → A | p (σ j)} : Finset _), F (σ j)) =
      𝔼 a ∈ ({a | p a} : Finset A), F a := by
  classical
  calc
    _ = 𝔼 z ∈ ({a | p a} : Finset A) ×ˢ
        (univ : Finset ({r : R // r ≠ j} → A)), F z.1 := by
      apply expect_equiv (Equiv.piSplitAt j (fun _ : R => A))
      · intro σ
        simp
      · intro σ _
        rfl
    _ = _ := by rw [expect_product]; simp

end Finset
