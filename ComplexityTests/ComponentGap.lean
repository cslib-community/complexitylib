/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import ComplexityTests.BoxProductExpander
import Complexity.Probability.PairwiseIndependentHash.ComponentGap

/-!
# The product walk over channels and free bits

Concrete moves of a product of permutation families and of the free-bit torus, the Poincaré
inequality on the cube `(ZMod 2) ^ 3` inherited from the two-point walk, a client of the torus
inequality for every number of bits, and conditional averaging over two channels over `𝔽₅` and
`𝔽₇` with eight-valued free bits, with every hypothesis discharged.
-/

namespace ComplexityTests.ComponentGap

open Cslib Cslib.Probability Cslib.RotationMap Finset
open ComplexityTests.BoxProductExpander (flip poincare_flip)
open scoped BigOperators

-- A move of the product changes only its component.
example : piPerms (fun _ : Fin 3 ↦ flip) ⟨1, ()⟩ ![0, 0, 1] = ![0, 1, 1] := by
  rw [piPerms_apply]
  decide

/-- The cube `(ZMod 2) ^ 3`, a product of three edges, inherits the constant `4`. -/
example (f : (Fin 3 → ZMod 2) → ℝ) (hf : 𝔼 x, f x = 0) :
    4 * 𝔼 x, f x ^ 2 ≤ ∑ k, 𝔼 x, (f (piPerms (fun _ : Fin 3 ↦ flip) k x) - f x) ^ 2 :=
  mul_expect_sq_le_piPerms _ (fun _ ↦ poincare_flip) f hf

-- On the torus `(ZMod 8) ^ 3`, `1 + E_01` adds the coordinate `1` to the coordinate `0`, wrapping
-- around, and a translation adds `1` to one coordinate.
example : torusMove 3 8 (.inl ⟨(0, 1), by decide⟩) ![7, 1, 0] = ![0, 1, 0] := by
  rw [torusMove_inl]
  decide
example : torusMove 3 8 (.inr 2) ![7, 1, 7] = ![7, 1, 0] := by
  rw [torusMove_inr]
  decide

-- Two channels and the torus have `3 · 3 ^ 2 = 27` moves.
example : Fintype.card ((Σ _ : Fin 2, {p : Fin 3 × Fin 3 // p.1 ≠ p.2} ⊕ Fin 3) ⊕
    ({p : Fin 3 × Fin 3 // p.1 ≠ p.2} ⊕ Fin 3)) = 27 := card_componentMove_index

/-- **A client of the torus inequality**: for every number `q` of bits per coordinate, a real
function on `(ZMod (2 ^ q)) ^ 2` invariant under the affine moves is constant. -/
example (q : ℕ) (f : (Fin 2 → ZMod (2 ^ q)) → ℝ) (hf : ∀ k w, f (torusMove 2 (2 ^ q) k w) = f w)
    (w w' : Fin 2 → ZMod (2 ^ q)) : f w = f w' := by
  set f₀ := fun w ↦ f w - 𝔼 v, f v
  have h := expect_sq_le_torusMove le_rfl f₀ (by simp [f₀, expect_sub_distrib])
  simp only [f₀, hf, sub_self] at h
  norm_num at h
  have h0 := (Fintype.expect_eq_zero_iff_of_nonneg fun w ↦ sq_nonneg (f w - 𝔼 v, f v)).1
    (le_antisymm h (expect_nonneg fun _ _ ↦ sq_nonneg _))
  have e (w) : f w = 𝔼 v, f v := sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h0 w))
  rw [e w, e w']

instance (j : Fin 2) : Fact (![5, 7] j).Prime := by
  fin_cases j
  exacts [⟨Nat.prime_five⟩, ⟨by decide⟩]

instance (j : Fin 2) : NeZero (![3, 4] j) := by
  fin_cases j
  exacts [⟨by norm_num⟩, ⟨by norm_num⟩]

/-- **Conditional averaging over two channels and free bits, with every hypothesis discharged**:
channels over `𝔽₅` and `𝔽₇` with sides `3` and `4`, conditioned on retaining any identifiers
`y`, together with free bits in `(ZMod 8) ^ 3`. Each step of the lazy product walk contracts the
variance by `(1 - 1 / 37822464) ^ 2`. -/
example (y : ∀ j : Fin 2, ZMod (![5, 7] j))
    (f : (∀ j, RetentionSlice (![5, 7] j) 3 1 (![3, 4] j) (y j)) × (Fin 3 → ZMod 8) → ℝ)
    (t : ℕ) :
    𝔼 A, ((((ofPerms (componentMove 3 8 ![5, 7] ![3, 4])).lazy.reindex
        (componentEquiv 8 (fun j ↦ by fin_cases j <;> decide) y).symm).walk ^ t) f A -
          𝔼 B, f B) ^ 2 ≤ (1 - 1 / 37822464) ^ (2 * t) * 𝔼 A, (f A - 𝔼 B, f B) ^ 2 := by
  have h := expect_walk_pow_componentMove_sub_expect_sq_le le_rfl
    (fun j ↦ by fin_cases j <;> decide) y f t
  norm_num at h ⊢
  exact h

end ComplexityTests.ComponentGap
