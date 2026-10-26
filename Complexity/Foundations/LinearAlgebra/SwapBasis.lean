/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

/-!
# An explicit basis for exchanging two coordinates

The one-pair construction in §4.2 (pp. 27–28) of [OpenAI2026ETH] uses diagonal vectors,
symmetric sums, and antisymmetric differences. Here the ambient space is functions on ordered
pairs of `Fin r`, over the rationals. The change of coordinates is explicit, including when
`r = 0` or `r = 1`. This module does not construct the paper's exchange matrix or claim an
algorithmic complexity bound.
-/

public section

namespace Cslib.SwapBasis

/-- Rational coordinates indexed by ordered pairs. -/
abbrev Coordinates (r : ℕ) := (Fin r × Fin r) → ℚ

/-- Exchange the two indices of a coordinate vector. -/
def exchange (r : ℕ) : Coordinates r →ₗ[ℚ] Coordinates r where
  toFun v p := v p.swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coefficients in the diagonal, symmetric, and antisymmetric basis. The antisymmetric
coordinate indexed by `(a, b)` with `b < a` multiplies `e_(b,a) - e_(a,b)`. -/
def coefficients {r : ℕ} (v : Coordinates r) (p : Fin r × Fin r) : ℚ :=
  if p.1 = p.2 then v p
  else if p.1 < p.2 then (v p + v p.swap) / 2
  else (v p.swap - v p) / 2

/-- Reconstruct ordinary coordinates from diagonal, symmetric, and antisymmetric coefficients. -/
def reconstruct {r : ℕ} (c : Coordinates r) (p : Fin r × Fin r) : ℚ :=
  if p.1 = p.2 then c p
  else if p.1 < p.2 then c p + c p.swap
  else c p.swap - c p

/-- Reconstruction cancels coefficient extraction. -/
theorem reconstruct_coefficients {r : ℕ} (v : Coordinates r) :
    reconstruct (coefficients v) = v := by
  funext p
  rcases p with ⟨a, b⟩
  rcases lt_trichotomy a b with h | h | h
  · simp only [reconstruct, coefficients, Prod.fst, Prod.snd, Prod.swap_prod_mk,
      ne_of_lt h, ne_of_gt h, h, not_lt_of_gt h, ↓reduceIte]
    ring
  · subst b
    simp only [reconstruct, coefficients, Prod.fst, Prod.snd, ↓reduceIte]
  · simp only [reconstruct, coefficients, Prod.fst, Prod.snd, Prod.swap_prod_mk,
      ne_of_lt h, ne_of_gt h, h, not_lt_of_gt h, ↓reduceIte]
    ring

/-- Coefficient extraction cancels reconstruction. -/
theorem coefficients_reconstruct {r : ℕ} (c : Coordinates r) :
    coefficients (reconstruct c) = c := by
  funext p
  rcases p with ⟨a, b⟩
  rcases lt_trichotomy a b with h | h | h
  · simp only [reconstruct, coefficients, Prod.fst, Prod.snd, Prod.swap_prod_mk,
      ne_of_lt h, ne_of_gt h, h, not_lt_of_gt h, ↓reduceIte]
    ring
  · subst b
    simp only [reconstruct, coefficients, Prod.fst, Prod.snd, ↓reduceIte]
  · simp only [reconstruct, coefficients, Prod.fst, Prod.snd, Prod.swap_prod_mk,
      ne_of_lt h, ne_of_gt h, h, not_lt_of_gt h, ↓reduceIte]
    ring

/-- Explicit rational change of coordinates for the one-pair swap basis. -/
def coefficientEquiv (r : ℕ) : Coordinates r ≃ₗ[ℚ] Coordinates r where
  toFun := coefficients
  invFun := reconstruct
  left_inv := reconstruct_coefficients
  right_inv := coefficients_reconstruct
  map_add' v w := by
    funext p
    simp only [coefficients, Pi.add_apply]
    split_ifs <;> ring
  map_smul' q v := by
    funext p
    simp only [coefficients, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The diagonal/symmetric/antisymmetric basis, indexed without discarding either ordering. -/
noncomputable def basis (r : ℕ) : Basis (Fin r × Fin r) ℚ (Coordinates r) :=
  Basis.ofEquivFun (coefficientEquiv r)

/-- Every vector is reconstructed from its swap-basis coefficients. -/
theorem basis_repr {r : ℕ} (v : Coordinates r) (p : Fin r × Fin r) :
    (basis r).repr v p = coefficients v p := by
  exact Basis.ofEquivFun_repr_apply _ _ _

/-- Swapping twice is the identity, including on the empty space. -/
theorem exchange_exchange {r : ℕ} (v : Coordinates r) : exchange r (exchange r v) = v := rfl

end Cslib.SwapBasis
