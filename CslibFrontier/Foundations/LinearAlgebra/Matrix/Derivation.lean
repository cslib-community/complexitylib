/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, derivations of determinants)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of determinants

A derivation that vanishes on every entry of a square matrix vanishes on its determinant
(`Matrix.derivation_det_eq_zero`). If it vanishes on every entry outside row `i`, Laplace expansion
along row `i` and the vanishing of the derivation on the adjugate entries `adjugate A j i` give
`D (det A) = ∑ j, adjugate A j i • D (A i j)` (`Matrix.derivation_det_eq_sum_adjugate`).

## Main results

* `Matrix.derivation_det_eq_zero`: derivations vanishing on the entries vanish on the determinant.
* `Matrix.derivation_adjugate_eq_zero`: derivations vanishing outside row `i` vanish on the
  cofactors of row `i`.
* `Matrix.derivation_det_eq_sum_adjugate`: the derivative of the determinant along one row.
-/

public section

namespace Matrix

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A derivation that vanishes on every entry of a matrix vanishes on its determinant. -/
theorem derivation_det_eq_zero (D : Derivation R A M) (B : Matrix ι ι A)
    (h : ∀ i j, D (B i j) = 0) : D B.det = 0 := by
  rw [det_apply', map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hprod : D (∏ i, B (σ i) i) = 0 :=
    Finset.prod_induction _ (fun a => D a = 0)
      (fun a b ha hb => by rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero])
      (Derivation.map_one_eq_zero D) fun i _ => h _ _
  rw [Derivation.leibniz, hprod, smul_zero, zero_add, Derivation.map_intCast, smul_zero]

/-- A derivation that vanishes on every entry outside row `i` vanishes on the adjugate entries
`adjugate B j i`, whose determinant formula replaces row `i`. -/
theorem derivation_adjugate_eq_zero (D : Derivation R A M) (B : Matrix ι ι A) (i : ι)
    (h : ∀ k, k ≠ i → ∀ j, D (B k j) = 0) (j : ι) : D (adjugate B j i) = 0 := by
  rw [adjugate_apply]
  refine derivation_det_eq_zero D _ fun k l => ?_
  by_cases hk : k = i
  · subst hk
    rw [updateRow_self, Pi.single_apply]
    split_ifs
    · exact Derivation.map_one_eq_zero D
    · exact map_zero D
  · rw [updateRow_ne hk]
    exact h k hk l

/-- If a derivation vanishes on every entry outside row `i`, it acts on the determinant as on
row `i`, weighted by the cofactors of that row. -/
theorem derivation_det_eq_sum_adjugate (D : Derivation R A M) (B : Matrix ι ι A) (i : ι)
    (h : ∀ k, k ≠ i → ∀ j, D (B k j) = 0) :
    D B.det = ∑ j, adjugate B j i • D (B i j) := by
  rw [det_eq_sum_mul_adjugate_row B i, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz, derivation_adjugate_eq_zero D B i h, smul_zero, zero_add]

end Matrix
