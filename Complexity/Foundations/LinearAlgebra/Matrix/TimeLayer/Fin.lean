/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.TimeLayer

/-!
# Time layers with consecutive natural-number identifiers

Reindex `Matrix.timeLayer` on `Fin ((T + 1) * n)` by the identifier `i * n + u` for clock `i`
and base vertex `u`. Division and remainder recover the two components. The order, row bound,
linear system and inverse formula are transported from the existing time-layer construction.

## Main definitions

* `Matrix.timeLayerEquiv`: the explicit clock/base equivalence.
* `Matrix.finTimeLayer`, `Matrix.finTimeLayerReward`, `Matrix.finTimeLayerPotential`: the
  existing time-layer construction on consecutive finite identifiers.

## Main results

* `Matrix.finTimeLayer_isStrictUpperTriangular`: numeric order is the forward clock order.
* `Matrix.finTimeLayer_mulVec_one_le`, `Matrix.finTimeLayerPotential_mem_Icc`: global bounds.
* `Matrix.one_sub_finTimeLayer_mulVec`, `Matrix.inv_one_sub_finTimeLayer_mulVec`: exact equations.
-/

public section

namespace Matrix

variable {n : ℕ} {R : Type*}

/-- Split a consecutive identifier into its clock and base vertex. -/
@[expose] def timeLayerEquiv (T n : ℕ) :
    Fin ((T + 1) * n) ≃ Lex (Fin (T + 1) × Fin n) :=
  finProdFinEquiv.symm.trans toLex

/-- The clock is the quotient and the base vertex is the remainder. -/
theorem timeLayerEquiv_apply (T n : ℕ) (a : Fin ((T + 1) * n)) :
    timeLayerEquiv T n a = toLex (a.divNat, a.modNat) := rfl

/-- The identifier has the usual row-major arithmetic value. -/
theorem timeLayerEquiv_val (T n : ℕ) (a : Fin ((T + 1) * n)) :
    a.val = (ofLex (timeLayerEquiv T n a)).2.val +
      n * (ofLex (timeLayerEquiv T n a)).1.val := by
  have h := finProdFinEquiv_apply_val (ofLex (timeLayerEquiv T n a))
  simp only [timeLayerEquiv, Equiv.trans_apply, ofLex_toLex, Equiv.apply_symm_apply] at h
  exact h

/-- Numeric identifiers reflect the clock-then-base lexicographic order. -/
theorem timeLayerEquiv_lt (T n : ℕ) {a b : Fin ((T + 1) * n)}
    (h : timeLayerEquiv T n a < timeLayerEquiv T n b) : a < b := by
  rw [Fin.lt_def, timeLayerEquiv_val T n a, timeLayerEquiv_val T n b]
  rcases Prod.Lex.lt_iff.mp h with hclock | ⟨hclock, hbase⟩
  · have hc : (ofLex (timeLayerEquiv T n a)).1.val + 1 ≤
        (ofLex (timeLayerEquiv T n b)).1.val := hclock
    have hb := (ofLex (timeLayerEquiv T n a)).2.isLt
    nlinarith
  · rw [hclock]
    exact Nat.add_lt_add_right hbase _

/-- The existing clocked matrix, indexed consecutively by clock then base vertex. -/
@[expose] def finTimeLayer [Zero R] (T : ℕ) (P : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin ((T + 1) * n)) (Fin ((T + 1) * n)) R :=
  (timeLayer T P).submatrix (timeLayerEquiv T n) (timeLayerEquiv T n)

/-- The existing terminal reward on consecutive identifiers. -/
@[expose] def finTimeLayerReward [Zero R] (T : ℕ) (e : Fin n → R) :
    Fin ((T + 1) * n) → R := timeLayerReward T e ∘ timeLayerEquiv T n

/-- The existing remaining-time potential on consecutive identifiers. -/
@[expose] def finTimeLayerPotential [Semiring R] (T : ℕ)
    (P : Matrix (Fin n) (Fin n) R) (e : Fin n → R) : Fin ((T + 1) * n) → R :=
  timeLayerPotential T P e ∘ timeLayerEquiv T n

/-- A finite-index entry tests the next clock and then uses the two base remainders. -/
theorem finTimeLayer_apply [Zero R] (T : ℕ) (P : Matrix (Fin n) (Fin n) R)
    (a b : Fin ((T + 1) * n)) : finTimeLayer T P a b =
      if a.val / n + 1 = b.val / n then P a.modNat b.modNat else 0 := rfl

/-- Numeric order gives strict forwardness for the reindexed matrix. -/
theorem finTimeLayer_isStrictUpperTriangular [Zero R] (T : ℕ)
    (P : Matrix (Fin n) (Fin n) R) : (finTimeLayer T P).IsStrictUpperTriangular := by
  intro a b hab
  exact timeLayer_isStrictUpperTriangular T P (fun h => hab (timeLayerEquiv_lt T n h))

/-- Nonnegativity is preserved by the explicit reindexing. -/
theorem finTimeLayer_nonneg [Zero R] [Preorder R] {P : Matrix (Fin n) (Fin n) R}
    (hP : ∀ a b, 0 ≤ P a b) (T : ℕ) : ∀ a b, 0 ≤ finTimeLayer T P a b :=
  fun a b => timeLayer_nonneg hP T (timeLayerEquiv T n a) (timeLayerEquiv T n b)

/-- Clocking and explicit reindexing preserve the substochastic row bound. -/
theorem finTimeLayer_mulVec_one_le [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {P : Matrix (Fin n) (Fin n) R} (hP : P *ᵥ 1 ≤ 1) (T : ℕ) :
    finTimeLayer T P *ᵥ 1 ≤ 1 := by
  intro a
  rw [finTimeLayer, submatrix_mulVec_equiv]
  exact timeLayer_mulVec_one_le hP T (timeLayerEquiv T n a)

/-- The finite-index potential is bounded at every clock and base identifier. -/
theorem finTimeLayerPotential_mem_Icc [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {P : Matrix (Fin n) (Fin n) R} {e : Fin n → R} (hP0 : ∀ a b, 0 ≤ P a b)
    (hP1 : P *ᵥ 1 ≤ 1) (he : e ∈ Set.Icc 0 1) (T : ℕ) :
    finTimeLayerPotential T P e ∈ Set.Icc 0 1 := by
  have h := timeLayerPotential_mem_Icc hP0 hP1 he T
  exact ⟨fun a => h.1 (timeLayerEquiv T n a), fun a => h.2 (timeLayerEquiv T n a)⟩

/-- At clock zero, the potential is the original terminal expectation. -/
theorem finTimeLayerPotential_zero [Semiring R] (T : ℕ) (P : Matrix (Fin n) (Fin n) R)
    (e : Fin n → R) (x : Fin n) :
    finTimeLayerPotential T P e ((timeLayerEquiv T n).symm (toLex (0, x))) =
      (P ^ T *ᵥ e) x := by
  rw [finTimeLayerPotential, Function.comp_apply, Equiv.apply_symm_apply,
    timeLayerPotential_zero]

private theorem one_sub_finTimeLayer [Ring R] (T : ℕ) (P : Matrix (Fin n) (Fin n) R) :
    1 - finTimeLayer T P =
      (1 - timeLayer T P).submatrix (timeLayerEquiv T n) (timeLayerEquiv T n) := by
  simp only [submatrix_sub, Pi.sub_apply, submatrix_one_equiv, finTimeLayer]

/-- The finite-index potential solves the same terminal-reward linear system. -/
theorem one_sub_finTimeLayer_mulVec [Ring R] (T : ℕ) (P : Matrix (Fin n) (Fin n) R)
    (e : Fin n → R) :
    (1 - finTimeLayer T P) *ᵥ finTimeLayerPotential T P e = finTimeLayerReward T e := by
  rw [one_sub_finTimeLayer, submatrix_mulVec_equiv]
  simpa only [finTimeLayerPotential, finTimeLayerReward, Function.comp_def,
    Equiv.apply_symm_apply] using
    congrArg (fun f => f ∘ timeLayerEquiv T n) (one_sub_timeLayer_mulVec T P e)

/-- The inverse-matrix formula is preserved by the explicit finite reindexing. -/
theorem inv_one_sub_finTimeLayer_mulVec [CommRing R] (T : ℕ)
    (P : Matrix (Fin n) (Fin n) R) (e : Fin n → R) :
    (1 - finTimeLayer T P)⁻¹ *ᵥ finTimeLayerReward T e = finTimeLayerPotential T P e := by
  rw [one_sub_finTimeLayer, inv_submatrix_equiv, submatrix_mulVec_equiv]
  simpa only [finTimeLayerReward, finTimeLayerPotential, Function.comp_def,
    Equiv.apply_symm_apply] using
    congrArg (fun f => f ∘ timeLayerEquiv T n) (inv_one_sub_timeLayer_mulVec T P e)

end Matrix
