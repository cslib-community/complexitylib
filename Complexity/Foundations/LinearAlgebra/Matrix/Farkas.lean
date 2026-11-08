/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `LinearAlgebra/Matrix/Farkas.lean`; maybe via PointedCone.DualFG)

public import Complexity.Foundations.LinearAlgebra.Matrix.FourierMotzkin
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Farkas' lemma over linearly ordered fields

A finite system of linear inequalities over a linearly ordered field has no solution exactly when
some nonnegative combination of its rows reads `0 ≤ c` with `c < 0`. The proofs eliminate all
variables by Fourier–Motzkin elimination (`Matrix.FourierMotzkin.exists_projection`), so they hold
over every linearly ordered field, including `ℚ`, and need no topology.

Mathlib proves a topological Farkas lemma for closed convex cones in real locally convex spaces
(`ProperCone.hyperplane_separation`). Its algebraic cone duality `PointedCone.dual` has no Farkas
or Minkowski–Weyl theorem for finitely generated cones. The polyhedral statements below cover
that gap for matrices over an arbitrary linearly ordered field.

See also [DvorakKolmogorov2024], an independent Lean 4 formalization of Farkas-type theorems and
linear-programming duality over linearly ordered fields, with extensions to infinite values.

## Main results

* `Matrix.exists_mulVec_le_iff`: `A *ᵥ x ≤ b` is solvable iff `0 ≤ y ⬝ᵥ b` for every `y ≥ 0`
  with `y ᵥ* A = 0`.
* `Matrix.not_exists_mulVec_le_iff`: the certificate form, `A *ᵥ x ≤ b` is infeasible iff
  there is `y ≥ 0` with `y ᵥ* A = 0` and `y ⬝ᵥ b < 0`.
* `Matrix.exists_nonneg_mulVec_eq_iff`: the equality form, `A *ᵥ x = b` has a solution `x ≥ 0`
  iff `0 ≤ y ⬝ᵥ b` whenever `0 ≤ y ᵥ* A`.
* `Matrix.not_exists_nonneg_mulVec_eq_iff`: its certificate form.

## References

* [DvorakKolmogorov2024]
* [MatousekGartner2007], Sections 6.4 and 6.7
* [Schrijver1986], Section 7.3, Corollaries 7.1d and 7.1e
* [Ziegler1995], Section 1.4
-/

public section

open Matrix

namespace Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Farkas' lemma** for systems of inequalities: `A *ᵥ x ≤ b` has a solution iff every
nonnegative combination `y` of the rows with `y ᵥ* A = 0` satisfies `0 ≤ y ⬝ᵥ b`
[Schrijver1986, Corollary 7.1e]. -/
theorem exists_mulVec_le_iff (A : Matrix ι κ K) (b : ι → K) :
    (∃ x, A *ᵥ x ≤ b) ↔ ∀ y, 0 ≤ y → y ᵥ* A = 0 → 0 ≤ y ⬝ᵥ b := by
  constructor
  · rintro ⟨x, hx⟩ y hy hyA
    have := dotProduct_le_dotProduct_of_nonneg_left hx hy
    rwa [dotProduct_mulVec, hyA, zero_dotProduct] at this
  · intro h
    obtain ⟨ρ, _, T, hT, hTA, hiff⟩ :=
      FourierMotzkin.exists_projection A (0 : Matrix ι PEmpty.{1} K) b
    obtain ⟨x, hx⟩ := (hiff fun j => j.elim).2 fun r => by
      rw [Matrix.mul_zero, zero_mulVec, Pi.zero_apply]
      exact h (T r) (hT r) (congr_fun hTA r)
    exact ⟨x, by rwa [zero_mulVec, add_zero] at hx⟩

/-- **Farkas' lemma**, certificate form: `A *ᵥ x ≤ b` is infeasible iff some `y ≥ 0` has
`y ᵥ* A = 0` and `y ⬝ᵥ b < 0` [Schrijver1986, Corollary 7.1e]. -/
theorem not_exists_mulVec_le_iff (A : Matrix ι κ K) (b : ι → K) :
    (¬∃ x, A *ᵥ x ≤ b) ↔ ∃ y, 0 ≤ y ∧ y ᵥ* A = 0 ∧ y ⬝ᵥ b < 0 := by
  rw [exists_mulVec_le_iff]
  push Not
  rfl

/-- **Farkas' lemma**, equality form: `A *ᵥ x = b` has a solution `x ≥ 0` iff `0 ≤ y ⬝ᵥ b` for
every `y` with `0 ≤ y ᵥ* A` [Schrijver1986, Corollary 7.1d]. -/
theorem exists_nonneg_mulVec_eq_iff (A : Matrix ι κ K) (b : ι → K) :
    (∃ x, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∀ y, 0 ≤ y ᵥ* A → 0 ≤ y ⬝ᵥ b := by
  classical
  constructor
  · rintro ⟨x, hx, rfl⟩ y hy
    rw [dotProduct_mulVec]
    exact dotProduct_nonneg_of_nonneg hy hx
  · intro h
    -- `A x = b` and `x ≥ 0` as the system `A x ≤ b`, `-A x ≤ -b`, `-x ≤ 0`
    let M : Matrix (ι ⊕ ι ⊕ κ) κ K := fromRows A (fromRows (-A) (-1))
    let r : ι ⊕ ι ⊕ κ → K := Sum.elim b (Sum.elim (-b) 0)
    obtain ⟨x, hx⟩ := (exists_mulVec_le_iff M r).2 fun w hw hwM => by
      have hwM' : (w ∘ Sum.inl - (w ∘ Sum.inr) ∘ Sum.inl) ᵥ* A = (w ∘ Sum.inr) ∘ Sum.inr := by
        simp only [M, vecMul_fromRows, vecMul_neg, vecMul_one] at hwM
        rw [sub_vecMul]
        linear_combination hwM
      have hy : 0 ≤ (w ∘ Sum.inl - (w ∘ Sum.inr) ∘ Sum.inl) ᵥ* A := by
        rw [hwM']
        exact fun k => hw _
      have := h _ hy
      rw [← Sum.elim_comp_inl_inr w, ← Sum.elim_comp_inl_inr (w ∘ Sum.inr)]
      rw [sub_dotProduct] at this
      simp only [r, sumElim_dotProduct_sumElim, dotProduct_neg, dotProduct_zero, add_zero]
      linarith
    refine ⟨x, fun k => ?_, le_antisymm (fun i => hx (.inl i)) fun i => ?_⟩
    · have := hx (.inr (.inr k))
      simp only [M, r, fromRows_mulVec, neg_mulVec, one_mulVec, Sum.elim_inr, Pi.neg_apply,
        Pi.zero_apply, neg_nonpos] at this
      exact this
    · have := hx (.inr (.inl i))
      simp only [M, r, fromRows_mulVec, neg_mulVec, Sum.elim_inr, Sum.elim_inl, Pi.neg_apply,
        neg_le_neg_iff] at this
      exact this

/-- **Farkas' lemma**, equality certificate form: `A *ᵥ x = b` has no solution `x ≥ 0` iff some
`y` has `0 ≤ y ᵥ* A` and `y ⬝ᵥ b < 0` [Schrijver1986, Corollary 7.1d]. -/
theorem not_exists_nonneg_mulVec_eq_iff (A : Matrix ι κ K) (b : ι → K) :
    (¬∃ x, 0 ≤ x ∧ A *ᵥ x = b) ↔ ∃ y, 0 ≤ y ᵥ* A ∧ y ⬝ᵥ b < 0 := by
  rw [exists_nonneg_mulVec_eq_iff]
  push Not
  rfl

end Matrix
