/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Foundations.LinearAlgebra.Matrix.HessianPermanent
import Complexity.Foundations.Data.Matrix.Permanent.Blocks
import Complexity.Foundations.LinearAlgebra.Matrix.GrenetPermanent
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Determinantal complexity: the Mignon–Ressayre and Grenet bounds

A polynomial `f` has a *determinantal representation of size `m`* if it is the determinant of an
`m × m` matrix whose entries are affine-linear polynomials (total degree at most one). Its
*determinantal complexity* `determinantalComplexity f : ℕ∞` is the least such `m`.

Valiant [Valiant1979Algebra] shows that every polynomial has a determinantal representation, so
the determinantal complexity is finite. That universality theorem is not formalized here, so in
general `determinantalComplexity f = ⊤` means that `f` has no representation.

**Grenet's theorem** [Grenet][Grenet2011]: the generic `n × n` permanent is a projection of the
generic `(2ⁿ - 1) × (2ⁿ - 1)` determinant (`isProjection_permanent_det_two_pow_sub_one`), over
every commutative ring. Hence `dc(perm_n) ≤ 2ⁿ - 1` (`determinantalComplexity_permanent_le`), so
the determinantal complexity of the permanent is finite. The matrix is
`Matrix.grenetMatrix`.

**Mignon–Ressayre theorem** [Mignon and Ressayre][MignonRessayre2004]: over a field of
characteristic zero, the generic `n × n` permanent has determinantal complexity at least `n² / 2`
(`sq_le_two_mul_determinantalComplexity_permanent_of_charZero`). With Grenet's theorem,
`n² / 2 ≤ dc(perm_n) ≤ 2ⁿ - 1` in characteristic zero. The proof compares Hessian ranks
at a zero of the permanent. The Hessian of the determinant of a matrix of affine polynomials has
rank at most `2 m` at every zero of the determinant (`Matrix.rank_hessian_det_le`), while the
Hessian of the permanent has full rank `n²` at the Mignon–Ressayre point
(`Matrix.rank_hessian_permanent_mignonRessayrePoint`).

The general-field statement `sq_le_two_mul_determinantalComplexity_permanent` only assumes
`(n - 1)! ≠ 0` in the field, that is, characteristic zero or a characteristic at least `n`.
Mignon and Ressayre state characteristic zero; the extension of Cai, Chen and Li to every
characteristic other than `2` is not formalized. To apply the bound to a concrete matrix, use the
representation form `sq_le_two_mul_of_hasDeterminantalRepresentation_permanent` or
`Matrix.card_mul_card_le_two_mul_card_of_permanent_eq_det`.

## Main definitions

* `Cslib.Circuits.Arithmetic.HasDeterminantalRepresentation`: `f` is the determinant of an
  `m × m` matrix of affine polynomials.
* `Cslib.Circuits.Arithmetic.determinantalComplexity`: the least such `m`, in `ℕ∞`.

## Main results

* `Cslib.Circuits.Arithmetic.hasDeterminantalRepresentation_of_isProjection`: a projection of the
  generic `m × m` determinant has a determinantal representation of size `m`.
* `Cslib.Circuits.Arithmetic.isProjection_det_of_forall_exists_eq`: the determinant of a matrix of
  variables and constants is a projection of the generic determinant.
* `Cslib.Circuits.Arithmetic.isProjection_permanent_det_two_pow_sub_one`: Grenet's theorem, the
  `n × n` permanent is a projection of the `(2ⁿ - 1) × (2ⁿ - 1)` determinant.
* `Cslib.Circuits.Arithmetic.determinantalComplexity_permanent_le`: `dc(perm_n) ≤ 2ⁿ - 1`.
* `Cslib.Circuits.Arithmetic.sq_le_two_mul_of_hasDeterminantalRepresentation_permanent`: a
  determinantal representation of the `n × n` permanent has size at least `n² / 2`.
* `Cslib.Circuits.Arithmetic.sq_le_two_mul_determinantalComplexity_permanent_of_charZero`:
  `n² ≤ 2 · dc(perm_n)` in characteristic zero.
* `Cslib.Circuits.Arithmetic.sq_le_two_mul_of_isProjection_permanent_det`: if the `n × n`
  permanent is a projection of the `m × m` determinant, then `n² ≤ 2 m`.

## References

* [B. Grenet, *An upper bound for the permanent versus determinant problem*][Grenet2011]
* [T. Mignon, N. Ressayre, *A quadratic bound for the determinant and permanent
  problem*][MignonRessayre2004]
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Determinantal Complexity Lower Bounds",
  Theorem `thm:Mignon-Ressayre-mainthm`.
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

section Defs

variable {K : Type*} [CommRing K] {σ : Type*}

/-- `f` is the determinant of an `m × m` matrix whose entries are affine-linear polynomials, that
is, polynomials of total degree at most one. -/
@[expose] def HasDeterminantalRepresentation (f : MvPolynomial σ K) (m : ℕ) : Prop :=
  ∃ A : Matrix (Fin m) (Fin m) (MvPolynomial σ K), (∀ i j, (A i j).totalDegree ≤ 1) ∧ A.det = f

/-- The *determinantal complexity* of `f`: the least size of a determinantal representation of
`f`, or `⊤` if there is none. -/
noncomputable def determinantalComplexity (f : MvPolynomial σ K) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : HasDeterminantalRepresentation f m), (m : ℕ∞)

theorem determinantalComplexity_le {f : MvPolynomial σ K} {m : ℕ}
    (h : HasDeterminantalRepresentation f m) : determinantalComplexity f ≤ m :=
  iInf₂_le m h

theorem le_determinantalComplexity_iff {f : MvPolynomial σ K} {k : ℕ∞} :
    k ≤ determinantalComplexity f ↔ ∀ m, HasDeterminantalRepresentation f m → k ≤ m :=
  le_iInf₂_iff

/-- A projection of the generic `m × m` determinant has a determinantal representation of size
`m`. -/
theorem hasDeterminantalRepresentation_of_isProjection [Nontrivial K] {f : MvPolynomial σ K}
    {m : ℕ} (h : IsProjection f (genericMatrix K m).det) : HasDeterminantalRepresentation f m := by
  obtain ⟨ρ, rfl⟩ := h
  refine ⟨(genericMatrix K m).map (projection ρ), fun i j => ?_, ?_⟩
  · simp only [Matrix.map_apply, genericMatrix, Matrix.of_apply, projection_X]
    cases ρ (finProdFinEquiv (i, j)) <;> simp
  · rw [AlgHom.map_det]
    rfl

/-- The generic `m × m` determinant has a determinantal representation of size `m`. -/
theorem hasDeterminantalRepresentation_det [Nontrivial K] (m : ℕ) :
    HasDeterminantalRepresentation (genericMatrix K m).det m :=
  hasDeterminantalRepresentation_of_isProjection (IsProjection.refl _)

/-- The generic `m × m` determinant has determinantal complexity at most `m`. -/
theorem determinantalComplexity_det_le [Nontrivial K] (m : ℕ) :
    determinantalComplexity (genericMatrix K m).det ≤ m :=
  determinantalComplexity_le (hasDeterminantalRepresentation_det m)

/-- The determinant of an `m × m` matrix whose entries are variables or constants is a projection
of the generic `m × m` determinant. -/
theorem isProjection_det_of_forall_exists_eq {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (MvPolynomial σ K))
    (hM : ∀ i j, ∃ s : σ ⊕ K, Sum.elim X (fun a => C a) s = M i j) :
    IsProjection M.det (genericMatrix K m).det := by
  choose ρ hρ using hM
  refine ⟨fun v => ρ (finProdFinEquiv.symm v).1 (finProdFinEquiv.symm v).2, ?_⟩
  rw [AlgHom.map_det]
  congr 1
  refine Matrix.ext fun i j => ?_
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, genericMatrix, Matrix.of_apply, projection_X,
    Equiv.symm_apply_apply, hρ]

/-- **Grenet's theorem** [Grenet][Grenet2011]: over every commutative ring, the generic `n × n`
permanent is a projection of the generic `(2ⁿ - 1) × (2ⁿ - 1)` determinant, with every variable
of the determinant sent to a variable of the permanent, to `0` or to `-1`. The matrix is
`Matrix.grenetMatrix`. -/
theorem isProjection_permanent_det_two_pow_sub_one (n : ℕ) :
    IsProjection (genericMatrix K n).permanent (genericMatrix K (2 ^ n - 1)).det := by
  rw [Matrix.permanent_eq_det_grenetMatrix]
  refine isProjection_det_of_forall_exists_eq _ fun a b => ?_
  rcases Matrix.grenetMatrix_apply_eq (genericMatrix K n) a b with ⟨i, j, h⟩ | h | h
  · exact ⟨Sum.inl (finProdFinEquiv (i, j)), by rw [h]; rfl⟩
  · exact ⟨Sum.inr 0, by simp [h]⟩
  · exact ⟨Sum.inr (-1), by simp [h]⟩

/-- Grenet's theorem as a determinantal representation of size `2ⁿ - 1` of the generic `n × n`
permanent [Grenet][Grenet2011], over every commutative ring. -/
theorem hasDeterminantalRepresentation_permanent_two_pow_sub_one (n : ℕ) :
    HasDeterminantalRepresentation (genericMatrix K n).permanent (2 ^ n - 1) := by
  refine ⟨(genericMatrix K n).grenetMatrix, fun a b => ?_,
    (Matrix.permanent_eq_det_grenetMatrix _).symm⟩
  rcases Matrix.grenetMatrix_apply_eq (genericMatrix K n) a b with ⟨i, j, h⟩ | h | h
  · rw [h, genericMatrix, Matrix.of_apply, X]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  · simp [h]
  · rw [h, totalDegree_neg, totalDegree_one]
    exact zero_le_one

/-- **Grenet's upper bound** [Grenet][Grenet2011]: over every commutative ring, the generic
`n × n` permanent has determinantal complexity at most `2ⁿ - 1`; in particular it is finite. -/
theorem determinantalComplexity_permanent_le (n : ℕ) :
    determinantalComplexity (genericMatrix K n).permanent ≤ (2 ^ n - 1 : ℕ) :=
  determinantalComplexity_le (hasDeterminantalRepresentation_permanent_two_pow_sub_one n)

end Defs

variable {K : Type*} [Field K]

/-- **Mignon–Ressayre bound for representations**: if the generic `n × n` permanent is the
determinant of an `m × m` matrix of affine polynomials over a field with `(n - 1)! ≠ 0`
(characteristic `0` or at least `n`), then `n² ≤ 2 m` [Mignon and Ressayre][MignonRessayre2004]. -/
theorem sq_le_two_mul_of_hasDeterminantalRepresentation_permanent {n m : ℕ}
    (hfact : ((n - 1).factorial : K) ≠ 0)
    (h : HasDeterminantalRepresentation (genericMatrix K n).permanent m) : n ^ 2 ≤ 2 * m := by
  obtain ⟨A, hA, hdet⟩ := h
  have h1 : (A.map (rename finProdFinEquiv.symm)).det = rename finProdFinEquiv.symm A.det := by
    rw [AlgHom.map_det]
    rfl
  have h2' : (genericMatrix K n).permanent =
      rename finProdFinEquiv (Matrix.mvPolynomialX (Fin n) (Fin n) K).permanent := by
    rw [AlgHom.map_permanent, genericMatrix_eq_map_rename]
  have hperm : (Matrix.mvPolynomialX (Fin n) (Fin n) K).permanent =
      (A.map (rename finProdFinEquiv.symm)).det := by
    rw [h1, hdet, h2', rename_rename]
    simp
  have hA' : ∀ i j, ((A.map (rename finProdFinEquiv.symm)) i j).totalDegree ≤ 1 := fun i j =>
    (totalDegree_rename_le _ _).trans (hA i j)
  have := Matrix.card_mul_card_le_two_mul_card_of_permanent_eq_det (ι := Fin n)
    (by simpa using hfact) _ hA' hperm
  simpa [sq] using this

/-- **Mignon–Ressayre theorem** over a field with `(n - 1)! ≠ 0` (characteristic `0` or at least
`n`): the generic `n × n` permanent has determinantal complexity at least `n² / 2`
[Mignon and Ressayre][MignonRessayre2004]. The determinantal complexity is finite, at most
`2ⁿ - 1` (`determinantalComplexity_permanent_le`); see
`sq_le_two_mul_of_hasDeterminantalRepresentation_permanent` for the form about a given
representation. -/
theorem sq_le_two_mul_determinantalComplexity_permanent {n : ℕ}
    (hfact : ((n - 1).factorial : K) ≠ 0) :
    (n : ℕ∞) ^ 2 ≤ 2 * determinantalComplexity (genericMatrix K n).permanent := by
  have hk : (((n ^ 2 + 1) / 2 : ℕ) : ℕ∞) ≤
      determinantalComplexity (genericMatrix K n).permanent :=
    le_determinantalComplexity_iff.2 fun m hm => by
      have := sq_le_two_mul_of_hasDeterminantalRepresentation_permanent hfact hm
      exact_mod_cast (show (n ^ 2 + 1) / 2 ≤ m by omega)
  calc (n : ℕ∞) ^ 2 = ((n ^ 2 : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ ((2 * ((n ^ 2 + 1) / 2) : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
    _ = 2 * (((n ^ 2 + 1) / 2 : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ _ := by gcongr

/-- **Mignon–Ressayre theorem** [Mignon and Ressayre][MignonRessayre2004]: over a field of
characteristic zero, the generic `n × n` permanent has determinantal complexity at least
`n² / 2`. With `determinantalComplexity_permanent_le`, `n² / 2 ≤ dc(perm_n) ≤ 2ⁿ - 1`; see
`sq_le_two_mul_of_hasDeterminantalRepresentation_permanent` for the form about a given
representation. -/
theorem sq_le_two_mul_determinantalComplexity_permanent_of_charZero [CharZero K] (n : ℕ) :
    (n : ℕ∞) ^ 2 ≤ 2 * determinantalComplexity (genericMatrix K n).permanent :=
  sq_le_two_mul_determinantalComplexity_permanent (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))

/-- In characteristic zero, if the generic `n × n` permanent is a projection of the generic
`m × m` determinant, then `n² ≤ 2 m` [Mignon and Ressayre][MignonRessayre2004]. -/
theorem sq_le_two_mul_of_isProjection_permanent_det [CharZero K] {n m : ℕ}
    (h : IsProjection (genericMatrix K n).permanent (genericMatrix K m).det) : n ^ 2 ≤ 2 * m :=
  sq_le_two_mul_of_hasDeterminantalRepresentation_permanent
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    (hasDeterminantalRepresentation_of_isProjection h)

end Cslib.Circuits.Arithmetic
