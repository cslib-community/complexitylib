/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
import Complexity.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Closure properties of permanent projections

A polynomial is a projection of the `m × m` generic permanent exactly when it is the permanent of
an `m × m` matrix whose entries are variables or constants. Through this description, such
projections are closed under products, with the dimensions adding, and under padding to a larger
dimension. The matrix description is private proof plumbing; the formula simulation in
`Cslib.Circuits.Formula.isProjection_permanent` reuses it through `import all`.

## Main results

* `Cslib.Circuits.Arithmetic.IsProjection.permanent_mul`: multiply projections by adding dimensions.
* `Cslib.Circuits.Arithmetic.isProjection_permanent_mono`: pad to a larger dimension.

These proofs moved here from `Complexity.Computability.Circuit.Arithmetic.Permanent.Formula`,
whose construction adapts saved Complexitylib source at revision `5b8acca7`.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial Finset

universe u

variable {K : Type u} [CommSemiring K] {n m : ℕ} {σ : Type*}

/-- Evaluating the permanent of `genericMatrix K n` at `x` gives the permanent of the matrix of
values `x (finProdFinEquiv (i, j))`. -/
private theorem aeval_permanent_genericMatrix {A : Type*} [CommSemiring A] [Algebra K A]
    (x : Fin (n * n) → A) :
    aeval x (genericMatrix K n).permanent =
      (Matrix.of fun i j : Fin n => x (finProdFinEquiv (i, j))).permanent := by
  rw [AlgHom.map_permanent]
  congr 1
  ext i j
  simp [genericMatrix]

/-- Applying a projection `ρ` to `(genericMatrix K m).permanent` gives the permanent of the
specialized matrix. -/
private theorem projection_permanent_genericMatrix {σ : Type*} (ρ : Fin (m * m) → σ ⊕ K) :
    projection ρ (genericMatrix K m).permanent =
      (Matrix.of fun i j : Fin m =>
        Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j)))).permanent :=
  aeval_permanent_genericMatrix _

/-- A polynomial in `MvPolynomial σ K` is a projection substitution entry if it is either a
variable `X i` or a constant `C c`. -/
private def IsSubstEntry (p : MvPolynomial σ K) : Prop :=
  ∃ s : σ ⊕ K, Sum.elim X (fun a => C a) s = p

namespace IsSubstEntry

private theorem C (c : K) : IsSubstEntry (MvPolynomial.C c : MvPolynomial σ K) :=
  ⟨Sum.inr c, rfl⟩

private theorem X (i : σ) : IsSubstEntry (MvPolynomial.X i : MvPolynomial σ K) :=
  ⟨Sum.inl i, rfl⟩

private theorem zero : IsSubstEntry (0 : MvPolynomial σ K) :=
  ⟨Sum.inr 0, map_zero _⟩

private theorem one : IsSubstEntry (1 : MvPolynomial σ K) :=
  ⟨Sum.inr 1, map_one _⟩

end IsSubstEntry

/-- A matrix over `MvPolynomial σ K` is a specialization of a generic matrix if every entry is a
variable `X i` or a constant `C c`. -/
private def IsSubstMatrix {α β : Type*} (M : Matrix α β (MvPolynomial σ K)) : Prop :=
  ∀ i j, IsSubstEntry (M i j)

namespace IsSubstMatrix

private theorem zero {α β : Type*} : IsSubstMatrix (0 : Matrix α β (MvPolynomial σ K)) :=
  fun _ _ => .zero

private theorem one {α : Type*} [DecidableEq α] :
    IsSubstMatrix (1 : Matrix α α (MvPolynomial σ K)) :=
  fun i j => by
    rw [Matrix.one_apply]
    split_ifs <;> [exact .one; exact .zero]

private theorem fromBlocks {α₁ α₂ β₁ β₂ : Type*}
    {A : Matrix α₁ β₁ (MvPolynomial σ K)} {B : Matrix α₁ β₂ (MvPolynomial σ K)}
    {C : Matrix α₂ β₁ (MvPolynomial σ K)} {D : Matrix α₂ β₂ (MvPolynomial σ K)}
    (hA : IsSubstMatrix A) (hB : IsSubstMatrix B) (hC : IsSubstMatrix C) (hD : IsSubstMatrix D) :
    IsSubstMatrix (Matrix.fromBlocks A B C D) := by
  rintro (i | i) (j | j)
  · exact hA i j
  · exact hB i j
  · exact hC i j
  · exact hD i j

private theorem submatrix {α β α' β' : Type*} {M : Matrix α β (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) (f : α' → α) (g : β' → β) :
    IsSubstMatrix (M.submatrix f g) :=
  fun i j => hM (f i) (g j)

private theorem toBlocks₁₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₁ :=
  fun i j => hM (.inl i) (.inl j)

private theorem toBlocks₁₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₁₂ :=
  fun i j => hM (.inl i) (.inr j)

private theorem toBlocks₂₁ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₁ :=
  fun i j => hM (.inr i) (.inl j)

private theorem toBlocks₂₂ {α₁ α₂ β₁ β₂ : Type*} {M : Matrix (α₁ ⊕ α₂) (β₁ ⊕ β₂) (MvPolynomial σ K)}
    (hM : IsSubstMatrix M) : IsSubstMatrix M.toBlocks₂₂ :=
  fun i j => hM (.inr i) (.inr j)

/-- The permanent of any specialization matrix indexed by `α ≃ Fin m` is a projection of
`(genericMatrix K m).permanent`. -/
private theorem isProjection_permanent {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (MvPolynomial σ K)} (hM : IsSubstMatrix M) {m : ℕ} (e : Fin m ≃ α) :
    IsProjection M.permanent (genericMatrix K m).permanent := by
  choose ρ hρ using hM
  refine ⟨fun idx =>
    let pq := finProdFinEquiv.symm idx
    ρ (e pq.1) (e pq.2), ?_⟩
  rw [projection_permanent_genericMatrix, ← M.permanent_submatrix_equiv e]
  exact congrArg Matrix.permanent (Matrix.ext fun i j => by simpa using hρ (e i) (e j))

end IsSubstMatrix

/-- A polynomial `P` is a projection of `(genericMatrix K m).permanent` if and only if it is the
permanent of an `m × m` specialization matrix. -/
private theorem isProjection_permanent_iff_exists_substMatrix {P : MvPolynomial σ K} {m : ℕ} :
    IsProjection P (genericMatrix K m).permanent ↔
      ∃ M : Matrix (Fin m) (Fin m) (MvPolynomial σ K), IsSubstMatrix M ∧ M.permanent = P := by
  constructor
  · rintro ⟨ρ, rfl⟩
    refine ⟨Matrix.of fun i j => Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j))),
      fun i j => ⟨ρ (finProdFinEquiv (i, j)), rfl⟩,
      (projection_permanent_genericMatrix ρ).symm⟩
  · rintro ⟨M, hM, rfl⟩
    exact hM.isProjection_permanent (Equiv.refl _)

/-- The constant polynomial `1` is a projection of the `m × m` generic permanent for every `m`. -/
private theorem isProjection_permanent_one (m : ℕ) :
    IsProjection (1 : MvPolynomial σ K) (genericMatrix K m).permanent :=
  isProjection_permanent_iff_exists_substMatrix.mpr ⟨1, .one, Matrix.permanent_one⟩

/-- **Multiplicative closure of permanent projections**: if `P` is a projection of the `m × m`
generic permanent and `Q` is a projection of the `k × k` generic permanent, then `P * Q` is a
projection of the `(m + k) × (m + k)` generic permanent. -/
theorem IsProjection.permanent_mul {P Q : MvPolynomial σ K} {m k : ℕ}
    (hP : IsProjection P (genericMatrix K m).permanent)
    (hQ : IsProjection Q (genericMatrix K k).permanent) :
    IsProjection (P * Q) (genericMatrix K (m + k)).permanent := by
  obtain ⟨M₁, hM₁, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hP
  obtain ⟨M₂, hM₂, rfl⟩ := isProjection_permanent_iff_exists_substMatrix.mp hQ
  rw [← Matrix.permanent_fromBlocks_zero M₁ M₂]
  exact (hM₁.fromBlocks .zero .zero hM₂).isProjection_permanent finSumFinEquiv.symm

/-- **Monotonicity of permanent projections in the matrix dimension**: if `m ≤ k` and `P` is a
projection of `(genericMatrix K m).permanent`, then `P` is a projection of
`(genericMatrix K k).permanent`. -/
theorem isProjection_permanent_mono {P : MvPolynomial σ K} {m k : ℕ} (hmk : m ≤ k)
    (hP : IsProjection P (genericMatrix K m).permanent) :
    IsProjection P (genericMatrix K k).permanent := by
  have hmul := hP.permanent_mul (isProjection_permanent_one (K := K) (σ := σ) (k - m))
  rwa [mul_one, Nat.add_sub_of_le hmk] at hmul

end Cslib.Circuits.Arithmetic
