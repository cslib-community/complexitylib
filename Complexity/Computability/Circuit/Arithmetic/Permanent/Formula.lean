/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.Formula
import Complexity.Foundations.Data.Matrix.Permanent.Blocks

/-!
# Arithmetic formulas are projections of the permanent

Every existing arithmetic formula `F : Formula (arithSignature K) n` computes a formal
polynomial that is a projection of the generic permanent of dimension `F.size + 1`. Here `K`
is any commutative semiring and size counts every operation node, including constants, with
input leaves free. Substitution uses the existing `IsProjection`: each matrix entry is a
variable or a scalar, without an extra scalar multiplier on the result.

This is the permanent's formula-simulation property
[Orzel et al., Definition 1 and Lemma 4][OrzelSrinivasanTavenasYehudayoff2025]. The explicit
linear bound and semiring generality are proved directly. That source uses fields of
characteristic other than two and permits a nonzero scalar multiplier in projections. No
characteristic restriction or multiplier is needed for formula simulation. Valiant's full
VNP-hardness reduction and uniform construction runtime are separate, unproved obligations.

The private invariant represents a polynomial by a permanent with one distinguished root,
whose internal block has permanent `1`. Addition and multiplication combine two such matrices
with one additional internal vertex. No new formula or complexity-class model is introduced.

## Main results

* `Cslib.Circuits.Formula.isProjection_permanent`: dimension `F.size + 1` suffices.
* `Cslib.Circuits.Formula.isProjection_permanent_toCircuit`: the existing formula compiler
  computes the same polynomial.
* `Cslib.Circuits.Arithmetic.IsProjection.permanent_mul`: multiply projections by adding dimensions.
* `Cslib.Circuits.Arithmetic.isProjection_permanent_mono`: pad to a larger dimension.

## References

* [I. Orzel et al.][OrzelSrinivasanTavenasYehudayoff2025], *The Algebraic Cost of a Boolean Sum*,
  Definition 1 (p. 47:3), Lemma 4 (p. 47:4) and projection conventions (p. 47:5)

The rooted construction and proof adapt saved Complexitylib source at revision `5b8acca7`.
-/

@[expose] public section

namespace Matrix

open Equiv Equiv.Perm Finset Fintype

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommSemiring R]

/-- Involution on `(Unit ⊕ m) ⊕ (Unit ⊕ n)` swapping the two root elements `inl (inl ())` and
`inr (inl ())`. -/
private def swapRootEquiv (m n : Type*) :
    ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ≃ ((Unit ⊕ m) ⊕ (Unit ⊕ n)) where
  toFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl (.inl u) => .inr (.inl u)
    | .inl (.inr i) => .inl (.inr i)
    | .inr (.inl u) => .inl (.inl u)
    | .inr (.inr j) => .inr (.inr j)
  left_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl
  right_inv x := by rcases x with (⟨⟨⟩⟩ | i) | (⟨⟨⟩⟩ | j) <;> rfl

/-- Rooted permanent multiplication block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
private def rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks M₁ 0 (fromBlocks (1 : Matrix Unit Unit R) 0 0 0) M₂).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    ((Equiv.sumAssoc Unit m (Unit ⊕ n)).symm.trans (swapRootEquiv m n))

/-- The permanent of `rootedMul M₁ M₂` is the product of the permanents of `M₁` and `M₂`. -/
private theorem permanent_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    (rootedMul M₁ M₂).permanent = M₁.permanent * M₂.permanent := by
  rw [rootedMul, permanent_submatrix_equiv_equiv, permanent_fromBlocks_zero₁₂]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedMul M₁ M₂`. -/
private theorem permanent_toBlocks₂₂_rootedMul (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedMul M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedMul M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ (of fun i => Sum.elim (M₁.toBlocks₂₁ i) 0) 0
        (fromBlocks (1 : Matrix Unit Unit R) M₂.toBlocks₁₂ 0 M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₂₁, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- Rooted permanent addition block matrix on `Unit ⊕ (m ⊕ (Unit ⊕ n))`. -/
private def rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R) (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R) :
    Matrix (Unit ⊕ (m ⊕ (Unit ⊕ n))) (Unit ⊕ (m ⊕ (Unit ⊕ n))) R :=
  (fromBlocks
    M₁
    (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
    (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)).submatrix
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm
    (Equiv.sumAssoc Unit m (Unit ⊕ n)).symm

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then so does the internal block of
`rootedAdd M₁ M₂`. -/
private theorem permanent_toBlocks₂₂_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).toBlocks₂₂.permanent = 1 := by
  have hblk : (rootedAdd M₁ M₂).toBlocks₂₂ =
      fromBlocks M₁.toBlocks₂₂ 0 0
        (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂) := by
    ext (i₁ | (⟨⟩ | i₂)) (j₁ | (⟨⟩ | j₂)) <;> rfl
  rw [hblk, permanent_fromBlocks_zero, permanent_fromBlocks_zero₁₂, permanent_one,
    h₁, h₂, mul_one, mul_one]

/-- If the internal blocks of `M₁` and `M₂` have permanent `1`, then the permanent of
`rootedAdd M₁ M₂` is the sum of the permanents of `M₁` and `M₂`. -/
private theorem permanent_rootedAdd (M₁ : Matrix (Unit ⊕ m) (Unit ⊕ m) R)
    (M₂ : Matrix (Unit ⊕ n) (Unit ⊕ n) R)
    (h₁ : M₁.toBlocks₂₂.permanent = 1) (h₂ : M₂.toBlocks₂₂.permanent = 1) :
    (rootedAdd M₁ M₂).permanent = M₁.permanent + M₂.permanent := by
  rw [rootedAdd, permanent_submatrix_equiv]
  let B₁ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0) 0
      (fromBlocks (1 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  let B₂ : Matrix ((Unit ⊕ m) ⊕ (Unit ⊕ n)) ((Unit ⊕ m) ⊕ (Unit ⊕ n)) R :=
    fromBlocks M₁ (fromBlocks M₂.toBlocks₁₁ M₂.toBlocks₁₂ 0 0)
      (fromBlocks (1 : Matrix Unit Unit R) 0 0 0)
      (fromBlocks (0 : Matrix Unit Unit R) 0 M₂.toBlocks₂₁ M₂.toBlocks₂₂)
  rw [permanent_add_of_row_eq _ B₁ B₂ (Sum.inr (Sum.inl ()))
    (fun j => by rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> simp [B₁, B₂])
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)
    (fun i hi j => by
      rcases i with (⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl
      · exact (hi rfl).elim
      · rcases j with (⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂) <;> rfl)]
  have hB₁ : B₁.permanent = M₁.permanent := by
    rw [permanent_fromBlocks_zero₂₁, permanent_fromBlocks_zero₁₂, permanent_one, h₂, mul_one,
      mul_one]
  have hB₂_swap : B₂.submatrix (swapRootEquiv m n) (Equiv.refl _) =
      fromBlocks (fromBlocks (1 : Matrix Unit Unit R) 0 M₁.toBlocks₂₁ M₁.toBlocks₂₂) 0
        (fromBlocks M₁.toBlocks₁₁ M₁.toBlocks₁₂ 0 0) M₂ := by
    ext ((⟨⟨⟩⟩ | i₁) | (⟨⟨⟩⟩ | i₂)) ((⟨⟨⟩⟩ | j₁) | (⟨⟨⟩⟩ | j₂)) <;> rfl
  have hB₂ : B₂.permanent = M₂.permanent := by
    rw [← permanent_submatrix_equiv_equiv (swapRootEquiv m n) (Equiv.refl _), hB₂_swap,
      permanent_fromBlocks_zero₁₂, permanent_fromBlocks_zero₁₂, permanent_one, h₁, mul_one,
      one_mul]
  rw [hB₁, hB₂]

end Matrix

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

private theorem rootedMul {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedMul M₁ M₂) :=
  (h₁.fromBlocks .zero (IsSubstMatrix.one.fromBlocks .zero .zero .zero) h₂).submatrix _ _

private theorem rootedAdd {α β : Type*}
    {M₁ : Matrix (Unit ⊕ α) (Unit ⊕ α) (MvPolynomial σ K)}
    {M₂ : Matrix (Unit ⊕ β) (Unit ⊕ β) (MvPolynomial σ K)}
    (h₁ : IsSubstMatrix M₁) (h₂ : IsSubstMatrix M₂) :
    IsSubstMatrix (Matrix.rootedAdd M₁ M₂) :=
  (h₁.fromBlocks (h₂.toBlocks₁₁.fromBlocks h₂.toBlocks₁₂ .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero .zero .zero)
    (IsSubstMatrix.one.fromBlocks .zero h₂.toBlocks₂₁ h₂.toBlocks₂₂)).submatrix _ _

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

/-- A polynomial `P` has a *rooted permanent representation* of internal dimension `m` if it is
the permanent of a `(1 + m) × (1 + m)` specialization matrix `M` on `Unit ⊕ Fin m` whose internal
block `M.toBlocks₂₂` has permanent `1`. -/
private def IsRootedPermProjection (m : ℕ) (P : MvPolynomial σ K) : Prop :=
  ∃ M : Matrix (Unit ⊕ Fin m) (Unit ⊕ Fin m) (MvPolynomial σ K),
    IsSubstMatrix M ∧ M.toBlocks₂₂.permanent = 1 ∧ M.permanent = P

namespace IsRootedPermProjection

/-- A rooted permanent representation of internal dimension `m` gives a projection of the
`(m + 1) × (m + 1)` generic permanent. -/
private theorem to_isProjection_permanent {m : ℕ} {P : MvPolynomial σ K}
    (h : IsRootedPermProjection m P) :
    IsProjection P (genericMatrix K (m + 1)).permanent := by
  obtain ⟨M, hM, -, rfl⟩ := h
  have e : Fin (m + 1) ≃ Unit ⊕ Fin m :=
    (finCongr (Nat.add_comm m 1)).trans
      (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))
  exact hM.isProjection_permanent e

/-- Every single-entry substitution `P` (a variable or constant) has a rooted permanent
representation of internal dimension `0`. -/
private theorem of_isSubstEntry {P : MvPolynomial σ K} (hP : IsSubstEntry P) :
    IsRootedPermProjection 0 P := by
  refine ⟨Matrix.fromBlocks (Matrix.of fun _ _ => P) 0 0 0,
    IsSubstMatrix.fromBlocks (fun _ _ => hP) .zero .zero .zero,
    Matrix.permanent_isEmpty, ?_⟩
  rw [Matrix.permanent_fromBlocks_zero, Matrix.permanent_unique, Matrix.permanent_isEmpty, mul_one]
  rfl

/-- Every constant `C c` has a rooted permanent representation of internal dimension `0`. -/
private theorem C (c : K) : IsRootedPermProjection 0 (MvPolynomial.C c : MvPolynomial σ K) :=
  .of_isSubstEntry (.C c)

/-- Every variable `X i` has a rooted permanent representation of internal dimension `0`. -/
private theorem X (i : σ) : IsRootedPermProjection 0 (MvPolynomial.X i : MvPolynomial σ K) :=
  .of_isSubstEntry (.X i)

/-- Equivalence `Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂)` used to flatten internal blocks of
rooted permanent representations. -/
private def innerEquiv (m₁ m₂ : ℕ) : Fin (m₁ + 1 + m₂) ≃ Fin m₁ ⊕ (Unit ⊕ Fin m₂) :=
  (finCongr (Nat.add_assoc m₁ 1 m₂)).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl _)
        (finSumFinEquiv.symm.trans (Equiv.sumCongr finOneEquiv (Equiv.refl _)))))

/-- Equivalence `Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂))`. -/
private def outerEquiv (m₁ m₂ : ℕ) :
    Unit ⊕ Fin (m₁ + 1 + m₂) ≃ Unit ⊕ (Fin m₁ ⊕ (Unit ⊕ Fin m₂)) :=
  Equiv.sumCongr (Equiv.refl Unit) (innerEquiv m₁ m₂)

/-- **Additive closure of rooted permanent representations**: if `P` and `Q` have rooted permanent
representations of internal dimensions `m₁` and `m₂`, then `P + Q` has one of internal dimension
`m₁ + 1 + m₂`. -/
private theorem add {m₁ m₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P + Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedAdd M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedAdd hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedAdd M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedAdd M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedAdd M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedAdd M₁ M₂ hU₁ hU₂]

/-- **Multiplicative closure of rooted permanent representations**: if `P` and `Q` have rooted
permanent representations of internal dimensions `m₁` and `m₂`, then `P * Q` has one of internal
dimension `m₁ + 1 + m₂`. -/
private theorem mul {m₁ m₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsRootedPermProjection m₁ P) (hQ : IsRootedPermProjection m₂ Q) :
    IsRootedPermProjection (m₁ + 1 + m₂) (P * Q) := by
  obtain ⟨M₁, hM₁, hU₁, rfl⟩ := hP
  obtain ⟨M₂, hM₂, hU₂, rfl⟩ := hQ
  refine ⟨(Matrix.rootedMul M₁ M₂).submatrix (outerEquiv m₁ m₂) (outerEquiv m₁ m₂),
    (hM₁.rootedMul hM₂).submatrix _ _, ?_, ?_⟩
  · have hblk : ((Matrix.rootedMul M₁ M₂).submatrix
        (outerEquiv m₁ m₂) (outerEquiv m₁ m₂)).toBlocks₂₂ =
        (Matrix.rootedMul M₁ M₂).toBlocks₂₂.submatrix (innerEquiv m₁ m₂) (innerEquiv m₁ m₂) := rfl
    rw [hblk, Matrix.permanent_submatrix_equiv, Matrix.permanent_toBlocks₂₂_rootedMul M₁ M₂ hU₁ hU₂]
  · rw [Matrix.permanent_submatrix_equiv, Matrix.permanent_rootedMul M₁ M₂]

end IsRootedPermProjection

/-- Every arithmetic formula `F` computes a polynomial with a rooted permanent representation of
internal dimension at most `F.size`. -/
private theorem _root_.Cslib.Circuits.Formula.exists_isRootedPermProjection
    (F : Formula (arithSignature K) n) :
    ∃ m ≤ F.size, IsRootedPermProjection m (F.eval (arithInterpretationWith K C) X) := by
  induction F with
  | input i =>
    exact ⟨0, le_rfl, .X i⟩
  | gate op args ih =>
    cases op with
    | const c =>
      exact ⟨0, Nat.zero_le _, .C c⟩
    | add =>
      obtain ⟨m₀, hm₀, h₀⟩ := ih 0
      obtain ⟨m₁, hm₁, h₁⟩ := ih 1
      refine ⟨m₀ + 1 + m₁, ?_, h₀.add h₁⟩
      rw [Formula.size_gate]
      change m₀ + 1 + m₁ ≤ (∑ j : Fin 2, (args j).size) + 1
      rw [Fin.sum_univ_two]
      omega
    | mul =>
      obtain ⟨m₀, hm₀, h₀⟩ := ih 0
      obtain ⟨m₁, hm₁, h₁⟩ := ih 1
      refine ⟨m₀ + 1 + m₁, ?_, h₀.mul h₁⟩
      rw [Formula.size_gate]
      change m₀ + 1 + m₁ ≤ (∑ j : Fin 2, (args j).size) + 1
      rw [Fin.sum_univ_two]
      omega

/-- **Formula universality for the permanent**: the formal polynomial computed by an
arithmetic formula `F` is a projection of the `(F.size + 1) × (F.size + 1)` generic permanent.
This gives an explicit semiring version of the permanent part of
[Orzel et al., Lemma 4][OrzelSrinivasanTavenasYehudayoff2025]. `size` counts operation nodes,
including constants; the linear dimension bound is proved directly by the construction. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent
    (F : Formula (arithSignature K) n) :
    IsProjection (F.eval (arithInterpretationWith K C) X)
      (genericMatrix K (F.size + 1)).permanent := by
  obtain ⟨m, hm, hroot⟩ := F.exists_isRootedPermProjection
  exact isProjection_permanent_mono (Nat.add_le_add_right hm 1) hroot.to_isProjection_permanent

/-- The formal polynomial `(F.toCircuit).polynomial 0` of any arithmetic formula `F` is a
projection of `(genericMatrix K (F.size + 1)).permanent`. -/
theorem _root_.Cslib.Circuits.Formula.isProjection_permanent_toCircuit
    (F : Formula (arithSignature K) n) :
    IsProjection (F.toCircuit.polynomial 0) (genericMatrix K (F.size + 1)).permanent := by
  simpa [Circuit.polynomial] using F.isProjection_permanent

end Cslib.Circuits.Arithmetic
