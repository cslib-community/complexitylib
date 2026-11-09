/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/NonnegRank.lean`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Nonnegative factorizations and nonnegative rank

A *nonnegative factorization* of a matrix `M : Matrix m n R` over an ordered semiring, with inner
index type `ρ`, writes `M = T * U` with `T : Matrix m ρ R` and `U : Matrix ρ n R` entrywise
nonnegative (`Matrix.HasNonnegFactorization`). The *nonnegative rank* `rank₊ M` is the least `r`
for which `M` has a nonnegative factorization with inner dimension `r`, or `⊤` if there is none
(`Matrix.nonnegRank`); equivalently, it is the least number of nonnegative rank-one matrices
summing to `M` [FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.1]. A matrix has finite
nonnegative rank exactly when it is entrywise nonnegative (`Matrix.nonnegRank_ne_top_iff`), and
then at most its number of rows and of columns (`Matrix.nonnegRank_le_card_height`,
`Matrix.nonnegRank_le_card_width`). Over a commutative semiring with the strong rank condition,
such as an ordered field, the rank is at most the nonnegative rank (`Matrix.rank_le_nonnegRank`).

In a nonnegative factorization, an entry of `T * U` is nonzero exactly when some inner index `k`
has `T i k ≠ 0` and `U k j ≠ 0` (`Matrix.mul_apply_ne_zero_iff_of_nonneg`). So the support of `M`
is the union of the `r` combinatorial rectangles `{i | T i k ≠ 0} × {j | U k j ≠ 0}`, which is the
rectangle-covering lower bound on the nonnegative rank
(`Cslib.Communication.Nondeterministic.coverNumberFun_ne_zero_le_nonnegRank`).

The nonnegative rank of a slack matrix of a polytope is its extension complexity
(`extensionComplexity_eq_nonnegRank_slackMatrix`), by Yannakakis's factorization theorem.

## Main definitions

* `Matrix.HasNonnegFactorization`: nonnegative factorizations with a given inner index type.
* `Matrix.nonnegRank`: the nonnegative rank, valued in `ℕ∞`.

## Main results

* `Matrix.nonnegRank_le_iff`, `Matrix.le_nonnegRank_iff`,
  `Matrix.HasNonnegFactorization.nonnegRank_le`: bounds through factorizations.
* `Matrix.HasNonnegFactorization.of_embedding`: padding the inner dimension.
* `Matrix.HasNonnegFactorization.nonneg`, `Matrix.nonnegRank_ne_top_iff`: only nonnegative
  matrices have nonnegative factorizations, and all of them do.
* `Matrix.nonnegRank_le_card_height`, `Matrix.nonnegRank_le_card_width`: the trivial bounds.
* `Matrix.nonnegRank_submatrix_le`: submatrices have smaller nonnegative rank.
* `Matrix.nonnegRank_transpose`: transposition preserves the nonnegative rank.
* `Matrix.nonnegRank_eq_zero_iff`: only the zero matrix has nonnegative rank zero.
* `Matrix.rank_le_nonnegRank`: rank is at most nonnegative rank.
* `Matrix.mul_apply_ne_zero_iff_of_nonneg`: the support of a product of nonnegative matrices.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.1
* [Yannakakis1991]
-/

public section

open Matrix

namespace Matrix

variable {R : Type*} {l m n o : Type*}

/-- `M` has a **nonnegative factorization** with inner index type `ρ`: `M = T * U` for entrywise
nonnegative matrices `T : Matrix m ρ R` and `U : Matrix ρ n R`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.1]. -/
@[expose] def HasNonnegFactorization [Semiring R] [PartialOrder R] (M : Matrix m n R) (ρ : Type*)
    [Fintype ρ] : Prop :=
  ∃ (T : Matrix m ρ R) (U : Matrix ρ n R), (∀ i k, 0 ≤ T i k) ∧ (∀ k j, 0 ≤ U k j) ∧ T * U = M

/-- The **nonnegative rank** `rank₊ M`: the least `r` such that `M = T * U` with `T` and `U`
entrywise nonnegative of inner dimension `r`, or `⊤` if `M` has no nonnegative factorization
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.1]. -/
noncomputable def nonnegRank [Semiring R] [PartialOrder R] (M : Matrix m n R) : ℕ∞ :=
  ⨅ r : {r : ℕ // M.HasNonnegFactorization (Fin r)}, (r.1 : ℕ∞)

section Semiring

variable [Semiring R] [PartialOrder R] {M : Matrix m n R} {ρ ρ' : Type*} [Fintype ρ] [Fintype ρ']

/-- A nonnegative factorization can be transported along an equivalence of inner index types. -/
theorem HasNonnegFactorization.of_equiv (e : ρ ≃ ρ') (h : M.HasNonnegFactorization ρ) :
    M.HasNonnegFactorization ρ' := by
  obtain ⟨T, U, hT, hU, hTU⟩ := h
  refine ⟨T.submatrix id e.symm, U.submatrix e.symm id, fun i k => hT _ _, fun k j => hU _ _, ?_⟩
  rw [submatrix_mul_equiv T U id e.symm id, submatrix_id_id, hTU]

/-- A nonnegative factorization through `ρ` gives one through any `ρ'` into which `ρ` embeds:
pad `T` with zero columns and `U` with zero rows. -/
theorem HasNonnegFactorization.of_embedding (e : ρ ↪ ρ') (h : M.HasNonnegFactorization ρ) :
    M.HasNonnegFactorization ρ' := by
  classical
  obtain ⟨T, U, hT, hU, rfl⟩ := h
  have hext : ∀ (f : ρ → R) (k' : ρ'), (∀ k, 0 ≤ f k) → 0 ≤ Function.extend e f 0 k' := by
    intro f k' hf
    by_cases hk : ∃ k, e k = k'
    · obtain ⟨k, rfl⟩ := hk
      rw [e.injective.extend_apply]
      exact hf k
    · rw [Function.extend_apply' _ _ _ hk]
      exact le_rfl
  refine ⟨of fun i => Function.extend e (T i) 0, of fun k' j => Function.extend e (U · j) 0 k',
    fun i k' => hext _ _ (hT i), fun k' j => hext _ _ (hU · j), ?_⟩
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.mul_apply, of_apply]
  refine (Fintype.sum_of_injective e e.injective _ _ (fun k' hk' => ?_) fun k => ?_).symm
  · rw [Function.extend_apply' _ _ _ (by simpa using hk'), Pi.zero_apply, zero_mul]
  · rw [e.injective.extend_apply, e.injective.extend_apply]

/-- A nonnegative factorization through `ρ` bounds the nonnegative rank by `|ρ|`. -/
theorem HasNonnegFactorization.nonnegRank_le (h : M.HasNonnegFactorization ρ) :
    M.nonnegRank ≤ Fintype.card ρ :=
  iInf_le (fun r : {r : ℕ // M.HasNonnegFactorization (Fin r)} => (r.1 : ℕ∞))
    ⟨_, h.of_equiv (Fintype.equivFin ρ)⟩

/-- Lower bounds on the nonnegative rank are lower bounds on the inner dimension of every
nonnegative factorization. -/
theorem le_nonnegRank_iff {c : ℕ∞} :
    c ≤ M.nonnegRank ↔ ∀ r, M.HasNonnegFactorization (Fin r) → c ≤ r := by
  simp [nonnegRank, le_iInf_iff, Subtype.forall]

/-- `M` has nonnegative rank at most `r` exactly when it has a nonnegative factorization with
inner dimension `r`. -/
theorem nonnegRank_le_iff {r : ℕ} : M.nonnegRank ≤ r ↔ M.HasNonnegFactorization (Fin r) := by
  refine ⟨fun h => ?_, fun h => by simpa using h.nonnegRank_le⟩
  have : Nonempty {r : ℕ // M.HasNonnegFactorization (Fin r)} := by
    rw [← ENat.iInf_natCast_ne_top]
    exact ne_top_of_le_ne_top (ENat.natCast_ne_top r) h
  obtain ⟨⟨s, hs⟩, hmin⟩ := ENat.exists_eq_iInf
    (fun r : {r : ℕ // M.HasNonnegFactorization (Fin r)} => (r.1 : ℕ∞))
  exact hs.of_embedding (Fin.castLEEmb (by exact_mod_cast (hmin.trans_le h : (s : ℕ∞) ≤ r)))

/-- The zero matrix has nonnegative rank zero. -/
@[simp] theorem nonnegRank_zero : (0 : Matrix m n R).nonnegRank = 0 :=
  nonpos_iff_eq_zero.1 <| nonnegRank_le_iff (r := 0) |>.2
    ⟨0, 0, fun _ k => k.elim0, fun k _ => k.elim0, Matrix.mul_zero 0⟩

/-- Only the zero matrix has nonnegative rank zero. -/
theorem nonnegRank_eq_zero_iff : M.nonnegRank = 0 ↔ M = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ nonnegRank_zero⟩
  obtain ⟨T, U, -, -, rfl⟩ := nonnegRank_le_iff (r := 0) |>.1 h.le
  exact Matrix.ext fun i j => by simp [Matrix.mul_apply]

/-- Restricting the rows and columns does not increase the nonnegative rank. -/
theorem nonnegRank_submatrix_le (M : Matrix m n R) (e₁ : l → m) (e₂ : o → n) :
    (M.submatrix e₁ e₂).nonnegRank ≤ M.nonnegRank :=
  le_nonnegRank_iff.2 fun r ⟨T, U, hT, hU, hTU⟩ =>
    nonnegRank_le_iff.2 ⟨T.submatrix e₁ id, U.submatrix id e₂, fun _ _ => hT _ _,
      fun _ _ => hU _ _, by rw [← hTU, submatrix_mul _ _ _ _ _ Function.bijective_id]⟩

end Semiring

section CommSemiring

variable [CommSemiring R] [PartialOrder R] {M : Matrix m n R}

/-- A nonnegative factorization of `M` transposes to one of `Mᵀ`. -/
theorem HasNonnegFactorization.transpose {ρ : Type*} [Fintype ρ]
    (h : M.HasNonnegFactorization ρ) : Mᵀ.HasNonnegFactorization ρ := by
  obtain ⟨T, U, hT, hU, rfl⟩ := h
  exact ⟨Uᵀ, Tᵀ, fun j k => hU k j, fun k i => hT i k, (transpose_mul T U).symm⟩

/-- Transposition preserves the nonnegative rank. -/
@[simp] theorem nonnegRank_transpose : Mᵀ.nonnegRank = M.nonnegRank := by
  refine le_antisymm (le_nonnegRank_iff.2 fun r h => ?_) (le_nonnegRank_iff.2 fun r h => ?_)
  · simpa using h.transpose.nonnegRank_le
  · simpa using h.transpose.nonnegRank_le

/-- **Rank is at most nonnegative rank**: a nonnegative factorization with inner dimension `r` is
in particular a factorization through `R ^ r`. -/
theorem rank_le_nonnegRank [StrongRankCondition R] [Fintype n] :
    (M.rank : ℕ∞) ≤ M.nonnegRank :=
  le_nonnegRank_iff.2 fun r ⟨T, U, _, _, hTU⟩ => by
    rw [← hTU]
    exact_mod_cast (rank_mul_le_right T U).trans (rank_le_card_height U |>.trans_eq
      (Fintype.card_fin r))

end CommSemiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix m n R}

/-- Only entrywise nonnegative matrices have nonnegative factorizations. -/
theorem HasNonnegFactorization.nonneg {ρ : Type*} [Fintype ρ] (h : M.HasNonnegFactorization ρ)
    (i : m) (j : n) : 0 ≤ M i j := by
  obtain ⟨T, U, hT, hU, rfl⟩ := h
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hT i k) (hU k j)

/-- A nonnegative matrix factors trivially through its rows: `M = 1 * M`. -/
theorem hasNonnegFactorization_height [Fintype m] (hM : ∀ i j, 0 ≤ M i j) :
    M.HasNonnegFactorization m := by
  classical
  exact ⟨1, M, fun i k => by rw [Matrix.one_apply]; split_ifs <;> simp, hM, Matrix.one_mul M⟩

/-- A nonnegative matrix factors trivially through its columns: `M = M * 1`. -/
theorem hasNonnegFactorization_width [Fintype n] (hM : ∀ i j, 0 ≤ M i j) :
    M.HasNonnegFactorization n := by
  classical
  exact ⟨M, 1, hM, fun k j => by rw [Matrix.one_apply]; split_ifs <;> simp, Matrix.mul_one M⟩

/-- The nonnegative rank of a nonnegative matrix is at most its number of rows. -/
theorem nonnegRank_le_card_height [Fintype m] (hM : ∀ i j, 0 ≤ M i j) :
    M.nonnegRank ≤ Fintype.card m :=
  (hasNonnegFactorization_height hM).nonnegRank_le

/-- The nonnegative rank of a nonnegative matrix is at most its number of columns. -/
theorem nonnegRank_le_card_width [Fintype n] (hM : ∀ i j, 0 ≤ M i j) :
    M.nonnegRank ≤ Fintype.card n :=
  (hasNonnegFactorization_width hM).nonnegRank_le

/-- A matrix with finitely many rows has finite nonnegative rank exactly when it is entrywise
nonnegative. -/
theorem nonnegRank_ne_top_iff [Finite m] : M.nonnegRank ≠ ⊤ ↔ ∀ i j, 0 ≤ M i j := by
  have := Fintype.ofFinite m
  refine ⟨fun h i j => ?_, fun hM => ne_top_of_le_ne_top (ENat.natCast_ne_top _)
    (nonnegRank_le_card_height hM)⟩
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 h
  exact (nonnegRank_le_iff.1 hr.symm.le).nonneg i j

/-- **The support of a product of nonnegative matrices**: an entry of `T * U` is nonzero exactly
when some inner index `k` has `T i k ≠ 0` and `U k j ≠ 0`. -/
theorem mul_apply_ne_zero_iff_of_nonneg [NoZeroDivisors R] {ρ : Type*} [Fintype ρ]
    {T : Matrix m ρ R} {U : Matrix ρ n R} (hT : ∀ i k, 0 ≤ T i k) (hU : ∀ k j, 0 ≤ U k j)
    (i : m) (j : n) : (T * U) i j ≠ 0 ↔ ∃ k, T i k ≠ 0 ∧ U k j ≠ 0 := by
  rw [Matrix.mul_apply, Ne, Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    mul_nonneg (hT i k) (hU k j)]
  simp only [Finset.mem_univ, true_implies, not_forall, mul_ne_zero_iff]

end OrderedSemiring

end Matrix
