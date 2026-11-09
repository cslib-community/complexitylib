/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, next to `LinearAlgebra/Matrix/Determinant/TotallyUnimodular`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Totally regular matrices and Cauchy matrices

A matrix is *totally regular* when every square submatrix, on distinct rows and distinct
columns, is nonsingular; Valiant calls such matrices *superregular* [Valiant1977]. The definition
follows `Matrix.IsTotallyUnimodular` and `Matrix.IsTotallyNonneg`. For the linear map `x ↦ A x`
of a totally regular matrix, no small set of outputs is blind to a large set of inputs: a vector
supported on a set `C` of columns that `A` maps to zero on a set `R` of at least `|C|` rows is zero
(`Matrix.IsTotallyRegular.eq_zero_of_mulVec_eq_zero`).

*Cauchy matrices* `A i j = 1 / (x i - y j)`, with distinct `x i`, distinct `y j` and
`x i ≠ y j`, are totally regular: every square submatrix is again a Cauchy matrix, and a square
Cauchy matrix is nonsingular (`Matrix.det_cauchy_ne_zero`). The proof avoids Cauchy's
determinant formula: a vector `v` in the kernel gives a polynomial of degree less than `k`, the
Lagrange interpolant of `v j / w j` at the nodes `y j` (where the `w j` are the nodal weights),
that vanishes at the `k` points `x i`.

The explicit family `1 / (i - (N + j))` for `0 ≤ i, j < N` is totally regular over every field
of characteristic zero (`Matrix.isTotallyRegular_cauchyNat`) and over `ZMod q` for every prime
`q ≥ 2 N` (`Matrix.isTotallyRegular_cauchyNat_zmod`).

## Main definitions

* `Matrix.IsTotallyRegular`: every square submatrix is nonsingular.
* `Matrix.cauchy`: the Cauchy matrix with nodes `x` and `y`.
* `Matrix.cauchyNat`: the Cauchy matrix with nodes `0, ..., N - 1` and `N, ..., 2 N - 1`.

## Main results

* `Matrix.isTotallyRegular_iff_fintype`: square submatrices indexed by any finite type.
* `Matrix.IsTotallyRegular.submatrix`, `Matrix.IsTotallyRegular.transpose`,
  `Matrix.IsTotallyRegular.reindex`: closure properties.
* `Matrix.IsTotallyRegular.eq_zero_of_mulVec_eq_zero`: square submatrices act injectively.
* `Matrix.det_cauchy_ne_zero`: square Cauchy matrices are nonsingular.
* `Matrix.isTotallyRegular_cauchy`: Cauchy matrices are totally regular.

## References

* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
-/

@[expose] public section

namespace Matrix

variable {m n m' n' R : Type*}

section CommRing

variable [CommRing R]

/-- `A.IsTotallyRegular` means that every square submatrix of `A`, on distinct rows and distinct
columns, is nonsingular. These are the *superregular* matrices of [Valiant1977]. -/
def IsTotallyRegular (A : Matrix m n R) : Prop :=
  ∀ k : ℕ, ∀ f : Fin k → m, ∀ g : Fin k → n, f.Injective → g.Injective →
    (A.submatrix f g).det ≠ 0

/-- A matrix is totally regular exactly when its square submatrices on distinct rows and distinct
columns, indexed by any finite type, are nonsingular. -/
theorem isTotallyRegular_iff_fintype.{w} (A : Matrix m n R) : A.IsTotallyRegular ↔
    ∀ (ι : Type w) [Fintype ι] [DecidableEq ι] (f : ι → m) (g : ι → n), f.Injective →
      g.Injective → (A.submatrix f g).det ≠ 0 := by
  constructor
  · intro hA ι _ _ f g hf hg
    have := hA (Fintype.card ι) (f ∘ (Fintype.equivFin ι).symm) (g ∘ (Fintype.equivFin ι).symm)
      (hf.comp (Fintype.equivFin ι).symm.injective) (hg.comp (Fintype.equivFin ι).symm.injective)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at this
  · intro hA k f g hf hg
    have := hA (ULift (Fin k)) (f ∘ Equiv.ulift) (g ∘ Equiv.ulift)
      (hf.comp Equiv.ulift.injective) (hg.comp Equiv.ulift.injective)
    rwa [← submatrix_submatrix, det_submatrix_equiv_self] at this

variable {A : Matrix m n R}

/-- Every entry of a totally regular matrix is nonzero: it is a `1 × 1` submatrix. -/
theorem IsTotallyRegular.apply_ne_zero (hA : A.IsTotallyRegular) (i : m) (j : n) : A i j ≠ 0 := by
  simpa [det_unique] using hA 1 (fun _ => i) (fun _ => j)
    (Function.injective_of_subsingleton _) (Function.injective_of_subsingleton _)

/-- A submatrix of a totally regular matrix, on distinct rows and distinct columns, is totally
regular. -/
theorem IsTotallyRegular.submatrix (hA : A.IsTotallyRegular) {f : m' → m} {g : n' → n}
    (hf : f.Injective) (hg : g.Injective) : (A.submatrix f g).IsTotallyRegular :=
  fun k f' g' hf' hg' => by
    simpa only [submatrix_submatrix] using hA k (f ∘ f') (g ∘ g') (hf.comp hf') (hg.comp hg')

/-- The transpose of a totally regular matrix is totally regular. -/
theorem IsTotallyRegular.transpose (hA : A.IsTotallyRegular) : Aᵀ.IsTotallyRegular :=
  fun k f g hf hg => by
    rw [← transpose_submatrix, det_transpose]
    exact hA k g f hg hf

/-- The transpose of `A` is totally regular exactly when `A` is. -/
theorem transpose_isTotallyRegular_iff (A : Matrix m n R) :
    Aᵀ.IsTotallyRegular ↔ A.IsTotallyRegular :=
  ⟨IsTotallyRegular.transpose, IsTotallyRegular.transpose⟩

/-- Reindexing a totally regular matrix keeps it totally regular. -/
theorem IsTotallyRegular.reindex (hA : A.IsTotallyRegular) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyRegular :=
  hA.submatrix em.symm.injective en.symm.injective

/-- A reindexing of `A` along equivalences is totally regular exactly when `A` is. -/
theorem reindex_isTotallyRegular (A : Matrix m n R) (em : m ≃ m') (en : n ≃ n') :
    (A.reindex em en).IsTotallyRegular ↔ A.IsTotallyRegular :=
  ⟨fun hA => by simpa using hA.reindex em.symm en.symm, fun hA => hA.reindex em en⟩

/-- **Square submatrices act injectively.** If `A` is totally regular, `v` is supported on a set
`cols` of columns, and `A v` vanishes on a set `rows` of rows with `|cols| ≤ |rows|`, then
`v = 0`. -/
theorem IsTotallyRegular.eq_zero_of_mulVec_eq_zero [Fintype n] [NoZeroDivisors R]
    (hA : A.IsTotallyRegular) {rows : Finset m} {cols : Finset n} (hcard : cols.card ≤ rows.card)
    {v : n → R} (hv : ∀ j ∉ cols, v j = 0) (hAv : ∀ i ∈ rows, (A *ᵥ v) i = 0) : v = 0 := by
  classical
  -- Pair the columns with some of the rows.
  obtain ⟨r⟩ : Nonempty (cols ↪ rows) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_coe] using hcard)
  let f : cols → m := fun j => r j
  let g : cols → n := Subtype.val
  have hf : f.Injective := Subtype.val_injective.comp r.injective
  -- On the rows `f`, the vector `A v` is the submatrix on `f` and `g` applied to `v ∘ g`.
  have hzero : A.submatrix f g *ᵥ (v ∘ g) = 0 := by
    funext j
    rw [Pi.zero_apply, ← hAv _ (r j).2]
    simp only [mulVec, dotProduct, submatrix_apply, Function.comp_apply, g]
    rw [Finset.sum_coe_sort cols fun j' => A (f j) j' * v j']
    exact Finset.sum_subset (Finset.subset_univ cols) fun j' _ hj' => by simp [hv j' hj']
  have hvc := Matrix.eq_zero_of_mulVec_eq_zero
    ((isTotallyRegular_iff_fintype A).1 hA cols f g hf Subtype.val_injective) hzero
  funext j
  by_cases hj : j ∈ cols
  · simpa using congrFun hvc ⟨j, hj⟩
  · exact hv j hj

end CommRing

/-! ### Cauchy matrices -/

section Cauchy

variable {F : Type*} [Field F]

/-- The *Cauchy matrix* with nodes `x` and `y`: `A i j = 1 / (x i - y j)`. -/
def cauchy (x : m → F) (y : n → F) : Matrix m n F :=
  of fun i j => (x i - y j)⁻¹

/-- The entry of the Cauchy matrix at `(i, j)` is `(x i - y j)⁻¹`. -/
@[simp] theorem cauchy_apply (x : m → F) (y : n → F) (i : m) (j : n) :
    cauchy x y i j = (x i - y j)⁻¹ :=
  rfl

/-- A submatrix of a Cauchy matrix is the Cauchy matrix of the restricted nodes. -/
@[simp] theorem submatrix_cauchy (x : m → F) (y : n → F) (r : m' → m) (c : n' → n) :
    (cauchy x y).submatrix r c = cauchy (x ∘ r) (y ∘ c) :=
  rfl

/-- **Square Cauchy matrices are nonsingular.** If `∑ j, v j / (x i - y j) = 0` for every `i`,
then the polynomial interpolating `v j / w j` at the nodes `y j`, where the `w j` are the nodal
weights, vanishes at the `k` points `x i`. Its degree is less than `k`, so it is zero, and so is
`v`. -/
theorem det_cauchy_ne_zero [Fintype n] [DecidableEq n] {x y : n → F}
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) :
    (cauchy x y).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := exists_mulVec_eq_zero_iff.mpr hdet
  have hweight : ∀ j, Lagrange.nodalWeight Finset.univ y j ≠ 0 := fun j =>
    Lagrange.nodalWeight_ne_zero hy.injOn (Finset.mem_univ j)
  let w : n → F := fun j => (Lagrange.nodalWeight Finset.univ y j)⁻¹ * v j
  have hP : Lagrange.interpolate Finset.univ y w = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Finset.univ hx.injOn
      (Lagrange.degree_interpolate_lt w hy.injOn) fun i _ => ?_
    rw [Lagrange.eval_interpolate_not_at_node w fun j _ => hxy i j]
    have hsum : ∑ j, Lagrange.nodalWeight Finset.univ y j * (x i - y j)⁻¹ * w j =
        (cauchy x y *ᵥ v) i := by
      simp only [mulVec, dotProduct, cauchy_apply, w]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp [hweight j]
    rw [hsum, hv, Pi.zero_apply, mul_zero]
  refine hv0 (funext fun j => ?_)
  have h := Lagrange.eval_interpolate_at_node w hy.injOn (Finset.mem_univ j)
  rw [hP, Polynomial.eval_zero] at h
  simpa [w, hweight j] using h.symm

/-- **Cauchy matrices are totally regular**: every square submatrix is again a square Cauchy
matrix. -/
theorem isTotallyRegular_cauchy {x : m → F} {y : n → F} (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) : (cauchy x y).IsTotallyRegular :=
  fun _ r c hr hc => by
    rw [submatrix_cauchy]
    exact det_cauchy_ne_zero (hx.comp hr) (hy.comp hc) fun i j => hxy (r i) (c j)

variable (F) in
/-- The explicit `N × N` Cauchy matrix `A i j = 1 / (i - (N + j))`, with nodes `0, ..., N - 1`
and `N, ..., 2 N - 1`. -/
def cauchyNat (N : ℕ) : Matrix (Fin N) (Fin N) F :=
  cauchy (fun i : Fin N => ((i : ℕ) : F)) fun j : Fin N => ((N + j : ℕ) : F)

/-- **The explicit Cauchy matrices are totally regular** over fields of characteristic zero. -/
theorem isTotallyRegular_cauchyNat [CharZero F] (N : ℕ) : (cauchyNat F N).IsTotallyRegular :=
  isTotallyRegular_cauchy (fun i i' h => Fin.ext (by exact_mod_cast h))
    (fun j j' h => Fin.ext (Nat.add_left_cancel (by exact_mod_cast h)))
    fun i j h => by
      have : (i : ℕ) = N + j := by exact_mod_cast h
      omega

/-- **The explicit Cauchy matrices are totally regular** over `ZMod q`, for every prime
`q ≥ 2 N`. -/
theorem isTotallyRegular_cauchyNat_zmod {q : ℕ} [Fact q.Prime] {N : ℕ} (hq : 2 * N ≤ q) :
    (cauchyNat (ZMod q) N).IsTotallyRegular := by
  have hcast : ∀ a b : ℕ, a < q → b < q → ((a : ZMod q) = b ↔ a = b) := fun a b ha hb => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  refine isTotallyRegular_cauchy (fun i i' h => Fin.ext ?_) (fun j j' h => Fin.ext ?_)
    fun i j h => ?_
  · exact (hcast _ _ (by omega) (by omega)).mp h
  · have := (hcast _ _ (by omega) (by omega)).mp h
    omega
  · have := (hcast _ _ (by omega) (by omega)).mp h
    omega

end Cauchy

end Matrix
