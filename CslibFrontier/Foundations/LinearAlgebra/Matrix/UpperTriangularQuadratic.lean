/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Canonical upper-triangular quadratic matrix representatives

For a square matrix `M` over a commutative ring with a linearly ordered index type,
`Matrix.upperQuadratic M` is its canonical upper-triangular representative for the same quadratic
form, defined entrywise by

* `M.upperQuadratic i i = M i i`,
* `M.upperQuadratic i j = M i j + M j i` when `i < j`, and
* `M.upperQuadratic i j = 0` when `j < i`.

Because the difference `M.upperQuadratic - M` induces an alternating bilinear form
(`Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub`), Mathlib's bridge
`LinearMap.BilinMap.toQuadraticMap_eq_zero` gives
`M.upperQuadratic.toQuadraticForm' = M.toQuadraticForm'` (`Matrix.toQuadraticForm'_upperQuadratic`)
in every characteristic, including characteristic two. Moreover, `M.upperQuadratic` is the unique
upper-triangular matrix whose difference from `M` is alternating
(`Matrix.eq_upperQuadratic_of_isUpperTriangular_of_isAlt`), equivalently the unique upper-triangular
matrix inducing `M.toQuadraticForm'`
(`Matrix.eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq`).

## Main definitions

* `Matrix.upperQuadratic`: the canonical upper-triangular quadratic representative of a square
  matrix.

## Main results

* `Matrix.upperQuadratic_apply`, `Matrix.upperQuadratic_apply_self`,
  `Matrix.upperQuadratic_apply_of_lt`, `Matrix.upperQuadratic_apply_of_gt`: entry equations.
* `Matrix.isUpperTriangular_upperQuadratic`: `M.upperQuadratic` is `Matrix.IsUpperTriangular`.
* `Matrix.isAlt_toLinearMap₂'_iff`: characterization of alternating matrix bilinear forms in any
  characteristic via vanishing diagonal and skew-symmetric off-diagonal entries.
* `Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub`: `Matrix.toLinearMap₂' R (M.upperQuadratic - M)`
  is alternating.
* `Matrix.toQuadraticForm'_upperQuadratic`:
  `M.upperQuadratic.toQuadraticForm' = M.toQuadraticForm'`.
* `Matrix.eq_upperQuadratic_of_isUpperTriangular_of_isAlt`,
  `Matrix.eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq`: uniqueness of the
  upper-triangular representative.
* `Matrix.upperQuadratic_eq_self_iff`, `Matrix.upperQuadratic_eq_upperQuadratic_iff`:
  fixed-point and equivalence-class characterizations.

## References

* [UOV2026], §3.1, pp. 11–13 (`Upper(M)`).
-/

public section

namespace Matrix

section Definition

variable {ι R : Type*} [LinearOrder ι]

/-- The canonical upper-triangular representative of a square matrix `M` for its quadratic form:
`M i i` on the diagonal, `M i j + M j i` strictly above the diagonal (`i < j`), and `0` below it
(`j < i`). Over a commutative ring, `M.upperQuadratic` is `Matrix.IsUpperTriangular`, induces the
same `Matrix.toQuadraticForm'` as `M` in every characteristic, and is the unique upper-triangular
matrix whose difference from `M` is alternating (`LinearMap.IsAlt`). -/
@[expose] def upperQuadratic [Add R] [Zero R] (M : Matrix ι ι R) : Matrix ι ι R :=
  Matrix.of fun i j => if i < j then M i j + M j i else if j < i then 0 else M i i

theorem upperQuadratic_apply [Add R] [Zero R] (M : Matrix ι ι R) (i j : ι) :
    M.upperQuadratic i j = if i < j then M i j + M j i else if j < i then 0 else M i i :=
  rfl

@[simp]
theorem upperQuadratic_apply_self [Add R] [Zero R] (M : Matrix ι ι R) (i : ι) :
    M.upperQuadratic i i = M i i := by
  simp [upperQuadratic_apply]

@[simp]
theorem upperQuadratic_apply_of_lt [Add R] [Zero R] (M : Matrix ι ι R) {i j : ι} (h : i < j) :
    M.upperQuadratic i j = M i j + M j i := by
  simp [upperQuadratic_apply, h]

@[simp]
theorem upperQuadratic_apply_of_gt [Add R] [Zero R] (M : Matrix ι ι R) {i j : ι} (h : j < i) :
    M.upperQuadratic i j = 0 := by
  simp [upperQuadratic_apply, h, lt_asymm h]

@[simp]
theorem diag_upperQuadratic [Add R] [Zero R] (M : Matrix ι ι R) :
    M.upperQuadratic.diag = M.diag :=
  funext fun i => upperQuadratic_apply_self M i

/-- `M.upperQuadratic` is upper triangular (`Matrix.IsUpperTriangular`). -/
theorem isUpperTriangular_upperQuadratic [Add R] [Zero R] (M : Matrix ι ι R) :
    M.upperQuadratic.IsUpperTriangular :=
  fun _ _ h => upperQuadratic_apply_of_gt M h

@[simp]
theorem upperQuadratic_zero [AddZeroClass R] :
    (0 : Matrix ι ι R).upperQuadratic = 0 := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji <;> simp [*]

theorem upperQuadratic_add [AddCommMonoid R] (M N : Matrix ι ι R) :
    (M + N).upperQuadratic = M.upperQuadratic + N.upperQuadratic := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [upperQuadratic_apply_of_lt, hij, Matrix.add_apply]
    abel
  · simp only [upperQuadratic_apply_self, Matrix.add_apply]
  · simp only [upperQuadratic_apply_of_gt, hji, Matrix.add_apply, add_zero]

theorem upperQuadratic_neg [AddCommGroup R] (M : Matrix ι ι R) :
    (-M).upperQuadratic = -M.upperQuadratic := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [upperQuadratic_apply_of_lt, hij, Matrix.neg_apply, neg_add]
  · simp only [upperQuadratic_apply_self, Matrix.neg_apply]
  · simp only [upperQuadratic_apply_of_gt, hji, Matrix.neg_apply, neg_zero]

theorem upperQuadratic_sub [AddCommGroup R] (M N : Matrix ι ι R) :
    (M - N).upperQuadratic = M.upperQuadratic - N.upperQuadratic := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [upperQuadratic_apply_of_lt, hij, Matrix.sub_apply]
    abel
  · simp only [upperQuadratic_apply_self, Matrix.sub_apply]
  · simp only [upperQuadratic_apply_of_gt, hji, Matrix.sub_apply, sub_zero]

theorem upperQuadratic_smul {S : Type*} [Monoid S] [AddMonoid R] [DistribMulAction S R]
    (c : S) (M : Matrix ι ι R) :
    (c • M).upperQuadratic = c • M.upperQuadratic := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [upperQuadratic_apply_of_lt, hij, Matrix.smul_apply, smul_add]
  · simp only [upperQuadratic_apply_self, Matrix.smul_apply]
  · simp only [upperQuadratic_apply_of_gt, hji, Matrix.smul_apply, smul_zero]

end Definition

section Quadratic

variable {ι R : Type*}

private theorem sum_sum_eq_zero_of_diag_of_lt {α : Type*} [Fintype α] [LinearOrder α]
    [AddCommMonoid R] (f : α → α → R) (hdiag : ∀ i, f i i = 0)
    (hlt : ∀ ⦃i j⦄, i < j → f i j + f j i = 0) :
    ∑ i, ∑ j, f i j = 0 := by
  have hsplit : ∀ i j : α, f i j =
      (if i = j then f i j else 0) + (if i < j then f i j else 0) +
        (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, ne_of_lt hij, lt_asymm hij]
    · simp
    · simp [hji, (ne_of_lt hji).symm, lt_asymm hji]
  have hdiagSum : ∑ i : α, ∑ j : α, (if i = j then f i j else 0) = 0 := by
    simp [hdiag]
  have hswap : ∑ i : α, ∑ j : α, (if j < i then f i j else 0) =
      ∑ i : α, ∑ j : α, (if i < j then f j i else 0) :=
    Finset.sum_comm
  have hpair : (∑ i : α, ∑ j : α, (if i < j then f i j else 0)) +
      ∑ i : α, ∑ j : α, (if i < j then f j i else 0) = 0 := by
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    by_cases hij : i < j
    · simp [hij, hlt hij]
    · simp [hij]
  calc
    ∑ i : α, ∑ j : α, f i j
        = ∑ i : α, ∑ j : α, ((if i = j then f i j else 0) +
            (if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = (∑ i : α, ∑ j : α, (if i = j then f i j else 0)) +
          (∑ i : α, ∑ j : α, (if i < j then f i j else 0)) +
          ∑ i : α, ∑ j : α, (if j < i then f i j else 0) := by
          simp only [Finset.sum_add_distrib]
    _ = 0 := by
          rw [hdiagSum, zero_add, hswap, hpair]

/-- Evaluate `Matrix.toQuadraticForm'` as `v ⬝ᵥ M *ᵥ v`. -/
@[simp]
theorem toQuadraticForm'_apply [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (v : ι → R) :
    M.toQuadraticForm' v = v ⬝ᵥ M *ᵥ v := by
  rw [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply']

private theorem isAlt_toLinearMap₂'_diag_and_symm [Fintype ι] [DecidableEq ι] [CommRing R]
    {A : Matrix ι ι R} (h : (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) A).IsAlt) :
    (∀ i, A i i = 0) ∧ ∀ i j, A i j + A j i = 0 := by
  have hsingle (a b : ι) : Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) A
      (Pi.single a 1) (Pi.single b 1) = A a b := by
    simp [Matrix.toLinearMap₂'_apply, Pi.single_apply]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have hi := h (Pi.single i 1)
    rwa [hsingle i i] at hi
  · have hij := h.neg (Pi.single i 1) (Pi.single j 1)
    rw [hsingle i j, hsingle j i] at hij
    exact neg_eq_iff_add_eq_zero.mp hij

/-- Over a commutative ring (in any characteristic), `Matrix.toLinearMap₂' R A` is alternating
(`LinearMap.IsAlt`) if and only if the diagonal of `A` vanishes and `A i j + A j i = 0` for all
`i, j`. -/
theorem isAlt_toLinearMap₂'_iff [Fintype ι] [DecidableEq ι] [CommRing R] {A : Matrix ι ι R} :
    (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) A).IsAlt ↔
      (∀ i, A i i = 0) ∧ ∀ i j, A i j + A j i = 0 := by
  refine ⟨isAlt_toLinearMap₂'_diag_and_symm, ?_⟩
  rintro ⟨hdiag, hsymm⟩ x
  rw [Matrix.toLinearMap₂'_apply]
  let e := Fintype.equivFin ι
  have he : ∑ i, ∑ j, x i • x j • A i j =
      ∑ a, ∑ b, x (e.symm a) * x (e.symm b) * A (e.symm a) (e.symm b) := by
    refine (Fintype.sum_equiv e _ (fun a => ∑ j, x (e.symm a) • x j • A (e.symm a) j)
      fun i => ?_).trans ?_
    · simp [e.symm_apply_apply]
    · refine Finset.sum_congr rfl fun a _ => ?_
      refine Fintype.sum_equiv e _
        (fun b => x (e.symm a) * x (e.symm b) * A (e.symm a) (e.symm b)) fun j => ?_
      simp [e.symm_apply_apply, smul_eq_mul, mul_assoc]
  rw [he]
  refine sum_sum_eq_zero_of_diag_of_lt _ (fun a => ?_) (fun a b _ => ?_)
  · simp [hdiag]
  · calc
      x (e.symm a) * x (e.symm b) * A (e.symm a) (e.symm b) +
          x (e.symm b) * x (e.symm a) * A (e.symm b) (e.symm a)
          = x (e.symm a) * x (e.symm b) *
              (A (e.symm a) (e.symm b) + A (e.symm b) (e.symm a)) := by
            ring
      _ = 0 := by
            rw [hsymm, mul_zero]

/-- Linear-order form of `Matrix.isAlt_toLinearMap₂'_iff`: it suffices to check `A i j + A j i = 0`
on `i < j`. -/
theorem isAlt_toLinearMap₂'_iff_of_lt [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]
    {A : Matrix ι ι R} :
    (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) A).IsAlt ↔
      (∀ i, A i i = 0) ∧ ∀ ⦃i j⦄, i < j → A i j + A j i = 0 := by
  constructor
  · intro h
    obtain ⟨hd, hs⟩ := isAlt_toLinearMap₂'_diag_and_symm h
    exact ⟨hd, fun i j _ => hs i j⟩
  · rintro ⟨hdiag, hlt⟩ x
    rw [Matrix.toLinearMap₂'_apply]
    refine sum_sum_eq_zero_of_diag_of_lt _ (fun i => ?_) (fun i j hij => ?_)
    · simp [hdiag]
    · calc
        x i • x j • A i j + x j • x i • A j i
            = x i * x j * (A i j + A j i) := by
              simp only [smul_eq_mul]
              ring
        _ = 0 := by
              rw [hlt hij, mul_zero]

/-- Two matrices induce the same quadratic form (`Matrix.toQuadraticForm'`) if and only if the
bilinear form of their difference is alternating. -/
theorem toQuadraticForm'_eq_iff_isAlt_toLinearMap₂'_sub [Fintype ι] [DecidableEq ι] [CommRing R]
    {N M : Matrix ι ι R} :
    N.toQuadraticForm' = M.toQuadraticForm' ↔
      (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) (N - M)).IsAlt := by
  rw [← sub_eq_zero, ← LinearMap.BilinMap.toQuadraticMap_eq_zero, map_sub,
    LinearMap.BilinMap.toQuadraticMap_sub, Matrix.toQuadraticForm', Matrix.toQuadraticForm']

/-- The bilinear form of `M.upperQuadratic - M` is alternating (`LinearMap.IsAlt`). -/
theorem isAlt_toLinearMap₂'_upperQuadratic_sub [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] (M : Matrix ι ι R) :
    (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) (M.upperQuadratic - M)).IsAlt := by
  refine isAlt_toLinearMap₂'_iff_of_lt.mpr ⟨fun i => ?_, fun i j hij => ?_⟩
  · simp [Matrix.sub_apply]
  · simp only [Matrix.sub_apply, upperQuadratic_apply_of_lt _ hij, upperQuadratic_apply_of_gt _ hij]
    ring

/-- `M.upperQuadratic` induces the same quadratic form as `M`, proved through Mathlib's
`LinearMap.BilinMap.toQuadraticMap_eq_zero` ↔ `LinearMap.IsAlt` bridge. -/
@[simp]
theorem toQuadraticForm'_upperQuadratic [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]
    (M : Matrix ι ι R) :
    M.upperQuadratic.toQuadraticForm' = M.toQuadraticForm' :=
  toQuadraticForm'_eq_iff_isAlt_toLinearMap₂'_sub.mpr (isAlt_toLinearMap₂'_upperQuadratic_sub M)

/-- Uniqueness: every upper-triangular matrix `N` whose difference from `M` induces an alternating
bilinear form equals `M.upperQuadratic`. -/
theorem eq_upperQuadratic_of_isUpperTriangular_of_isAlt [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] {N M : Matrix ι ι R} (hN : N.IsUpperTriangular)
    (hAlt : (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) (N - M)).IsAlt) :
    N = M.upperQuadratic := by
  obtain ⟨hdiag, hsymm⟩ := isAlt_toLinearMap₂'_diag_and_symm hAlt
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hji0 : N j i = 0 := hN hij
    have hs := hsymm i j
    simp only [Matrix.sub_apply, hji0, zero_sub, ← sub_eq_add_neg, sub_sub] at hs
    rw [upperQuadratic_apply_of_lt _ hij]
    exact sub_eq_zero.mp hs
  · have hd := hdiag i
    simp only [Matrix.sub_apply, sub_eq_zero] at hd
    rwa [upperQuadratic_apply_self]
  · rw [upperQuadratic_apply_of_gt _ hji]
    exact hN hji

/-- Uniqueness in quadratic-form terms: every upper-triangular matrix `N` inducing the same
`Matrix.toQuadraticForm'` as `M` equals `M.upperQuadratic`. -/
theorem eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq [Fintype ι] [DecidableEq ι]
    [LinearOrder ι] [CommRing R] {N M : Matrix ι ι R} (hN : N.IsUpperTriangular)
    (hQ : N.toQuadraticForm' = M.toQuadraticForm') :
    N = M.upperQuadratic :=
  eq_upperQuadratic_of_isUpperTriangular_of_isAlt hN
    (toQuadraticForm'_eq_iff_isAlt_toLinearMap₂'_sub.mp hQ)

/-- Characterization of `M.upperQuadratic` by upper triangularity and alternating difference. -/
theorem eq_upperQuadratic_iff [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]
    {N M : Matrix ι ι R} :
    (N.IsUpperTriangular ∧ (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R) (N - M)).IsAlt) ↔
      N = M.upperQuadratic :=
  ⟨fun ⟨hN, hAlt⟩ => eq_upperQuadratic_of_isUpperTriangular_of_isAlt hN hAlt,
   fun h => h ▸ ⟨isUpperTriangular_upperQuadratic M, isAlt_toLinearMap₂'_upperQuadratic_sub M⟩⟩

/-- Characterization of `M.upperQuadratic` by upper triangularity and equal quadratic form. -/
theorem eq_upperQuadratic_iff_toQuadraticForm'_eq [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] {N M : Matrix ι ι R} :
    (N.IsUpperTriangular ∧ N.toQuadraticForm' = M.toQuadraticForm') ↔ N = M.upperQuadratic := by
  rw [toQuadraticForm'_eq_iff_isAlt_toLinearMap₂'_sub]
  exact eq_upperQuadratic_iff

/-- `M.upperQuadratic = M` if and only if `M` is upper triangular. -/
theorem upperQuadratic_eq_self_iff [LinearOrder ι] [AddZeroClass R] {M : Matrix ι ι R} :
    M.upperQuadratic = M ↔ M.IsUpperTriangular := by
  constructor
  · intro h
    rw [← h]
    exact isUpperTriangular_upperQuadratic M
  · intro hM
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [upperQuadratic_apply_of_lt _ hij, hM hij, add_zero]
    · exact upperQuadratic_apply_self M i
    · rw [upperQuadratic_apply_of_gt _ hji, hM hji]

/-- An upper-triangular matrix equals its own canonical upper-triangular quadratic
representative. -/
theorem IsUpperTriangular.upperQuadratic_eq [LinearOrder ι] [AddZeroClass R]
    {M : Matrix ι ι R} (hM : M.IsUpperTriangular) :
    M.upperQuadratic = M :=
  upperQuadratic_eq_self_iff.mpr hM

@[simp]
theorem upperQuadratic_upperQuadratic [LinearOrder ι] [AddZeroClass R] (M : Matrix ι ι R) :
    M.upperQuadratic.upperQuadratic = M.upperQuadratic :=
  upperQuadratic_eq_self_iff.mpr (isUpperTriangular_upperQuadratic M)

/-- Two matrices have the same canonical upper-triangular representative if and only if they induce
the same quadratic form. -/
theorem upperQuadratic_eq_upperQuadratic_iff [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    [CommRing R] {M N : Matrix ι ι R} :
    M.upperQuadratic = N.upperQuadratic ↔ M.toQuadraticForm' = N.toQuadraticForm' := by
  constructor
  · intro h
    rw [← toQuadraticForm'_upperQuadratic M, h, toQuadraticForm'_upperQuadratic N]
  · intro h
    exact eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq
      (isUpperTriangular_upperQuadratic M) ((toQuadraticForm'_upperQuadratic M).trans h)

end Quadratic

end Matrix
