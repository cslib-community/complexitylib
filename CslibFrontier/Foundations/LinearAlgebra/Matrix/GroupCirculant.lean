/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.DFT
public import CslibFrontier.Foundations.Combinatorics.Expander.Cayley
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.KroneckerRank
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.LinearAlgebra.Matrix.Circulant
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Group-circulant spectra, character matrices, and Boolean-cube diagonalization

For a finite additive abelian group `G` and weight function `w : G → R`, Mathlib's
`Matrix.circulant w : Matrix G G R` has `(x, y)`-entry `w (x - y)`. Every additive character
`ψ : AddChar G R` is an eigenvector of `Matrix.circulant w` with eigenvalue
`Matrix.circulantEigenvalue w ψ = ∑ g : G, w g * ψ (-g)` (`Matrix.circulant_mulVec_addChar`),
and multiplication of group-circulant matrices corresponds to pointwise multiplication of these
character eigenvalues (`Matrix.circulantEigenvalue_mulVec`).

Assembling the characters as columns of `Matrix.addCharMatrix G L` and conjugate rows of
`Matrix.dualAddCharMatrix G L` diagonalizes `Matrix.circulant w` over any field `L` with
`(Fintype.card G : L) ≠ 0` and `Fintype.card (AddChar G L) = Fintype.card G` (a character-splitting
field for `G`), yielding `(Matrix.circulant w).rank = Nat.card {ψ // circulantEigenvalue w ψ ≠ 0}`
(`Matrix.rank_circulant_of_card_addChar_eq`, and finset-cardinality form
`Matrix.rank_circulant_eq_card_filter`). Combining Pontryagin duality (`AddChar.card_eq`) with
`Matrix.rank_map_of_field` (`CslibFrontier/Foundations/LinearAlgebra/Matrix/Rank.lean`) gives
`Matrix.rank_circulant_of_field_hom`, `Matrix.rank_circulant_complex`,
`Matrix.rank_circulant_rat`, and `Matrix.rank_circulant_real`.

On the Boolean cube `ι → Bool`, the character (Walsh–Hadamard) matrix `Matrix.cubeCharMatrix R ι`
factors on `Fin n → Bool` as the `n`-th Kronecker power
`Matrix.kroneckerPow (Matrix.sylvesterTwo R) n` (`Matrix.cubeCharMatrix_eq_kroneckerPow`),
satisfies `cubeCharMatrix R ι * cubeCharMatrix R ι = (2 ^ Fintype.card ι : R) • 1`
(`Matrix.cubeCharMatrix_mul_self`), and diagonalizes every Boolean-cube circulant directly over any
field `K` with `(2 : K) ≠ 0` (`Matrix.rank_circulant_cube`). Specialization lemmas connect
Boolean-cube circulants to the walk operator and generator bias of `Cslib.RotationMap.cubeCayley`
(`Matrix.cubeCayley_walk_eq_circulant_mulVec`, `Matrix.circulantEigenvalue_cubeCayleyWeight`) and
cyclic circulants on `Fin n` to `Cslib.dft` (`Matrix.circulant_mulVec_pow_eq_dft_smul`).

## Main definitions

* `Matrix.circulantEigenvalue`: eigenvalue `∑ g, w g * ψ (-g)` of `Matrix.circulant w` on `ψ`.
* `Matrix.addCharMatrix`, `Matrix.dualAddCharMatrix`: character and dual-character matrices on `G`.
* `Matrix.sylvesterTwo`, `Matrix.cubeCharMatrix`: `2 × 2` Sylvester kernel and Walsh–Hadamard
  Boolean-cube character matrix.
* `Matrix.cubeCayleyWeight`: transition weight vector realizing `(cubeCayley s).walk` as a
  Boolean-cube circulant.

## Main results

* `Matrix.circulant_mulVec_addChar`, `Matrix.circulantEigenvalue_mulVec`: character eigenpairs and
  convolution multiplicativity.
* `Matrix.circulant_mul_addCharMatrix`, `Matrix.dualAddCharMatrix_mul_addCharMatrix`,
  `Matrix.diagonalize_circulant_of_card_addChar_eq`: character-matrix orthogonality and similarity
  diagonalization.
* `Matrix.rank_circulant_of_card_addChar_eq`, `Matrix.rank_circulant_eq_card_filter`,
  `Matrix.rank_circulant_of_rank_map_eq`, `Matrix.rank_circulant_complex`: rank equals the count
  of nonzero character eigenvalues.
* `Matrix.cubeCharMatrix_eq_kroneckerPow`, `Matrix.cubeCharMatrix_mul_self`,
  `Matrix.rank_cubeCharMatrix`, `Matrix.rank_circulant_cube`: Walsh–Hadamard Kronecker power,
  orthogonality, and Boolean-cube circulant rank in characteristic `≠ 2`.
* `Matrix.cubeCayley_walk_eq_circulant_mulVec`, `Matrix.circulantEigenvalue_cubeCayleyWeight`,
  `Matrix.circulant_mulVec_pow_eq_dft_smul`: bridges to `Cslib.RotationMap.cubeCayley` and
  `Cslib.dft`.
-/

public section

namespace Matrix

open Finset
open scoped BigOperators

/-! ### Group-circulant eigenvectors and character eigenvalues -/

section Eigenvalues

variable {G R : Type*} [AddCommGroup G] [Fintype G]

/-- The character eigenvalue associated to `w : G → R` at `ψ : AddChar G R`, given by
`∑ g : G, w g * ψ (-g)`. -/
@[expose] def circulantEigenvalue [CommSemiring R] (w : G → R) (ψ : AddChar G R) : R :=
  ∑ g : G, w g * ψ (-g)

/-- Every additive character `ψ : AddChar G R` is an eigenvector of `Matrix.circulant w` with
eigenvalue `circulantEigenvalue w ψ`. -/
theorem circulant_mulVec_addChar [CommSemiring R] (w : G → R) (ψ : AddChar G R) :
    circulant w *ᵥ (⇑ψ) = circulantEigenvalue w ψ • (⇑ψ) := by
  funext x
  simp only [mulVec, dotProduct, circulant_apply, Pi.smul_apply, smul_eq_mul,
    circulantEigenvalue, sum_mul]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ fun y => ?_
  have hy : y = x + -(x - y) := by abel
  have hψ : ψ y = ψ x * ψ (-(x - y)) := by
    conv_lhs => rw [hy]
    exact ψ.map_add_eq_mul _ _
  rw [Equiv.subLeft_apply, hψ, mul_comm (ψ x), ← mul_assoc]

@[simp]
theorem circulantEigenvalue_zero [CommSemiring R] (ψ : AddChar G R) :
    circulantEigenvalue (0 : G → R) ψ = 0 := by
  simp [circulantEigenvalue]

theorem circulantEigenvalue_add [CommSemiring R] (u v : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (u + v) ψ = circulantEigenvalue u ψ + circulantEigenvalue v ψ := by
  simp only [circulantEigenvalue, Pi.add_apply, add_mul, sum_add_distrib]

theorem circulantEigenvalue_smul [CommSemiring R] (c : R) (w : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (c • w) ψ = c * circulantEigenvalue w ψ := by
  simp only [circulantEigenvalue, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]

@[simp]
theorem circulantEigenvalue_single_zero [CommSemiring R] [DecidableEq G] (a : R)
    (ψ : AddChar G R) :
    circulantEigenvalue (Pi.single 0 a : G → R) ψ = a := by
  rw [circulantEigenvalue, Fintype.sum_eq_single 0 fun g hg => by simp [hg]]
  simp

@[simp]
theorem circulantEigenvalue_trivial [CommSemiring R] (w : G → R) :
    circulantEigenvalue w (0 : AddChar G R) = ∑ g : G, w g := by
  simp [circulantEigenvalue]

/-- When `w` is negation-symmetric (`w (-g) = w g`, e.g. undirected Cayley graphs or `𝔽₂^n`),
`circulantEigenvalue w ψ` equals `∑ g, w g * ψ g`. -/
theorem circulantEigenvalue_of_symm [CommSemiring R] {w : G → R} (hw : ∀ g, w (-g) = w g)
    (ψ : AddChar G R) :
    circulantEigenvalue w ψ = ∑ g : G, w g * ψ g := by
  unfold circulantEigenvalue
  refine Fintype.sum_equiv (Equiv.neg G) _ _ fun g => ?_
  simp [hw g]

/-- **Convolution multiplicativity**: the character eigenvalue of the convolution vector
`circulant u *ᵥ v` (which generates `circulant u * circulant v` via `Matrix.circulant_mul`) is the
product of the character eigenvalues of `u` and `v`. -/
theorem circulantEigenvalue_mulVec [CommSemiring R] (u v : G → R) (ψ : AddChar G R) :
    circulantEigenvalue (circulant u *ᵥ v) ψ =
      circulantEigenvalue u ψ * circulantEigenvalue v ψ := by
  have h1 := congrFun (circulant_mulVec_addChar (circulant u *ᵥ v) ψ) 0
  have h2 : (circulant (circulant u *ᵥ v) *ᵥ (⇑ψ)) 0 =
      (circulantEigenvalue u ψ * circulantEigenvalue v ψ) * ψ 0 := by
    rw [← circulant_mul, ← mulVec_mulVec, circulant_mulVec_addChar, mulVec_smul,
      circulant_mulVec_addChar, smul_smul]
    simp [mul_comm]
  simpa using h1.symm.trans h2

/-- Scalar homomorphisms commute with `circulantEigenvalue`. -/
theorem map_circulantEigenvalue {S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (w : G → R) (ψ : AddChar G R) :
    f (circulantEigenvalue w ψ) =
      circulantEigenvalue (f ∘ w) (f.toMonoidHom.compAddChar ψ) := by
  simp [circulantEigenvalue, map_sum, map_mul]

end Eigenvalues

/-! ### Character matrices, diagonalization, and rank over splitting fields and `ℂ` -/

section Diagonalization

/-- Matrix whose columns are the additive characters `ψ : AddChar G R` evaluated on `G`. -/
@[expose] def addCharMatrix (G R : Type*) [AddCommGroup G] [CommMonoid R] :
    Matrix G (AddChar G R) R :=
  of fun g ψ => ψ g

/-- Dual character matrix with `(ψ, g)`-entry `ψ (-g)`. -/
@[expose] def dualAddCharMatrix (G R : Type*) [AddCommGroup G] [CommMonoid R] :
    Matrix (AddChar G R) G R :=
  of fun ψ g => ψ (-g)

@[simp]
theorem addCharMatrix_apply {G R : Type*} [AddCommGroup G] [CommMonoid R]
    (g : G) (ψ : AddChar G R) :
    addCharMatrix G R g ψ = ψ g :=
  rfl

@[simp]
theorem dualAddCharMatrix_apply {G R : Type*} [AddCommGroup G] [CommMonoid R]
    (ψ : AddChar G R) (g : G) :
    dualAddCharMatrix G R ψ g = ψ (-g) :=
  rfl

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Right-multiplying `circulant w` by `addCharMatrix` scales each column `ψ` by
`circulantEigenvalue w ψ`. -/
theorem circulant_mul_addCharMatrix {R : Type*} [CommSemiring R] [Fintype (AddChar G R)]
    [DecidableEq (AddChar G R)] (w : G → R) :
    circulant w * addCharMatrix G R =
      addCharMatrix G R * diagonal (circulantEigenvalue w) := by
  ext x ψ
  have h := congrFun (circulant_mulVec_addChar w ψ) x
  rw [mul_diagonal]
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using h

/-- Character orthogonality in matrix form: `dualAddCharMatrix * addCharMatrix = |G| • 1` over any
integral domain. -/
theorem dualAddCharMatrix_mul_addCharMatrix {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq (AddChar G R)] :
    dualAddCharMatrix G R * addCharMatrix G R =
      (Fintype.card G : R) • (1 : Matrix (AddChar G R) (AddChar G R) R) := by
  ext ψ χ
  have hsum : (∑ g : G, ψ (-g) * χ g) = ∑ g : G, (χ - ψ) g := by
    refine sum_congr rfl fun g _ => ?_
    rw [AddChar.sub_apply, mul_comm]
  rw [Matrix.mul_apply]
  dsimp only [dualAddCharMatrix_apply, addCharMatrix_apply]
  rw [hsum, AddChar.sum_eq_ite]
  simp [Matrix.one_apply, sub_eq_zero, eq_comm]

/-- **Similarity diagonalization of a group circulant** over any field `L` with
`(Fintype.card G : L) ≠ 0` and `Fintype.card (AddChar G L) = Fintype.card G`. -/
theorem diagonalize_circulant_of_card_addChar_eq {L : Type*} [Field L] [Fintype (AddChar G L)]
    [DecidableEq G] (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
    let P : Matrix G G L := (addCharMatrix G L).submatrix id e
    let Q : Matrix G G L := (Fintype.card G : L)⁻¹ • (dualAddCharMatrix G L).submatrix e id
    Q * P = 1 ∧ IsUnit P ∧ IsUnit Q ∧
      Q * circulant w * P = diagonal (fun g => circulantEigenvalue w (e g)) := by
  classical
  dsimp only
  let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
  let P : Matrix G G L := (addCharMatrix G L).submatrix id e
  let Q : Matrix G G L := (Fintype.card G : L)⁻¹ • (dualAddCharMatrix G L).submatrix e id
  have hQP : Q * P = 1 := by
    have hm : (dualAddCharMatrix G L).submatrix e id * (addCharMatrix G L).submatrix id e =
        (dualAddCharMatrix G L * addCharMatrix G L).submatrix e e := by
      ext i j
      simp [Matrix.mul_apply]
    dsimp only [Q, P]
    rw [smul_mul, hm, dualAddCharMatrix_mul_addCharMatrix]
    ext i j
    simp [Matrix.one_apply, e.injective.eq_iff, inv_mul_cancel₀ hchar]
  have hdetQP : Q.det * P.det = 1 := by rw [← det_mul, hQP, det_one]
  have hQunit : IsUnit Q :=
    (isUnit_iff_isUnit_det Q).mpr (IsUnit.mk0 _ (left_ne_zero_of_mul_eq_one hdetQP))
  have hPunit : IsUnit P :=
    (isUnit_iff_isUnit_det P).mpr (IsUnit.mk0 _ (right_ne_zero_of_mul_eq_one hdetQP))
  have hCP : circulant w * P = P * diagonal (fun g => circulantEigenvalue w (e g)) := by
    have hc := circulant_mul_addCharMatrix w
    ext x g
    have hxg := congrFun (congrFun hc x) (e g)
    rw [mul_diagonal] at hxg ⊢
    simpa [P, Matrix.mul_apply] using hxg
  have hdiag : Q * circulant w * P = diagonal (fun g => circulantEigenvalue w (e g)) := by
    rw [Matrix.mul_assoc, hCP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  exact ⟨hQP, hPunit, hQunit, hdiag⟩

/-- **Rank of a group-circulant matrix over a character-splitting field**: when `AddChar G L` has
cardinality `|G|` and `(|G| : L) ≠ 0`, `(circulant w).rank` equals the number of characters with
nonzero eigenvalue. -/
theorem rank_circulant_of_card_addChar_eq {L : Type*} [Field L] [Fintype (AddChar G L)]
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue w ψ ≠ 0} := by
  classical
  let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
  obtain ⟨_, hPunit, hQunit, hdiag⟩ := diagonalize_circulant_of_card_addChar_eq hchar hcard w
  let P : Matrix G G L := (addCharMatrix G L).submatrix id e
  let Q : Matrix G G L := (Fintype.card G : L)⁻¹ • (dualAddCharMatrix G L).submatrix e id
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hPunit
  have hQdet : IsUnit Q.det := (isUnit_iff_isUnit_det Q).mp hQunit
  have hr : (Q * circulant w * P).rank = (circulant w).rank := by
    rw [rank_mul_eq_left_of_isUnit_det P (Q * circulant w) hPdet,
      rank_mul_eq_right_of_isUnit_det Q (circulant w) hQdet]
  rw [← hr, hdiag, rank_diagonal, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

/-- Finset-cardinality form of `rank_circulant_of_card_addChar_eq` when `L` has decidable
equality. -/
theorem rank_circulant_eq_card_filter {L : Type*} [Field L] [DecidableEq L] [Fintype (AddChar G L)]
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    (circulant w).rank = #{ψ : AddChar G L | circulantEigenvalue w ψ ≠ 0} := by
  rw [rank_circulant_of_card_addChar_eq hchar hcard w, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **Rank of a group-circulant matrix via a rank-preserving scalar extension** `f : K →+* L` into
a character-splitting field `L`. -/
theorem rank_circulant_of_rank_map_eq {K L : Type*} [Field K] [Field L] [Fintype (AddChar G L)]
    (f : K →+* L) {w : G → K} (hrank : ((circulant w).map f).rank = (circulant w).rank)
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue (f ∘ w) ψ ≠ 0} := by
  rw [← hrank, map_circulant]
  exact rank_circulant_of_card_addChar_eq hchar hcard (f ∘ w)

/-- **Rank of a group-circulant matrix via scalar extension** along `f : K →+* L` into a
character-splitting field `L`, reusing `Matrix.rank_map_of_field`. -/
theorem rank_circulant_of_field_hom {K L : Type*} [Field K] [Field L] [Fintype (AddChar G L)]
    (f : K →+* L) (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → K) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue (f ∘ w) ψ ≠ 0} :=
  rank_circulant_of_rank_map_eq f (rank_map_of_field f (circulant w)) hchar hcard

/-- **Rank of a complex group-circulant matrix**: `(circulant w).rank` equals the number of complex
characters with nonzero eigenvalue. -/
theorem rank_circulant_complex (w : G → ℂ) :
    (circulant w).rank = Nat.card {ψ : AddChar G ℂ // circulantEigenvalue w ψ ≠ 0} :=
  rank_circulant_of_card_addChar_eq (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    AddChar.card_eq w

/-- **Rank of a rational group-circulant matrix**: `(circulant w).rank` equals the number of
complex characters where `∑ g, (w g : ℂ) * ψ (-g) ≠ 0`. -/
theorem rank_circulant_rat (w : G → ℚ) :
    (circulant w).rank =
      Nat.card {ψ : AddChar G ℂ // circulantEigenvalue (fun g => (w g : ℂ)) ψ ≠ 0} :=
  rank_circulant_of_field_hom (Rat.castHom ℂ)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) AddChar.card_eq w

/-- **Rank of a real group-circulant matrix**: `(circulant w).rank` equals the number of complex
characters where `∑ g, (w g : ℂ) * ψ (-g) ≠ 0`. -/
theorem rank_circulant_real (w : G → ℝ) :
    (circulant w).rank =
      Nat.card {ψ : AddChar G ℂ // circulantEigenvalue (fun g => (w g : ℂ)) ψ ≠ 0} :=
  rank_circulant_of_field_hom Complex.ofRealHom
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) AddChar.card_eq w

end Diagonalization

/-! ### Boolean-cube character (Walsh–Hadamard) matrices and Kronecker powers -/

section BooleanCube

/-- The `2 × 2` Sylvester–Hadamard kernel `[[1, 1], [1, -1]]` indexed by `Bool`. -/
@[expose] def sylvesterTwo (R : Type*) [Ring R] : Matrix Bool Bool R :=
  of fun a b => if a && b then -1 else 1

@[simp]
theorem sylvesterTwo_apply {R : Type*} [Ring R] (a b : Bool) :
    sylvesterTwo R a b = if a && b then -1 else 1 :=
  rfl

/-- `sylvesterTwo R * sylvesterTwo R = 2 • 1` over any commutative ring. -/
theorem sylvesterTwo_mul_self (R : Type*) [CommRing R] :
    sylvesterTwo R * sylvesterTwo R = (2 : R) • (1 : Matrix Bool Bool R) := by
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases a <;> cases b <;> simp [sylvesterTwo] <;> ring

/-- The Walsh–Hadamard character matrix on the Boolean cube `ι → Bool`, with `(x, y)`-entry
`χ_{supp y}(x) = ∏_{i : y i} (-1)^{x i}`. -/
@[expose] def cubeCharMatrix (R ι : Type*) [CommRing R] [Fintype ι] :
    Matrix (ι → Bool) (ι → Bool) R :=
  of fun x y => Cslib.BitString.chi R (univ.filter fun i => y i = true) x

theorem cubeCharMatrix_apply {R ι : Type*} [CommRing R] [Fintype ι] (x y : ι → Bool) :
    cubeCharMatrix R ι x y = ∏ i : ι, sylvesterTwo R (x i) (y i) := by
  simp only [cubeCharMatrix, of_apply, Cslib.BitString.chi, prod_filter, sylvesterTwo_apply]
  refine prod_congr rfl fun i _ => ?_
  cases x i <;> cases y i <;> simp

/-- **Walsh–Hadamard Kronecker-power factorization**: on `Fin n → Bool`, `cubeCharMatrix R (Fin n)`
is identically the `n`-th Kronecker power of `sylvesterTwo R`. -/
theorem cubeCharMatrix_eq_kroneckerPow (R : Type*) [CommRing R] (n : ℕ) :
    cubeCharMatrix R (Fin n) = kroneckerPow (sylvesterTwo R) n := by
  ext x y
  rw [cubeCharMatrix_apply, kroneckerPow_apply]

/-- `cubeCharMatrix R ι` is symmetric. -/
theorem transpose_cubeCharMatrix (R ι : Type*) [CommRing R] [Fintype ι] :
    (cubeCharMatrix R ι)ᵀ = cubeCharMatrix R ι := by
  ext x y
  simp only [transpose_apply, cubeCharMatrix_apply, sylvesterTwo_apply, Bool.and_comm]

/-- **Orthogonality of the Boolean-cube character matrix** over any commutative ring:
`cubeCharMatrix R ι * cubeCharMatrix R ι = (2 ^ |ι| : R) • 1`. -/
theorem cubeCharMatrix_mul_self (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    cubeCharMatrix R ι * cubeCharMatrix R ι =
      ((2 : R) ^ Fintype.card ι) • (1 : Matrix (ι → Bool) (ι → Bool) R) := by
  ext x z
  have hrhs : (((2 : R) ^ Fintype.card ι) • (1 : Matrix (ι → Bool) (ι → Bool) R)) x z =
      if x = z then (2 : R) ^ Fintype.card ι else 0 := by
    simp [Matrix.one_apply]
  rw [hrhs]
  simp only [Matrix.mul_apply, cubeCharMatrix_apply, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
    sylvesterTwo R (x i) b * sylvesterTwo R b (z i))]
  by_cases hxz : x = z
  · subst hxz
    have hpair : ∀ i : ι, (∑ b : Bool, sylvesterTwo R (x i) b * sylvesterTwo R b (x i)) = 2 := by
      intro i
      rw [Fintype.sum_bool]
      cases x i <;> simp [sylvesterTwo] <;> ring
    simp_rw [hpair]
    simp
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hxz
    rw [ite_eq_right hxz]
    refine prod_eq_zero (mem_univ i₀) ?_
    rw [Fintype.sum_bool]
    revert hi₀
    cases x i₀ <;> cases z i₀ <;> simp [sylvesterTwo]

/-- Over any field of characteristic different from `2`, `cubeCharMatrix K ι` is invertible and has
full rank `2 ^ |ι|`. -/
theorem isUnit_cubeCharMatrix {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) :
    IsUnit (cubeCharMatrix K ι) := by
  have hpow : ((2 : K) ^ Fintype.card ι) ≠ 0 := pow_ne_zero _ h2
  have hmul : (((2 : K) ^ Fintype.card ι)⁻¹ • cubeCharMatrix K ι) * cubeCharMatrix K ι = 1 := by
    rw [smul_mul, cubeCharMatrix_mul_self, smul_smul, inv_mul_cancel₀ hpow, one_smul]
  have hdet : (((2 : K) ^ Fintype.card ι)⁻¹ • cubeCharMatrix K ι).det *
      (cubeCharMatrix K ι).det = 1 := by
    rw [← det_mul, hmul, det_one]
  exact (isUnit_iff_isUnit_det _).mpr (IsUnit.mk0 _ (right_ne_zero_of_mul_eq_one hdet))

theorem rank_cubeCharMatrix {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) :
    (cubeCharMatrix K ι).rank = 2 ^ Fintype.card ι := by
  simpa using rank_of_isUnit (cubeCharMatrix K ι) (isUnit_cubeCharMatrix h2)

private theorem bitString_neg_eq_self {ι : Type*} (x : ι → Bool) : -x = x :=
  neg_eq_of_add_eq_zero_right (Cslib.BitString.add_self x)

/-- Right-multiplying a Boolean-cube circulant `circulant w` by `cubeCharMatrix R ι` scales column
`y` by the Walsh–Hadamard eigenvalue `∑ x, w x * cubeCharMatrix R ι x y`. -/
theorem circulant_mul_cubeCharMatrix {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (w : (ι → Bool) → R) :
    circulant w * cubeCharMatrix R ι =
      cubeCharMatrix R ι * diagonal (fun y => ∑ x, w x * cubeCharMatrix R ι x y) := by
  ext x y
  let S : Finset ι := univ.filter fun i => y i = true
  have hc := congrFun (circulant_mulVec_addChar w (Cslib.BitString.chiChar R S)) x
  have hsymm : circulantEigenvalue w (Cslib.BitString.chiChar R S) =
      ∑ g, w g * cubeCharMatrix R ι g y := by
    rw [circulantEigenvalue_of_symm (fun g => by rw [bitString_neg_eq_self])]
    rfl
  rw [mul_diagonal, Matrix.mul_apply]
  change (circulant w *ᵥ ⇑(Cslib.BitString.chiChar R S)) x =
    cubeCharMatrix R ι x y * ∑ g, w g * cubeCharMatrix R ι g y
  rw [hc, Pi.smul_apply, smul_eq_mul, hsymm, mul_comm]
  rfl

/-- **Rank of a Boolean-cube circulant** over any field `K` with `(2 : K) ≠ 0` (`ℚ`, `ℝ`, or odd
characteristic): `(circulant w).rank` equals the number of subsets `S : Finset ι` whose Walsh
transform `∑ x, w x * χ_S(x)` is nonzero. -/
theorem rank_circulant_cube {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (w : (ι → Bool) → K) :
    (circulant w).rank =
      #{S : Finset ι | ∑ x : ι → Bool, w x * Cslib.BitString.chi K S x ≠ 0} := by
  let H := cubeCharMatrix K ι
  have hpow : ((2 : K) ^ Fintype.card ι) ≠ 0 := pow_ne_zero _ h2
  let Hinv := ((2 : K) ^ Fintype.card ι)⁻¹ • H
  have hHH : Hinv * H = 1 := by
    rw [smul_mul, cubeCharMatrix_mul_self, smul_smul, inv_mul_cancel₀ hpow, one_smul]
  have hHdet : IsUnit H.det := (isUnit_iff_isUnit_det H).mp (isUnit_cubeCharMatrix h2)
  have hHinv_det : IsUnit Hinv.det := by
    have hd : Hinv.det * H.det = 1 := by rw [← det_mul, hHH, det_one]
    exact IsUnit.mk0 _ (left_ne_zero_of_mul_eq_one hd)
  have hdiag : Hinv * circulant w * H =
      diagonal (fun y => ∑ x, w x * H x y) := by
    rw [Matrix.mul_assoc, circulant_mul_cubeCharMatrix, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hr : (Hinv * circulant w * H).rank = (circulant w).rank := by
    rw [rank_mul_eq_left_of_isUnit_det H (Hinv * circulant w) hHdet,
      rank_mul_eq_right_of_isUnit_det Hinv (circulant w) hHinv_det]
  rw [← hr, hdiag, rank_diagonal, Fintype.card_subtype]
  refine Finset.card_bij (fun y _ => univ.filter fun i => y i = true)
    (fun y hy => ?_) (fun y₁ _ y₂ _ h => ?_) (fun S hS => ?_)
  · simpa [H, cubeCharMatrix] using hy
  · funext i
    have hi := Finset.ext_iff.mp h i
    simp only [mem_filter, mem_univ, true_and] at hi
    exact Bool.eq_iff_iff.mpr hi
  · refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
    · have hS' : (univ.filter fun i => decide (i ∈ S) = true) = S := by
        ext i
        simp
      simpa [H, cubeCharMatrix, hS'] using hS
    · ext i
      simp

end BooleanCube

/-! ### Bridges to Boolean-cube Cayley graphs (`Cslib.RotationMap.cubeCayley`) and cyclic DFT -/

section Bridges

/-- Normalized generator-multiplicity weight of `Cslib.RotationMap.cubeCayley s`. -/
@[expose] noncomputable def cubeCayleyWeight {ι : Type*} [Fintype ι] {d : ℕ}
    (s : Fin d → ι → Bool) (g : ι → Bool) : ℝ :=
  (#{j : Fin d | s j = g} : ℝ) / d

/-- The walk operator of `Cslib.RotationMap.cubeCayley s` acts as matrix-vector multiplication by
`Matrix.circulant (cubeCayleyWeight s)`. -/
theorem cubeCayley_walk_eq_circulant_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (s : Fin d → ι → Bool) (f : (ι → Bool) → ℝ) :
    (Cslib.RotationMap.cubeCayley s).walk f = circulant (cubeCayleyWeight s) *ᵥ f := by
  funext u
  rw [Cslib.RotationMap.walk_apply]
  simp only [Cslib.RotationMap.cubeCayley_neighbor, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, mulVec, dotProduct, circulant_apply, cubeCayleyWeight]
  have hsum : (∑ y : ι → Bool, (#{j : Fin d | s j = u - y} : ℝ) / d * f y) =
      (∑ y : ι → Bool, ∑ j : Fin d, if s j = u - y then f y / d else 0) := by
    refine sum_congr rfl fun y _ => ?_
    rw [card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_div, sum_mul, ite_div, zero_div,
      ite_mul, zero_mul]
    exact sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [hsum, sum_comm, sum_div]
  refine sum_congr rfl fun j _ => ?_
  have heq : ∀ y : ι → Bool, (s j = u - y) ↔ (y = u + s j) := fun y => by
    rw [sub_eq_add_neg, bitString_neg_eq_self]
    constructor
    · intro h
      rw [h, ← add_assoc, Cslib.BitString.add_self, zero_add]
    · intro h
      rw [h, ← add_assoc, Cslib.BitString.add_self, zero_add]
  simp [heq]

/-- The character eigenvalue of `cubeCayleyWeight s` at `chiChar ℝ S` agrees with the generator
bias `Cslib.BitString.bias ((Cslib.Probability.PMF.uniformOfFintype (Fin d)).map s) S`. -/
theorem circulantEigenvalue_cubeCayleyWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    [NeZero d] (s : Fin d → ι → Bool) (S : Finset ι) :
    circulantEigenvalue (cubeCayleyWeight s) (Cslib.BitString.chiChar ℝ S) =
      Cslib.BitString.bias ((Cslib.Probability.PMF.uniformOfFintype (Fin d)).map s) S := by
  have hw := congrFun (cubeCayley_walk_eq_circulant_mulVec s (Cslib.BitString.chi ℝ S)) 0
  rw [show Cslib.BitString.chi ℝ S = ⇑(Cslib.BitString.chiChar ℝ S) from rfl,
    circulant_mulVec_addChar] at hw
  have hw0 : (Cslib.RotationMap.cubeCayley s).walk (Cslib.BitString.chi ℝ S) 0 =
      circulantEigenvalue (cubeCayleyWeight s) (Cslib.BitString.chiChar ℝ S) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hw
  rw [← hw0, Cslib.BitString.bias_uniformOfFintype_map, Cslib.RotationMap.walk_apply]
  refine expect_congr rfl fun j _ => ?_
  simp [Cslib.RotationMap.cubeCayley_neighbor]

/-- On `Fin (n + 1)`, the `k`-th Fourier mode `j ↦ ω ^ (j * k)` (for `ω ^ (n + 1) = 1`) is an
eigenvector of `Matrix.circulant w` with eigenvalue `Cslib.dft ω (fun i => w (-i)) k`. -/
theorem circulant_mulVec_pow_eq_dft_smul {R : Type*} [CommRing R] {n : ℕ} {ω : R}
    (hω : ω ^ (n + 1) = 1) (w : Fin (n + 1) → R) (k : Fin (n + 1)) :
    circulant w *ᵥ (fun j : Fin (n + 1) => ω ^ ((j : ℕ) * k)) =
      Cslib.dft ω (fun i : Fin (n + 1) => w (-i)) k •
        (fun j : Fin (n + 1) => ω ^ ((j : ℕ) * k)) := by
  funext x
  simp only [mulVec, dotProduct, circulant_apply, Cslib.dft, Pi.smul_apply, smul_eq_mul, sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun j => ?_
  rw [Equiv.subRight_apply]
  have hpow : ω ^ (((j - x : Fin (n + 1)) : ℕ) * k) * ω ^ ((x : ℕ) * k) =
      ω ^ ((j : ℕ) * k) := by
    have hadd : (j - x) + x = j := sub_add_cancel j x
    calc ω ^ (((j - x : Fin (n + 1)) : ℕ) * k) * ω ^ ((x : ℕ) * k)
        = ω ^ ((((j - x) + x : Fin (n + 1)) : ℕ) * k) := by
            symm
            rw [Fin.val_add, pow_eq_pow_mod _ hω, Nat.mod_mul_mod, ← pow_eq_pow_mod _ hω,
              add_mul, pow_add]
      _ = ω ^ ((j : ℕ) * k) := by rw [hadd]
  rw [neg_sub, mul_assoc, hpow]

end Bridges

end Matrix
