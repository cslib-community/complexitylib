/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDeterminantDoubleContact

/-!
# Generic determinant irreducibility

The determinant is written as a primitive linear polynomial in a pivot
variable.  Induction on the matrix size and a sparse permutation-matrix
specialization exclude divisibility of the constant term by the leading
minor.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`GenericDeterminantIrreducible.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace SquarePolynomial

theorem detPoly_one_eq :
    detPoly 1 = MvPolynomial.X ((0 : Fin 1), (0 : Fin 1)) := by
  rw [detPoly, Matrix.det_fin_one]
  rfl

theorem detPoly_one_irreducible : Irreducible (detPoly 1) := by
  rw [detPoly_one_eq]
  exact MvPolynomial.prime_X.irreducible

/-- The distinguished lower-right entry of a two-by-two matrix. -/
abbrev pivot2 : Var 2 := ((1 : Fin 2), (1 : Fin 2))
/-- The three undistinguished entries of a two-by-two matrix. -/
abbrev Other2 := Free pivot2

/-- The upper-left variable among the undistinguished two-by-two entries. -/
def other2TopLeft : Other2 := ⟨((0 : Fin 2), (0 : Fin 2)), by decide⟩
/-- The upper-right variable among the undistinguished two-by-two entries. -/
def other2TopRight : Other2 := ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩
/-- The lower-left variable among the undistinguished two-by-two entries. -/
def other2BottomLeft : Other2 := ⟨((1 : Fin 2), (0 : Fin 2)), by decide⟩

lemma detPoly_two_nested :
    toNested (R := ℝ) pivot2 (detPoly 2) =
      Polynomial.C (MvPolynomial.X other2TopLeft) * Polynomial.X +
        Polynomial.C (-(MvPolynomial.X other2TopRight *
          MvPolynomial.X other2BottomLeft)) := by
  rw [detPoly, Matrix.det_fin_two]
  simp [pivot2, other2TopLeft, other2TopRight, other2BottomLeft]
  ring

theorem detPoly_two_irreducible : Irreducible (detPoly 2) := by
  have hnotdiv : ¬(MvPolynomial.X other2TopLeft : MvPolynomial Other2 ℝ) ∣
      -(MvPolynomial.X other2TopRight * MvPolynomial.X other2BottomLeft) := by
    simp only [dvd_neg, MvPolynomial.X_dvd_mul_iff, MvPolynomial.X_dvd_X]
    decide
  have hrel : IsRelPrime
      (MvPolynomial.X other2TopLeft : MvPolynomial Other2 ℝ)
      (-(MvPolynomial.X other2TopRight * MvPolynomial.X other2BottomLeft)) :=
    MvPolynomial.prime_X.irreducible.isRelPrime_iff_not_dvd.mpr hnotdiv
  have hnested : Irreducible (toNested (R := ℝ) pivot2 (detPoly 2)) := by
    rw [detPoly_two_nested]
    exact Polynomial.irreducible_C_mul_X_add_C
      (MvPolynomial.X_ne_zero other2TopLeft) hrel
  exact (MulEquiv.irreducible_iff
    (toNested (R := ℝ) pivot2).toMulEquiv).mp hnested

section GenericInduction

variable {K : Type*} [Field K]

/-- The generic determinant over an arbitrary field. -/
@[expose] def genericDetPoly (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) K :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) K)

@[simp] lemma genericDetPoly_real (n : ℕ) :
    genericDetPoly ℝ n = detPoly n := rfl

/-- The distinguished upper-left entry of a square matrix. -/
abbrev pivotZero (n : ℕ) : Fin (n + 1) × Fin (n + 1) :=
  ((0 : Fin (n + 1)), (0 : Fin (n + 1)))

/-- All square-matrix entries except the distinguished determinant pivot. -/
abbrev DetCoeffVar (n : ℕ) := Free (pivotZero n)

/-- Embed the variables of the lower-right block into the pivot coefficient variables. -/
@[expose] def lowerVarEmbedding (n : ℕ) :
    (Fin n × Fin n) ↪ DetCoeffVar n where
  toFun ij := ⟨(ij.1.succ, ij.2.succ), by
    intro h
    have hfst := congrArg Prod.fst h
    simp at hfst⟩
  inj' := by
    intro x y h
    apply Prod.ext
    · apply Fin.ext
      simpa using congrArg (fun z : DetCoeffVar n => z.1.1.val) h
    · apply Fin.ext
      simpa using congrArg (fun z : DetCoeffVar n => z.1.2.val) h

/-- The determinant of the generic lower-right block in the pivot coefficient ring. -/
@[expose] def lowerDet (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  MvPolynomial.rename (lowerVarEmbedding n) (genericDetPoly K n)

/-- The generic matrix with its distinguished pivot set to zero. -/
def pivotBaseMatrix (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1))
      (MvPolynomial (DetCoeffVar n) K) :=
  fun i j => if h : (i, j) = pivotZero n then 0 else MvPolynomial.X ⟨(i, j), h⟩

/-- The coordinate vector selecting the distinguished pivot row. -/
def pivotDirection (K : Type*) [Field K] (n : ℕ) :
    Fin (n + 1) → MvPolynomial (DetCoeffVar n) K :=
  fun i => if i = 0 then 1 else 0

/-- The leading coefficient of the determinant in its distinguished entry. -/
@[expose] def detPivotLeading (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  Matrix.det ((pivotBaseMatrix K n).updateCol 0 (pivotDirection K n))

/-- The constant coefficient of the determinant in its distinguished entry. -/
@[expose] def detPivotRemainder (K : Type*) [Field K] (n : ℕ) :
    MvPolynomial (DetCoeffVar n) K :=
  Matrix.det (pivotBaseMatrix K n)

lemma genericDetPoly_pivot_nested (n : ℕ) :
    toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1)) =
      Polynomial.C (detPivotLeading K n) * Polynomial.X +
        Polynomial.C (detPivotRemainder K n) := by
  classical
  let M := pivotBaseMatrix K n
  let u : Fin (n + 1) → MvPolynomial (DetCoeffVar n) K := fun i => M i 0
  let v := pivotDirection K n
  have hmatrix :
      (toNested (R := K) (pivotZero n)).toRingHom.mapMatrix
          (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) K) =
        (M.map Polynomial.C).updateCol 0 (affineColumn u v) := by
    apply Matrix.ext
    intro i j
    simp only [RingHom.mapMatrix_apply]
    by_cases hj : j = 0
    · subst j
      by_cases hi : i = 0
      · subst i
        simp [M, u, v, pivotBaseMatrix, pivotDirection, affineColumn]
      · have hne : (i, (0 : Fin (n + 1))) ≠ pivotZero n := by
          intro h
          exact hi (congrArg Prod.fst h)
        simp [M, u, v, pivotBaseMatrix, pivotDirection, affineColumn, hi, hne]
    · have hne : (i, j) ≠ pivotZero n := by
        intro h
        exact hj (congrArg Prod.snd h)
      simp [M, u, v, pivotBaseMatrix, hj, hne]
  calc
    toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1)) =
        Matrix.det
          ((toNested (R := K) (pivotZero n)).toRingHom.mapMatrix
            (Matrix.mvPolynomialX (Fin (n + 1)) (Fin (n + 1)) K)) :=
      (toNested (R := K) (pivotZero n)).toRingHom.map_det _
    _ = Matrix.det ((M.map Polynomial.C).updateCol 0 (affineColumn u v)) := by
      rw [hmatrix]
    _ = Polynomial.C (Matrix.det (M.updateCol 0 u)) +
        Polynomial.C (Matrix.det (M.updateCol 0 v)) * Polynomial.X :=
      det_updateCol_affine M 0 u v
    _ = Polynomial.C (detPivotLeading K n) * Polynomial.X +
        Polynomial.C (detPivotRemainder K n) := by
      have hu : M.updateCol 0 u = M := by
        ext i j
        by_cases hj : j = 0 <;> simp [hj, u]
      simp [detPivotLeading, detPivotRemainder, M, v, hu, add_comm]

lemma detPivotLeading_eq_lowerDet (n : ℕ) :
    detPivotLeading K n = lowerDet K n := by
  classical
  rw [detPivotLeading, Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  simp only [Nat.succ_eq_add_one, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero,
    Matrix.updateCol_self, pivotDirection, ↓reduceIte, mul_one, Fin.succAbove_zero,
    one_mul, Fin.val_succ, Fin.succ_ne_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  have hmatrix :
      ((pivotBaseMatrix K n).updateCol 0 (pivotDirection K n)).submatrix
          Fin.succ Fin.succ =
        (MvPolynomial.rename (lowerVarEmbedding n)).mapMatrix
          (Matrix.mvPolynomialX (Fin n) (Fin n) K) := by
    apply Matrix.ext
    intro i j
    simp [pivotBaseMatrix, lowerVarEmbedding]
  rw [hmatrix]
  simp only [lowerDet, genericDetPoly]
  exact (MvPolynomial.rename (R := K) (lowerVarEmbedding n)).map_det _ |>.symm

lemma lowerDet_prime (n : ℕ) (hprime : Prime (genericDetPoly K n)) :
    Prime (lowerDet K n) := by
  classical
  let s : Set (DetCoeffVar n) := Set.range (lowerVarEmbedding n)
  let e : (Fin n × Fin n) ≃ s := Equiv.ofInjective (lowerVarEmbedding n)
    (lowerVarEmbedding n).injective
  have he : Prime
      (MvPolynomial.rename e (genericDetPoly K n) : MvPolynomial s K) :=
    (MulEquiv.prime_iff (MvPolynomial.renameEquiv K e).toMulEquiv).mpr hprime
  have hs : Prime
      (MvPolynomial.rename ((↑) : s → DetCoeffVar n)
        (MvPolynomial.rename e (genericDetPoly K n))) :=
    (MvPolynomial.prime_rename_iff (R := K) s).mpr he
  rw [lowerDet]
  convert hs using 1
  rw [MvPolynomial.rename_rename]
  apply congrArg (fun f => MvPolynomial.rename f (genericDetPoly K n))
  funext ij
  rfl

/-- Exchange the first two indices of a nontrivial finite alphabet. -/
def swapZeroOne {n : ℕ} (hn : 0 < n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap (0 : Fin (n + 1)) ⟨1, by omega⟩

/-- Specialize the pivot coefficient variables to a transposition matrix. -/
def swapCoeffAssignment {n : ℕ} (hn : 0 < n) : DetCoeffVar n → K :=
  fun q => (swapZeroOne hn).permMatrix K q.1.1 q.1.2

lemma eval_lowerDet_swap_eq_zero {n : ℕ} (hn : 0 < n) :
    MvPolynomial.eval (swapCoeffAssignment (K := K) hn) (lowerDet K n) = 0 := by
  rw [lowerDet, MvPolynomial.eval_rename]
  rw [genericDetPoly, Matrix.eval_det_mvPolynomialX (Fin n) K]
  let i0 : Fin n := ⟨0, hn⟩
  apply Matrix.det_eq_zero_of_row_eq_zero i0
  intro j
  simp only [lowerVarEmbedding, ne_eq, Function.Embedding.coeFn_mk, Function.comp_apply,
    swapCoeffAssignment, Equiv.Perm.permMatrix, swapZeroOne, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Matrix.of_apply, Fin.succ_mk,
    zero_add, Equiv.swap_apply_right, ite_eq_right_iff, one_ne_zero, imp_false, i0]
  exact (Fin.succ_ne_zero j).symm

lemma eval_detPivotRemainder_swap_eq_neg_one {n : ℕ} (hn : 0 < n) :
    MvPolynomial.eval (swapCoeffAssignment (K := K) hn)
      (detPivotRemainder K n) = -1 := by
  let y := swapCoeffAssignment (K := K) hn
  have hcoeff :
      (toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1))).coeff 0 =
        detPivotRemainder K n := by
    rw [genericDetPoly_pivot_nested]
    simp
  have heval := toNested_map_eval (R := K) (pivotZero n)
    (genericDetPoly K (n + 1)) 0 y
  rw [← Polynomial.coeff_zero_eq_eval_zero] at heval
  rw [Polynomial.coeff_map, hcoeff] at heval
  have hinsert : insertDistinguished (pivotZero n) 0 y =
      fun ij => (swapZeroOne hn).permMatrix K ij.1 ij.2 := by
    funext ij
    by_cases h : ij = pivotZero n
    · subst ij
      simp [insertDistinguished, swapZeroOne, Equiv.Perm.permMatrix,
        Equiv.toPEquiv_apply]
    · simp [insertDistinguished, y, swapCoeffAssignment, h]
  rw [hinsert, genericDetPoly, Matrix.eval_det_mvPolynomialX (Fin (n + 1)) K] at heval
  change (MvPolynomial.eval y) (detPivotRemainder K n) =
    Matrix.det ((swapZeroOne hn).permMatrix K) at heval
  rw [Matrix.det_permutation] at heval
  dsimp [swapZeroOne] at heval
  rw [Equiv.Perm.sign_swap] at heval
  · simpa [y] using heval
  · intro h
    have hv := congrArg Fin.val h
    simp at hv

lemma detPivotLeading_not_dvd_remainder {n : ℕ} (hn : 0 < n) :
    ¬detPivotLeading K n ∣ detPivotRemainder K n := by
  intro hdvd
  have hmap := map_dvd (MvPolynomial.eval (swapCoeffAssignment (K := K) hn)) hdvd
  rw [detPivotLeading_eq_lowerDet, eval_lowerDet_swap_eq_zero hn,
    eval_detPivotRemainder_swap_eq_neg_one hn] at hmap
  simp only [zero_dvd_iff, neg_eq_zero, one_ne_zero] at hmap

/-- The generic determinant is irreducible over every field. -/
theorem genericDetPoly_irreducible (n : ℕ) (hn : 0 < n) :
    Irreducible (genericDetPoly K n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      by_cases hm : m = 0
      · subst m
        rw [genericDetPoly, Matrix.det_fin_one]
        exact MvPolynomial.prime_X.irreducible
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hsmallIrr : Irreducible (genericDetPoly K m) := ih m (by omega) hmpos
        have hsmallPrime : Prime (genericDetPoly K m) :=
          UniqueFactorizationMonoid.irreducible_iff_prime.mp hsmallIrr
        have hleadPrime : Prime (detPivotLeading K m) := by
          rw [detPivotLeading_eq_lowerDet]
          exact lowerDet_prime m hsmallPrime
        have hrel : IsRelPrime (detPivotLeading K m) (detPivotRemainder K m) :=
          hleadPrime.irreducible.isRelPrime_iff_not_dvd.mpr
            (detPivotLeading_not_dvd_remainder hmpos)
        have hnested : Irreducible
            (toNested (R := K) (pivotZero m) (genericDetPoly K (m + 1))) := by
          rw [genericDetPoly_pivot_nested]
          exact Polynomial.irreducible_C_mul_X_add_C hleadPrime.ne_zero hrel
        exact (MulEquiv.irreducible_iff
          (toNested (R := K) (pivotZero m)).toMulEquiv).mp hnested

theorem detPoly_irreducible {n : ℕ} (hn : 0 < n) :
    Irreducible (detPoly n) := by
  exact genericDetPoly_irreducible (K := ℝ) n hn

/-- In pivot coordinates, the generic determinant is primitive over the ring
of the remaining variables. -/
theorem genericDetPoly_pivot_isPrimitive {n : ℕ} (hn : 0 < n) :
    (toNested (R := K) (pivotZero n)
      (genericDetPoly K (n + 1))).IsPrimitive := by
  have hsmallIrr : Irreducible (genericDetPoly K n) :=
    genericDetPoly_irreducible (K := K) n hn
  have hsmallPrime : Prime (genericDetPoly K n) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hsmallIrr
  have hleadPrime : Prime (detPivotLeading K n) := by
    rw [detPivotLeading_eq_lowerDet]
    exact lowerDet_prime n hsmallPrime
  have hirrFull : Irreducible (genericDetPoly K (n + 1)) :=
    genericDetPoly_irreducible (K := K) (n + 1) (by omega)
  have hirrNested : Irreducible
      (toNested (R := K) (pivotZero n) (genericDetPoly K (n + 1))) :=
    (MulEquiv.irreducible_iff
      (toNested (R := K) (pivotZero n)).toMulEquiv).mpr hirrFull
  apply hirrNested.isPrimitive
  rw [genericDetPoly_pivot_nested,
    Polynomial.natDegree_linear hleadPrime.ne_zero]
  norm_num

/-- The square of the pivot-coordinate determinant is primitive as well. -/
theorem genericDetPoly_pivot_sq_isPrimitive {n : ℕ} (hn : 0 < n) :
    (toNested (R := K) (pivotZero n)
      (genericDetPoly K (n + 1)) ^ 2).IsPrimitive := by
  let : NormalizedGCDMonoid (MvPolynomial (DetCoeffVar n) K) :=
    Nonempty.some inferInstance
  have hp := genericDetPoly_pivot_isPrimitive (K := K) hn
  simpa [pow_two] using hp.mul hp

end GenericInduction

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
