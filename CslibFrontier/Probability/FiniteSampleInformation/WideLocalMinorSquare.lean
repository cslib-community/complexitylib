/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WideSchurCoordinates

/-!
# Local Schur translation and double-contact square membership

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideLocalMinorSquare.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace WidePolynomial

variable {k r : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Translation

variable {A σ : Type*} [CommRing A]

/-- The polynomial substitution translating each variable by a fixed scalar. -/
def mvTranslateHom (rho : σ → A) :
    MvPolynomial σ A →+* MvPolynomial σ A :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => MvPolynomial.X i + MvPolynomial.C (rho i))

@[simp]
lemma mvTranslateHom_C (rho : σ → A) (a : A) :
    mvTranslateHom rho (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [mvTranslateHom]

@[simp]
lemma mvTranslateHom_X (rho : σ → A) (i : σ) :
    mvTranslateHom rho (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (rho i) := by
  simp [mvTranslateHom]

lemma mvTranslateHom_neg_leftInverse (rho : σ → A) :
    Function.LeftInverse (mvTranslateHom (-rho)) (mvTranslateHom rho) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, mvTranslateHom_X, map_add, mvTranslateHom_C,
        hP, Pi.neg_apply]
      rw [map_neg]
      ring

/-- Translation `X i ↦ X i + rho i` as a ring automorphism. -/
def mvTranslateEquiv (rho : σ → A) :
    MvPolynomial σ A ≃+* MvPolynomial σ A where
  toFun := mvTranslateHom rho
  invFun := mvTranslateHom (-rho)
  left_inv := mvTranslateHom_neg_leftInverse rho
  right_inv := by
    intro P
    simpa only [neg_neg] using mvTranslateHom_neg_leftInverse (-rho) P
  map_add' := map_add _
  map_mul' := map_mul _

lemma eval_mvTranslateEquiv (rho x : σ → A) (P : MvPolynomial σ A) :
    MvPolynomial.eval x (mvTranslateEquiv rho P) =
      MvPolynomial.eval (x + rho) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [mvTranslateEquiv]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      change MvPolynomial.eval x (mvTranslateHom rho P) =
        MvPolynomial.eval (x + rho) P at hP
      simp [mvTranslateEquiv, hP, Pi.add_apply]

lemma constantCoeff_mvTranslateEquiv (rho : σ → A)
    (P : MvPolynomial σ A) :
    MvPolynomial.constantCoeff (mvTranslateEquiv rho P) =
      MvPolynomial.eval rho P := by
  rw [← MvPolynomial.eval_zero]
  simpa using eval_mvTranslateEquiv rho (0 : σ → A) P

lemma pderiv_mvTranslateEquiv (rho : σ → A) (i : σ)
    (P : MvPolynomial σ A) :
    MvPolynomial.pderiv i (mvTranslateEquiv rho P) =
      mvTranslateEquiv rho (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [mvTranslateEquiv]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      change MvPolynomial.pderiv i (mvTranslateHom rho P) =
        mvTranslateHom rho (MvPolynomial.pderiv i P) at hP
      by_cases hji : j = i
      · subst j
        simp [mvTranslateEquiv, hP]
      · simp [mvTranslateEquiv,
          MvPolynomial.pderiv_X_of_ne hji, hP]

lemma constantCoeff_pderiv_eq_coeff_single (i : σ)
    (P : MvPolynomial σ A) :
    MvPolynomial.constantCoeff (MvPolynomial.pderiv i P) =
      (P.coeff (Finsupp.single i 1)) := by
  classical
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv]
  simp

lemma coeff_single_mvTranslateEquiv (rho : σ → A) (i : σ)
    (P : MvPolynomial σ A) :
    ((mvTranslateEquiv rho P).coeff (Finsupp.single i 1)) =
      MvPolynomial.eval rho (MvPolynomial.pderiv i P) := by
  rw [← constantCoeff_pderiv_eq_coeff_single]
  rw [pderiv_mvTranslateEquiv, constantCoeff_mvTranslateEquiv]

end Translation

section CoordinateIdeal

variable {A σ : Type*} [CommRing A]

theorem mem_coordinateIdeal_sq_iff (P : MvPolynomial σ A) :
    P ∈ MvPolynomial.idealOfVars σ A ^ 2 ↔
      MvPolynomial.constantCoeff P = 0 ∧
      ∀ i, (P.coeff (Finsupp.single i 1)) = 0 := by
  rw [MvPolynomial.mem_pow_idealOfVars_iff']
  constructor
  · intro h
    constructor
    · rw [MvPolynomial.constantCoeff_eq]
      exact h 0 (by simp [Finsupp.degree])
    · intro i
      exact h (Finsupp.single i 1) (by simp only [Finsupp.degree_single]; decide)
  · rintro ⟨hzero, hone⟩ x hx
    have hdegree : Finsupp.degree x = 0 ∨ Finsupp.degree x = 1 := by omega
    rcases hdegree with hdegree | hdegree
    · have hxzero : x = 0 := (Finsupp.degree_eq_zero_iff x).mp hdegree
      subst x
      simpa [MvPolynomial.constantCoeff_eq] using hzero
    · obtain ⟨i, rfl⟩ := (Finsupp.sum_eq_one_iff x).mp hdegree
      exact hone i

end CoordinateIdeal

/-! ## Base polynomials and the localized graph coordinate -/

/-- The generic pivot block in the base-coordinate polynomial ring. -/
def schurABaseMatrix (k r : ℕ) :
    Matrix (Fin k) (Fin k) (SchurBasePoly k r) :=
  fun i j => MvPolynomial.X (Sum.inl (i, j))

/-- The pivot-block determinant in the base-coordinate polynomial ring. -/
def pivotMinorBase (k r : ℕ) : SchurBasePoly k r :=
  Matrix.det (schurABaseMatrix k r)

/-- A top-right column expressed in the base-coordinate polynomial ring. -/
def schurBBaseColumn (k r : ℕ) (β : Fin r) :
    Matrix (Fin k) (Fin 1) (SchurBasePoly k r) :=
  fun i _ => MvPolynomial.X (Sum.inr (Sum.inl (i, β)))

/-- The bottom-left row expressed in the base-coordinate polynomial ring. -/
def schurCBaseRow (k r : ℕ) :
    Matrix (Fin 1) (Fin k) (SchurBasePoly k r) :=
  fun _ j => MvPolynomial.X (Sum.inr (Sum.inr j))

/-- The adjugate numerator for a missing bottom entry of the Schur chart. -/
def schurNumeratorBase (k r : ℕ) (β : Fin r) : SchurBasePoly k r :=
  (schurCBaseRow k r * (schurABaseMatrix k r).adjugate *
    schurBBaseColumn k r β) 0 0

@[simp]
lemma schurNestedEquiv_X_pivot (k r : ℕ) (i j : Fin k) :
    schurNestedEquiv k r
      (MvPolynomial.X (Fin.castSucc i, Fin.castAdd r j)) =
      MvPolynomial.C (MvPolynomial.X (Sum.inl (i, j))) := by
  simp [schurNestedEquiv, wideVarSchurEquiv]

@[simp]
lemma schurNestedEquiv_X_topFree (k r : ℕ) (i : Fin k) (β : Fin r) :
    schurNestedEquiv k r
      (MvPolynomial.X (Fin.castSucc i, Fin.natAdd k β)) =
      MvPolynomial.C
        (MvPolynomial.X (Sum.inr (Sum.inl (i, β)))) := by
  simp [schurNestedEquiv, wideVarSchurEquiv]

@[simp]
lemma schurNestedEquiv_X_bottomPivot (k r : ℕ) (j : Fin k) :
    schurNestedEquiv k r
      (MvPolynomial.X (Fin.last k, Fin.castAdd r j)) =
      MvPolynomial.C (MvPolynomial.X (Sum.inr (Sum.inr j))) := by
  simp [schurNestedEquiv, wideVarSchurEquiv]

@[simp]
lemma schurNestedEquiv_X_bottomFree (k r : ℕ) (β : Fin r) :
    schurNestedEquiv k r
      (MvPolynomial.X (Fin.last k, Fin.natAdd k β)) =
      MvPolynomial.X β := by
  simp [schurNestedEquiv, wideVarSchurEquiv]

lemma schurNestedEquiv_map_pivotBlock (k r : ℕ) :
    (pivotBlock
        (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)).map
      (schurNestedEquiv k r) =
        (schurABaseMatrix k r).map MvPolynomial.C := by
  ext i j
  simp [pivotBlock, Matrix.mvPolynomialX, pivotRow, pivotColumn,
    schurABaseMatrix]

lemma schurNestedEquiv_map_bottomRow (k r : ℕ) :
    (schurBottomRow
        (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)).map
      (schurNestedEquiv k r) =
        (schurCBaseRow k r).map MvPolynomial.C := by
  ext i j
  simp [schurBottomRow, Matrix.mvPolynomialX, schurLastRow, pivotColumn,
    schurCBaseRow]

lemma schurNestedEquiv_map_topColumn (k r : ℕ) (β : Fin r) :
    (schurTopColumn
        (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ) β).map
      (schurNestedEquiv k r) =
        (schurBBaseColumn k r β).map MvPolynomial.C := by
  ext i j
  simp [schurTopColumn, Matrix.mvPolynomialX, pivotRow, freeColumn,
    schurBBaseColumn]

lemma schurNestedEquiv_pivotMinor (k r : ℕ) :
    schurNestedEquiv k r (pivotMinor k r) =
      MvPolynomial.C (pivotMinorBase k r) := by
  rw [pivotMinor]
  rw [(schurNestedEquiv k r).map_det, pivotMinorBase,
    MvPolynomial.C.map_det]
  rw [RingEquiv.mapMatrix_apply, RingHom.mapMatrix_apply]
  exact congrArg Matrix.det (schurNestedEquiv_map_pivotBlock k r)

lemma schurNestedEquiv_schurMinor (k r : ℕ) (β : Fin r) :
    schurNestedEquiv k r (schurMinor k r β) =
      MvPolynomial.C (pivotMinorBase k r) * MvPolynomial.X β -
        MvPolynomial.C (schurNumeratorBase k r β) := by
  rw [schurMinor_eq_adjugateNumerator]
  simp only [schurAdjugateNumerator, map_sub, map_mul]
  rw [schurNestedEquiv_pivotMinor]
  congr 1
  · simp [schurBottomEntry, Matrix.mvPolynomialX, schurLastRow, freeColumn,
      schurNestedEquiv_X_bottomFree]
  · change ((schurBottomRow
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ) *
          (pivotBlock
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)).adjugate *
          schurTopColumn
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ) β).map
        (schurNestedEquiv k r)) 0 0 = _
    rw [Matrix.map_mul, Matrix.map_mul]
    have hadj :
        ((pivotBlock
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)).adjugate).map
            (schurNestedEquiv k r) =
          ((pivotBlock
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)).map
              (schurNestedEquiv k r)).adjugate := by
      apply Matrix.ext
      intro i j
      have h := congrArg (fun M => M i j)
        ((schurNestedEquiv k r).toRingHom.map_adjugate
          (pivotBlock
            (Matrix.mvPolynomialX (Fin (k + 1)) (Fin (k + r)) ℝ)))
      exact h
    rw [hadj]
    rw [schurNestedEquiv_map_bottomRow,
      schurNestedEquiv_map_pivotBlock,
      schurNestedEquiv_map_topColumn]
    have hCadj :=
      (MvPolynomial.C : SchurBasePoly k r →+*
        MvPolynomial (Fin r) (SchurBasePoly k r)).map_adjugate
          (schurABaseMatrix k r)
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at hCadj
    rw [← hCadj]
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    rfl

lemma eval_pivotMinorBase (y : SchurBaseVar k r → ℝ) :
    MvPolynomial.eval y (pivotMinorBase k r) = schurDelta y := by
  rw [pivotMinorBase, schurDelta]
  calc
    MvPolynomial.eval y (Matrix.det (schurABaseMatrix k r)) =
        Matrix.det ((schurABaseMatrix k r).map (MvPolynomial.eval y)) :=
      (MvPolynomial.eval y).map_det _
    _ = Matrix.det (schurA y) := by
      congr 1
      ext i j
      simp [schurABaseMatrix, schurA]

lemma eval_schurNumeratorBase (y : SchurBaseVar k r → ℝ) (β : Fin r) :
    MvPolynomial.eval y (schurNumeratorBase k r β) =
      (Matrix.of (fun (_ : Fin 1) j => schurC y j) *
        (schurA y).adjugate *
        Matrix.of (fun i (_ : Fin 1) => schurB y i β)) 0 0 := by
  let e : SchurBasePoly k r →+* ℝ := MvPolynomial.eval y
  change e (schurNumeratorBase k r β) = _
  simp only [schurNumeratorBase]
  change e ((schurCBaseRow k r * (schurABaseMatrix k r).adjugate *
    schurBBaseColumn k r β) 0 0) = _
  change ((schurCBaseRow k r * (schurABaseMatrix k r).adjugate *
    schurBBaseColumn k r β).map e) 0 0 = _
  rw [Matrix.map_mul, Matrix.map_mul]
  rw [show ((schurABaseMatrix k r).adjugate).map e =
      ((schurABaseMatrix k r).map e).adjugate by
    simpa only [RingHom.mapMatrix_apply] using e.map_adjugate (schurABaseMatrix k r)]
  have hC : (schurCBaseRow k r).map e =
      Matrix.of (fun (_ : Fin 1) j => schurC y j) := by
    ext i j
    simp [schurCBaseRow, schurC, e]
  have hA : (schurABaseMatrix k r).map e = schurA y := by
    ext i j
    simp [schurABaseMatrix, schurA, e]
  have hB : (schurBBaseColumn k r β).map e =
      Matrix.of (fun i (_ : Fin 1) => schurB y i β) := by
    ext i j
    simp [schurBBaseColumn, schurB, e]
  rw [hC, hA, hB]

lemma schurRho_eq_numerator_div_delta
    {y : SchurBaseVar k r → ℝ} (_hδ : schurDelta y ≠ 0) (β : Fin r) :
    schurRho y β =
      MvPolynomial.eval y (schurNumeratorBase k r β) /
        MvPolynomial.eval y (pivotMinorBase k r) := by
  rw [eval_pivotMinorBase, eval_schurNumeratorBase]
  rw [schurRho, schurLambda]
  rw [Matrix.inv_def]
  simp only [Ring.inverse_eq_inv']
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul, schurDelta]
  have hfactor :
      (∑ x, (∑ x_1, schurC y x_1 *
        ((schurA y).det⁻¹ * (schurA y).adjugate x_1 x)) * schurB y x β) =
      (schurA y).det⁻¹ *
        ∑ x, (∑ x_1, schurC y x_1 * (schurA y).adjugate x_1 x) *
          schurB y x β := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    calc
      (∑ x_1, schurC y x_1 *
          ((schurA y).det⁻¹ * (schurA y).adjugate x_1 x)) * schurB y x β =
          ((schurA y).det⁻¹ *
            ∑ x_1, schurC y x_1 * (schurA y).adjugate x_1 x) *
              schurB y x β := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x_1 hx_1
        ring
      _ = (schurA y).det⁻¹ *
          ((∑ x_1, schurC y x_1 * (schurA y).adjugate x_1 x) *
            schurB y x β) := by ring
  rw [hfactor]
  rw [div_eq_mul_inv]
  ring

/-- Localize the base-coordinate ring at the pivot determinant. -/
abbrev SchurLocalizedBase (k r : ℕ) := Localization.Away (pivotMinorBase k r)

/-- The Schur-complement root in the localized base ring. -/
def schurRhoLocalized (k r : ℕ) (β : Fin r) : SchurLocalizedBase k r :=
  algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
      (schurNumeratorBase k r β) *
    IsLocalization.Away.invSelf (pivotMinorBase k r)

/-- The nested polynomial after localizing its coefficient ring. -/
def localizedNested (k r : ℕ)
    (P : MvPolynomial (Fin r) (SchurBasePoly k r)) :
    MvPolynomial (Fin r) (SchurLocalizedBase k r) :=
  MvPolynomial.map (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)) P

/-- Translate the localized bottom-entry variables to their Schur roots. -/
def translatedLocalizedNested (k r : ℕ)
    (P : MvPolynomial (Fin r) (SchurBasePoly k r)) :
    MvPolynomial (Fin r) (SchurLocalizedBase k r) :=
  mvTranslateEquiv (schurRhoLocalized k r) (localizedNested k r P)

/-- The ideal of the localized equations for the bottom-entry Schur roots. -/
def schurShiftedIdeal (k r : ℕ) :
    Ideal (MvPolynomial (Fin r) (SchurLocalizedBase k r)) :=
  Ideal.map (mvTranslateEquiv (-(schurRhoLocalized k r))).toRingHom
    (MvPolynomial.idealOfVars (Fin r) (SchurLocalizedBase k r))

/-- The canonical localization map on the nested coordinate polynomial ring. -/
def schurLocalizeHom (k r : ℕ) :
    WidePoly (k + 1) (k + r) →+*
      MvPolynomial (Fin r) (SchurLocalizedBase k r) :=
  (MvPolynomial.map
    (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r))).comp
      (schurNestedEquiv k r).toRingHom

/-- The maximal-minor ideal after changing to localized nested coordinates. -/
def localizedMaximalMinorIdeal (k r : ℕ) :
    Ideal (MvPolynomial (Fin r) (SchurLocalizedBase k r)) :=
  Ideal.map (schurLocalizeHom k r) (maximalMinorIdeal (k + 1) (k + r))

/-- The maximal-minor ideal after changing to nested coordinates. -/
def nestedMaximalMinorIdeal (k r : ℕ) :
    Ideal (MvPolynomial (Fin r) (SchurBasePoly k r)) :=
  Ideal.map (schurNestedEquiv k r).toRingHom
    (maximalMinorIdeal (k + 1) (k + r))

lemma localizedMaximalMinorIdeal_eq_map (k r : ℕ) :
    localizedMaximalMinorIdeal k r =
      Ideal.map
        (algebraMap
          (MvPolynomial (Fin r) (SchurBasePoly k r))
          (MvPolynomial (Fin r) (SchurLocalizedBase k r)))
        (nestedMaximalMinorIdeal k r) := by
  rw [localizedMaximalMinorIdeal, nestedMaximalMinorIdeal, Ideal.map_map]
  rfl

/-- A Schur minor in the localized nested-coordinate ring. -/
def localizedSchurMinor (k r : ℕ) (β : Fin r) :
    MvPolynomial (Fin r) (SchurLocalizedBase k r) :=
  schurLocalizeHom k r (schurMinor k r β)

lemma localizedSchurMinor_eq (k r : ℕ) (β : Fin r) :
    localizedSchurMinor k r β =
      MvPolynomial.C
          (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
            (pivotMinorBase k r)) *
        (MvPolynomial.X β - MvPolynomial.C (schurRhoLocalized k r β)) := by
  have hcancel :
      algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
          (pivotMinorBase k r) * schurRhoLocalized k r β =
        algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
          (schurNumeratorBase k r β) := by
    rw [schurRhoLocalized]
    calc
      algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
            (pivotMinorBase k r) *
          (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
              (schurNumeratorBase k r β) *
            IsLocalization.Away.invSelf (pivotMinorBase k r)) =
          algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
              (schurNumeratorBase k r β) *
            (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)
                (pivotMinorBase k r) *
              IsLocalization.Away.invSelf (pivotMinorBase k r)) := by ring
      _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]
  rw [localizedSchurMinor, schurLocalizeHom,
    RingHom.comp_apply]
  change MvPolynomial.map
      (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r))
        (schurNestedEquiv k r (schurMinor k r β)) = _
  rw [schurNestedEquiv_schurMinor]
  simp only [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  rw [mul_sub, ← MvPolynomial.C_mul, hcancel]

lemma localizedSchurMinor_mem_localizedMaximalMinorIdeal
    (k r : ℕ) (β : Fin r) :
    localizedSchurMinor k r β ∈ localizedMaximalMinorIdeal k r := by
  exact Ideal.mem_map_of_mem (schurLocalizeHom k r)
    (schurMinor_mem_maximalMinorIdeal k r β)

lemma schurShiftedGenerator_mem_localizedMaximalMinorIdeal
    (k r : ℕ) (β : Fin r) :
    MvPolynomial.X β - MvPolynomial.C (schurRhoLocalized k r β) ∈
      localizedMaximalMinorIdeal k r := by
  have hminor := localizedSchurMinor_mem_localizedMaximalMinorIdeal k r β
  have hmul := (localizedMaximalMinorIdeal k r).mul_mem_left
    (MvPolynomial.C
      (IsLocalization.Away.invSelf (pivotMinorBase k r))) hminor
  rw [localizedSchurMinor_eq] at hmul
  rw [← mul_assoc, ← MvPolynomial.C_mul] at hmul
  rw [mul_comm (IsLocalization.Away.invSelf (pivotMinorBase k r)),
    IsLocalization.Away.mul_invSelf, MvPolynomial.C_1, one_mul] at hmul
  exact hmul

lemma schurShiftedIdeal_le_localizedMaximalMinorIdeal (k r : ℕ) :
    schurShiftedIdeal k r ≤ localizedMaximalMinorIdeal k r := by
  rw [schurShiftedIdeal, Ideal.map_le_iff_le_comap]
  rw [MvPolynomial.idealOfVars, Ideal.span_le]
  rintro Q ⟨β, rfl⟩
  change mvTranslateEquiv (-(schurRhoLocalized k r))
      (MvPolynomial.X β) ∈ localizedMaximalMinorIdeal k r
  simpa [mvTranslateEquiv, sub_eq_add_neg] using
    schurShiftedGenerator_mem_localizedMaximalMinorIdeal k r β

theorem exists_pivot_pow_mul_mem_maximalMinorIdeal_sq_of_localized
    {k r : ℕ} (H : WidePoly (k + 1) (k + r))
    (hlocal : schurLocalizeHom k r H ∈
      localizedMaximalMinorIdeal k r ^ 2) :
    ∃ N : ℕ, pivotMinor k r ^ N * H ∈
      maximalMinorIdeal (k + 1) (k + r) ^ 2 := by
  let e := schurNestedEquiv k r
  let I := maximalMinorIdeal (k + 1) (k + r)
  let J := nestedMaximalMinorIdeal k r
  have hlocal' :
      algebraMap
          (MvPolynomial (Fin r) (SchurBasePoly k r))
          (MvPolynomial (Fin r) (SchurLocalizedBase k r))
          (e H) ∈
        Ideal.map
          (algebraMap
            (MvPolynomial (Fin r) (SchurBasePoly k r))
            (MvPolynomial (Fin r) (SchurLocalizedBase k r)))
          (J ^ 2) := by
    change schurLocalizeHom k r H ∈ _
    rw [Ideal.map_pow, ← localizedMaximalMinorIdeal_eq_map]
    exact hlocal
  obtain ⟨s, hsM, hs⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff
      ((Submonoid.powers (pivotMinorBase k r)).map
        (MvPolynomial.C : SchurBasePoly k r →+*
          MvPolynomial (Fin r) (SchurBasePoly k r)))
      (S := MvPolynomial (Fin r) (SchurLocalizedBase k r))
      (J ^ 2) (e H)).mp hlocal'
  rcases hsM with ⟨d, hd, rfl⟩
  rcases (Submonoid.mem_powers_iff d (pivotMinorBase k r)).mp hd with
    ⟨N, rfl⟩
  have himage :
      e (pivotMinor k r ^ N * H) ∈ J ^ 2 := by
    rw [map_mul, map_pow, schurNestedEquiv_pivotMinor]
    simpa only [map_pow] using hs
  have hinv := Ideal.mem_map_of_mem e.symm himage
  rw [Ideal.map_pow] at hinv
  change e.symm (e (pivotMinor k r ^ N * H)) ∈
    (Ideal.map e.symm (Ideal.map e I)) ^ 2 at hinv
  rw [e.symm_apply_apply] at hinv
  have hmap : Ideal.map e.symm (Ideal.map e I) = I :=
    Ideal.map_of_equiv e
  rw [hmap] at hinv
  exact ⟨N, hinv⟩

/-- Evaluation on a chart point where the pivot determinant is nonzero. -/
def schurLocalizationEval (y : SchurBaseVar k r → ℝ)
    (hδ : MvPolynomial.eval y (pivotMinorBase k r) ≠ 0) :
    SchurLocalizedBase k r →+* ℝ :=
  IsLocalization.lift (S := SchurLocalizedBase k r)
    (g := MvPolynomial.eval y) (fun s => by
      obtain ⟨N, hN⟩ :=
        (Submonoid.mem_powers_iff s.1 (pivotMinorBase k r)).mp s.2
      rw [← hN, map_pow]
      exact (isUnit_iff_ne_zero.mpr (pow_ne_zero N hδ)))

lemma schurLocalizationEval_algebraMap
    (y : SchurBaseVar k r → ℝ)
    (hδ : MvPolynomial.eval y (pivotMinorBase k r) ≠ 0)
    (a : SchurBasePoly k r) :
    schurLocalizationEval y hδ
      (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r) a) =
      MvPolynomial.eval y a := by
  unfold schurLocalizationEval
  apply IsLocalization.lift_eq

lemma schurLocalizationEval_invSelf
    (y : SchurBaseVar k r → ℝ)
    (hδ : MvPolynomial.eval y (pivotMinorBase k r) ≠ 0) :
    schurLocalizationEval y hδ
      (IsLocalization.Away.invSelf (pivotMinorBase k r)) =
      (MvPolynomial.eval y (pivotMinorBase k r))⁻¹ := by
  have hmul := congrArg (schurLocalizationEval y hδ)
    (IsLocalization.Away.mul_invSelf (S := SchurLocalizedBase k r)
      (pivotMinorBase k r))
  rw [map_mul, schurLocalizationEval_algebraMap, map_one] at hmul
  apply (mul_left_cancel₀ hδ)
  rw [hmul]
  field_simp

lemma schurLocalizationEval_rho
    (y : SchurBaseVar k r → ℝ)
    (hδ : MvPolynomial.eval y (pivotMinorBase k r) ≠ 0) (β : Fin r) :
    schurLocalizationEval y hδ (schurRhoLocalized k r β) =
      schurRho y β := by
  rw [schurRhoLocalized, map_mul, schurLocalizationEval_algebraMap,
    schurLocalizationEval_invSelf]
  rw [schurRho_eq_numerator_div_delta
    (by rwa [eval_pivotMinorBase] at hδ) β]
  rw [div_eq_mul_inv]

lemma schurLocalizationEval_eval_localizedNested
    (Q : MvPolynomial (Fin r) (SchurBasePoly k r))
    (y : SchurBaseVar k r → ℝ)
    (hδ : MvPolynomial.eval y (pivotMinorBase k r) ≠ 0) :
    schurLocalizationEval y hδ
      (MvPolynomial.eval (schurRhoLocalized k r) (localizedNested k r Q)) =
    MvPolynomial.eval (schurRho y)
      (MvPolynomial.map (MvPolynomial.eval y) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [localizedNested, schurLocalizationEval_algebraMap]
  | add Q T hQ hT =>
      change schurLocalizationEval y hδ
          (MvPolynomial.eval (schurRhoLocalized k r)
            (MvPolynomial.map
              (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)) Q)) =
        MvPolynomial.eval (schurRho y)
          (MvPolynomial.map (MvPolynomial.eval y) Q) at hQ
      change schurLocalizationEval y hδ
          (MvPolynomial.eval (schurRhoLocalized k r)
            (MvPolynomial.map
              (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)) T)) =
        MvPolynomial.eval (schurRho y)
          (MvPolynomial.map (MvPolynomial.eval y) T) at hT
      change schurLocalizationEval y hδ
          (MvPolynomial.eval (schurRhoLocalized k r)
            (MvPolynomial.map
              (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)) (Q + T))) =
        MvPolynomial.eval (schurRho y)
          (MvPolynomial.map (MvPolynomial.eval y) (Q + T))
      simp only [map_add, hQ, hT]
  | mul_X Q β hQ =>
      change schurLocalizationEval y hδ
          (MvPolynomial.eval (schurRhoLocalized k r)
            (MvPolynomial.map
              (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r)) Q)) =
        MvPolynomial.eval (schurRho y)
          (MvPolynomial.map (MvPolynomial.eval y) Q) at hQ
      change schurLocalizationEval y hδ
          (MvPolynomial.eval (schurRhoLocalized k r)
            (MvPolynomial.map
              (algebraMap (SchurBasePoly k r) (SchurLocalizedBase k r))
                (Q * MvPolynomial.X β))) =
        MvPolynomial.eval (schurRho y)
          (MvPolynomial.map (MvPolynomial.eval y) (Q * MvPolynomial.X β))
      simp only [map_mul, MvPolynomial.map_X,
        MvPolynomial.eval_X, hQ, schurLocalizationEval_rho]

theorem schurLocalized_eq_zero_of_eval_zero_on_open_box
    (c : SchurLocalizedBase k r)
    (l u : SchurBaseVar k r → ℝ)
    (hlu : ∀ q, l q < u q)
    (hpivot : ∀ y : SchurBaseVar k r → ℝ,
      (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
      MvPolynomial.eval y (pivotMinorBase k r) ≠ 0)
    (hzero : ∀ y : SchurBaseVar k r → ℝ,
      (hy : ∀ q, y q ∈ Set.Ioo (l q) (u q)) →
      schurLocalizationEval y (hpivot y hy) c = 0) :
    c = 0 := by
  obtain ⟨a, s, hs⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (pivotMinorBase k r)) c
  have ha : a = 0 := by
    apply SquarePolynomial.mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box
      a l u hlu
    intro y hy
    have hc := hzero y hy
    rw [← hs] at hc
    have hspec := congrArg (schurLocalizationEval y (hpivot y hy))
      (IsLocalization.mk'_spec (SchurLocalizedBase k r) a s)
    rw [map_mul, hc, zero_mul,
      schurLocalizationEval_algebraMap] at hspec
    exact hspec.symm
  rw [← hs, ha]
  exact IsLocalization.mk'_zero s

/-- The tau-homogenized polynomial translated by the localized Schur roots. -/
def translatedTauHom (k r : ℕ) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r)) :
    MvPolynomial (Fin r) (SchurLocalizedBase k r) :=
  translatedLocalizedNested k r
    (schurNestedEquiv k r
      (tauHomogenizeWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) P))

theorem translatedTauHom_constantCoeff_eq_zero
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    MvPolynomial.constantCoeff (translatedTauHom k r hr P) = 0 := by
  obtain ⟨l, u, hlu, hbox⟩ :=
    exists_positive_schur_graph_open_box (k := k) (r := r) hk
  let hpivot : ∀ y : SchurBaseVar k r → ℝ,
      (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
      MvPolynomial.eval y (pivotMinorBase k r) ≠ 0 := by
    intro y hy
    have hδ := (hbox y hy).1
    rw [eval_pivotMinorBase]
    exact hδ
  apply schurLocalized_eq_zero_of_eval_zero_on_open_box _ l u hlu hpivot
  intro y hy
  obtain ⟨hδ, hpos, hlambda, hrow, hminor⟩ := hbox y hy
  rw [translatedTauHom, translatedLocalizedNested,
    constantCoeff_mvTranslateEquiv]
  rw [schurLocalizationEval_eval_localizedNested]
  rw [eval_schurNestedEquiv, assembleSchurMatrix_rho]
  exact tauHom_value_zero_on_positive_schur_graph
    hk hr P hDPI hRKO hδ hpos hlambda

theorem translatedTauHom_linearCoeff_eq_zero
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    (β : Fin r) :
    ((translatedTauHom k r hr P).coeff (Finsupp.single β 1)) = 0 := by
  obtain ⟨l, u, hlu, hbox⟩ :=
    exists_positive_schur_graph_open_box (k := k) (r := r) hk
  let hpivot : ∀ y : SchurBaseVar k r → ℝ,
      (∀ q, y q ∈ Set.Ioo (l q) (u q)) →
      MvPolynomial.eval y (pivotMinorBase k r) ≠ 0 := by
    intro y hy
    have hδ := (hbox y hy).1
    rw [eval_pivotMinorBase]
    exact hδ
  apply schurLocalized_eq_zero_of_eval_zero_on_open_box _ l u hlu hpivot
  intro y hy
  obtain ⟨hδ, hpos, hlambda, hrow, hminor⟩ := hbox y hy
  rw [translatedTauHom, translatedLocalizedNested,
    coeff_single_mvTranslateEquiv]
  rw [localizedNested, MvPolynomial.pderiv_map]
  change schurLocalizationEval y (hpivot y hy)
    (MvPolynomial.eval (schurRhoLocalized k r)
      (localizedNested k r
        (MvPolynomial.pderiv β
          (schurNestedEquiv k r
            (tauHomogenizeWide (by omega : 0 < k + 1)
              (by omega : 0 < k + r) P))))) = 0
  rw [schurLocalizationEval_eval_localizedNested]
  rw [pderiv_schurNestedEquiv_normal]
  rw [eval_schurNestedEquiv, assembleSchurMatrix_rho]
  exact tauHom_normal_derivative_zero_on_positive_schur_graph
    hk hr P hDPI hRKO hδ hpos hlambda β

theorem translatedTauHom_mem_coordinateIdeal_sq
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    translatedTauHom k r hr P ∈
      MvPolynomial.idealOfVars (Fin r) (SchurLocalizedBase k r) ^ 2 := by
  rw [mem_coordinateIdeal_sq_iff]
  exact ⟨translatedTauHom_constantCoeff_eq_zero hk hr P hDPI hRKO,
    translatedTauHom_linearCoeff_eq_zero hk hr P hDPI hRKO⟩

lemma mem_schurShiftedIdeal_sq_of_translate_mem
    {k r : ℕ} {Q : MvPolynomial (Fin r) (SchurLocalizedBase k r)}
    (hQ : mvTranslateEquiv (schurRhoLocalized k r) Q ∈
      MvPolynomial.idealOfVars (Fin r) (SchurLocalizedBase k r) ^ 2) :
    Q ∈ schurShiftedIdeal k r ^ 2 := by
  have hmap := Ideal.mem_map_of_mem
    (mvTranslateEquiv (-(schurRhoLocalized k r))).toRingHom hQ
  rw [Ideal.map_pow] at hmap
  change mvTranslateHom (-(schurRhoLocalized k r))
      (mvTranslateHom (schurRhoLocalized k r) Q) ∈ _ at hmap
  rw [mvTranslateHom_neg_leftInverse (schurRhoLocalized k r) Q] at hmap
  exact hmap

theorem localizedTauHom_mem_schurShiftedIdeal_sq
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    localizedNested k r
      (schurNestedEquiv k r
        (tauHomogenizeWide (by omega : 0 < k + 1)
          (by omega : 0 < k + r) P)) ∈
      schurShiftedIdeal k r ^ 2 := by
  apply mem_schurShiftedIdeal_sq_of_translate_mem
  exact translatedTauHom_mem_coordinateIdeal_sq hk hr P hDPI hRKO

theorem localizedTauHom_mem_localizedMaximalMinorIdeal_sq
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    schurLocalizeHom k r
        (tauHomogenizeWide (by omega : 0 < k + 1)
          (by omega : 0 < k + r) P) ∈
      localizedMaximalMinorIdeal k r ^ 2 := by
  apply Ideal.pow_right_mono
      (schurShiftedIdeal_le_localizedMaximalMinorIdeal k r) 2
  exact localizedTauHom_mem_schurShiftedIdeal_sq hk hr P hDPI hRKO

theorem exists_pivot_pow_mul_tauHomogenize_mem_maximalMinorIdeal_sq
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    ∃ N : ℕ,
      pivotMinor k r ^ N *
          tauHomogenizeWide (by omega : 0 < k + 1)
            (by omega : 0 < k + r) P ∈
        maximalMinorIdeal (k + 1) (k + r) ^ 2 := by
  apply exists_pivot_pow_mul_mem_maximalMinorIdeal_sq_of_localized
  exact localizedTauHom_mem_localizedMaximalMinorIdeal_sq
    hk hr P hDPI hRKO


end WidePolynomial

end

end Cslib.FiniteSampleInformation
