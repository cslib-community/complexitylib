/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WideLocalDoubleContact

/-!
# Splitting Schur base and normal variables

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideSchurCoordinates.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace WidePolynomial

variable {k r : ℕ}

/-- The variable equivalence with normal variables first and Schur-base
variables second. -/
@[expose] def wideVarSchurEquiv (k r : ℕ) :
    WideVar (k + 1) (k + r) ≃ Fin r ⊕ SchurBaseVar k r where
  toFun ia :=
    match finSumFinEquiv.symm ia.1, finSumFinEquiv.symm ia.2 with
    | Sum.inl i, Sum.inl j => Sum.inr (Sum.inl (i, j))
    | Sum.inl i, Sum.inr β => Sum.inr (Sum.inr (Sum.inl (i, β)))
    | Sum.inr _, Sum.inl j => Sum.inr (Sum.inr (Sum.inr j))
    | Sum.inr _, Sum.inr β => Sum.inl β
  invFun v :=
    match v with
    | Sum.inl β =>
        (finSumFinEquiv (Sum.inr (0 : Fin 1)), finSumFinEquiv (Sum.inr β))
    | Sum.inr (Sum.inl (i, j)) =>
        (finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inl j))
    | Sum.inr (Sum.inr (Sum.inl (i, β))) =>
        (finSumFinEquiv (Sum.inl i), finSumFinEquiv (Sum.inr β))
    | Sum.inr (Sum.inr (Sum.inr j)) =>
        (finSumFinEquiv (Sum.inr (0 : Fin 1)), finSumFinEquiv (Sum.inl j))
  left_inv ia := by
    rcases ia with ⟨i, a⟩
    generalize hri : finSumFinEquiv.symm i = ri
    generalize hca : finSumFinEquiv.symm a = ca
    have hi : i = finSumFinEquiv ri := by
      rw [← finSumFinEquiv.apply_symm_apply i, hri]
    have ha : a = finSumFinEquiv ca := by
      rw [← finSumFinEquiv.apply_symm_apply a, hca]
    subst i
    subst a
    cases ri with
    | inl i =>
        cases ca <;> simp
    | inr q =>
        fin_cases q
        cases ca <;> simp
  right_inv v := by
    rcases v with β | b
    · simp
    · rcases b with a | bc
      · rcases a with ⟨i, j⟩
        simp
      · rcases bc with b | c
        · rcases b with ⟨i, β⟩
          simp
        · simp

/-- Polynomials in the non-Schur coordinates of the rectangular chart. -/
abbrev SchurBasePoly (k r : ℕ) := MvPolynomial (SchurBaseVar k r) ℝ

/-- The wide polynomial ring as a polynomial ring in the normal coordinates
with Schur-base polynomial coefficients. -/
@[expose] def schurNestedEquiv (k r : ℕ) :
    WidePoly (k + 1) (k + r) ≃+*
      MvPolynomial (Fin r) (SchurBasePoly k r) :=
  (MvPolynomial.renameEquiv ℝ (wideVarSchurEquiv k r)).toRingEquiv.trans
    (MvPolynomial.sumRingEquiv ℝ (Fin r) (SchurBaseVar k r))

/-- Assemble a rectangular matrix from base coordinates and its free bottom entries. -/
def assembleSchurMatrix {k r : ℕ}
    (y : SchurBaseVar k r → ℝ) (d : Fin r → ℝ) :
    GeneralAsymmetricC1.Mat (k + 1) (k + r) :=
  fun i a =>
    match finSumFinEquiv.symm i, finSumFinEquiv.symm a with
    | Sum.inl i', Sum.inl j => schurA y i' j
    | Sum.inl i', Sum.inr β => schurB y i' β
    | Sum.inr _, Sum.inl j => schurC y j
    | Sum.inr _, Sum.inr β => d β

lemma assembleSchurMatrix_rho (y : SchurBaseVar k r → ℝ) :
    assembleSchurMatrix y (schurRho y) = positiveSchurGraph y := by
  rfl

lemma eval_schurNestedEquiv (P : WidePoly (k + 1) (k + r))
    (y : SchurBaseVar k r → ℝ) (d : Fin r → ℝ) :
    MvPolynomial.eval d
      (MvPolynomial.map (MvPolynomial.eval y) (schurNestedEquiv k r P)) =
      peval P (assembleSchurMatrix y d) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [schurNestedEquiv, peval]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ, peval]
  | mul_X P ia hP =>
      rw [map_mul, map_mul, MvPolynomial.eval_mul, hP]
      rw [show peval (P * MvPolynomial.X ia) (assembleSchurMatrix y d) =
          peval P (assembleSchurMatrix y d) *
            assembleSchurMatrix y d ia.1 ia.2 by simp [peval]]
      congr 1
      rw [← (wideVarSchurEquiv k r).symm_apply_apply ia]
      cases h : wideVarSchurEquiv k r ia with
      | inl β =>
          simp [schurNestedEquiv, wideVarSchurEquiv, assembleSchurMatrix]
      | inr b =>
          rcases b with a | bc
          · rcases a with ⟨i, j⟩
            simp [schurNestedEquiv, wideVarSchurEquiv, assembleSchurMatrix,
              schurA]
          · rcases bc with b | c
            · rcases b with ⟨i, β⟩
              simp [schurNestedEquiv, wideVarSchurEquiv, assembleSchurMatrix,
                schurB]
            · simp [schurNestedEquiv, wideVarSchurEquiv,
                assembleSchurMatrix, schurC]

lemma pderiv_schurNestedEquiv_normal
    (P : WidePoly (k + 1) (k + r)) (β : Fin r) :
    MvPolynomial.pderiv β (schurNestedEquiv k r P) =
      schurNestedEquiv k r
        (MvPolynomial.pderiv (Fin.last k, Fin.natAdd k β) P) := by
  let e := wideVarSchurEquiv k r
  let v : WideVar (k + 1) (k + r) := (Fin.last k, Fin.natAdd k β)
  have hev : e v = Sum.inl β := by
    simp [e, v, wideVarSchurEquiv]
  have hrename := MvPolynomial.pderiv_rename e.injective v P
  rw [hev] at hrename
  change MvPolynomial.pderiv β
      (MvPolynomial.sumRingEquiv ℝ (Fin r) (SchurBaseVar k r)
        (MvPolynomial.rename e P)) =
    MvPolynomial.sumRingEquiv ℝ (Fin r) (SchurBaseVar k r)
      (MvPolynomial.rename e
        (MvPolynomial.pderiv (Fin.last k, Fin.natAdd k β) P))
  rw [MvPolynomial.pderiv_sumRingEquiv]
  exact congrArg (MvPolynomial.sumRingEquiv ℝ (Fin r) (SchurBaseVar k r)) hrename

end WidePolynomial

end

end Cslib.FiniteSampleInformation
