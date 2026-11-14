/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.WideSquarePullback

/-!
# Wide row-cone vanishing and homogeneous cone contact

The analytic wide row-cone statement is reduced to the compiled square
determinant theorem.  The factorization `U = V * B` uses normalized leading
rows in the row-stochastic matrix `B`; the last column of `V` is zero, so `V`
is singular.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideTauHomConeContact.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators Topology
open Set

namespace WidePolynomial

open GeneralAsymmetricC1

/-- The total mass in a leading row, before normalization. -/
def leadingRowMass {k m : ℕ} (U : Mat (k + 1) m) (i : Fin k) : ℝ :=
  ∑ a, U i.castSucc a

lemma leadingRowMass_pos {k m : ℕ} (hm : 0 < m)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a) (i : Fin k) :
    0 < leadingRowMass U i := by
  let a0 : Fin m := ⟨0, hm⟩
  exact Finset.sum_pos' (fun a _ => (hpos i.castSucc a).le)
    ⟨a0, Finset.mem_univ _, hpos i.castSucc a0⟩

/-- Normalize the leading rows and append a uniform row. -/
def rowConeB {k m : ℕ} (_hm : 0 < m) (U : Mat (k + 1) m) :
    Mat (k + 1) m :=
  fun i => Fin.lastCases
    (fun _ => (m : ℝ)⁻¹)
    (fun j a => (leadingRowMass U j)⁻¹ * U j.castSucc a)
    i

/-- The square stochastic factor obtained from the row-cone coefficients. -/
def rowConeSquare {k m : ℕ} (U : Mat (k + 1) m)
    (lambda : Fin k → ℝ) : Mat (k + 1) (k + 1) :=
  fun i => Fin.lastCases
    (fun j => Fin.lastCases 0
      (fun j' => lambda j' * leadingRowMass U j') j)
    (fun i' j => Fin.lastCases 0
      (fun j' => if i' = j' then leadingRowMass U i' else 0) j)
    i

lemma rowConeB_rowStochastic {k m : ℕ} (hm : 0 < m)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a) :
    RowStochastic (rowConeB hm U) := by
  constructor
  · intro i a
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [rowConeB, Fin.lastCases_last]
      exact inv_nonneg.mpr (show 0 ≤ (m : ℝ) from Nat.cast_nonneg m)
    · simp only [rowConeB, Fin.lastCases_castSucc]
      exact mul_nonneg (inv_nonneg.mpr (leadingRowMass_pos hm hpos j).le)
        (hpos j.castSucc a).le
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [rowConeB, hm.ne']
    · simp only [rowConeB, Fin.lastCases_castSucc]
      rw [← Finset.mul_sum]
      exact inv_mul_cancel₀ (leadingRowMass_pos hm hpos j).ne'

lemma rowConeSquare_nonnegative {k m : ℕ}
    {U : Mat (k + 1) m} (hU : Nonnegative U)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i) :
    Nonnegative (rowConeSquare U lambda) := by
  intro i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [rowConeSquare]
    · simp only [rowConeSquare, Fin.lastCases_last,
        Fin.lastCases_castSucc]
      exact mul_nonneg (hlambda j')
        (Finset.sum_nonneg fun a _ => hU j'.castSucc a)
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [rowConeSquare]
    · by_cases hij : i' = j'
      · subst j'
        simp only [rowConeSquare, Fin.lastCases_castSucc, ite_eq_left]
        exact Finset.sum_nonneg fun a _ => hU i'.castSucc a
      · simp [rowConeSquare, hij]

lemma rowConeSquare_mul_B {k m : ℕ} (hm : 0 < m)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ}
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    rowConeSquare U lambda * rowConeB hm U = U := by
  ext i a
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · rw [mat_mul_apply, Fin.sum_univ_castSucc]
    simp only [rowConeSquare, rowConeB, Fin.lastCases_last,
      Fin.lastCases_castSucc, zero_mul, add_zero]
    calc
      (∑ j : Fin k,
          lambda j * leadingRowMass U j *
            ((leadingRowMass U j)⁻¹ * U j.castSucc a)) =
          ∑ j : Fin k, lambda j * U j.castSucc a := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_assoc, ← mul_assoc (leadingRowMass U j),
          mul_inv_cancel₀ (leadingRowMass_pos hm hpos j).ne', one_mul]
      _ = U (Fin.last k) a := (hrow a).symm
  · rw [mat_mul_apply, Fin.sum_univ_castSucc]
    simp only [rowConeSquare, rowConeB, Fin.lastCases_castSucc,
      Fin.lastCases_last, zero_mul, add_zero]
    rw [Finset.sum_eq_single i']
    · rw [ite_eq_left rfl, ← mul_assoc, mul_inv_cancel₀
        (leadingRowMass_pos hm hpos i').ne', one_mul]
    · intro j hj hji
      simp [Ne.symm hji]
    · simp

lemma rowConeSquare_simplex {k m : ℕ} (hm : 0 < m)
    {U : Mat (k + 1) m} (hU : Simplex U)
    (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    Simplex (rowConeSquare U lambda) := by
  have hB := rowConeB_rowStochastic hm hpos
  have hmul := rowConeSquare_mul_B hm hpos hrow
  constructor
  · exact rowConeSquare_nonnegative hU.1 hlambda
  · have hmass := right_mul_mass (rowConeSquare U lambda) hB
    rw [hmul, hU.2] at hmass
    exact hmass.symm

lemma rowConeSquare_det_zero {k m : ℕ}
    (U : Mat (k + 1) m) (lambda : Fin k → ℝ) :
    Matrix.det (Matrix.of (rowConeSquare U lambda)) = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last k)
  intro i
  refine Fin.lastCases ?_ (fun i' => ?_) i <;>
    simp [rowConeSquare]

theorem wide_row_cone_vanishing {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m)
    (P : WidePoly (k + 1) m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat (k + 1) m} (hU : Simplex U)
    (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    peval P U = 0 := by
  let B : Mat (k + 1) m := rowConeB hm U
  let V : Mat (k + 1) (k + 1) := rowConeSquare U lambda
  let G : SquarePolynomial.Poly (k + 1) := rightPullbackPoly P B
  have hB : RowStochastic B := rowConeB_rowStochastic hm hpos
  have hV : Simplex V :=
    rowConeSquare_simplex hm hU hpos hlambda hrow
  have hVB : V * B = U := rowConeSquare_mul_B hm hpos hrow
  have hdet : Matrix.det (Matrix.of V) = 0 :=
    rowConeSquare_det_zero U lambda
  have hGDPI : SquarePolynomial.PolynomialDPI G :=
    rightPullback_polynomialDPI P hB hDPI
  have hGRKO : SquarePolynomial.PolynomialRKO G :=
    rightPullback_polynomialRKO P hB hRKO
  obtain ⟨Q, K, hfactor⟩ := SquarePolynomial.square_simplex_det_sq
    (by omega : 2 ≤ k + 1) G hGDPI hGRKO
  have hdetEval : MvPolynomial.eval (fun ia => V ia.1 ia.2)
      (SquarePolynomial.detPoly (k + 1)) = 0 := by
    change SquarePolynomial.peval (SquarePolynomial.detPoly (k + 1)) V = 0
    rw [SquarePolynomial.peval_detPoly, hdet]
  have htauEval : MvPolynomial.eval (fun ia => V ia.1 ia.2)
      (SquarePolynomial.tauPoly
        (SquarePolynomial.simplexStar (by omega : 2 ≤ k + 1))) = 1 := by
    change SquarePolynomial.peval
      (SquarePolynomial.tauPoly
        (SquarePolynomial.simplexStar (by omega : 2 ≤ k + 1))) V = 1
    rw [SquarePolynomial.peval_tauPoly_eq_mass, hV.2]
  have hGzero : SquarePolynomial.peval G V = 0 := by
    unfold SquarePolynomial.peval
    rw [hfactor]
    simp [hdetEval, htauEval]
  rw [peval_rightPullbackPoly, hVB] at hGzero
  exact hGzero

lemma mass_pos_of_entrywise_pos {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {U : Mat n m} (hpos : ∀ i a, 0 < U i a) :
    0 < mass U := by
  let i0 : Fin n := ⟨0, hn⟩
  let a0 : Fin m := ⟨0, hm⟩
  have hrows : ∀ i, 0 < ∑ a, U i a := by
    intro i
    exact Finset.sum_pos' (fun a _ => (hpos i a).le)
      ⟨a0, Finset.mem_univ _, hpos i a0⟩
  exact Finset.sum_pos' (fun i _ => (hrows i).le)
    ⟨i0, Finset.mem_univ _, hrows i0⟩

lemma inv_mass_smul_simplex_of_pos {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    {U : Mat n m} (hpos : ∀ i a, 0 < U i a) :
    Simplex ((mass U)⁻¹ • U) := by
  have hmass := mass_pos_of_entrywise_pos hn hm hpos
  constructor
  · intro i a
    exact mul_nonneg (inv_nonneg.mpr hmass.le) (hpos i a).le
  · rw [mass_smul, inv_mul_cancel₀ hmass.ne']

lemma peval_smul_of_isHomogeneous {n m d : ℕ}
    {P : WidePoly n m} (hP : P.IsHomogeneous d)
    (c : ℝ) (U : Mat n m) :
    peval P (c • U) = c ^ d * peval P U := by
  unfold peval
  simpa [Pi.smul_apply, smul_eq_mul] using
    SquarePolynomial.eval_smul_of_isHomogeneous hP c
      (fun ia => U ia.1 ia.2)

lemma tauHomogenizeWide_eval_eq_on_simplex {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : WidePoly n m)
    {U : Mat n m} (hU : Simplex U) :
    peval (tauHomogenizeWide hn hm P) U = peval P U := by
  apply SquarePolynomial.eval_tauHomogenize_of_eval_tau_eq_one
  change peval (tauPolyWide hn hm) U = 1
  rw [peval_tauPolyWide_eq_mass, hU.2]

theorem tauHom_nonnegative_on_positive_cone {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m)
    (P : WidePoly n m) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    {U : Mat n m} (hpos : ∀ i a, 0 < U i a) :
    0 ≤ peval (tauHomogenizeWide hn hm P) U := by
  let s : ℝ := mass U
  let Un : Mat n m := s⁻¹ • U
  have hs : 0 < s := mass_pos_of_entrywise_pos hn hm hpos
  have hUn : Simplex Un := inv_mass_smul_simplex_of_pos hn hm hpos
  have hPnonneg : 0 ≤ peval P Un :=
    nonneg_of_dpi_rko hDPI hRKO hUn ⟨0, hn⟩
  have hHnonneg : 0 ≤ peval (tauHomogenizeWide hn hm P) Un := by
    rw [tauHomogenizeWide_eval_eq_on_simplex hn hm P hUn]
    exact hPnonneg
  have hrecover : s • Un = U := by
    dsimp [Un]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hscale := peval_smul_of_isHomogeneous
    (tauHomogenizeWide_isHomogeneous hn hm P) s Un
  rw [hrecover] at hscale
  rw [hscale]
  exact mul_nonneg (pow_nonneg hs.le _) hHnonneg

theorem tauHom_positive_row_cone_zero {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m)
    (P : WidePoly (k + 1) m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    peval (tauHomogenizeWide (by omega : 0 < k + 1) hm P) U = 0 := by
  let s : ℝ := mass U
  let Un : Mat (k + 1) m := s⁻¹ • U
  have hs : 0 < s :=
    mass_pos_of_entrywise_pos (by omega : 0 < k + 1) hm hpos
  have hUn : Simplex Un :=
    inv_mass_smul_simplex_of_pos (by omega : 0 < k + 1) hm hpos
  have hposUn : ∀ i a, 0 < Un i a := by
    intro i a
    exact mul_pos (inv_pos.mpr hs) (hpos i a)
  have hrowUn : ∀ a, Un (Fin.last k) a =
      ∑ i : Fin k, lambda i * Un i.castSucc a := by
    intro a
    change s⁻¹ * U (Fin.last k) a =
      ∑ i : Fin k, lambda i * (s⁻¹ * U i.castSucc a)
    rw [hrow a, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hPzero : peval P Un = 0 :=
    wide_row_cone_vanishing hk hm P hDPI hRKO hUn hposUn hlambda hrowUn
  have hHzero :
      peval (tauHomogenizeWide (by omega : 0 < k + 1) hm P) Un = 0 := by
    rw [tauHomogenizeWide_eval_eq_on_simplex
      (by omega : 0 < k + 1) hm P hUn, hPzero]
  have hrecover : s • Un = U := by
    dsimp [Un]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have hscale := peval_smul_of_isHomogeneous
    (tauHomogenizeWide_isHomogeneous
      (by omega : 0 < k + 1) hm P) s Un
  rw [hrecover, hHzero, mul_zero] at hscale
  exact hscale

theorem tauHom_row_cone_isLocalMin {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m)
    (P : WidePoly (k + 1) m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    IsLocalMin (peval
      (tauHomogenizeWide (by omega : 0 < k + 1) hm P)) U := by
  have hzero := tauHom_positive_row_cone_zero hk hm P hDPI hRKO
    hpos hlambda hrow
  have heventually : ∀ᶠ V in 𝓝 U, ∀ i a, 0 < V i a := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro a
    exact continuousAt_const.eventually_lt
      (((continuous_apply a).comp (continuous_apply i)).continuousAt)
      (hpos i a)
  filter_upwards [heventually] with V hV
  rw [hzero]
  exact tauHom_nonnegative_on_positive_cone
    (by omega : 0 < k + 1) hm P hDPI hRKO hV

theorem tauHom_row_cone_all_directions_derivative_zero {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m)
    (P : WidePoly (k + 1) m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    fderiv ℝ (peval
      (tauHomogenizeWide (by omega : 0 < k + 1) hm P)) U = 0 :=
  (tauHom_row_cone_isLocalMin hk hm P hDPI hRKO
    hpos hlambda hrow).fderiv_eq_zero

/-- Restrict a multivariate polynomial to an affine coordinate line. -/
def unitLinePoly {n m : ℕ} (P : WidePoly n m)
    (U : Mat n m) (i : Fin n) (a : Fin m) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun ja => Polynomial.C (U ja.1 ja.2) +
      Polynomial.C (unit i a ja.1 ja.2) * Polynomial.X) P

lemma unitLinePoly_eval {n m : ℕ} (P : WidePoly n m)
    (U : Mat n m) (i : Fin n) (a : Fin m) (t : ℝ) :
    Polynomial.eval t (unitLinePoly P U i a) =
      peval P (U + t • unit i a) := by
  unfold unitLinePoly peval
  rw [MvPolynomial.polynomial_eval_eval₂]
  simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]
  apply MvPolynomial.eval₂Hom_congr
  · ext r
    simp
  · funext ja
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rfl

lemma unitLinePoly_derivative {n m : ℕ} (P : WidePoly n m)
    (U : Mat n m) (i : Fin n) (a : Fin m) :
    Polynomial.eval 0 (Polynomial.derivative (unitLinePoly P U i a)) =
      MvPolynomial.eval (fun ja => U ja.1 ja.2)
        (MvPolynomial.pderiv (i, a) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [unitLinePoly]
  | add P Q hP hQ =>
      rw [unitLinePoly, MvPolynomial.eval₂_add]
      change Polynomial.eval 0
          (Polynomial.derivative
            (unitLinePoly P U i a + unitLinePoly Q U i a)) = _
      rw [Polynomial.derivative_add, Polynomial.eval_add, map_add,
        MvPolynomial.eval_add, hP, hQ]
  | mul_X P ja hP =>
      rw [unitLinePoly, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_X, Polynomial.derivative_mul,
        Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul]
      rw [show MvPolynomial.eval₂ Polynomial.C
          (fun ja => Polynomial.C (U ja.1 ja.2) +
            Polynomial.C (unit i a ja.1 ja.2) * Polynomial.X) P =
          unitLinePoly P U i a by rfl]
      simp only [Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X,
        Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one,
        mul_zero, add_zero, hP]
      rw [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_X, MvPolynomial.eval_mul]
      rw [unitLinePoly_eval P U i a 0]
      simp only [peval, zero_smul, Pi.add_apply, Pi.zero_apply, add_zero,
      GeneralAsymmetricC1.unit, mul_one,
    zero_add, mul_ite, mul_zero, Pi.single_apply, MonoidWithZeroHom.map_ite_one_zero, add_right_inj]
      simp [Prod.ext_iff]

theorem tauHom_row_cone_all_partials_zero {k m : ℕ}
    (hk : 0 < k) (hm : 0 < m)
    (P : WidePoly (k + 1) m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    {U : Mat (k + 1) m} (hpos : ∀ i a, 0 < U i a)
    {lambda : Fin k → ℝ} (hlambda : ∀ i, 0 ≤ lambda i)
    (hrow : ∀ a, U (Fin.last k) a =
      ∑ i : Fin k, lambda i * U i.castSucc a) :
    ∀ i a,
      MvPolynomial.eval (fun ja => U ja.1 ja.2)
        (MvPolynomial.pderiv (i, a)
          (tauHomogenizeWide (by omega : 0 < k + 1) hm P)) = 0 := by
  let : NeZero (k + 1) := ⟨by omega⟩
  let : NeZero m := ⟨by omega⟩
  intro i a
  let H : WidePoly (k + 1) m :=
    tauHomogenizeWide (by omega : 0 < k + 1) hm P
  have hfderiv := tauHom_row_cone_all_directions_derivative_zero
    hk hm P hDPI hRKO hpos hlambda hrow
  change fderiv ℝ (peval H) U = 0 at hfderiv
  have hdAffine := GeneralAsymmetricC1.hasDerivAt_affine
    (U := U) (V := unit i a)
    ((peval_contDiff H).differentiable (by norm_num) U)
  rw [hfderiv] at hdAffine
  simp only [zero_apply] at hdAffine
  have hdPoly := Polynomial.hasDerivAt (unitLinePoly H U i a) 0
  have hline : (fun t : ℝ => Polynomial.eval t (unitLinePoly H U i a)) =
      fun t : ℝ => peval H (U + t • unit i a) := by
    funext t
    exact unitLinePoly_eval H U i a t
  rw [hline] at hdPoly
  rw [← unitLinePoly_derivative H U i a]
  exact hdPoly.unique hdAffine

end WidePolynomial


end

end Cslib.FiniteSampleInformation
