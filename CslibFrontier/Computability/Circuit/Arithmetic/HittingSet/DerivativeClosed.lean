/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ClosedWronskian
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Polynomials in a derivative-closed space do not vanish to high order on the logarithmic curve

Let `V` be a space of polynomials in `n` variables over a field of characteristic zero, closed
under every partial derivative and of finite dimension `r`. If the power series
`Pᵢ = ln (1 + (i + 1) t)` are algebraically independent, then for every nonzero `f` in `V` the
power series `f (P)` is not divisible by `t ^ (n r ^ 2 + r)`
(`not_X_pow_dvd_aeval_logSeries`). This is Theorem 4.1 of
[Bhardwaj et al.][BhardwajEtAl2026].

For a basis `g` of `V`, the series `gⱼ (P)` are linearly independent, so their Wronskian for
`δ = Q * d/dt` is nonzero. It is the image of the Wronskian of `g` for the derivation `D`, hence a
polynomial `w` of degree at most `n r ^ 2`. If `t ^ B` divides `f (P)` then `t ^ (B - r + 1)`
divides a whole column of a matrix whose determinant is a nonzero multiple of `w`, which is
impossible for `B = n r ^ 2 + r`.

## Main results

* `not_X_pow_dvd_aeval_logSeries`: the order of `f (P)` is less than `n r ^ 2 + r`.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026], Theorem 4.1
-/

public section

open scoped Polynomial PowerSeries

namespace Cslib.Circuits.Arithmetic

open Finset Matrix

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

variable (F n) in
/-- The derivation `δ = Q * d/dt` of power series. -/
private noncomputable def logDelta : Derivation F F⟦X⟧ F⟦X⟧ :=
  (logDenom F n : F⟦X⟧) • (PowerSeries.derivative : Derivation F F⟦X⟧ F⟦X⟧)

omit [CharZero F] in
private theorem logDelta_apply (h : F⟦X⟧) : logDelta F n h = (logDenom F n : F⟦X⟧) * d⁄dX h :=
  rfl

omit [CharZero F] in
private theorem coe_logDenom_ne_zero : (logDenom F n : F⟦X⟧) ≠ 0 := by
  rw [Ne, ← Polynomial.coe_zero, Polynomial.coe_inj, logDenom, prod_eq_zero_iff]
  rintro ⟨i, -, hi⟩
  simpa using congrArg (fun p : F[X] => p.coeff 0) hi

private theorem logDelta_const (a b : F⟦X⟧) (hb : b ≠ 0)
    (h : b * logDelta F n a = a * logDelta F n b) : ∃ c : F, a = c • b := by
  refine PowerSeries.exists_eq_smul_of_mul_derivative_eq hb
    (mul_left_cancel₀ (coe_logDenom_ne_zero (F := F) (n := n)) ?_)
  rw [logDelta_apply, logDelta_apply] at h
  linear_combination h

omit [CharZero F] in
private theorem X_pow_dvd_iterate_logDelta (m : ℕ) :
    ∀ {B : ℕ} {h : F⟦X⟧}, PowerSeries.X ^ B ∣ h →
      PowerSeries.X ^ (B - m) ∣ (logDelta F n)^[m] h := by
  induction m with
  | zero => intro B h hB; simpa using hB
  | succ m ih =>
    intro B h hB
    rw [Function.iterate_succ_apply', logDelta_apply, Nat.sub_succ]
    exact Dvd.dvd.mul_left (PowerSeries.X_pow_dvd_derivative (ih hB)) _

/-- The substitution of the logarithms into a polynomial over `F` factors through polynomials
with coefficients in `F[X]`. -/
private theorem aeval_map_algebraMap (f : MvPolynomial (Fin n) F) :
    MvPolynomial.aeval (logSeries F n) (MvPolynomial.map (algebraMap F F[X]) f) =
      MvPolynomial.aeval (logSeries F n) f := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.aeval_C,
      ← IsScalarTower.algebraMap_apply]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X,
      MvPolynomial.aeval_X, hp]

variable {V : Submodule F (MvPolynomial (Fin n) F)}

/-- **Theorem 4.1 of the source.** For a nonzero `f` in a derivative-closed space `V` of finite
dimension `r`, the series `f (ln (1 + t), …, ln (1 + n t))` is not divisible by
`t ^ (n r ^ 2 + r)`. -/
theorem not_X_pow_dvd_aeval_logSeries (hindep : AlgebraicIndependent F[X] (logSeries F n))
    (hV : ∀ i, ∀ p ∈ V, MvPolynomial.pderiv i p ∈ V) [Module.Finite F V]
    {f : MvPolynomial (Fin n) F} (hf : f ∈ V) (hf0 : f ≠ 0) :
    ¬ PowerSeries.X ^ (n * Module.finrank F V ^ 2 + Module.finrank F V) ∣
      MvPolynomial.aeval (logSeries F n) f := by
  classical
  intro hdvd
  set r := Module.finrank F V with hr
  let g : Module.Basis (Fin r) F V := Module.finBasis F V
  obtain ⟨w, hwdeg, hW⟩ := exists_wronskian_eq_C hV g
  set Ψ : MvPolynomial (Fin n) F →ₐ[F] F⟦X⟧ := MvPolynomial.aeval (logSeries F n) with hΨ
  set h : Fin r → F⟦X⟧ := fun j => Ψ (g j : MvPolynomial (Fin n) F) with hh
  have hiter (m : ℕ) (x : MvPolynomial (Fin n) F[X]) :
      MvPolynomial.aeval (logSeries F n) ((logDeriv F n)^[m] x) =
        (logDelta F n)^[m] (MvPolynomial.aeval (logSeries F n) x) := by
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', aeval_logDeriv, ih,
        Function.iterate_succ_apply', logDelta_apply]
  -- the Wronskian of the series is the polynomial `w`
  have hWh : (logDelta F n).wronskian h = (w : F⟦X⟧) := by
    have h₁ := congrArg (MvPolynomial.aeval (logSeries F n)) hW
    rw [MvPolynomial.aeval_C, Derivation.wronskian, AlgHom.map_det] at h₁
    rw [Derivation.wronskian, ← (show algebraMap F[X] F⟦X⟧ w = (w : F⟦X⟧) by
      simp [PowerSeries.algebraMap_apply']), ← h₁]
    refine congrArg det (Matrix.ext fun m j => ?_)
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Derivation.wronskianMatrix,
      Matrix.of_apply, hiter, aeval_map_algebraMap]
    rfl
  -- the series are linearly independent
  have hΨinj : Function.Injective Ψ := fun p q hpq => by
    have h₁ : MvPolynomial.aeval (logSeries F n) (MvPolynomial.map (algebraMap F F[X]) p) =
        MvPolynomial.aeval (logSeries F n) (MvPolynomial.map (algebraMap F F[X]) q) := by
      rw [aeval_map_algebraMap, aeval_map_algebraMap]; exact hpq
    exact MvPolynomial.map_injective _ (algebraMap F F[X]).injective (hindep h₁)
  have hind : LinearIndependent F h :=
    g.linearIndependent.map' (Ψ.toLinearMap ∘ₗ V.subtype)
      (LinearMap.ker_eq_bot.2 (hΨinj.comp V.injective_subtype))
  have hwne : (w : F⟦X⟧) ≠ 0 :=
    hWh ▸ Derivation.wronskian_ne_zero (logDelta F n) logDelta_const hind
  -- expand `f` in the basis
  set u := g.repr ⟨f, hf⟩ with hu
  have hfu : Ψ f = ∑ j, u j • h j := by
    have h₁ := congrArg (fun v : V => Ψ (v : MvPolynomial (Fin n) F)) (g.sum_repr ⟨f, hf⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul] at h₁
    exact h₁.symm
  obtain ⟨j₀, hj₀⟩ : ∃ j, u j ≠ 0 := by
    by_contra hall
    refine hf0 (hΨinj ?_)
    rw [hfu, map_zero]
    exact sum_eq_zero fun j _ => by rw [not_not.1 fun hj => hall ⟨j, hj⟩, zero_smul]
  -- a column of the Wronskian matrix is replaced by the derivatives of `f (P)`
  set k := n * r ^ 2 + 1 with hk
  have hcol (m : Fin r) : PowerSeries.X ^ k ∣ (logDelta F n)^[m] (Ψ f) := by
    refine (pow_dvd_pow _ ?_).trans (X_pow_dvd_iterate_logDelta m hdvd)
    have := m.2
    omega
  choose c hc using hcol
  have hlin (m : Fin r) : (logDelta F n)^[m] (Ψ f) =
      ∑ j, algebraMap F F⟦X⟧ (u j) • (logDelta F n).wronskianMatrix h m j := by
    have hpow : ∀ x : F⟦X⟧, ((logDelta F n : F⟦X⟧ →ₗ[F] F⟦X⟧) ^ (m : ℕ)) x =
        (logDelta F n)^[m] x := fun x => Module.End.pow_apply _ _ x
    rw [← hpow, hfu, map_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [map_smul, hpow, smul_eq_mul, ← Algebra.smul_def]
    rfl
  have hdet : (((logDelta F n).wronskianMatrix h).updateCol j₀
      fun m => (logDelta F n)^[m] (Ψ f)).det = algebraMap F F⟦X⟧ (u j₀) * (w : F⟦X⟧) := by
    have h₀ := det_updateCol_sum ((logDelta F n).wronskianMatrix h) j₀
      fun j => algebraMap F F⟦X⟧ (u j)
    rw [← hWh, Derivation.wronskian, ← smul_eq_mul, ← h₀]
    exact congrArg det (congrArg _ (funext hlin))
  have hdvdw : PowerSeries.X ^ k ∣ (w : F⟦X⟧) := by
    have h₁ : PowerSeries.X ^ k ∣ algebraMap F F⟦X⟧ (u j₀) * (w : F⟦X⟧) := by
      rw [← hdet, show (fun m : Fin r => (logDelta F n)^[m] (Ψ f)) =
        (PowerSeries.X : F⟦X⟧) ^ k • c from
        funext fun m => by rw [hc m, Pi.smul_apply, smul_eq_mul], det_updateCol_smul]
      exact dvd_mul_right _ _
    have h₂ : (w : F⟦X⟧) = algebraMap F F⟦X⟧ (u j₀)⁻¹ * (algebraMap F F⟦X⟧ (u j₀) * w) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hj₀, map_one, one_mul]
    rw [h₂]
    exact Dvd.dvd.mul_left h₁ _
  -- but `w` is a nonzero polynomial of degree less than `k`
  refine hwne ?_
  rw [← Polynomial.coe_zero, Polynomial.coe_inj]
  ext d
  rw [Polynomial.coeff_zero]
  by_cases hd : d < k
  · have := PowerSeries.X_pow_dvd_iff.1 hdvdw d hd
    rwa [Polynomial.coeff_coe] at this
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

end Cslib.Circuits.Arithmetic
