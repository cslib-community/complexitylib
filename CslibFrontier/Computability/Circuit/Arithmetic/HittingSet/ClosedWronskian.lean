/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LogCurve
public import CslibFrontier.Foundations.Data.MvPolynomial.PDerivConst
public import CslibFrontier.Foundations.RingTheory.Derivation.Wronskian
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# The Wronskian of a derivative-closed space

Let `V` be a finite-dimensional space of polynomials in `x` that is closed under every partial
derivative, with basis `g`. The Wronskian of `g` for the derivation `D = Q ∂ₜ + ∑ᵢ bᵢ ∂ᵢ` of
`MvPolynomial (Fin n) F[X]` is a polynomial in `t` alone, of degree at most `n r ^ 2`
(`exists_wronskian_eq_C`). This is Lemma 3.1 and Corollary 3.5 of
[Bhardwaj et al.][BhardwajEtAl2026], with the denominator `Q` cleared.

A partial derivative `∂ᵢ` commutes with `D` and maps each column of the Wronskian matrix to a
combination of the columns, with the matrix `T` of `∂ᵢ` on `V` as coefficients. So `∂ᵢ` of the
determinant is `tr T` times the determinant, and `tr T = 0` because `∂ᵢ` is nilpotent on `V`.
The degree bound holds for the constant coefficient in `x`, which is a determinant over `F[X]`
whose row `m` has degree at most `m n`.

## Main results

* `exists_wronskian_eq_C`: the `D`-Wronskian of a basis of a closed space is `C w` with
  `natDegree w ≤ n * r ^ 2`.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026], §3
-/

public section

open scoped Polynomial

namespace Cslib.Circuits.Arithmetic

open Finset Matrix

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
private theorem natDegree_one_add_C_mul_X_le (a : F) :
    (1 + Polynomial.C a * Polynomial.X : F[X]).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
  exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

omit [CharZero F] in
private theorem natDegree_logDenom_le : (logDenom F n).natDegree ≤ n :=
  (Polynomial.natDegree_prod_le _ _).trans
    ((sum_le_sum fun _ _ => natDegree_one_add_C_mul_X_le _).trans (by simp))

omit [CharZero F] in
private theorem natDegree_logCoeff_le (i : Fin n) : (logCoeff F n i).natDegree ≤ n :=
  (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans
    ((sum_le_sum fun _ _ => natDegree_one_add_C_mul_X_le _).trans (by simp)))

omit [CharZero F] in
/-- `D` raises the degree in `t` of every coefficient by at most `n`. -/
private theorem natDegree_coeff_logDeriv_le {g : MvPolynomial (Fin n) F[X]} {k : ℕ}
    (h : ∀ μ, (g.coeff μ).natDegree ≤ k) (μ : Fin n →₀ ℕ) :
    ((logDeriv F n g).coeff μ).natDegree ≤ k + n := by
  rw [coeff_logDeriv]
  refine Polynomial.natDegree_add_le_of_degree_le ?_ ?_
  · refine Polynomial.natDegree_mul_le.trans ?_
    have := (Polynomial.natDegree_derivative_le (g.coeff μ)).trans (Nat.sub_le _ _)
    have := h μ
    have := natDegree_logDenom_le (F := F) (n := n)
    omega
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    have hcast : ((μ i : F[X]) + 1).natDegree = 0 := by
      rw [← Nat.cast_succ, Polynomial.natDegree_natCast]
    refine Polynomial.natDegree_mul_le.trans ?_
    have h₁ := Polynomial.natDegree_mul_le (p := g.coeff (μ + Finsupp.single i 1))
      (q := (μ i : F[X]) + 1)
    have := h (μ + Finsupp.single i 1)
    have := natDegree_logCoeff_le (F := F) i
    omega

omit [CharZero F] in
private theorem natDegree_coeff_iterate_logDeriv_le (p : MvPolynomial (Fin n) F) (m : ℕ)
    (μ : Fin n →₀ ℕ) :
    (((logDeriv F n)^[m] (MvPolynomial.map (algebraMap F F[X]) p)).coeff μ).natDegree ≤ m * n := by
  induction m generalizing μ with
  | zero => simp [MvPolynomial.coeff_map]
  | succ m ih =>
    rw [Function.iterate_succ_apply', Nat.succ_mul]
    exact natDegree_coeff_logDeriv_le ih μ

omit [CharZero F] in
/-- The degree of a determinant over `F[X]` is at most the sum of the degree bounds of its
rows. -/
private theorem natDegree_det_le {r : ℕ} (N : Matrix (Fin r) (Fin r) F[X]) (b : Fin r → ℕ)
    (h : ∀ i j, (N i j).natDegree ≤ b i) : N.det.natDegree ≤ ∑ i, b i := by
  rw [det_apply']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [Polynomial.natDegree_intCast, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  rw [← Equiv.sum_comp σ b]
  exact sum_le_sum fun i _ => h (σ i) i

variable {V : Submodule F (MvPolynomial (Fin n) F)}
  (hV : ∀ i, ∀ p ∈ V, MvPolynomial.pderiv i p ∈ V)

/-- The restriction of a partial derivative to a closed space. -/
private noncomputable def pderivRestrict (i : Fin n) : V →ₗ[F] V :=
  (MvPolynomial.pderiv (R := F) (σ := Fin n) i).toLinearMap.restrict fun p hp => hV i p hp

omit [CharZero F] in
include hV in
private theorem trace_pderivRestrict [Module.Finite F V] (i : Fin n) :
    LinearMap.trace F V (pderivRestrict hV i) = 0 := by
  refine (LinearMap.isNilpotent_trace_of_isNilpotent ?_).eq_zero
  rw [Module.End.isNilpotent_iff_of_finite]
  intro v
  refine ⟨(v : MvPolynomial (Fin n) F).totalDegree + 1, Subtype.ext ?_⟩
  have hiter : ∀ (k : ℕ) (u : V), (((pderivRestrict hV i) ^ k) u : MvPolynomial (Fin n) F) =
      (MvPolynomial.pderiv i)^[k] u := by
    intro k
    induction k with
    | zero => intro u; rfl
    | succ k ih =>
      intro u
      rw [pow_succ, Module.End.mul_apply, ih, Function.iterate_succ_apply]
      rfl
  rw [hiter, Submodule.coe_zero]
  exact MvPolynomial.iterate_pderiv_eq_zero i (Nat.lt_succ_self _)

include hV in
/-- The `D`-Wronskian of a basis of a derivative-closed space is a polynomial in `t` alone, of
degree at most `n * r ^ 2`. -/
theorem exists_wronskian_eq_C [Module.Finite F V] {r : ℕ} (g : Module.Basis (Fin r) F V) :
    ∃ w : F[X], w.natDegree ≤ n * r ^ 2 ∧
      (logDeriv F n).wronskian
        (fun j => MvPolynomial.map (algebraMap F F[X]) (g j : MvPolynomial (Fin n) F)) =
        MvPolynomial.C w := by
  classical
  set G : Fin r → MvPolynomial (Fin n) F[X] :=
    fun j => MvPolynomial.map (algebraMap F F[X]) (g j : MvPolynomial (Fin n) F) with hG
  set M := (logDeriv F n).wronskianMatrix G with hM
  -- every partial derivative kills the determinant
  have hpd (i : Fin n) : MvPolynomial.pderiv i M.det = 0 := by
    set T := LinearMap.toMatrix g g (pderivRestrict hV i) with hT
    have hcomm (m : ℕ) (x : MvPolynomial (Fin n) F[X]) :
        MvPolynomial.pderiv i ((logDeriv F n)^[m] x) =
          (logDeriv F n)^[m] (MvPolynomial.pderiv i x) := by
      induction m generalizing x with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply, ih, ← logDeriv_pderiv,
          ← Function.iterate_succ_apply]
    have hbasis (j : Fin r) : MvPolynomial.pderiv i (G j) = ∑ k, T k j • G k := by
      have h₁ : (MvPolynomial.pderiv i (g j : MvPolynomial (Fin n) F)) =
          ∑ k, T k j • (g k : MvPolynomial (Fin n) F) := by
        have h := congrArg (Subtype.val) (g.sum_repr (pderivRestrict hV i (g j)))
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h
        rw [← (show ((pderivRestrict hV i (g j) : V) : MvPolynomial (Fin n) F) =
          MvPolynomial.pderiv i (g j : MvPolynomial (Fin n) F) from rfl), ← h]
        exact sum_congr rfl fun k _ => by rw [hT, LinearMap.toMatrix_apply]
      rw [hG]
      simp only [MvPolynomial.pderiv_map, h₁, map_sum, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C]
      exact sum_congr rfl fun k _ => by
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply F F[X] (MvPolynomial (Fin n) F[X]),
          MvPolynomial.algebraMap_eq]
    have hlin (m j : Fin r) : MvPolynomial.pderiv i (M m j) =
        ∑ k, (algebraMap F (MvPolynomial (Fin n) F[X]) (T k j)) • M m k := by
      have hiter : ∀ (m : ℕ) (x : MvPolynomial (Fin n) F[X]),
          ((logDeriv F n : MvPolynomial (Fin n) F[X] →ₗ[F] MvPolynomial (Fin n) F[X]) ^ m) x =
            (logDeriv F n)^[m] x := fun m x => Module.End.pow_apply _ m x
      change MvPolynomial.pderiv i ((logDeriv F n)^[m] (G j)) = _
      rw [hcomm, hbasis, ← hiter, map_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_smul, hiter, Algebra.smul_def]
      rfl
    have hdet := Derivation.map_det (MvPolynomial.pderiv i :
      Derivation F[X] (MvPolynomial (Fin n) F[X]) (MvPolynomial (Fin n) F[X])) M
    rw [hdet]
    have hcol (j : Fin r) : (M.updateCol j fun m => MvPolynomial.pderiv i (M m j)).det =
        algebraMap F (MvPolynomial (Fin n) F[X]) (T j j) * M.det := by
      have h := det_updateCol_sum M j fun k => algebraMap F (MvPolynomial (Fin n) F[X]) (T k j)
      rw [smul_eq_mul] at h
      rw [← h]
      exact congrArg det (congrArg (M.updateCol j) (funext fun m => hlin m j))
    rw [sum_congr rfl fun j _ => hcol j, ← sum_mul, ← map_sum]
    have htr : ∑ j, T j j = 0 := by
      have h := LinearMap.trace_eq_matrix_trace F g (pderivRestrict hV i)
      rw [trace_pderivRestrict hV i] at h
      exact h.symm
    rw [htr, map_zero, zero_mul]
  refine ⟨MvPolynomial.constantCoeff M.det, ?_, MvPolynomial.eq_C_of_pderiv_eq_zero hpd⟩
  -- the constant coefficient is a determinant over `F[X]`
  rw [RingHom.map_det]
  refine (natDegree_det_le _ (fun m : Fin r => (m : ℕ) * n) fun m j => ?_).trans ?_
  · exact natDegree_coeff_iterate_logDeriv_le (g j : MvPolynomial (Fin n) F) m 0
  · calc ∑ m : Fin r, (m : ℕ) * n ≤ ∑ _m : Fin r, r * n :=
          sum_le_sum fun m _ => Nat.mul_le_mul_right n m.2.le
      _ = n * r ^ 2 := by simp; ring

end Cslib.Circuits.Arithmetic
