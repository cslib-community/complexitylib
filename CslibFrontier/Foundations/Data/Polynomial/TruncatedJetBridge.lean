/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Cslib, bridge between `Polynomial.Truncated` and `Cslib.JetTable`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Polynomial.StagedJetArithmetic
public import CslibFrontier.Foundations.Data.Polynomial.TruncatedAlgebra
import Mathlib.Tactic.Ring

/-!
# Bridge between `Polynomial.Truncated` and `Cslib.JetTable`

Connects the general quotient algebra `Polynomial.Truncated R r = R[T] / (T ^ r)` to the
univariate specializations `Cslib.JetTable r 1 R` (`R[z] / (z ^ r)`) and `Cslib.JetTable 1 r R`
(`R[V] / (V ^ r)`) from `StagedJetArithmetic.lean`.

## Main definitions

* `Polynomial.Truncated.equivJetTableR1`: ring isomorphism `Truncated R r ≃+* Cslib.JetTable r 1 R`.
* `Polynomial.Truncated.equivJetTable1R`: ring isomorphism `Truncated R r ≃+* Cslib.JetTable 1 r R`.

## Main results

* `Polynomial.Truncated.equivJetTableR1_mk`: `equivJetTableR1` sends `mk r p` to
  `Cslib.JetTable.ofPolyZ r 1 p`.
* `Polynomial.Truncated.equivJetTable1R_mk`: `equivJetTable1R` sends `mk r p` to
  `Cslib.JetTable.ofPolyVPolyZ 1 r (p.map Polynomial.C)`.
-/

public section

namespace Polynomial.Truncated

open Finset Cslib

noncomputable section

variable {R : Type*} [CommRing R]

private def toJetTableR1Hom (R : Type*) [CommRing R] (r : ℕ) :
    Truncated R r →+* JetTable r 1 R :=
  Ideal.Quotient.lift (Ideal.span {(X : R[X]) ^ r}) (JetTable.ofPolyZ r 1) fun p hp => by
    rw [Ideal.mem_span_singleton, Polynomial.X_pow_dvd_iff] at hp
    ext j u
    simp only [JetTable.ofPolyZ_apply, JetTable.coe_zero]
    split_ifs
    · exact hp j.val j.isLt
    · rfl

/-- Ring isomorphism between `Truncated R r` and `Cslib.JetTable r 1 R` (`R[z] / (z ^ r)`). -/
def equivJetTableR1 (R : Type*) [CommRing R] (r : ℕ) :
    Truncated R r ≃+* JetTable r 1 R where
  toFun := toJetTableR1Hom R r
  invFun := fun A => mk r (∑ j : Fin r, C (A j 0) * X ^ (j : ℕ))
  left_inv := fun x => by
    induction x using induction_on with
    | hp p =>
      rw [mk_eq_mk_iff]
      intro i hi
      have hto : toJetTableR1Hom R r (mk r p) = JetTable.ofPolyZ r 1 p := by
        rw [toJetTableR1Hom, mk_apply, Ideal.Quotient.lift_mk]
      rw [hto, ← Polynomial.lcoeff_apply, map_sum]
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single ⟨i, hi⟩]
      · simp [JetTable.ofPolyZ_apply]
      · intro b _ hbi
        have hne : i ≠ (b : ℕ) := fun h => hbi (Fin.ext h.symm)
        simp only [hne, ↓reduceIte]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
  right_inv := fun A => by
    ext j u
    have hu0 : (u : ℕ) = 0 := by omega
    have hto : toJetTableR1Hom R r (mk r (∑ k : Fin r, C (A k 0) * X ^ (k : ℕ))) =
        JetTable.ofPolyZ r 1 (∑ k : Fin r, C (A k 0) * X ^ (k : ℕ)) := by
      rw [toJetTableR1Hom, mk_apply, Ideal.Quotient.lift_mk]
    rw [hto, JetTable.ofPolyZ_apply]
    simp only [hu0, ↓reduceIte]
    rw [← Polynomial.lcoeff_apply, map_sum]
    simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp [Fin.eq_zero u]
    · intro k _ hkj
      have hne : (j : ℕ) ≠ (k : ℕ) := fun h => hkj (Fin.ext h.symm)
      simp only [hne, ↓reduceIte]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  map_mul' := (toJetTableR1Hom R r).map_mul
  map_add' := (toJetTableR1Hom R r).map_add

@[simp]
theorem equivJetTableR1_mk (r : ℕ) (p : R[X]) :
    equivJetTableR1 R r (mk r p) = JetTable.ofPolyZ r 1 p := by
  change toJetTableR1Hom R r (mk r p) = _
  rw [toJetTableR1Hom, mk_apply, Ideal.Quotient.lift_mk]

@[simp]
theorem coeff_equivJetTableR1_symm {r : ℕ} (i : ℕ) (A : JetTable r 1 R) :
    coeff i ((equivJetTableR1 R r).symm A) = if h : i < r then A ⟨i, h⟩ 0 else 0 := by
  have hmem := (equivJetTableR1 R r).apply_symm_apply A
  have heq : coeff i ((equivJetTableR1 R r).symm A) =
      if h : i < r then (JetTable.ofPolyZ r 1 (toPoly ((equivJetTableR1 R r).symm A))) ⟨i, h⟩ 0
      else 0 := by
    split_ifs with hi
    · rw [JetTable.ofPolyZ_apply]
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, coeff_toPoly]
    · exact coeff_eq_zero_of_le (not_lt.mp hi) _
  rw [heq]
  split_ifs with hi
  · have h2 : JetTable.ofPolyZ r 1 (toPoly ((equivJetTableR1 R r).symm A)) = A := by
      rw [← equivJetTableR1_mk, mk_toPoly, hmem]
    rw [h2]
  · rfl

private def transposeEquiv (J ℓ : ℕ) (R : Type*) [CommRing R] :
    JetTable ℓ J R ≃+* JetTable J ℓ R where
  toFun := JetTable.transpose
  invFun := JetTable.transpose
  left_inv _ := JetTable.ext fun _ _ => rfl
  right_inv _ := JetTable.ext fun _ _ => rfl
  map_mul' := (JetTable.transpose (J := J) (ℓ := ℓ)).map_mul
  map_add' := (JetTable.transpose (J := J) (ℓ := ℓ)).map_add

/-- Ring isomorphism between `Truncated R r` and `Cslib.JetTable 1 r R` (`R[V] / (V ^ r)`). -/
def equivJetTable1R (R : Type*) [CommRing R] (r : ℕ) :
    Truncated R r ≃+* JetTable 1 r R :=
  (equivJetTableR1 R r).trans (transposeEquiv 1 r R)

@[simp]
theorem equivJetTable1R_mk (r : ℕ) (p : R[X]) :
    equivJetTable1R R r (mk r p) =
      JetTable.ofPolyVPolyZ 1 r (Polynomial.mapRingHom Polynomial.C p) := by
  rw [equivJetTable1R, RingEquiv.trans_apply, equivJetTableR1_mk]
  ext j u
  change JetTable.ofPolyZ r 1 p u j =
    (JetTable.ofPolyVPolyZ 1 r (Polynomial.map Polynomial.C p)) j u
  rw [JetTable.ofPolyZ_apply, JetTable.ofPolyVPolyZ_apply, Polynomial.coeff_map, Polynomial.coeff_C]

@[simp]
theorem coeff_equivJetTable1R_symm {r : ℕ} (i : ℕ) (A : JetTable 1 r R) :
    coeff i ((equivJetTable1R R r).symm A) =
      if h : i < r then A 0 ⟨i, h⟩ else 0 := by
  have heq : (equivJetTable1R R r).symm A = (equivJetTableR1 R r).symm A.transpose := by
    rw [equivJetTable1R]
    rfl
  rw [heq, coeff_equivJetTableR1_symm]
  split_ifs <;> rfl

end

end Polynomial.Truncated
