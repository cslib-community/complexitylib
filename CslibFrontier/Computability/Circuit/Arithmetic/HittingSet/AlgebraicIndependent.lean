/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LogCurve
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finsupp.Weight

/-!
# Algebraic independence of the logarithms

Over a field `F` of characteristic zero, the power series `ln (1 + (i + 1) t)`, `i : Fin n`, are
algebraically independent over `F[t]`
([Bhardwaj et al.][BhardwajEtAl2026], Lemmas 2.3 and 2.4).

The proof is the source's, with denominators cleared. Take a nonzero `g` in the kernel of the
substitution `Φ` with the lowest degree `d` in `x` and, among those, the fewest monomials of degree
`d`, and let `α` be one of its coefficients of degree `d`. By the chain rule
`LogCurve.aeval_logDeriv`, the polynomial `α * D g - Q * α' * g` is in the kernel too; it has
fewer monomials of degree `d`, so it vanishes. In degree `d` this says that every coefficient of
`g` is a constant multiple `c * α`. In degree `d - 1` it says that a coefficient `γ` satisfies
`Q * (α * γ' - α' * γ) = -α ^ 2 * ∑ᵢ cᵢ * bᵢ`. Dividing by `Q * α ^ 2`, the left side is the
derivative of `γ / α`, which has no simple pole, whereas `bᵢ / Q` has a simple pole at
`-1 / (i + 1)` and nowhere else: so every `cᵢ` vanishes, contradicting the choice of `α`.

## Main results

* `algebraicIndependent_logSeries`: the series `ln (1 + (i + 1) t)` are algebraically independent
  over `F[t]`.

## References

* [S. Bhardwaj, F. Lakhani, P. Mukhopadhyay, R. Saptharishi, P. Shastri,
  A. K. Sinhababu, *Hitting sets from derivations: Waring rank and noncommutative
  ABPs*][BhardwajEtAl2026], Lemmas 2.3 and 2.4 of revision 1
-/

public section

open scoped Polynomial PowerSeries

namespace Cslib.Circuits.Arithmetic

open Finset Polynomial

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

/-- The derivative of a rational function `γ / α` has no simple pole: if `Q = (t - a) * R` has a
simple root at `a` and `Q * (γ / α)' = S`, then `S` vanishes at `a`. -/
private theorem eval_eq_zero_of_mul_wronskian {a : F} {R α γ S : F[X]} (hR : R.eval a ≠ 0)
    (hα : α ≠ 0)
    (h : (X - C a) * R * (α * derivative γ - derivative α * γ) = α ^ 2 * S) : S.eval a = 0 := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · have hS : S = 0 := by simpa [hα] using h.symm
    rw [hS, eval_zero]
  obtain ⟨α₀, hα', hα₀⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd α hα a
  obtain ⟨γ₀, hγ', hγ₀⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd γ hγ a
  generalize rootMultiplicity a α = p at hα'
  generalize rootMultiplicity a γ = q at hγ'
  subst hα' hγ'
  rw [dvd_iff_isRoot, IsRoot] at hα₀ hγ₀
  have hL (k : ℕ) : (X - C a) * derivative ((X - C a) ^ k) = (k : F[X]) * (X - C a) ^ k := by
    cases k with
    | zero => simp
    | succ k => rw [derivative_X_sub_C_pow, Nat.add_sub_cancel, pow_succ, C_eq_natCast]; ring
  have key : R * (X - C a) ^ (p + q) * (((q : F[X]) - (p : F[X])) * (α₀ * γ₀) +
      (X - C a) * (α₀ * derivative γ₀ - derivative α₀ * γ₀)) =
      (X - C a) ^ (2 * p) * (α₀ ^ 2 * S) := by
    simp only [derivative_mul] at h
    linear_combination h - R * (X - C a) ^ p * α₀ * γ₀ * hL q + R * α₀ * (X - C a) ^ q * γ₀ * hL p
  have hX : (X - C a : F[X]) ≠ 0 := X_sub_C_ne_zero a
  rcases le_or_gt p q with hpq | hpq
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
    have h' := congrArg (eval a) (mul_left_cancel₀ (pow_ne_zero (2 * p) hX)
      (b := R * (X - C a) ^ k * ((k : F[X]) * (α₀ * γ₀) +
        (X - C a) * (α₀ * derivative γ₀ - derivative α₀ * γ₀))) (by
        rw [← key]; push_cast; ring))
    cases k <;> simpa [hα₀] using h'.symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hpq
    have h' := congrArg (eval a) (mul_left_cancel₀ (pow_ne_zero (2 * q + k + 1) hX)
      (b := R * (-((k : F[X]) + 1) * (α₀ * γ₀) +
        (X - C a) * (α₀ * derivative γ₀ - derivative α₀ * γ₀)))
      (c := (X - C a) ^ (k + 1) * (α₀ ^ 2 * S)) (by
        have := key
        push_cast at this
        linear_combination this))
    have hk : -((k : F) + 1) = 0 := by simpa [hR, hα₀, hγ₀] using h'
    exact (Nat.cast_add_one_ne_zero k (neg_eq_zero.1 hk)).elim

/-- `Q` has a simple root at `-1 / (i + 1)`, with cofactor `bᵢ`. -/
private theorem logDenom_eq (i : Fin n) :
    logDenom F n = (X - C (-((i : ℕ) + 1 : F)⁻¹)) * logCoeff F n i := by
  have hi : ((i : ℕ) + 1 : F) ≠ 0 := Nat.cast_add_one_ne_zero i
  have h : C ((i : ℕ) + 1 : F) * (X - C (-((i : ℕ) + 1 : F)⁻¹)) = 1 + C ((i : ℕ) + 1 : F) * X := by
    rw [mul_sub, ← C_mul, mul_neg, mul_inv_cancel₀ hi]
    simp [add_comm]
  refine mul_left_cancel₀ (C_ne_zero.2 hi) ?_
  rw [← logCoeff_mul, ← h]
  ring

/-- Among the `bⱼ`, only `bᵢ` does not vanish at `-1 / (i + 1)`. -/
private theorem eval_logCoeff_eq_zero_iff (i j : Fin n) :
    (logCoeff F n j).eval (-((i : ℕ) + 1 : F)⁻¹) = 0 ↔ j ≠ i := by
  have hi : ((i : ℕ) + 1 : F) ≠ 0 := Nat.cast_add_one_ne_zero i
  have h (k : Fin n) : 1 + ((k : ℕ) + 1 : F) * (-((i : ℕ) + 1 : F)⁻¹) = 0 ↔ k = i := by
    rw [mul_neg, ← sub_eq_add_neg, sub_eq_zero, eq_comm, mul_inv_eq_one₀ hi, add_left_inj,
      Nat.cast_inj, Fin.val_inj]
  rw [logCoeff, eval_mul, eval_C, eval_prod, mul_eq_zero, prod_eq_zero_iff]
  simp only [eval_add, eval_one, eval_mul, eval_C, eval_X, h, mem_erase, mem_univ, and_true]
  simp [Nat.cast_add_one_ne_zero, ne_comm]

/-- The inductive form of `algebraicIndependent_logSeries`: a polynomial of degree less than `d`
in `x` that vanishes at the logarithms is zero. -/
private theorem eq_zero_of_aeval_logSeries (d : ℕ) (g : MvPolynomial (Fin n) F[X])
    (hd : ∀ m, d ≤ m.degree → g.coeff m = 0)
    (hg : MvPolynomial.aeval (logSeries F n) g = 0) : g = 0 := by
  induction d generalizing g with
  | zero => exact MvPolynomial.ext _ _ fun m => hd m (Nat.zero_le _)
  | succ d ihd =>
  induction hk : #{m ∈ g.support | m.degree = d} using Nat.strong_induction_on generalizing g with
  | _ k ih =>
  by_cases htop : ∀ m, m.degree = d → g.coeff m = 0
  · exact ihd g (fun m hm => hm.eq_or_lt.elim (fun h => htop m h.symm) (hd m)) hg
  exfalso
  push Not at htop
  obtain ⟨m₀, hm₀, hα⟩ := htop
  set α := g.coeff m₀ with hαdef
  -- The coefficients of `D g` and of `α * D g - Q * α' * g` in degree at least `d`.
  have hD (m : Fin n →₀ ℕ) (hm : d ≤ m.degree) : (logDeriv F n g).coeff m =
      logDenom F n * derivative (g.coeff m) := by
    rw [coeff_logDeriv, sum_eq_zero fun i _ => ?_, add_zero]
    rw [hd _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul, mul_zero]
  have hcoeff (m : Fin n →₀ ℕ) : (MvPolynomial.C α * logDeriv F n g -
      MvPolynomial.C (logDenom F n * derivative α) * g).coeff m =
      α * (logDeriv F n g).coeff m - logDenom F n * derivative α * g.coeff m := by
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul]
  -- By minimality, `α * D g = Q * α' * g`.
  have hmin : MvPolynomial.C α * logDeriv F n g -
      MvPolynomial.C (logDenom F n * derivative α) * g = 0 := by
    refine ih _ ?_ _ (fun m hm => ?_) (by simp [aeval_logDeriv, hg]) rfl
    · rw [← hk]
      refine (card_le_card fun m hm => ?_).trans_lt
        (card_erase_lt_of_mem (mem_filter.2 ⟨MvPolynomial.mem_support_iff.2 hα, hm₀⟩))
      simp only [mem_filter, mem_erase, MvPolynomial.mem_support_iff, hcoeff] at hm ⊢
      obtain ⟨hm, hmd⟩ := hm
      rw [hD m hmd.ge] at hm
      refine ⟨fun h => hm ?_, fun h => hm ?_, hmd⟩
      · rw [h]; ring
      · rw [h]; simp
    · rw [hcoeff, hD m (Nat.le_of_succ_le hm), hd m hm]
      simp
  have H (m : Fin n →₀ ℕ) :
      α * (logDeriv F n g).coeff m = logDenom F n * derivative α * g.coeff m := by
    rw [← sub_eq_zero, ← hcoeff, hmin]
    simp
  have hQ : logDenom F n ≠ 0 := prod_ne_zero_iff.2 fun i _ h => by
    simpa using congrArg (eval 0) h
  -- In degree `d`, the coefficients of `g` are constant multiples of `α`.
  have hconst (m : Fin n →₀ ℕ) (hm : m.degree = d) : ∃ c : F, g.coeff m = c • α := by
    have h := H m
    rw [hD m hm.ge] at h
    have h' : α * derivative (g.coeff m) = g.coeff m * derivative α :=
      mul_left_cancel₀ hQ (by linear_combination h)
    obtain ⟨c, hc⟩ := PowerSeries.exists_eq_smul_of_mul_derivative_eq
      (a := (g.coeff m : F⟦X⟧)) (b := (α : F⟦X⟧)) (Polynomial.coe_eq_zero_iff.not.2 hα) (by
        rw [PowerSeries.derivative_coe, PowerSeries.derivative_coe, ← Polynomial.coe_mul,
          ← Polynomial.coe_mul, h'])
    exact ⟨c, Polynomial.coe_injective F (by rw [hc, Polynomial.coe_smul])⟩
  choose! c hc using hconst
  rcases eq_or_ne m₀ 0 with rfl | hne
  · -- `d = 0`: then `g = α` is a nonzero polynomial in `t`.
    rw [map_zero] at hm₀
    subst hm₀
    have hgα : g = MvPolynomial.C α := MvPolynomial.ext _ _ fun m => by
      rw [MvPolynomial.coeff_C]
      split_ifs with h
      · rw [← h]
      · exact hd m (Nat.pos_of_ne_zero fun h0 => h ((Finsupp.degree_eq_zero_iff m).1 h0).symm)
    rw [hgα, MvPolynomial.aeval_C] at hg
    exact hα (by simpa [PowerSeries.algebraMap_apply'] using hg)
  -- `d ≥ 1`: compare the coefficients at a monomial `m` of degree `d - 1` below `m₀`.
  obtain ⟨i, hi⟩ := DFunLike.ne_iff.1 hne
  have hm := Finsupp.sub_add_single_one_cancel hi
  set m := m₀ - Finsupp.single i 1
  have hdeg (j : Fin n) : (m + Finsupp.single j 1).degree = d := by
    rw [← hm₀, ← hm, map_add, map_add, Finsupp.degree_single, Finsupp.degree_single]
  have h := H m
  rw [coeff_logDeriv] at h
  have hsum (j : Fin n) : logCoeff F n j * (g.coeff (m + Finsupp.single j 1) * (m j + 1)) =
      α * (logCoeff F n j * C (c (m + Finsupp.single j 1) * (m j + 1))) := by
    rw [hc _ (hdeg j), smul_eq_C_mul, C_mul, C_add, C_1, C_eq_natCast]
    ring
  simp only [hsum, ← mul_sum] at h
  have h0 := eval_eq_zero_of_mul_wronskian (a := -((i : ℕ) + 1 : F)⁻¹)
    (mt (eval_logCoeff_eq_zero_iff i i).1 (by simp)) hα
    (S := -∑ j, logCoeff F n j * C (c (m + Finsupp.single j 1) * (m j + 1)))
    (γ := g.coeff m) (by rw [← logDenom_eq]; linear_combination h)
  rw [eval_neg, neg_eq_zero, eval_finsetSum, sum_eq_single i (fun j _ hj => by
    rw [eval_mul, (eval_logCoeff_eq_zero_iff i j).2 hj, zero_mul]) (by simp), hm, eval_mul,
    eval_C, mul_eq_zero, mul_eq_zero] at h0
  rcases h0 with h0 | h0 | h0
  · exact (eval_logCoeff_eq_zero_iff i i).1 h0 rfl
  · exact hα (by rw [hαdef, hc m₀ hm₀, h0, zero_smul])
  · exact Nat.cast_add_one_ne_zero _ h0

/-- Lemmas 2.3 and 2.4 of the source: the power series `ln (1 + (i + 1) t)` are algebraically
independent over `F[t]`. -/
theorem algebraicIndependent_logSeries (F : Type*) [Field F] [CharZero F] (n : ℕ) :
    AlgebraicIndependent F[X] (logSeries F n) :=
  (injective_iff_map_eq_zero _).2 fun g hg =>
    eq_zero_of_aeval_logSeries (g.totalDegree + 1) g (fun m hm =>
      by_contra fun h => (Nat.lt_of_succ_le hm).not_ge <| by
        simpa [Finsupp.degree_apply, Finsupp.sum] using
          MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.2 h)) hg

end Cslib.Circuits.Arithmetic
