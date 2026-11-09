/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.RingTheory.RootsOfUnity.Principal
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The discrete Fourier transform over a commutative ring

For an element `ω` of a commutative ring `R`, `Cslib.dft ω a` is the discrete Fourier transform
of a vector `a : Fin n → R`, that is, the evaluation of the polynomial `∑ i, a i X ^ i` at the
points `ω ^ j` for `j < n` ([CLRS2009], Section 30.2). Mathlib's `ZMod.dft` is the
complex-valued transform built on `ZMod.stdAddChar`. Here the ring is arbitrary and the root of
unity is explicit, which covers number-theoretic transforms over `ZMod p` and the rings used in
fast integer multiplication.

## Main definitions

* `Cslib.dft ω a`: the vector `j ↦ ∑ i, a i * ω ^ (i * j)`.
* `Cslib.cyclicConv a b`: the cyclic convolution `k ↦ ∑ i, a i * b (k - i)` over `Fin n`.

## Main results

* `Cslib.dft_eq_vandermonde_mulVec`: the DFT is multiplication by the Vandermonde matrix of the
  powers of `ω`.
* `Cslib.dft_coeff_eq_eval`: the DFT of a coefficient vector evaluates the polynomial.
* `Cslib.dft_cyclicConv`: the convolution theorem ([CLRS2009], Theorem 30.8, in cyclic form),
  for any `ω` with `ω ^ n = 1`.
* `Cslib.dft_dft_neg`: the inversion formula `dft ω (dft ω a) (-j) = n * a j` for a principal
  `n`-th root of unity `ω`.
* `Cslib.dft_eq_add_of_lt`, `Cslib.dft_eq_sub_of_le`: the Cooley–Tukey splitting of a transform
  of even length `2 m` into two transforms of length `m` with respect to `ω ^ 2`, under
  `ω ^ m = -1` for the upper half ([CooleyTukey1965]; [CLRS2009], Section 30.2).
* `Cslib.cyclicConv_coeff`: the cyclic convolution of coefficient vectors is the product when
  `natDegree p + natDegree q < n`.

## References

* [Cooley and Tukey, *An Algorithm for the Machine Calculation of Complex Fourier
  Series*][CooleyTukey1965].
* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009], Section 30.2.
-/

public section

open Finset

namespace Cslib

variable {R : Type*} [CommRing R]

/-- The discrete Fourier transform of `a : Fin n → R` with respect to `ω`: the vector of values
`∑ i, a i * ω ^ (i * j)` of the polynomial with coefficient vector `a` at the points `ω ^ j`. -/
@[expose] def dft {n : ℕ} (ω : R) (a : Fin n → R) (j : Fin n) : R :=
  ∑ i, a i * ω ^ ((i : ℕ) * j)

/-- The DFT is multiplication by the Vandermonde matrix of `1, ω, …, ω ^ (n - 1)`. -/
theorem dft_eq_vandermonde_mulVec {n : ℕ} (ω : R) (a : Fin n → R) :
    dft ω a = (Matrix.vandermonde fun j : Fin n => ω ^ (j : ℕ)).mulVec a := by
  ext j
  simp only [dft, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_comm, ← pow_mul, mul_comm (j : ℕ)]

/-- A transform of length one is the identity. -/
@[simp] theorem dft_fin_one (ω : R) (a : Fin 1 → R) : dft ω a = a := by
  funext j
  simp [dft, Fin.fin_one_eq_zero j]

/-- The DFT of the coefficient vector of a polynomial of degree less than `n` evaluates the
polynomial at the powers of `ω`. -/
theorem dft_coeff_eq_eval {n : ℕ} (ω : R) {p : Polynomial R} (hp : p.natDegree < n)
    (j : Fin n) : dft ω (fun i : Fin n => p.coeff i) j = p.eval (ω ^ (j : ℕ)) := by
  rw [Polynomial.eval_eq_sum_range' hp, dft, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm (j : ℕ)]

/-- The cyclic convolution of `a b : Fin n → R`: `k ↦ ∑ i, a i * b (k - i)`, with the index
subtraction taken in `Fin n`, that is, modulo `n`. -/
@[expose] def cyclicConv {n : ℕ} (a b : Fin n → R) (k : Fin n) : R :=
  ∑ i, a i * b (k - i)

private theorem pow_val_add {n : ℕ} {ω : R} (hω : ω ^ n = 1) (m i j : Fin n) :
    ω ^ (((m + i : Fin n) : ℕ) * j) = ω ^ ((m : ℕ) * j) * ω ^ ((i : ℕ) * j) := by
  rw [Fin.val_add, pow_eq_pow_mod _ hω, Nat.mod_mul_mod, ← pow_eq_pow_mod _ hω, add_mul, pow_add]

/-- **Convolution theorem** (cyclic form, [CLRS2009], Theorem 30.8): the DFT turns cyclic
convolution into the pointwise product. Only `ω ^ n = 1` is needed. -/
theorem dft_cyclicConv {n : ℕ} {ω : R} (hω : ω ^ n = 1) (a b : Fin n → R) (j : Fin n) :
    dft ω (cyclicConv a b) j = dft ω a j * dft ω b j := by
  rcases n with _ | n
  · exact j.elim0
  simp only [dft, cyclicConv]
  rw [sum_mul_sum]
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  refine (Fintype.sum_equiv (Equiv.addRight i) _ _ fun m => ?_).symm
  simp only [Equiv.coe_addRight, add_sub_cancel_right, pow_val_add hω m i]
  ring

/-- **DFT inversion**: for a principal `n`-th root of unity `ω`, applying the transform twice and
negating the index multiplies by `n`. When `n` is a unit, `a = n⁻¹ • (dft ω (dft ω a) ∘ Neg.neg)`.
-/
theorem dft_dft_neg {n : ℕ} [NeZero n] {ω : R} (hω : IsPrincipalRoot ω n) (a : Fin n → R)
    (j : Fin n) : dft ω (dft ω a) (-j) = n * a j := by
  have hdvd : ∀ i : Fin n, n ∣ (i : ℕ) + ((-j : Fin n) : ℕ) ↔ i = j := fun i => by
    rw [Nat.dvd_iff_mod_eq_zero, ← Fin.val_add, Fin.val_eq_zero_iff, add_neg_eq_zero]
  have hinner : ∀ i : Fin n, ∑ l : Fin n, a i * ω ^ ((i : ℕ) * l) * ω ^ ((l : ℕ) * (-j : Fin n)) =
      a i * ∑ l ∈ range n, (ω ^ ((i : ℕ) + (-j : Fin n))) ^ l := fun i => by
    rw [mul_sum, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_assoc, ← pow_add, ← pow_mul]
    ring_nf
  simp only [dft, sum_mul]
  rw [sum_comm]
  simp only [hinner, hω.geom_sum_pow, hdvd, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  ring

/-- Splitting a sum over `Fin (2 * m)` into its even- and odd-indexed halves. -/
private theorem sum_even_add_sum_odd {M : Type*} [AddCommMonoid M] {n m : ℕ} (hn : n = 2 * m)
    (f : Fin n → M) :
    ∑ i, f i = ∑ i : Fin m, f ⟨2 * i, by omega⟩ + ∑ i : Fin m, f ⟨2 * i + 1, by omega⟩ := by
  subst hn
  rw [← (finProdFinEquiv.trans (finCongr (mul_comm m 2))).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, sum_add_distrib]
  congr 1 <;> refine sum_congr rfl fun i _ => congrArg f (Fin.ext ?_)
  · simp only [Equiv.trans_apply, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast,
      Fin.val_zero, zero_add, mul_comm]
  · simp only [Equiv.trans_apply, finProdFinEquiv_apply_val, finCongr_apply, Fin.val_cast,
      Fin.val_one]
    ring

/-- **Cooley–Tukey splitting, lower half.** For `n = 2 m` and `j < m`, the transform of length
`n` at `j` combines the length-`m` transforms of the even and odd parts with respect to `ω ^ 2`:
`dft ω a j = E j + ω ^ j * O j`. -/
theorem dft_eq_add_of_lt {n m : ℕ} (hn : n = 2 * m) (ω : R) (a : Fin n → R) (j : Fin n)
    (hj : (j : ℕ) < m) :
    dft ω a j = dft (ω ^ 2) (fun i : Fin m => a ⟨2 * i, by omega⟩) ⟨j, hj⟩ +
      ω ^ (j : ℕ) * dft (ω ^ 2) (fun i : Fin m => a ⟨2 * i + 1, by omega⟩) ⟨j, hj⟩ := by
  rw [dft, sum_even_add_sum_odd hn, dft, dft, mul_sum]
  congr 1 <;> refine sum_congr rfl fun i _ => ?_
  · simp only [pow_mul]
  · simp only [pow_succ, pow_mul]
    ring

/-- **Cooley–Tukey splitting, upper half.** For `n = 2 m`, `ω ^ m = -1` and `m ≤ j`, the
transform at `j` is `E (j - m) - ω ^ (j - m) * O (j - m)`. -/
theorem dft_eq_sub_of_le {n m : ℕ} (hn : n = 2 * m) {ω : R} (hω : ω ^ m = -1) (a : Fin n → R)
    (j : Fin n) (hj : m ≤ (j : ℕ)) :
    dft ω a j = dft (ω ^ 2) (fun i : Fin m => a ⟨2 * i, by omega⟩) ⟨j - m, by omega⟩ -
      ω ^ ((j : ℕ) - m) * dft (ω ^ 2) (fun i : Fin m => a ⟨2 * i + 1, by omega⟩)
        ⟨j - m, by omega⟩ := by
  obtain ⟨d, hd⟩ : ∃ d, (j : ℕ) = d + m := ⟨j - m, by omega⟩
  rw [dft, sum_even_add_sum_odd hn, dft, dft, mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
  congr 1 <;> refine sum_congr rfl fun i _ => ?_ <;> simp only [hd, Nat.add_sub_cancel]
  · rw [show 2 * (i : ℕ) * (d + m) = 2 * (i * d) + m * 2 * i by ring, pow_add, pow_mul ω 2,
      pow_mul ω (m * 2), pow_mul ω m, hω, neg_one_sq, one_pow, mul_one, pow_mul]
  · rw [show (2 * (i : ℕ) + 1) * (d + m) = 2 * (i * d) + d + (m * 2 * i + m) by ring, pow_add,
      pow_add, pow_add, pow_mul ω 2, pow_mul ω (m * 2), pow_mul ω m, hω, neg_one_sq, one_pow,
      one_mul]
    ring

/-- The cyclic convolution of the coefficient vectors of `p` and `q` is the coefficient vector
of `p * q` when `natDegree p + natDegree q < n`, since then no index wraps around. -/
theorem cyclicConv_coeff {n : ℕ} {p q : Polynomial R} (hpq : p.natDegree + q.natDegree < n)
    (k : Fin n) :
    cyclicConv (fun i : Fin n => p.coeff i) (fun i : Fin n => q.coeff i) k = (p * q).coeff k := by
  have hsub : ∀ i : Fin n,
      ((k - i : Fin n) : ℕ) = if (i : ℕ) ≤ k then (k : ℕ) - i else n - i + k := fun i => by
    rw [Fin.val_sub]
    split_ifs with h
    · rw [show n - (i : ℕ) + k = (k - i) + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · exact Nat.mod_eq_of_lt (by omega)
  have hL : cyclicConv (fun i : Fin n => p.coeff i) (fun i : Fin n => q.coeff i) k =
      ∑ i ∈ range n, p.coeff i * q.coeff (if i ≤ (k : ℕ) then (k : ℕ) - i else n - i + k) := by
    rw [cyclicConv, ← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun i _ => by rw [hsub]
  rw [hL, Polynomial.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← sum_range_add_sum_Ico _ (show (k : ℕ) + 1 ≤ n by omega),
    sum_eq_zero (s := Ico _ _) fun i hi => ?_, add_zero]
  · refine sum_congr rfl fun i hi => ?_
    rw [mem_range] at hi
    rw [ite_eq_left (by omega)]
  · rw [mem_Ico] at hi
    rw [ite_eq_right (by omega)]
    by_cases hp : i ≤ p.natDegree
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := q) (by omega), mul_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

end Cslib
