/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.LineCode.Basic
public import CslibFrontier.Foundations.Combinatorics.LineCode.HighRate.Rate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
import CslibFrontier.Foundations.Combinatorics.LineCode.HighRate.Monomial
import CslibFrontier.Foundations.Combinatorics.LineCode.HighRate.Systematic
import CslibFrontier.Foundations.FieldTheory.Finite.ReducedMonomial
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A high-rate line-parity code

Let `K` be a field of characteristic two with `q = 2 ^ (h * m)` elements and let `ℓ ≤ 2 ^ h`.
Write every exponent `e < q` with `m` digits in base `2 ^ h`, so that the exponents of a reduced
monomial `∏ i, X i ^ e i` on `K ^ ℓ` form a digit matrix `D : Fin m → Fin ℓ → Fin (2 ^ h)`. The
code is spanned by the monomials whose digit matrix has a zero column `D j = 0`: digit `j` of
every exponent is zero. There are `retainedDimension A m = A ^ m - (A - 1) ^ m` of them, where
`A = 2 ^ (h * ℓ)`, out of `q ^ ℓ = A ^ m` points; by `HighRate.retainedDimension_rate` the
fraction tends to one as `m` grows.

Each retained monomial sums to zero on every affine line (`HighRate.sum_prod_digits_eq_zero`).
Rotating every exponent cyclically by `j + 1` digits moves the zero digit to the top, so each
rotated exponent is below `2 ^ (h * (m - 1))`, and with `ℓ ≤ 2 ^ h` coordinates their total is
below `q - 1`; the Frobenius twist `HighRate.sum_prod_add_mul_pow_eq_zero` applies. Removing the
term at the point itself, its value is the sum over the punctured line, since `-1 = 1` in
characteristic two. The retained monomials are distinct and reduced, hence linearly independent
(`FiniteField.linearIndependent_prod_pow`), so they span a line code with that many information
symbols (`LineCode.exists_card_info_eq_of_linearIndependent`).

Every codeword restricts on each line to a function of degree at most `q - 2`, so these codes are
subcodes of the lifted Reed–Solomon codes of [GuoKoppartySudan2013]; this is not formalized here.
The information set and the extension are chosen noncomputably; no efficient procedure for
finding them is claimed.

## Main results

* `Cslib.LineCode.HighRate.sum_prod_digits_eq_zero`: line sums of the retained monomials vanish.
* `Cslib.LineCode.HighRate.exists_lineCode`: the high-rate line code.

## References

* [A. Guo, S. Kopparty, M. Sudan, *New affine-invariant codes from lifting*][GuoKoppartySudan2013]
* Adapted from MassProduction/HighRate/Code.lean, MassProduction/HighRate/DigitMonomials.lean,
  MassProduction/HighRate/Residue.lean and MassProduction/HighRate/LineParity.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

public section

namespace Cslib.LineCode.HighRate

open Finset

variable {K : Type*} [Field K] [Fintype K] {ℓ : ℕ}

/-- Rotating an exponent `e < n ^ m` whose base-`n` digit `j` is zero by `j + 1` digits gives an
exponent below `n ^ (m - 1)`. -/
private theorem rotate_lt {n m j e : ℕ} (hj : j < m) (he : e < n ^ m)
    (hdigit : e / n ^ j % n = 0) :
    n ^ (m - (j + 1)) * (e % n ^ (j + 1)) + e / n ^ (j + 1) < n ^ (m - (j + 1)) * n ^ j := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn => by
    simp [hn, zero_pow (by omega : m ≠ 0)] at he
  have hlow : e % n ^ (j + 1) < n ^ j := by
    rw [Nat.mod_pow_succ, hdigit, mul_zero, add_zero]
    exact Nat.mod_lt _ (by positivity)
  have hhigh : e / n ^ (j + 1) < n ^ (m - (j + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.sub_add_cancel hj]
    exact he
  calc _ < n ^ (m - (j + 1)) * (e % n ^ (j + 1)) + n ^ (m - (j + 1)) := by omega
    _ = n ^ (m - (j + 1)) * (e % n ^ (j + 1) + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hlow

/-- If the digit matrix `D` has a zero column `j` and `ℓ ≤ n`, with `2 ≤ n`, the exponents it
encodes, rotated by `j + 1` base-`n` digits, have total below `n ^ m - 1`. -/
private theorem sum_rotate_lt {n m : ℕ} [NeZero n] (hn : 2 ≤ n) (hℓ : ℓ ≤ n)
    (D : Fin m → Fin ℓ → Fin n) {j : Fin m} (hj : D j = 0) :
    ∑ i, (n ^ (m - (j + 1 : ℕ)) * ((finFunctionFinEquiv fun k => D k i : ℕ) % n ^ (j + 1 : ℕ)) +
      (finFunctionFinEquiv fun k => D k i : ℕ) / n ^ (j + 1 : ℕ)) < n ^ m - 1 := by
  set R := n ^ (m - (j + 1 : ℕ)) * n ^ (j : ℕ) with hR_def
  have hterm (i : Fin ℓ) : n ^ (m - (j + 1 : ℕ)) * ((finFunctionFinEquiv fun k => D k i : ℕ) %
      n ^ (j + 1 : ℕ)) + (finFunctionFinEquiv fun k => D k i : ℕ) / n ^ (j + 1 : ℕ) ≤ R - 1 := by
    refine Nat.le_sub_one_of_lt (rotate_lt j.isLt (finFunctionFinEquiv _).isLt ?_)
    rw [← finFunctionFinEquiv_symm_apply_val, Equiv.symm_apply_apply, hj]
    rfl
  have hR : n * R = n ^ m := by
    rw [hR_def, ← mul_assoc, ← pow_succ', ← pow_add]
    congr 1
    omega
  have hnR := Nat.le_mul_of_pos_right n (show 0 < R by positivity)
  calc _ ≤ ∑ _i : Fin ℓ, (R - 1) := Finset.sum_le_sum fun i _ => hterm i
    _ = ℓ * (R - 1) := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    _ ≤ n * (R - 1) := Nat.mul_le_mul_right _ hℓ
    _ < n ^ m - 1 := by
      rw [← hR, Nat.mul_sub_one]
      omega

/-- **Line parity of the retained monomials.** Let `K` be a field of characteristic two with
`2 ^ (h * m)` elements and `ℓ ≤ 2 ^ h`. If the digit matrix `D : Fin m → Fin ℓ → Fin (2 ^ h)` has
a zero column, the monomial with exponents `e i = ∑ k, D k i * (2 ^ h) ^ k` sums to zero on every
affine line `x ↦ u + x • v`. -/
theorem sum_prod_digits_eq_zero [CharP K 2] {h m : ℕ} (hℓ : ℓ ≤ 2 ^ h)
    (hK : Fintype.card K = 2 ^ (h * m)) (D : Fin m → Fin ℓ → Fin (2 ^ h)) {j : Fin m}
    (hj : D j = 0) (u v : Fin ℓ → K) :
    ∑ x : K, ∏ i, (u i + x * v i) ^ (finFunctionFinEquiv fun k => D k i : ℕ) = 0 := by
  have hh : h ≠ 0 := by
    rintro rfl
    have := Fintype.one_lt_card (α := K)
    rw [hK, zero_mul, pow_zero] at this
    exact lt_irrefl 1 this
  apply sum_prod_add_mul_pow_eq_zero (r := h * (m - (j + 1 : ℕ))) (s := h * (j + 1 : ℕ))
  · rw [hK, ← mul_add, Nat.sub_add_cancel j.isLt]
  · simpa only [hK, pow_mul] using sum_rotate_lt (Nat.le_self_pow hh 2) hℓ D hj

/-- **High-rate line code.** Let `K` be a field of characteristic two with `2 ^ (h * m)`
elements and `ℓ ≤ 2 ^ h`. There is a line code on `K ^ ℓ` with exactly
`retainedDimension (2 ^ (h * ℓ)) m = 2 ^ (h * ℓ * m) - (2 ^ (h * ℓ) - 1) ^ m` information
symbols, out of `Fintype.card K ^ ℓ = 2 ^ (h * ℓ * m)` points. -/
theorem exists_lineCode [DecidableEq K] [CharP K 2] (h m : ℕ) (hℓ : ℓ ≤ 2 ^ h)
    (hK : Fintype.card K = 2 ^ (h * m)) :
    ∃ C : LineCode K ℓ, C.info.card = retainedDimension (2 ^ (h * ℓ)) m := by
  classical
  -- The retained monomials, indexed by digit matrices with a zero column.
  let e : {D : Fin m → Fin ℓ → Fin (2 ^ h) // ∃ j, D j = 0} → Fin ℓ → ℕ :=
    fun D i => finFunctionFinEquiv fun k => D.1 k i
  have he : Function.Injective e := fun D D' hD => Subtype.ext <| funext fun k => funext fun i =>
    congrFun (finFunctionFinEquiv.injective (Fin.ext (congrFun hD i))) k
  have hlt (D) (i) : e D i < Fintype.card K := by
    rw [hK, pow_mul]
    exact (finFunctionFinEquiv _).isLt
  obtain ⟨C, hC⟩ := exists_card_info_eq_of_linearIndependent
    (fun D (x : Fin ℓ → K) => ∏ i, x i ^ e D i) (FiniteField.linearIndependent_prod_pow e he hlt)
    fun D u v _ => by
      obtain ⟨j, hj⟩ := D.2
      have hline := sum_prod_digits_eq_zero hℓ hK D.1 hj u v
      rw [← Finset.add_sum_erase _ _ (mem_univ 0), CharTwo.add_eq_zero] at hline
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, add_zero] at hline ⊢
      exact hline.symm
  refine ⟨C, hC.trans ?_⟩
  rw [card_exists_eq_retainedDimension, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    pow_mul]

end Cslib.LineCode.HighRate
