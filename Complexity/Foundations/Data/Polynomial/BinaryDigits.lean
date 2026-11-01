/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Algebra/Polynomial`)

public import Complexity.Foundations.Data.Polynomial.CoeffList
public import Mathlib.Data.Nat.Size
import Complexity.Foundations.Data.Nat.Bits
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Binary digits as polynomial coefficients

`Polynomial.binaryDigits n` has the binary digits of `n` as its coefficients, starting with
the least significant bit. Evaluation at `2` recovers `n`; evaluation at `1` is at most the
binary length `n.size`. This separates a large integer's magnitude from the sizes of the
coefficients used in an exact polynomial computation.

For a polynomial over `ℕ`, every coefficient is at most its value at `1`. Consequently a
degree bound and a bound on this value give exact recovery from a list of coefficient residues.

## Main definitions

* `Polynomial.binaryDigits`: the polynomial of the binary digits of a natural number.

## Main results

* `Polynomial.eval_two_binaryDigits`: evaluation at `2` recovers the natural number.
* `Polynomial.eval_one_binaryDigits_le`: the coefficient sum is at most the binary length.
* `Polynomial.natDegree_binaryDigits_le`: the degree is at most the binary length less one.
* `Polynomial.coeff_le_eval_one`: a coefficient of a natural polynomial is at most its value at `1`.
* `Polynomial.ofCoeffList_coeffsBelow_mod`: recovery from bounded coefficient residues.
-/

public section

namespace Polynomial

/-- The polynomial whose coefficients are the binary digits of `n`, least significant first. -/
@[expose] noncomputable def binaryDigits (n : ℕ) : ℕ[X] := ofCoeffList (n.bits.map Bool.toNat)

/-- Evaluating the binary-digit polynomial at `2` recovers the natural number. -/
@[simp] theorem eval_two_binaryDigits (n : ℕ) : (binaryDigits n).eval 2 = n := by
  have h (bs : List Bool) : evalCoeffList 2 (bs.map Bool.toNat) = bs.foldr Nat.bit 0 := by
    induction bs with
    | nil => rfl
    | cons b bs ih =>
      rw [List.map_cons, evalCoeffList_cons, List.foldr_cons, ih, Nat.bit_val, Nat.add_comm]
  rw [binaryDigits, eval_ofCoeffList, h, Nat.foldr_bit_bits]

/-- The sum of the binary digits is at most the binary length. -/
theorem eval_one_binaryDigits_le (n : ℕ) : (binaryDigits n).eval 1 ≤ n.size := by
  have h (bs : List Bool) : evalCoeffList 1 (bs.map Bool.toNat) ≤ bs.length := by
    induction bs with
    | nil => exact Nat.zero_le _
    | cons b bs ih =>
      rw [List.map_cons, evalCoeffList_cons, one_mul, List.length_cons]
      cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  simpa only [binaryDigits, eval_ofCoeffList, Nat.size_eq_bits_len] using h n.bits

/-- The binary-digit polynomial has degree at most the binary length less one. -/
theorem natDegree_binaryDigits_le (n : ℕ) : (binaryDigits n).natDegree ≤ n.size - 1 := by
  simpa only [binaryDigits, List.length_map, Nat.size_eq_bits_len] using
    natDegree_ofCoeffList_le (n.bits.map Bool.toNat)

/-- A coefficient of a polynomial over the natural numbers is at most the sum of its
coefficients, its value at `1`. -/
theorem coeff_le_eval_one (p : ℕ[X]) (i : ℕ) : p.coeff i ≤ p.eval 1 := by
  rw [eval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
  simp only [one_pow, mul_one]
  by_cases hi : i ≤ p.natDegree
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  · rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hi)]
    exact Nat.zero_le _

/-- A polynomial over the natural numbers is recovered from the residues of sufficiently
many low coefficients when its coefficient sum is below the modulus. -/
theorem ofCoeffList_coeffsBelow_mod {p : ℕ[X]} {ℓ M : ℕ} (hdeg : p.natDegree < ℓ)
    (hM : p.eval 1 < M) :
    ofCoeffList ((List.range ℓ).map fun i => p.coeff i % M) = p := by
  have hlist : (List.range ℓ).map (fun i => p.coeff i % M) = p.coeffsBelow ℓ := by
    exact List.map_congr_left fun i _ => Nat.mod_eq_of_lt ((coeff_le_eval_one p i).trans_lt hM)
  rw [hlist, ofCoeffList_coeffsBelow hdeg]

end Polynomial
