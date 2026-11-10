/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Functions
public import CslibFrontier.Computability.Communication.Rank
public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix

/-!
# The rank of the inner-product matrix

The sign matrix `H` of the inner product modulo two of bit strings indexed by `ι`, with entry
`(-1) ^ (x ⬝ᵥ y)` at `x` and `y`, is a Hadamard matrix: `H H = 2 ^ |ι| I`
(`signMatrix_dotProduct_mul_self`), by character orthogonality
`∑_y (-1) ^ (w ⬝ᵥ y) = 2 ^ |ι| [w = 0]` (`BitString.sum_ite_dotProduct`); as `H` is symmetric
with entries `±1`, it is a Hadamard matrix in the sense of Mathlib's `Matrix.IsHadamard`
(`isHadamard_signMatrix_dotProduct`). So over a field in which `2` is invertible it has full rank
`2 ^ |ι|` (`rank_signMatrix_dotProduct`), and the `0/1` communication matrix of the inner product,
whose rank differs from that of `H` by at most one and which has a zero row, has rank exactly
`2 ^ |ι| - 1` (`rank_communicationMatrix_dotProduct`)
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997].

By the rank bound, a protocol computing the inner product has at least `2 ^ |ι| - 1` leaves
labelled `true` (`two_pow_sub_one_le_card_true_leaves_of_run_eq_dotProduct`). The area bound
`|A| |B| ≤ 2 ^ |ι|` for rectangles on which the inner product is constant, from which
`two_pow_lt_leafCount_of_run_eq_dotProduct` follows, gives only about half as many.

## Main results

* `Cslib.Communication.signMatrix_dotProduct_mul_self`,
  `Cslib.Communication.isHadamard_signMatrix_dotProduct`: the sign matrix of the inner product is a
  Hadamard matrix.
* `Cslib.Communication.rank_signMatrix_dotProduct`: it has full rank.
* `Cslib.Communication.rank_communicationMatrix_dotProduct`: the communication matrix of the inner
  product has rank `2 ^ |ι| - 1`.
* `Cslib.Communication.two_pow_sub_one_le_card_true_leaves_of_run_eq_dotProduct`: a protocol
  computing the inner product has at least `2 ^ |ι| - 1` leaves labelled `true`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

public section

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace Cslib.Communication

/-- The square of the sign matrix of the inner product is `2 ^ |ι|` times the identity. -/
theorem signMatrix_dotProduct_mul_self (R : Type*) [Ring R] :
    signMatrix R (fun x y : ι → Bool => x ⬝ᵥ y) * signMatrix R (fun x y : ι → Bool => x ⬝ᵥ y) =
      (2 ^ Fintype.card ι : R) • 1 := by
  ext x x'
  simp only [Matrix.mul_apply, signMatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  have hterm (y : ι → Bool) :
      ((if x ⬝ᵥ y then (-1 : R) else 1) * if y ⬝ᵥ x' then -1 else 1) =
        if (x + x') ⬝ᵥ y then -1 else 1 := by
    rw [add_dotProduct, dotProduct_comm y x']
    cases x ⬝ᵥ y <;> cases x' ⬝ᵥ y <;> simp [Bool.add_eq_xor]
  rw [Fintype.sum_congr _ _ hterm, BitString.sum_ite_dotProduct]
  by_cases hxx : x = x'
  · subst hxx
    simp
  · have : x + x' ≠ 0 := fun h => hxx (by simpa using congrArg (· + x') h)
    simp [hxx, this]

/-- **The sign matrix of the inner product is a Hadamard matrix** in the sense of
`Matrix.IsHadamard`: its entries `±1` are unitary, and it is symmetric with square `2 ^ |ι|` times
the identity. -/
theorem isHadamard_signMatrix_dotProduct (R : Type*) [Ring R] [StarRing R] :
    (signMatrix R fun x y : ι → Bool => x ⬝ᵥ y).IsHadamard := by
  have hstar : (signMatrix R fun x y : ι → Bool => x ⬝ᵥ y).conjTranspose =
      signMatrix R fun x y => x ⬝ᵥ y := by
    ext x y
    rw [Matrix.conjTranspose_apply, signMatrix_apply, signMatrix_apply, dotProduct_comm]
    split_ifs <;> simp
  have hcard : ((Fintype.card (ι → Bool) : ℕ) : R) = 2 ^ Fintype.card ι := by
    simp
  refine ⟨fun x y => ?_, ?_, ?_⟩
  · rw [signMatrix_apply]
    split_ifs <;> simp [Unitary.mem_iff]
  all_goals rw [hstar, signMatrix_dotProduct_mul_self, hcard]

variable {R : Type*} [Field R] [NeZero (2 : R)]

/-- Over a field in which `2` is invertible, the sign matrix of the inner product on bit strings
indexed by `ι` has full rank `2 ^ |ι|`. -/
theorem rank_signMatrix_dotProduct :
    (signMatrix R fun x y : ι → Bool => x ⬝ᵥ y).rank = 2 ^ Fintype.card ι := by
  set H := signMatrix R fun x y : ι → Bool => x ⬝ᵥ y
  have hunit : IsUnit H := by
    rw [Matrix.isUnit_iff_isUnit_det]
    refine Matrix.isUnit_det_of_right_inverse (B := ((2 : R) ^ Fintype.card ι)⁻¹ • H) ?_
    rw [Matrix.mul_smul, signMatrix_dotProduct_mul_self, smul_smul,
      inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), one_smul]
  rw [Matrix.rank_of_isUnit H hunit, Fintype.card_fun, Fintype.card_bool]

/-- **The rank of the inner-product matrix**
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]: over a field in which `2` is
invertible, such as `ℚ` or `ℝ`, the communication matrix of the inner product modulo two on bit
strings indexed by `ι` has rank `2 ^ |ι| - 1`. -/
theorem rank_communicationMatrix_dotProduct :
    (communicationMatrix R fun x y : ι → Bool => x ⬝ᵥ y).rank = 2 ^ Fintype.card ι - 1 := by
  set M := communicationMatrix R fun x y : ι → Bool => x ⬝ᵥ y
  refine le_antisymm ?_ ?_
  · -- The row of `0` vanishes, so `M` factors through the other `2 ^ |ι| - 1` rows.
    let E : Matrix (ι → Bool) {x : ι → Bool // x ≠ 0} R :=
      Matrix.of fun x j => if x = j.1 then 1 else 0
    let N : Matrix {x : ι → Bool // x ≠ 0} (ι → Bool) R := Matrix.of fun j y => M j.1 y
    have hEN : M = E * N := by
      ext x y
      simp only [Matrix.mul_apply, E, N, Matrix.of_apply, ite_mul, one_mul, zero_mul]
      by_cases hx : x = 0
      · subst hx
        rw [sum_eq_zero fun j _ => ite_eq_right fun h => j.2 h.symm]
        simp [M, zero_dotProduct]
      · rw [Fintype.sum_eq_single ⟨x, hx⟩ fun j hj => ite_eq_right fun h => hj (Subtype.ext h.symm)]
        simp
    rw [hEN]
    refine (Matrix.rank_mul_le_left E N).trans ((Matrix.rank_le_card_width E).trans_eq ?_)
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun, Fintype.card_bool]
  · have h : (signMatrix R fun x y : ι → Bool => x ⬝ᵥ y).rank ≤ M.rank + 1 :=
      rank_signMatrix_le _
    rw [rank_signMatrix_dotProduct] at h
    omega

omit [DecidableEq ι] in
/-- **A protocol computing the inner product has at least `2 ^ |ι| - 1` leaves labelled
`true`**, by the rank bound and `rank_communicationMatrix_dotProduct`. -/
theorem two_pow_sub_one_le_card_true_leaves_of_run_eq_dotProduct
    {p : Protocol (ι → Bool) (ι → Bool) Bool} (hp : p.run = fun x y => x ⬝ᵥ y) :
    2 ^ Fintype.card ι - 1 ≤ #{i | p.leafOutput i = true} := by
  classical
  have h := Protocol.rank_communicationMatrix_le (R := ℚ) hp
  rwa [rank_communicationMatrix_dotProduct] at h

end Cslib.Communication
