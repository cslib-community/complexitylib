/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.ZModTwo
public import CslibFrontier.Foundations.Data.Code.Linear
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Parity-check codes and binary linear codes

A *parity-check code* over a commutative ring `R` is the kernel
`Cslib.Code.parityCheckCode H = LinearMap.ker H.mulVecLin` of a parity-check matrix
`H : Matrix κ ι R` [MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. Over any finite
commutative ring (including `Bool` and `ZMod 2`), its cardinality is at least `|R| ^ (|ι| - |κ|)`
and its rate is at least `1 - |κ| / |ι|` (`pow_sub_le_card_parityCheckCode`,
`one_sub_card_div_card_le_rate_parityCheckCode`); over a field `F`, its dimension satisfies
`H.rank + finrank F (parityCheckCode H) = |ι|` (`finrank_parityCheckCode_add_rank`).

Shortening `parityCheckCode H` along an embedding `emb : κ' ↪ ι` yields
`parityCheckCode (H.submatrix id emb)` (`shortenLinear_parityCheckCode`). For binary parity-check
matrices `H : Matrix κ ι Bool`, the computable ring isomorphism `Cslib.BitString.bitEquiv`
transfers dimension, cardinality `2 ^ dim`, and rate from `ZMod 2`
(`card_parityCheckCode_bool_eq_two_pow_finrank`, `rate_parityCheckCode_bool`).

## Main definitions

* `Cslib.Code.parityCheckCode`: the kernel of `H.mulVecLin`.
* `Cslib.Code.syndrome`: the matrix-vector product `H *ᵥ x`.

## Main results

* `Cslib.Code.mem_parityCheckCode`, `Cslib.Code.mem_parityCheckCode_iff_forall_dotProduct`:
  membership characterizations.
* `Cslib.Code.pow_sub_le_card_parityCheckCode`,
  `Cslib.Code.one_sub_card_div_card_le_rate_parityCheckCode`,
  `Cslib.Code.finrank_parityCheckCode_add_rank`: rate and dimension bounds.
* `Cslib.Code.lt_minDist_parityCheckCode_iff`: minimum distance from minimum nonzero kernel weight.
* `Cslib.Code.shortenLinear_parityCheckCode`: shortening drops columns not in the retained image.
* `Cslib.Code.mem_parityCheckCode_zmodTwo_iff`,
  `Cslib.Code.card_parityCheckCode_bool_eq_two_pow_finrank`,
  `Cslib.Code.rate_parityCheckCode_bool`: binary `Bool` ↔ `ZMod 2` bridge.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

public section

namespace Cslib.Code

open Matrix

section CommRing

variable {κ ι R : Type*} [Fintype ι] [CommRing R]

/-- The parity-check code of `H : Matrix κ ι R`: the submodule of words `x` satisfying
`H *ᵥ x = 0`. -/
@[expose]
def parityCheckCode (H : Matrix κ ι R) : Submodule R (ι → R) :=
  LinearMap.ker H.mulVecLin

/-- The syndrome of `x` under parity-check matrix `H`. -/
def syndrome (H : Matrix κ ι R) (x : ι → R) : κ → R :=
  H *ᵥ x

/-- The syndrome of `x` under `H` is `H *ᵥ x`. -/
@[simp]
theorem syndrome_eq (H : Matrix κ ι R) (x : ι → R) : syndrome H x = H *ᵥ x := by
  rfl

/-- A word lies in `parityCheckCode H` iff its syndrome vanishes. -/
@[simp]
theorem mem_parityCheckCode {H : Matrix κ ι R} {x : ι → R} :
    x ∈ parityCheckCode H ↔ H *ᵥ x = 0 :=
  LinearMap.mem_ker

/-- A word lies in `parityCheckCode H` iff it is orthogonal to every row of `H`. -/
theorem mem_parityCheckCode_iff_forall_dotProduct {H : Matrix κ ι R} {x : ι → R} :
    x ∈ parityCheckCode H ↔ ∀ i, H i ⬝ᵥ x = 0 := by
  simp [mem_parityCheckCode, funext_iff, Matrix.mulVec]

/-- Over a finite commutative ring `R`, `|R| ^ |ι| ≤ |parityCheckCode H| * |R| ^ |κ|`. -/
theorem pow_card_le_card_parityCheckCode [Fintype κ] [Fintype R] (H : Matrix κ ι R) :
    Fintype.card R ^ Fintype.card ι ≤
      Nat.card (parityCheckCode H) * Fintype.card R ^ Fintype.card κ :=
  card_pow_le_card_ker_mul H.mulVecLin

/-- Over a finite commutative ring `R`, `|R| ^ (|ι| - |κ|) ≤ |parityCheckCode H|`. -/
theorem pow_sub_le_card_parityCheckCode [Fintype κ] [Fintype R] (H : Matrix κ ι R) :
    Fintype.card R ^ (Fintype.card ι - Fintype.card κ) ≤ Nat.card (parityCheckCode H) :=
  pow_sub_le_card_ker H.mulVecLin

/-- Over a finite nontrivial commutative ring `R`, `rate (parityCheckCode H) ≥ 1 - |κ| / |ι|`. -/
theorem one_sub_card_div_card_le_rate_parityCheckCode [Fintype κ] [Fintype R] [Nontrivial R]
    (hι : 0 < Fintype.card ι) (H : Matrix κ ι R) :
    1 - (Fintype.card κ : ℝ) / Fintype.card ι ≤ rate (parityCheckCode H : Set (ι → R)) :=
  one_sub_card_div_card_le_rate_ker hι H.mulVecLin

/-- The minimum distance of `parityCheckCode H` exceeds `r` iff every nonzero word in the kernel of
`H` has Hamming weight more than `r`. -/
theorem lt_minDist_parityCheckCode_iff [DecidableEq R] (H : Matrix κ ι R) {r : ℕ} :
    (r : ℕ∞) < minDist (parityCheckCode H : Set (ι → R)) ↔
      ∀ x : ι → R, x ≠ 0 → H *ᵥ x = 0 → r < hammingNorm x := by
  rw [← ENat.natCast_add_one_le_iff, le_minDist_iff_hammingNorm]
  simp only [ENat.natCast_add_one_le_iff, Nat.cast_lt, mem_parityCheckCode]
  exact forall_congr' fun _ => forall_comm

/-- Multiplying `H` by the zero-extension of `z` along `emb` equals multiplying the
column-restricted matrix `H.submatrix id emb` by `z`. -/
theorem mulVec_extend {κ' : Type*} [Fintype κ'] (H : Matrix κ ι R)
    (emb : κ' ↪ ι) (z : κ' → R) :
    H *ᵥ extend emb z = H.submatrix id emb *ᵥ z := by
  classical
  ext i
  simp only [Matrix.mulVec, dotProduct, extend_eq_sum, Finset.mul_sum, Matrix.submatrix_apply,
    id_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (emb j)]
  · simp
  · intro i' _ hi'
    simp [Ne.symm hi']
  · simp

/-- Shortening `parityCheckCode H` along `emb` gives `parityCheckCode (H.submatrix id emb)`. -/
theorem shortenLinear_parityCheckCode {κ' : Type*} [Fintype κ']
    (H : Matrix κ ι R) (emb : κ' ↪ ι) :
    shortenLinear (parityCheckCode H) emb = parityCheckCode (H.submatrix id emb) := by
  ext z
  simp [mem_parityCheckCode, mulVec_extend]

end CommRing

section Field

variable {κ ι F : Type*} [Fintype ι] [Field F]

/-- Over a field `F`, rank-nullity for `H : Matrix κ ι F`:
`H.rank + dim F (parityCheckCode H) = |ι|`. -/
theorem finrank_parityCheckCode_add_rank (H : Matrix κ ι F) :
    Matrix.rank H + Module.finrank F (parityCheckCode H) = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- Over a field `F` with finitely many checks `κ`,
`|ι| ≤ dim F (parityCheckCode H) + |κ|`. -/
theorem card_le_finrank_parityCheckCode_add [Fintype κ] (H : Matrix κ ι F) :
    Fintype.card ι ≤ Module.finrank F (parityCheckCode H) + Fintype.card κ := by
  have h1 := finrank_parityCheckCode_add_rank H
  have h2 := Matrix.rank_le_card_height H
  omega

end Field

section Binary

open Cslib.BitString

variable {κ ι : Type*} [Fintype ι]

/-- Membership in a Boolean parity-check code `parityCheckCode H` is equivalent to membership in the
corresponding `ZMod 2` parity-check code under `bitEquiv.symm`. -/
theorem mem_parityCheckCode_zmodTwo_iff (H : Matrix κ ι Bool) (x : ι → Bool) :
    (fun i => bitEquiv.symm (x i)) ∈ parityCheckCode (H.map bitEquiv.symm) ↔
      x ∈ parityCheckCode H := by
  simp only [mem_parityCheckCode_iff_forall_dotProduct, Matrix.map_apply, dotProduct]
  refine forall_congr' fun i => ?_
  have hmap : ∑ j : ι, bitEquiv.symm (H i j) * bitEquiv.symm (x j) =
      bitEquiv.symm (∑ j : ι, H i j * x j) := by
    simp only [map_sum, map_mul]
  rw [hmap]
  exact ⟨fun h => bitEquiv.symm.injective (h.trans bitEquiv.symm.map_zero.symm),
    fun h => by rw [h, bitEquiv.symm.map_zero]⟩

/-- A binary parity-check code `parityCheckCode H` (`Bool`) has cardinality `2 ^ dim` matching its
`ZMod 2` partner. -/
theorem card_parityCheckCode_bool_eq_two_pow_finrank (H : Matrix κ ι Bool) :
    Nat.card (parityCheckCode H) =
      2 ^ Module.finrank (ZMod 2) (parityCheckCode (H.map bitEquiv.symm)) := by
  let e : parityCheckCode H ≃ parityCheckCode (H.map bitEquiv.symm) :=
    { toFun := fun x => ⟨fun i => bitEquiv.symm (x.1 i),
        (mem_parityCheckCode_zmodTwo_iff H x.1).2 x.2⟩
      invFun := fun y => ⟨fun i => bitEquiv (y.1 i), by
        rw [← mem_parityCheckCode_zmodTwo_iff H]
        simpa only [RingEquiv.symm_apply_apply] using y.2⟩
      left_inv := fun x => Subtype.ext (funext fun i => bitEquiv.apply_symm_apply (x.1 i))
      right_inv := fun y => Subtype.ext (funext fun i => bitEquiv.symm_apply_apply (y.1 i)) }
  rw [Nat.card_congr e, card_linearCode_eq_pow_finrank, ZMod.card]

/-- The rate of a binary parity-check code `parityCheckCode H` equals its `ZMod 2` dimension
divided by `|ι|`. -/
theorem rate_parityCheckCode_bool (H : Matrix κ ι Bool) :
    rate (parityCheckCode H : Set (ι → Bool)) =
      Module.finrank (ZMod 2) (parityCheckCode (H.map bitEquiv.symm)) / Fintype.card ι := by
  have h1 : (Fintype.card Bool : ℝ) = 2 := by norm_num
  have hcard : Nat.card (parityCheckCode H : Set (ι → Bool)) = Nat.card (parityCheckCode H) := rfl
  rw [rate, h1, hcard, card_parityCheckCode_bool_eq_two_pow_finrank]
  push_cast
  rw [← Real.rpow_natCast (2 : ℝ), Real.logb_rpow (by norm_num) (by norm_num)]

end Binary

end Cslib.Code
