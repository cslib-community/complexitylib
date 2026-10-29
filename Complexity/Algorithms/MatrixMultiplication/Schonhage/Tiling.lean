/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Batch
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Layout
import Mathlib.Tactic.Ring

/-!
# Padding and tiling correctness

## Main results

* `nonempty_layout`: valid layouts exist whenever `m ≤ L`.
* `Full.bandArray_eq_mul`: product entries as `Full.result` values of band arrays.
* `outStrOfPos_injective`: positions in a tile have distinct output strings.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-! ### The numbers -/

/-- The square of the natural square root `K0 L m` is at most `K L m`. -/
theorem K0_sq_le_K (L m : ℕ) : K0 L m ^ 2 ≤ K L m :=
  Nat.sqrt_le' _

/-- The binomial count `K L m` is at most four times `K0 L m ^ 2`. -/
theorem K_le_four_mul_K0_sq (L m : ℕ) : K L m ≤ 4 * K0 L m ^ 2 := by
  have hlt : K L m < (K0 L m + 1) ^ 2 := Nat.lt_succ_sqrt' _
  rcases Nat.eq_zero_or_pos (K0 L m) with h0 | h0
  · rw [h0] at hlt ⊢
    omega
  · calc K L m ≤ (K0 L m + 1) ^ 2 := hlt.le
      _ ≤ (2 * K0 L m) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * K0 L m ^ 2 := by ring

/-- A band has at least one row. -/
theorem bandSize_pos {L m : ℕ} (hmL : m ≤ L) : 0 < bandSize L m :=
  Nat.mul_pos (K0_pos hmL) (N0_pos L m)

/-- The padded dimension is a multiple of the band size. -/
theorem bandSize_dvd_padN (L m N : ℕ) : bandSize L m ∣ padN L m N :=
  Dvd.intro_left _ rfl

/-- For `m ≤ L`, padding covers all `N` original positions. The parameter condition ensures a
positive band size. -/
theorem le_padN {L m : ℕ} (hmL : m ≤ L) (N : ℕ) : N ≤ padN L m N := by
  have h := Nat.lt_div_mul_add (a := N + bandSize L m - 1) (bandSize_pos hmL)
  unfold padN numBands
  omega

/-- For `m ≤ L`, the padded dimension is strictly less than `N + bandSize L m`, including `N =
0`. -/
theorem padN_lt_add_bandSize {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    padN L m N < N + bandSize L m := by
  have h := Nat.div_mul_le_self (N + bandSize L m - 1) (bandSize L m)
  have hb := bandSize_pos hmL
  unfold padN numBands
  omega

/-- If the band size is at most `N`, the padded dimension is at most `2 * N`. -/
theorem padN_le_two_mul (L m N : ℕ) (hN : K0 L m * N0 L m ≤ N) : padN L m N ≤ 2 * N := by
  rcases Nat.lt_or_ge L m with hLm | hmL
  · -- for `m > L` there are no subsets, `K₀ = 0`, and the padded size is 0
    have hK : K0 L m = 0 := by simp [K0, K, Nat.choose_eq_zero_of_lt hLm]
    simp [padN, bandSize, hK]
  · have h := padN_lt_add_bandSize hmL N
    have hN' : bandSize L m ≤ N := hN
    omega

/-- The number of tiles is the square of the number of bands. -/
theorem card_tiles (L m N : ℕ) : (tiles L m N).card = numBands L m N ^ 2 := by
  simp [tiles, sq]

/-- The tile count multiplied by `M L m` is at most `4 * padN L m N ^ 2`. The bound is stated
without division and requires no positivity hypothesis. -/
theorem card_tiles_mul_M_le (L m N : ℕ) : (tiles L m N).card * M L m ≤ 4 * padN L m N ^ 2 := by
  rw [card_tiles]
  calc numBands L m N ^ 2 * M L m
      = numBands L m N ^ 2 * N0 L m ^ 2 * K L m := by unfold M; ring
    _ ≤ numBands L m N ^ 2 * N0 L m ^ 2 * (4 * K0 L m ^ 2) :=
        Nat.mul_le_mul_left _ (K_le_four_mul_K0_sq L m)
    _ = 4 * padN L m N ^ 2 := by unfold padN bandSize; ring

/-! ### The table of subsets and the matrices of a tile -/

/-- Indexing data `Layout L m` exist for every `m ≤ L`, including `m = 0`. -/
theorem nonempty_layout {L m : ℕ} (hmL : m ≤ L) : Nonempty (Layout L m) := by
  have hcard : Fintype.card (Fin (K0 L m) × Fin (K0 L m))
      ≤ Fintype.card {Q : Finset (Fin L) // Q.card = m} := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype, card_subsets_eq_K, ← sq]
    exact K0_sq_le_K L m
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨{ hmL := hmL
           rowIdx := (Fintype.equivFinOfCardEq (card_outerStr L m)).symm
           colIdx := (Fintype.equivFinOfCardEq (card_outerStr L m)).symm
           innerIdx := (Fintype.equivFinOfCardEq (card_innerStr m)).symm
           table := fun gh => (e gh).1
           table_card := fun gh => (e gh).2
           table_injective := fun _ _ h => e.injective (Subtype.ext h) }⟩

/-- The subsets in the table are distinct, so a sum over the table that selects the subset of the
block product `gh` has one term. -/
private theorem sum_table_eq {L m : ℕ} {A : Type*} [AddCommMonoid A] (lay : Layout L m)
    (F : Fin (K0 L m) × Fin (K0 L m) → A) (gh : Fin (K0 L m) × Fin (K0 L m)) :
    (∑ gh', if lay.table gh' = lay.table gh then F gh' else 0) = F gh := by
  simp [lay.table_injective.eq_iff]

/-- At the table entry `(g, h)`, the left family selects row block `β * K0 L m + g`. -/
@[simp]
theorem bandFamilyL_table {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyL lay X β (lay.table (g, h)) = rowBlock lay X (β * K0 L m + g) :=
  sum_table_eq lay _ (g, h)

/-- The matrix `Y_Q` of the block product in position `(g, h)` is the `h`-th column block of the
column band. -/
@[simp]
theorem bandFamilyR_table {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β : ℕ)
    (g h : Fin (K0 L m)) :
    bandFamilyR lay Y β (lay.table (g, h)) = colBlock lay Y (β * K0 L m + h) :=
  sum_table_eq lay _ (g, h)

/-- The left family is zero at any level set outside the table image. -/
theorem bandFamilyL_eq_zero {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyL lay X β Q = 0 :=
  sum_eq_zero fun gh _ => ite_eq_right (hQ gh)

/-- The right family is zero at any level set outside the table image. -/
theorem bandFamilyR_eq_zero {L m N : ℕ} (lay : Layout L m) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (β : ℕ) {Q : Finset (Fin L)} (hQ : ∀ gh, lay.table gh ≠ Q) : bandFamilyR lay Y β Q = 0 :=
  sum_eq_zero fun gh _ => ite_eq_right (hQ gh)

/-! ### Product identities for tile arrays -/

/-- For the band arrays of tile `(β, β')`, `Full.result` at the output string for table entry
`(g, h)` equals the product entry of row block `β * K0 L m + g` and column block `β' * K0
L m + h`. -/
theorem Full.bandArray_eq_block_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (β β' : ℕ)
    (g h : Fin (K0 L m)) (r c : OuterStr L m) :
    Full.result L (bandArrayL lay X β) (bandArrayR lay Y β')
        (outStrOf (lay.table (g, h)) (lay.table_card (g, h)) r c)
      = (rowBlock lay X (β * K0 L m + g) * colBlock lay Y (β' * K0 L m + h)) r c := by
  rw [bandArrayL, bandArrayR, Full.arrays_eq_mul, bandFamilyL_table, bandFamilyR_table]

/-- A row (or column) is recovered from its band, the position of its block in the band and its
position in the block. -/
private theorem position_decomp {L m : ℕ} (lay : Layout L m) (I : ℕ) :
    (bandOf L m I * K0 L m + (blockOf lay I : ℕ)) * N0 L m + (offsetOf L m I : ℕ) = I := by
  have hband : bandOf L m I = I / N0 L m / K0 L m := by
    rw [bandOf, bandSize, Nat.mul_comm, Nat.div_div_eq_div_mul]
  have hblock : bandOf L m I * K0 L m + (blockOf lay I : ℕ) = I / N0 L m := by
    rw [hband]
    exact Nat.div_add_mod' _ _
  rw [hblock]
  exact Nat.div_add_mod' _ _

/-- The band arrays for the tile containing an original position `(I, J)` give `Full.result`
equal to `(X * Y) I J` at `outStrOfPos lay I J`. The matrices may have arbitrary signed
integer entries. -/
theorem Full.bandArray_eq_mul {L m N : ℕ} (lay : Layout L m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    Full.result L (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J)) (outStrOfPos
      lay I J)
      = (X * Y) I J := by
  unfold outStrOfPos
  rw [Full.bandArray_eq_block_mul, Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp lay.innerIdx]
  -- Both sides are sums over the `D` inner indices; the summands agree because row `I` is recovered
  -- from its band, block and place in the block, and likewise column `J`.
  refine sum_congr rfl fun k _ => ?_
  simp only [rowBlock, colBlock, Equiv.symm_apply_apply, position_decomp, padRows, padCols,
    I.isLt, J.isLt, dite_eq_left, Fin.eta]

/-- At the output string of an original position `(I, J)`, the bilinear product of its two
band arrays equals `(X * Y) I J`. -/
theorem bilinearProduct_bandArray_eq_mul {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin
  (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (I J : Fin N) :
    bilinearProduct (bandArrayL lay X (bandOf L m I)) (bandArrayR lay Y (bandOf L m J))
      (outStrOfPos lay I J)
      = (X * Y) I J := by
  rw [← Full.result_eq_bilinearProduct]
  exact Full.bandArray_eq_mul lay X Y I J

/-- For `m ≤ L`, any index `I < N` has band index below `numBands L m N`. -/
theorem bandOf_lt_numBands {L m : ℕ} (hmL : m ≤ L) (N I : ℕ) (hI : I < N) :
    bandOf L m I < numBands L m N := by
  rw [bandOf, Nat.div_lt_iff_lt_mul (bandSize_pos hmL)]
  exact hI.trans_le (le_padN hmL N)

/-! ### The output string of a position -/

/-- The inner set of a position's output string is the table entry indexed by its two
within-band block indices. -/
theorem innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    innerSetO (outStrOfPos lay I J) = lay.table (blockOf lay I, blockOf lay J) :=
  innerSetO_outStrOf _ _ _ _

/-- The inner set of the output string of a position has exactly `m` elements. -/
theorem card_innerSetO_outStrOfPos {L m : ℕ} (lay : Layout L m) (I J : ℕ) :
    (innerSetO (outStrOfPos lay I J)).card = m :=
  innerSetO_outStrOfPos lay I J ▸ lay.table_card _

/-- Within a fixed pair of row and column bands, equality of output strings implies equality
of both natural-number position indices. -/
theorem outStrOfPos_injective {L m : ℕ} (lay : Layout L m) (I J I' J' : ℕ)
    (hI : bandOf L m I = bandOf L m I') (hJ : bandOf L m J = bandOf L m J')
    (h : outStrOfPos lay I J = outStrOfPos lay I' J') : I = I' ∧ J = J' := by
  -- The two strings have the same inner set, row and column; so the two positions lie in the same
  -- block product and at the same place in it.
  obtain ⟨hQ, hr, hc⟩ := outStrOf_inj.mp h
  obtain ⟨hblockI, hblockJ⟩ := Prod.mk.inj (lay.table_injective hQ)
  constructor
  · rw [← position_decomp lay I, ← position_decomp lay I', hI, hblockI,
      lay.rowIdx.injective hr]
  · rw [← position_decomp lay J, ← position_decomp lay J', hJ, hblockJ,
      lay.colIdx.injective hc]

end Cslib.Algorithms.MatrixMultiplication.Schonhage
