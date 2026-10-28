/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Parameters

/-!
# Finite thin-product correctness and cardinality bounds

## Main results

* `thin_product_spec`: exact queried entries for arbitrary signed integer matrices.
* `encodings_total_le`, `total_leaves_le`, `total_passed_sets_le`: explicit finite totals.

Correctness holds for arbitrary signed integer matrices and any layout. For `D = 4^m`,
`L = 19m`, `D^18 ≤ N` and `W.card * 2^m ≤ N²`, the encoding entry count is at most
`4 * D^(-1/18) * N²`, the sum of contributing-leaf cardinalities is at most
`33 * D^(-1/18) * N²`, and the sum of passed request-set cardinalities is at most
`(19m + 1) * 33 * D^(-1/18) * N²`. Here `N` is the original matrix dimension.
The definitions permit zero parameters and empty request sets; the bounds retain their
stated size and sparsity hypotheses. No native program or instruction bound is proved.

## References

Adapted selectively from [AlmanWilliams2026, Section 2] and
[Anthropic's pinned formal source](https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec2).
Source pin: `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. These are finite mathematical
counts and identities; they give no native program or instruction-cost certificate.
-/

@[expose] public section

open Finset

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- For `m ≤ L`, the band pair of any position `(I, J) : Fin N × Fin N` belongs to the finite
tile set. -/
theorem tile_mem_tiles {L m N : ℕ} (hmL : m ≤ L) (I J : Fin N) :
    (bandOf L m I, bandOf L m J) ∈ tiles L m N :=
  mem_product.mpr ⟨mem_range.mpr (bandOf_lt_numBands hmL N I I.2),
    mem_range.mpr (bandOf_lt_numBands hmL N J J.2)⟩

/-- A requested position contributes its output string to `wantedStrings` for its band pair. -/
theorem outStrOfPos_mem_wantedStrings {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N))
    {I J : Fin N} (hIJ : (I, J) ∈ W) :
    outStrOfPos lay I J ∈ wantedStrings lay W (bandOf L m I) (bandOf L m J) :=
  mem_image.mpr ⟨(I, J), mem_filter.mpr ⟨hIJ, rfl, rfl⟩, rfl⟩

/-- Every string requested in a tile has exactly `m` inner positions. -/
theorem card_innerSetO_of_mem_wantedStrings {L m N : ℕ} (lay : Layout L m)
    (W : Finset (Fin N × Fin N)) (β β' : ℕ) (w : OutStr L) (hw : w ∈ wantedStrings lay W β β') :
    (innerSetO w).card = m := by
  obtain ⟨IJ, -, rfl⟩ := mem_image.mp hw
  exact card_innerSetO_outStrOfPos lay IJ.1 IJ.2

/-- For arbitrary signed integer matrices of shapes `N × D m` and `D m × N`, the pruned result
at any position in `W` equals the corresponding entry of `X * Y`. The encodings and
request set are those for that position's row and column bands. This holds for every
`Layout L m`, which includes `m ≤ L`, without the size or sparsity conditions used in the
counting bounds (cf. [AlmanWilliams2026, Theorem 5]). -/
theorem thin_product_spec {L m N : ℕ} (lay : Layout L m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (W : Finset (Fin N × Fin N)) (I J : Fin N)
    (hIJ : (I, J) ∈ W) :
    Pruned.result L (encodingL (bandArrayL lay X (bandOf L m I)))
        (encodingR (bandArrayR lay Y (bandOf L m J)))
        (wantedStrings lay W (bandOf L m I) (bandOf L m J)) (outStrOfPos lay I J)
      = (X * Y) I J := by
  -- Lemma 10, with Lemma 7: `Pruned` returns the output of `Full` restricted to the set passed to
  -- it.
  rw [Pruned.result_eq_piecewise_full, Finset.piecewise_eq_of_mem _ _ _
    (outStrOfPos_mem_wantedStrings lay W hIJ)]
  -- Lemma 9, through the tiling of Section 2.3.4.
  exact Full.bandArray_eq_mul lay X Y I J

/-- The real inequality `w ≤ N² / sqrt (D m)` is equivalent to the natural-number inequality
`w * 2 ^ m ≤ N ^ 2`, including `m = 0`. -/
theorem le_sq_div_sqrt_D_iff (m N w : ℕ) :
    (w : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt (D m) ↔ w * 2 ^ m ≤ N ^ 2 := by
  rw [← two_pow_eq_sqrt_D, le_div_iff₀ (by positivity)]
  exact_mod_cast Iff.rfl

/-- The number of bands times `N₀` is at most the padded size, because `K₀ ≥ 1`. -/
private theorem numBands_mul_N0_le {L m : ℕ} (hmL : m ≤ L) (N : ℕ) :
    numBands L m N * N0 L m ≤ padN L m N :=
  Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (K0_pos hmL))

/-- At `L = 19 * m` with `D m ^ 18 ≤ N`, the encodings of all row-band and column-band arrays
have at most `4 * D^(-1/18) * N²` entries in total, where `D = D m`. The counted quantity
is `2 * numBands L m N * 10 ^ L`, and `N` is the original dimension. This is an entry
count, not a bound on instructions or encoding time. -/
theorem encodings_total_le (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    ((2 * numBands (19 * m) m N * 10 ^ (19 * m) : ℕ) : ℝ)
      ≤ 4 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  have hbands : (numBands (19 * m) m N : ℝ) * N0 (19 * m) m ≤ 2 * N := by
    exact_mod_cast (numBands_mul_N0_le (by omega) N).trans (padN_le_two_mul_of_D_pow_le m N hN)
  have heq6 : (10 : ℝ) ^ (19 * m) ≤ saving m * N * N0 (19 * m) m := encoding_size_le m N hN
  have hc := saving_pos m
  rw [← saving_eq_D_rpow]
  push_cast
  calc 2 * (numBands (19 * m) m N : ℝ) * 10 ^ (19 * m)
      ≤ 2 * numBands (19 * m) m N * (saving m * N * N0 (19 * m) m) := by gcongr
    _ = 2 * saving m * (N * (numBands (19 * m) m N * N0 (19 * m) m)) := by ring
    _ ≤ 2 * saving m * (N * (2 * N)) := by gcongr
    _ = 4 * saving m * (N : ℝ) ^ 2 := by ring

/-- Summing the cardinalities of the requested-string sets over all tiles gives at most
`W.card`. -/
theorem sum_card_wantedStrings_le {L m N : ℕ} (lay : Layout L m) (W : Finset (Fin N × Fin N)) :
    ∑ T ∈ tiles L m N, (wantedStrings lay W T.1 T.2).card ≤ W.card := by
  have hmap : ∀ IJ ∈ W, (bandOf L m IJ.1, bandOf L m IJ.2) ∈ tiles L m N := fun IJ _ =>
    tile_mem_tiles lay.hmL IJ.1 IJ.2
  rw [card_eq_sum_card_fiberwise hmap]
  refine sum_le_sum fun T _ => ?_
  refine card_image_le.trans (le_of_eq ?_)
  congr 1

/-- The sum of `M L m` over the finite tile set is at most `4 * padN L m N ^ 2`. -/
theorem sum_M_le (L m N : ℕ) : ∑ _T ∈ tiles L m N, M L m ≤ 4 * padN L m N ^ 2 := by
  rw [sum_const, smul_eq_mul]
  exact card_tiles_mul_M_le L m N

/-- At `L = 19 * m`, bound the sum of contributing-leaf cardinalities for the tile request
sets by `saving m * (2 ^ m * W.card + 2 * ∑ T ∈ tiles L m N, M L m)`. A leaf used in
distinct tiles is counted once for each such tile. -/
theorem sum_card_leaves_le {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N)) :
    ((∑ T ∈ tiles (19 * m) m N, (leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ saving m * ((2 : ℝ) ^ m * (W.card : ℝ)
          + 2 * ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ)) := by
  have hc := saving_pos m
  have hsum : ((∑ T ∈ tiles (19 * m) m N, (wantedStrings lay W T.1 T.2).card : ℕ) : ℝ)
      ≤ (W.card : ℝ) := by
    exact_mod_cast sum_card_wantedStrings_le lay W
  push_cast at hsum ⊢
  calc ∑ T ∈ tiles (19 * m) m N, ((leaves (wantedStrings lay W T.1 T.2)).card : ℝ)
      ≤ ∑ T ∈ tiles (19 * m) m N, saving m
          * ((2 : ℝ) ^ m * ((wantedStrings lay W T.1 T.2).card : ℝ) + 2 * (M (19 * m) m : ℝ)) :=
        sum_le_sum fun T _ =>
          card_leaves_le_saving _ (card_innerSetO_of_mem_wantedStrings lay W T.1 T.2)
    _ = saving m
          * ((2 : ℝ) ^ m * ∑ T ∈ tiles (19 * m) m N, ((wantedStrings lay W T.1 T.2).card : ℝ)
              + 2 * ∑ _T ∈ tiles (19 * m) m N, (M (19 * m) m : ℝ)) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum, ← mul_sum]
    _ ≤ _ := by gcongr

/-- At `L = 19 * m`, assume `D m ^ 18 ≤ N` and `W.card * 2 ^ m ≤ N ^ 2`. The sum of
contributing-leaf cardinalities over all tiles is then at most `33 * D^(-1/18) * N²`,
where `D = D m` and `N` is the original dimension. This counts leaves with their tile
multiplicities, not executed instructions. -/
theorem total_leaves_le {m N : ℕ} (lay : Layout (19 * m) m) (W : Finset (Fin N × Fin N))
    (hN : D m ^ 18 ≤ N) (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((∑ T ∈ tiles (19 * m) m N, (leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ)
      ≤ 33 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2 := by
  have hc := saving_pos m
  have hWN : (2 : ℝ) ^ m * (W.card : ℝ) ≤ (N : ℝ) ^ 2 := by
    rw [mul_comm]
    exact_mod_cast hW
  have hM : ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ) ≤ 16 * (N : ℝ) ^ 2 := by
    have hpad := Nat.pow_le_pow_left (padN_le_two_mul_of_D_pow_le m N hN) 2
    exact_mod_cast (sum_M_le (19 * m) m N).trans (by linarith)
  refine (sum_card_leaves_le lay W).trans ?_
  rw [← saving_eq_D_rpow]
  calc saving m
          * ((2 : ℝ) ^ m * (W.card : ℝ) + 2 * ((∑ _T ∈ tiles (19 * m) m N, M (19 * m) m : ℕ) : ℝ))
      ≤ saving m * ((N : ℝ) ^ 2 + 2 * (16 * (N : ℝ) ^ 2)) := by gcongr
    _ = 33 * saving m * (N : ℝ) ^ 2 := by ring

/-- Lemma 10 summed over the tiles: the total size of the sets handled by the pruned recursions is
at most `L + 1` times the total number of leaves. -/
private theorem sum_totalSize_le {m N : ℕ} (lay : Layout (19 * m) m)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (W : Finset (Fin N × Fin N)) :
    ((∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2) : ℕ) : ℝ)
      ≤ ((19 * m + 1 : ℕ) : ℝ)
        * ((∑ T ∈ tiles (19 * m) m N, (leaves (wantedStrings lay W T.1 T.2)).card : ℕ) : ℝ) := by
  have h : ∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2)
      ≤ (19 * m + 1) * ∑ T ∈ tiles (19 * m) m N, (leaves (wantedStrings lay W T.1 T.2)).card := by
    rw [mul_sum]
    exact sum_le_sum fun T _ => Pruned.totalSize_le _ _ _
  exact_mod_cast h

/-- At `L = 19 * m`, assume `D m ^ 18 ≤ N` and `W.card * 2 ^ m ≤ N ^ 2`. Summing
`Pruned.totalSize` over all tiles gives at most `(19 * m + 1) * (33 * D^(-1/18) * N²)`,
where `D = D m` and `N` is the original dimension. The quantity sums request-set
cardinalities through the pruned recursions; it is not an instruction count. -/
theorem total_passed_sets_le {m N : ℕ} (lay : Layout (19 * m) m) (X : Matrix (Fin N) (Fin (D m)) ℤ)
    (Y : Matrix (Fin (D m)) (Fin N) ℤ) (W : Finset (Fin N × Fin N)) (hN : D m ^ 18 ≤ N)
    (hW : W.card * 2 ^ m ≤ N ^ 2) :
    ((∑ T ∈ tiles (19 * m) m N,
        Pruned.totalSize (encodingL (bandArrayL lay X T.1)) (encodingR (bandArrayR lay Y T.2))
          (wantedStrings lay W T.1 T.2) : ℕ) : ℝ)
      ≤ ((19 * m + 1 : ℕ) : ℝ) * (33 * (D m : ℝ) ^ (-(1 / 18 : ℝ)) * (N : ℝ) ^ 2) :=
  (sum_totalSize_le lay X Y W).trans
    (mul_le_mul_of_nonneg_left (total_leaves_le lay W hN hW) (Nat.cast_nonneg _))

end Cslib.Algorithms.MatrixMultiplication.Schonhage
