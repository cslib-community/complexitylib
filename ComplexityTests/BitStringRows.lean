/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.BernoulliInequality
import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Probability.BitString.List
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event

/-! # Clients of the padded-row API

Short words retain false padding, suffixes cannot change existing rows, and zero-width rows
remain empty. The old public crypto name still has its original statement.
-/

namespace ComplexityTests.BitStringRows

open Cslib

-- Row indexing, zero-padding on short words, suffix invariance for `listRow_flatMap_append`,
-- zero-width rows, and row replacement (`replaceRow` and `uniformList_replaceRow`).
example (word suffix Z : List Bool) (row : ℕ) :
    (BitString.listRow 3 row word).getD 2 false = word.getD (row * 3 + 2) false ∧
      (BitString.listRow 3 0 [true]).getD 2 false = false ∧
      (BitString.listRow 2 3 [true]).getD 1 false = false ∧
      BitString.listRow 2 1 ([[true, false], [false, true]].flatten ++ suffix) = [false, true] ∧
      BitString.listRow 0 1 ([[], []].flatten ++ suffix) = [] ∧
      BitString.listRow 0 0 word = [] ∧
      BitString.replaceRow 2 3 1 [true, false] [false, false, false, false, true, true] =
        [false, false, true, false, true, true] ∧
      BitString.listRow 2 1 (BitString.replaceRow 2 3 1 [true, false] Z) = [true, false] ∧
      (BitString.uniformList 2).bind (fun x =>
        (BitString.uniformList (3 * 2)).map (BitString.replaceRow 2 3 (1 : Fin 3).val x)) =
        BitString.uniformList (3 * 2) ∧
      (1 - (1 / 2 : ℝ)) ^ 4 ≤ 1 / (1 + (4 : ℝ) * (1 / 2)) :=
  ⟨BitString.getD_listRow (by decide),
    by rw [BitString.getD_listRow (by decide)]; rfl,
    by rw [BitString.getD_listRow (by decide)]; rfl,
    BitString.listRow_flatMap_append (width := 2) id [[true, false], [false, true]]
      (by simp) suffix 1 (by decide),
    BitString.listRow_flatMap_append (width := 0) id [[], []] (by simp) suffix 1 (by decide),
    by rw [BitString.listRow_zero]; rfl,
    by decide,
    by simpa using
      BitString.listRow_replaceRow (j := 1) (x := [true, false]) rfl Z (i := 1) (by decide),
    BitString.uniformList_replaceRow 2 3 1,
    Real.one_sub_pow_le_one_div_one_add_mul (by norm_num) (by norm_num) 4⟩

-- Pointwise XOR cancellation, `uniformList` invariance under one-time-pad masking, point-mass
-- bound `1 / 2 ^ n`, finite-set union bound, and finite-cache lookup union bound.
example :
    List.zipWith Bool.xor [true, false, true]
        (List.zipWith Bool.xor [true, false, true] [false, true, true]) =
      [false, true, true] ∧
    (BitString.uniformList 3).map (fun pad => List.zipWith Bool.xor pad [true, false, true]) =
      BitString.uniformList 3 ∧
    ((BitString.uniformList 3).map
        (fun pad => List.zipWith Bool.xor pad [true, false, true])) [false, false, false] ≤
      (1 : ENNReal) / 2 ^ 3 ∧
    (BitString.uniformList 3).map
        (fun pad => List.zipWith Bool.xor (pad.take 3) [true, false, true]) =
      BitString.uniformList 3 ∧
    BitString.uniformList 3 [true, false, true] ≤ (1 : ENNReal) / 2 ^ 3 ∧
    (BitString.uniformList 3).toOuterMeasure ({[true, false, true], [false, true, false]} :
        Finset (List Bool)) ≤
      (({[true, false, true], [false, true, false]} : Finset (List Bool)).card : ENNReal) *
        ((1 : ENNReal) / 2 ^ 3) ∧
    (BitString.uniformList 3).toOuterMeasure
        {r | ([([true, false, true], [false])] : List (List Bool × List Bool)).lookup r |>.isSome} ≤
      (([([true, false, true], [false])] : List (List Bool × List Bool)).length : ENNReal) *
        ((1 : ENNReal) / 2 ^ 3) :=
  ⟨BitString.zipWith_xor_self_left [true, false, true] [false, true, true] rfl,
    BitString.uniformList_map_zipWith_xor [true, false, true],
    by rw [show (3 : ℕ) = [true, false, true].length from rfl,
         BitString.uniformList_map_zipWith_xor [true, false, true]]
       exact BitString.uniformList_apply_le 3 [false, false, false],
    BitString.uniformList_map_take_zipWith_xor rfl,
    BitString.uniformList_apply_le 3 [true, false, true],
    BitString.toOuterMeasure_uniformList_finset_le 3 {[true, false, true], [false, true, false]},
    BitString.toOuterMeasure_lookup_uniformList_le 3 [([true, false, true], [false])]⟩

end ComplexityTests.BitStringRows
