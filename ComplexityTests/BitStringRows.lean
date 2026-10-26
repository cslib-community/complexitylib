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

-- The indexing rule needs no lower bound on the input length.
example (word : List Bool) (row : ℕ) :
    (BitString.listRow 3 row word).getD 2 false = word.getD (row * 3 + 2) false :=
  BitString.getD_listRow (by decide)

example : (BitString.listRow 3 0 [true]).getD 2 false = false := by
  rw [BitString.getD_listRow (by decide)]
  rfl

example : (BitString.listRow 2 3 [true]).getD 1 false = false := by
  rw [BitString.getD_listRow (by decide)]
  rfl

example (suffix : List Bool) :
    BitString.listRow 2 1 ([[true, false], [false, true]].flatten ++ suffix) = [false, true] :=
  BitString.listRow_flatMap_append (width := 2) id [[true, false], [false, true]]
    (by simp) suffix 1 (by decide)

-- Even a nonempty suffix does not become part of a zero-width row.
example (suffix : List Bool) : BitString.listRow 0 1 ([[], []].flatten ++ suffix) = [] :=
  BitString.listRow_flatMap_append (width := 0) id [[], []] (by simp) suffix 1 (by decide)

example (word : List Bool) : BitString.listRow 0 0 word = [] := by
  rw [BitString.listRow_zero]
  rfl

example : BitString.replaceRow 2 3 1 [true, false] [false, false, false, false, true, true] =
    [false, false, true, false, true, true] := by
  decide

example (Z : List Bool) :
    BitString.listRow 2 1 (BitString.replaceRow 2 3 1 [true, false] Z) = [true, false] := by
  simpa using BitString.listRow_replaceRow (j := 1) (x := [true, false]) rfl Z (i := 1) (by decide)

example (width count : ℕ) (j : Fin count) :
    (BitString.uniformList width).bind (fun x =>
      (BitString.uniformList (count * width)).map (BitString.replaceRow width count j.val x)) =
      BitString.uniformList (count * width) :=
  BitString.uniformList_replaceRow width count j

example {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 / (1 + (n : ℝ) * p) :=
  Real.one_sub_pow_le_one_div_one_add_mul hp₀ hp₁ n

-- Pointwise XOR cancellation and `uniformList` invariance under one-time-pad masking.
example :
    List.zipWith Bool.xor [true, false, true]
      (List.zipWith Bool.xor [true, false, true] [false, true, true]) =
      [false, true, true] :=
  BitString.zipWith_xor_self_left [true, false, true] [false, true, true] rfl

example :
    (BitString.uniformList 3).map (fun pad => List.zipWith Bool.xor pad [true, false, true]) =
      BitString.uniformList 3 :=
  BitString.uniformList_map_zipWith_xor [true, false, true]

example :
    ((BitString.uniformList 3).map
      (fun pad => List.zipWith Bool.xor pad [true, false, true])) [false, false, false] ≤
      (1 : ENNReal) / 2 ^ 3 := by
  rw [show (3 : ℕ) = [true, false, true].length from rfl,
    BitString.uniformList_map_zipWith_xor [true, false, true]]
  exact BitString.uniformList_apply_le 3 [false, false, false]

example :
    (BitString.uniformList 3).map
        (fun pad => List.zipWith Bool.xor (pad.take 3) [true, false, true]) =
      BitString.uniformList 3 :=
  BitString.uniformList_map_take_zipWith_xor rfl

-- Point-mass bound `1 / 2 ^ n`, finite-set union bound, and finite-cache lookup union bound.
example (r : List Bool) :
    BitString.uniformList 3 r ≤ (1 : ENNReal) / 2 ^ 3 :=
  BitString.uniformList_apply_le 3 r

example (s : Finset (List Bool)) :
    (BitString.uniformList 3).toOuterMeasure s ≤
      (s.card : ENNReal) * ((1 : ENNReal) / 2 ^ 3) :=
  BitString.toOuterMeasure_uniformList_finset_le 3 s

example (cache : List (List Bool × List Bool)) :
    (BitString.uniformList 3).toOuterMeasure {r | (cache.lookup r).isSome} ≤
      (cache.length : ENNReal) * ((1 : ENNReal) / 2 ^ 3) :=
  BitString.toOuterMeasure_lookup_uniformList_le 3 cache

end ComplexityTests.BitStringRows
