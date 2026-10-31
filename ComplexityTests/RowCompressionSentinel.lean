/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression.Sentinel
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Exact sentinel compression examples

Replacing the first entry `1000000` by `100` preserves a third rank and size threshold exactly
at their ceiling `2`. The old default is positive. Compression changes smaller signed entries,
while the marked entry's negative second coordinate `-17` is unchanged in both calculations.
Further cases check zero padding and why changing values exactly at the ceiling is excluded.
-/

namespace ComplexityTests.RowCompressionSentinel

open Finset Cslib.RowCompression

private def original : Fin 4 → Fin 2 → ℝ := ![![1000000, -17], ![4, 0], ![2, -1], ![-1, 1]]

private noncomputable def modified : Fin 4 → Fin 2 → ℝ := sentinelFirst {0} 100 original

private theorem modified_rank : firstRank univ 3 (1 / 2) modified = 2 := by
  norm_num [firstRank, kthLargest, modified, original, sentinelFirst, Fin.univ_succ,
    filter_insert, filter_singleton]

private theorem modified_threshold : threshold univ 3 1 (1 / 2) modified = 2 := by
  norm_num [threshold, kthLargest, entrySize, modified, original, sentinelFirst, Fin.univ_succ,
    filter_insert, filter_singleton]

private theorem marked_high : ∀ y ∈ (univ : Finset (Fin 4)), y ∈ ({0} : Finset (Fin 4)) →
    (3 : ℝ) * 2 < original y 0 := by
  intro y _ hy
  have hy0 : y = 0 := mem_singleton.mp hy
  subst y
  norm_num [original]

private theorem marked_above : ∀ y ∈ (univ : Finset (Fin 4)), y ∈ ({0} : Finset (Fin 4)) →
    (2 : ℝ) < original y 0 := by
  intro y _ hy
  have hy0 : y = 0 := mem_singleton.mp hy
  subst y
  norm_num [original]

private theorem original_rank : firstRank univ 3 (1 / 2) original = 2 := by
  rw [firstRank_eq_sentinelFirst (marked := {0}) (L := 100) (R := 2)
    (by norm_num) (by norm_num) (by norm_num) marked_above modified_rank.le]
  exact modified_rank

private theorem original_threshold : threshold univ 3 1 (1 / 2) original = 2 := by
  rw [threshold_eq_sentinelFirst (marked := {0}) (L := 100) (R := 2)
    (by norm_num) (by norm_num) (by norm_num) marked_above modified_threshold.le]
  exact modified_threshold

private theorem modified_default : newDefault univ 3 3 1 (1 / 2) modified = 2 := by
  change max (threshold univ 3 1 (1 / 2) modified)
    (min (firstRank univ 3 (1 / 2) modified) (3 * threshold univ 3 1 (1 / 2) modified)) = 2
  rw [modified_threshold, modified_rank]
  norm_num

private theorem original_default : newDefault univ 3 3 1 (1 / 2) original = 2 := by
  rw [newDefault_eq_sentinelFirst (marked := {0}) (L := 100) (R := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    marked_above modified_rank.le modified_threshold.le]
  exact modified_default

-- Both ranks meet the ceiling exactly; the old default is neither zero nor the new default.
example : firstRank univ 3 (1 / 2) original = 2 ∧
    threshold univ 3 1 (1 / 2) original = 2 ∧
    newDefault univ 3 3 1 (1 / 2) original = 2 :=
  ⟨original_rank, original_threshold, original_default⟩

-- This is the actual commutation theorem, with every structural hypothesis discharged.
example (y : Fin 4) : sentinelFirst {0} 100 (update univ 3 3 1 (1 / 2) original) y =
    update univ 3 3 1 (1 / 2) modified y := by
  exact sentinelFirst_update (R := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) marked_high modified_rank.le modified_threshold.le (mem_univ y)

-- Both channels of the marked entry survive, even though its second coordinate is negative.
example : update univ 3 3 1 (1 / 2) original 0 = ![1000000, -17] ∧
    update univ 3 3 1 (1 / 2) modified 0 = ![100, -17] := by
  have h := update_eq_self_of_mem_sentinelFirst (K := 3) (R := 2)
    (by norm_num) (by norm_num) (by norm_num) marked_high modified_threshold.le
    (mem_univ 0) (mem_singleton_self 0)
  refine ⟨h.1, h.2.trans ?_⟩
  funext ν
  fin_cases ν <;> norm_num [sentinelFirst, original]

-- The step is not identity on the whole row: these signed coordinates really change.
example : original 2 1 = -1 ∧ original 3 0 = -1 ∧
    update univ 3 3 1 (1 / 2) original 2 = ![2, 0] ∧
    update univ 3 3 1 (1 / 2) original 3 = ![2, 0] := by
  have h2 : update univ 3 3 1 (1 / 2) original 2 = ![2, 0] := by
    unfold update
    rw [original_threshold, original_default]
    funext ν
    fin_cases ν <;> norm_num [updateEntry, radius, entrySize, defaultEntry, original]
  have h3 : update univ 3 3 1 (1 / 2) original 3 = ![2, 0] := by
    unfold update
    rw [original_threshold, original_default]
    funext ν
    fin_cases ν <;> norm_num [updateEntry, radius, entrySize, defaultEntry, original]
  exact ⟨by norm_num [original], by norm_num [original], h2, h3⟩

-- The rank bound proves the strict capacity of the marked set, rather than assuming it.
example : #({0} : Finset (Fin 4)) < 3 :=
  card_marked_lt_of_sentinelFirst (R := 2) (w := original) (by norm_num) (by norm_num)
    (by norm_num : (2 : ℝ) < 100) (subset_univ _) modified_rank.le

-- Arbitrarily large positive replacement values cannot defeat zero padding when K > #s.
example : kthLargest 3 univ (![(-4 : ℝ), 1000000] : Fin 2 → ℝ) = 0 := by
  have h := kthLargest_eq_of_eq_or_gt (k := 3) (s := univ) (t := (0 : ℝ))
    (f := (![-4, 1000000] : Fin 2 → ℝ)) (g := (![-4, 10] : Fin 2 → ℝ))
    (by norm_num) (by norm_num)
    (fun y _ => by fin_cases y <;> norm_num)
    (by norm_num [kthLargest, Fin.univ_succ, filter_insert, filter_singleton])
  rw [h]
  norm_num [kthLargest, Fin.univ_succ, filter_insert, filter_singleton]

-- Strictness above the ceiling matters: replacing a value by the ceiling can change the rank.
example : kthLargest 1 univ (![(5 : ℝ), 4] : Fin 2 → ℝ) = 5 ∧
    kthLargest 1 univ (![(4 : ℝ), 4] : Fin 2 → ℝ) = 4 := by
  norm_num [kthLargest, Fin.univ_succ, filter_insert, filter_singleton]

end ComplexityTests.RowCompressionSentinel
