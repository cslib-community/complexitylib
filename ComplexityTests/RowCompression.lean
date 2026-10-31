/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.RowCompression
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Concrete compression updates

These examples exercise a preserved large entry, actual partial clipping between the two size
thresholds, negative inputs, dummy padding with a positive default, and the exception capacity.
-/

namespace ComplexityTests.RowCompression

open Finset Cslib.RowCompression

private def largeRow : Fin 2 → Fin 2 → ℝ := ![![10, 0], ![0, 0]]

private theorem large_threshold : threshold univ 2 1 0 largeRow = 1 := by
  norm_num [threshold, kthLargest, entrySize, largeRow, Fin.univ_succ, filter_insert,
    filter_singleton]

private theorem large_default : newDefault univ 2 1 1 0 largeRow = 3 := by
  unfold newDefault
  rw [large_threshold]
  norm_num [kthLargest, largeRow, Fin.univ_succ, filter_insert, filter_singleton]

-- A large entry survives and the small entry becomes the new default.
example : update univ 2 1 1 0 largeRow = ![![10, 0], ![3, 0]] := by
  unfold update
  rw [large_threshold, large_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, defaultEntry, radius, entrySize, largeRow]

-- The list really has one exception, strictly fewer than the capacity two.
example : candidates univ 2 1 0 largeRow = {0} := by
  unfold candidates
  rw [large_threshold]
  ext y
  fin_cases y <;> norm_num [entrySize, largeRow]

private noncomputable def transitionRow : Fin 2 → Fin 2 → ℝ := ![![0, 21 / 10], ![0, 0]]

private theorem transition_threshold : threshold univ 2 1 0 transitionRow = 1 := by
  have hr : kthLargest 2 univ (fun y => entrySize (transitionRow y)) = 0 := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) kthLargest_nonneg
    have hcard := (lt_kthLargest_iff (by norm_num) le_rfl).mp hlt
    have hsupport : ({y | 0 < entrySize (transitionRow y)} : Finset (Fin 2)) = {0} := by
      ext y
      fin_cases y <;> norm_num [entrySize, transitionRow]
    rw [hsupport] at hcard
    norm_num at hcard
  norm_num [threshold, hr]

private theorem transition_default : newDefault univ 2 1 1 0 transitionRow = 1 := by
  unfold newDefault
  rw [transition_threshold]
  norm_num [kthLargest, transitionRow, Fin.univ_succ, filter_insert, filter_singleton]

-- Size 2.1 is in the transition band (2,3); radius 0.7 clips both coordinates.
example : update univ 2 1 1 0 transitionRow = ![![3 / 10, 7 / 10], ![1, 0]] := by
  unfold update
  rw [transition_threshold, transition_default]
  funext y ν
  fin_cases y <;> fin_cases ν <;>
    norm_num [updateEntry, defaultEntry, radius, entrySize, transitionRow]

-- Large signed entries are preserved; no nonnegativity premise on row entries is hidden.
example : updateEntry 1 3 (![(-10), -4] : Fin 2 → ℝ) = ![-10, -4] := by
  apply updateEntry_eq_self_of_three_mul_le <;> norm_num [entrySize]

-- The old default exceeds the floor, and K exceeds the number of real positions.
-- The dummy padding still gives default two, with no candidate IDs.
example : newDefault (univ : Finset (Fin 1)) 2 3 1 2 (fun _ => defaultEntry 2) = 2 ∧
    candidates (univ : Finset (Fin 1)) 2 1 2 (fun _ => defaultEntry 2) = ∅ := by
  norm_num [newDefault, candidates, threshold, kthLargest, entrySize, defaultEntry,
    Fin.univ_succ]

-- The empty real row also has a well-defined default; dummies are not counted as real IDs.
example : newDefault (∅ : Finset (Fin 2)) 1 1 1 2 largeRow = 2 ∧
    candidates (∅ : Finset (Fin 2)) 1 1 2 largeRow = ∅ := by
  norm_num [newDefault, candidates, threshold, kthLargest]

-- A concrete perturbation invokes the width-independent stability theorem.
example (y : Fin 2) (ν : Fin 2) :
    |update univ 2 1 1 0 largeRow y ν -
      update univ 2 1 1 (1 / 10) (fun y ν => largeRow y ν + 1 / 10) y ν| ≤ 14 / 5 := by
  have h := abs_update_sub_update_le (s := univ) (n := 2) (K := 1) (ρ := 1)
    (z := 0) (z' := 1 / 10) (δ := 1 / 10) (w := largeRow)
    (w' := fun y ν => largeRow y ν + 1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (fun y _ ν => by norm_num) (mem_univ y) ν
  norm_num at h ⊢
  exact h

end ComplexityTests.RowCompression
