/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.TrimmedYates

/-!
# Tests for the trimmed Yates passes

Concrete runs of `CslibFrontier.Algorithms.Lean.TrimmedYates` on the coordinates `Fin 4`, with
ranked inputs supported on singletons (`t = 1`) and threshold `s = 1`:

* the returned entries, computed by running the program and checked against `ret_solveM`;
* the exact tick count, computed and checked against `time_solveM`;
* the covering product and the subset convolution differ on unranked inputs, so the ranked
  hypotheses of `ret_queryM_preprocessM_eq_subsetConvolution` are needed.
-/

namespace CslibFrontierTests.Algorithms.Lean.TrimmedYates

open Finset Cslib.Algorithms.Lean.TrimmedYates Cslib.BitString

/-- Left input: weight `2` on `{0}` and `3` on `{1}`. -/
def f : Finset (Fin 4) → ℤ := fun A => if A = {0} then 2 else if A = {1} then 3 else 0

/-- Right input: weight `5` on `{1}` and `7` on `{2}`. -/
def g : Finset (Fin 4) → ℤ := fun B => if B = {1} then 5 else if B = {2} then 7 else 0

/-- Three queries of size `2t = 2`. -/
def queries : List (Finset (Fin 4)) := [{0, 1}, {1, 2}, {0, 3}]

theorem f_ranked : ∀ A, f A ≠ 0 → #A = 1 := by
  intro A h
  unfold f at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem g_ranked : ∀ B, g B ≠ 0 → #B = 1 := by
  intro B h
  unfold g at h
  split_ifs at h with h₀ h₁ <;> simp_all

theorem queries_ok : ∀ C ∈ queries, C ⊆ (List.finRange 4).toFinset ∧ #C = 1 + 1 := by
  decide

/-- Running the program: `f{0} g{1} + f{1} g{0} = 10`, `f{1} g{2} = 21`, and `0` at `{0, 3}`. -/
example : (solveM (List.finRange 4) 1 f g queries).ret = [10, 21, 0] := by decide +kernel

/-- The same answers are the subset convolutions, by `ret_solveM`. -/
example : queries.map (subsetConvolution f g) = [10, 21, 0] := by
  rw [← ret_solveM (List.nodup_finRange 4) f_ranked g_ranked queries_ok (by norm_num : 1 ≤ 1 + 1)]
  decide +kernel

/-- The tick count of the run: `3 (4 + 1) ((1 + 4) + 3 (2 + 1)) = 210`. -/
example : (solveM (List.finRange 4) 1 f g queries).time = 210 := by decide +kernel

/-- The same count from `time_solveM`. -/
example : (solveM (List.finRange 4) 1 f g queries).time = 210 := by
  rw [time_solveM (List.nodup_finRange 4) 1 1 f g (by simpa [two_mul] using queries_ok)]
  decide

/-- Unranked inputs: with `f = g = 1` on all sets, the covering product at `{0}` counts the three
covers `(∅, {0}), ({0}, ∅), ({0}, {0})`, but the subset convolution only the two partitions. -/
example : coveringProduct (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 3 ∧
    subsetConvolution (fun _ => (1 : ℤ)) (fun _ => 1) ({0} : Finset (Fin 1)) = 2 := by
  decide +kernel

end CslibFrontierTests.Algorithms.Lean.TrimmedYates
