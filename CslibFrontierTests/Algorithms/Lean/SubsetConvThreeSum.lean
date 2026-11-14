/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.Reduction
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the reduction from 3SUM to subset convolution

Concrete runs of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum` with `A = {1, 2}`,
`B = {3, 5}`, queries `C = {4, 6, 9}`, modulus `p = 17`, dimension `d = 4` (`2 ^ 4 ≤ 17`), rank
`t = 1` and threshold `s = 1`:

* one trial, run by kernel reduction: the seed `(ξ, α, β) = (1, 0, 1)` reports `4 = 1 + 3` and the
  seed `(1, 0, 3)` reports `6 = 1 + 5`; `9` is never a sum and is never reported
  (`exists_add_eq_of_mem_ret_threeSumM`);
* the exact tick count of the first run, computed by kernel reduction;
* the hypotheses of the per-trial bound and of `miss_le` hold for `c = 6`: there are no false pairs
  modulo `17`, so at least `#P (p - 1) = 12 · 16 = 192` of the `16 · 17 ^ 2 = 4624` seeds accept
  (`card_accepts_add_ge`; a direct count, not run here, gives exactly `192`).
-/

namespace CslibFrontierTests.Algorithms.Lean.SubsetConvThreeSum

open Finset Cslib.Algorithms.Lean.SubsetConvThreeSum

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The seed `(1, 0, 1)` reports exactly `4 = 1 + 3`. -/
example : (threeSumM 4 1 1 17 [⟨1, 0, 1⟩] [1, 2] [3, 5] [4, 6, 9]).ret = [4] := by
  decide +kernel

/-- The seed `(1, 0, 3)` reports `6 = 1 + 5`. -/
example : 6 ∈ (threeSumM 4 1 1 17 [⟨1, 0, 3⟩] [1, 2] [3, 5] [4, 6, 9]).ret := by
  decide +kernel

/-- The run costs `193` ticks. -/
example : (threeSumM 4 1 1 17 [⟨1, 0, 1⟩] [1, 2] [3, 5] [4, 6, 9]).time = 193 := by
  decide +kernel

/-- Soundness: `9` is reported for no seeds at all, since it is not a sum. -/
example (seeds : List (Seed 17)) :
    9 ∉ (threeSumM 4 1 1 17 seeds [1, 2] [3, 5] [4, 6, 9]).ret := fun h => by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_mem_ret_threeSumM (by norm_num) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- `#P = (4 choose 2) (2 choose 1) = 12`. -/
example : #(rankedPairs 4 1) = 12 := by rw [card_rankedPairs]; rfl

theorem isolated_left : ∀ a ∈ [1, 2], Isolated 17 [1, 2] a := by decide

theorem isolated_right : ∀ b ∈ [3, 5], Isolated 17 [3, 5] b := by decide

/-- No pair of `{1, 2} × {3, 5}` sums to `6` modulo `17` without summing to `6`. -/
theorem falsePairs_six : falsePairs 17 6 [1, 2] [3, 5] = ∅ := by decide

/-- At least `192` of the `4624` seeds accept `6`: the per-trial bound, applied. -/
example : 12 * 16 ≤ #((seeds 17).filter fun s => Accepts 4 1 s [1, 2] [3, 5] 6) := by
  have h := card_accepts_add_ge (p := 17) (d := 4) (t := 1) (by norm_num)
    (A := [1, 2]) (B := [3, 5]) (fun _ h => h) (fun _ h => h) (a := 1) (b := 5) (c := 6)
    (by simp) (by simp) (isolated_left 1 (by simp)) (isolated_right 5 (by simp)) rfl
  rwa [falsePairs_six, card_empty, zero_mul, mul_zero, add_zero, card_rankedPairs] at h

/-- The prime `17` is good for `6`, so `miss_le` applies: `μ` uniform trials miss `6` with
probability at most `(1 - 3 · 12 / (4 · 17 ^ 2)) ^ μ`. -/
example (μ : ℕ) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds 17).filter fun ss =>
        6 ∉ (threeSumM 4 1 1 17 (List.ofFn ss) [1, 2] [3, 5] [4, 6, 9]).ret) : ℝ) /
        (#(seeds 17) : ℝ) ^ μ ≤
      (1 - 3 * #(rankedPairs 4 1) / (4 * ((17 : ℕ) : ℝ) ^ 2)) ^ μ := by
  refine miss_le (by norm_num) (by norm_num) (a := 1) (b := 5) (by simp) (by simp) rfl
    (by simp) ?_
  have : (([1, 2] : List ℕ).filter fun a => decide (Isolated 17 [1, 2] a)) = [1, 2] := by decide
  have h' : (([3, 5] : List ℕ).filter fun b => decide (Isolated 17 [3, 5] b)) = [3, 5] := by
    decide
  rw [this, h', falsePairs_six]
  decide

end CslibFrontierTests.Algorithms.Lean.SubsetConvThreeSum
