/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorReduction
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the base-`r` reduction

The base-`3` reduction `vthreeSumM` with `A = {1, 2}`, `B = {3, 5}`, `C = {4, 6, 9}`, `d = 3`,
`p = 29 ≥ 3 ^ 3` and threshold `s = 1`:

* with the seed `(1, 0, 3)` it reports exactly `4 = 1 + 3`, computed by kernel reduction;
* `9` is reported for no list of seeds (`exists_add_eq_of_mem_ret_vthreeSumM`);
* `29` is good for `c = 4` (no false pairs), so `vmiss_le` bounds the miss probability of `μ`
  uniform seeds by `(1 - 3 #P / (4 · 29 ^ 2)) ^ μ`.
-/

namespace CslibFrontierTests.Algorithms.Lean.VectorReduction

open Finset Cslib.Algorithms.Lean.SubsetConvThreeSum

instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- The seed `(1, 0, 3)` reports exactly `4`. -/
example : (vthreeSumM 3 3 1 29 [⟨1, 0, 3⟩] [1, 2] [3, 5] [4, 6, 9]).ret = [4] := by
  decide +kernel

/-- Soundness: `9` is reported for no seeds at all. -/
example (seeds : List (Seed 29)) :
    9 ∉ (vthreeSumM 3 3 1 29 seeds [1, 2] [3, 5] [4, 6, 9]).ret := fun h => by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_mem_ret_vthreeSumM (by decide) h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- The prime `29` is good for `4`, so `vmiss_le` applies. -/
example (μ : ℕ) :
    (#((Fintype.piFinset fun _ : Fin μ => seeds 29).filter fun ss =>
        4 ∉ (vthreeSumM 3 3 1 29 (List.ofFn ss) [1, 2] [3, 5] [4, 6, 9]).ret) : ℝ) /
        (#(seeds 29) : ℝ) ^ μ ≤
      (1 - 3 * #(balancedPairs 3 3) / (4 * ((29 : ℕ) : ℝ) ^ 2)) ^ μ := by
  refine vmiss_le (by decide) (by norm_num) (a := 1) (b := 3) (by simp) (by simp) rfl
    (by simp) ?_
  decide

end CslibFrontierTests.Algorithms.Lean.VectorReduction
