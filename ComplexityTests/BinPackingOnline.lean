/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.BinPacking.FirstFitWeight
public import Complexity.Algorithms.Lean.BinPacking.OnlineLowerBound

/-!
# Online bin packing and Yao's lower bound: examples

These kernel-checked examples (using no `native_decide`) exercise
`Complexity.Algorithms.Lean.BinPacking.Online` and
`Complexity.Algorithms.Lean.BinPacking.OnlineLowerBound`:

1. The certificate. Exactly 20 nonempty bin patterns (counts of the sizes `6`, `14` and `21`) fit
   into capacity `41`, and `a + 2x + 2y ≤ 2 + 2[a > 0] + 2[a + x > 0]` holds on each.
2. First Fit as an online packer on Yao's input with `m = 1`. It uses `1`, `4` and `10` bins
   after the three phases, against optima `1`, `3` and `6`, so it meets the bound after the third
   phase (`2 * 10 ≥ 3 * 6`).
3. Tightness. For `m = 8`, an online packer that follows the optimal solution of Yao's linear
   program uses `12`, `36` and `72` bins against optima `8`, `24` and `48`. That is exactly `3/2`
   after every phase, so the constant `3/2` of `OnlinePacker.yao_lower_bound` cannot be raised on
   this input.
4. An online packer whose rule always opens a new bin still yields a valid packing.
5. The bracket `[3/2, 17/10]`. First Fit, as the online packer `firstFitPacker`, satisfies
   `10 * ALG ≤ 17 * OPT + 8` against every packing (`ten_mul_length_firstFit_le`). Together with
   `OnlinePacker.exists_ratio_violation_of_lt`, this brackets the best asymptotic competitive ratio
   of deterministic online bin packing between `3/2` and `17/10`.
-/

public section

namespace ComplexityTests.BinPackingOnline

open Cslib.Algorithms.Lean.BinPacking

/-! ### 1. The certificate -/

/-- The 20 feasible bin patterns. -/
example : ((List.range 7 ×ˢ List.range 3 ×ˢ List.range 2).filter fun (a, x, y) =>
    0 < a + x + y ∧ 6 * a + 14 * x + 21 * y ≤ 41).length = 20 := by decide

/-- The certificate on every pattern (with room to spare in the ranges). -/
example : ∀ a < 8, ∀ x < 4, ∀ y < 3, 6 * a + 14 * x + 21 * y ≤ 41 →
    a + 2 * x + 2 * y ≤ 2 + 2 * (if 0 < a then 1 else 0) + 2 * (if 0 < a + x then 1 else 0) := by
  decide

/-- A tight bin: four `6`s and a `14` have weight `6`. -/
example : ([6, 6, 6, 6, 14].map yaoWeight).sum = 6 := by decide

/-! ### 2. First Fit on Yao's input -/

example : ((firstFitPacker 41).run (List.replicate 6 6)).length = 1 := by
  rw [run_firstFitPacker]; decide

example : ((firstFitPacker 41).run (List.replicate 6 6 ++ List.replicate 6 14)).length = 4 := by
  rw [run_firstFitPacker]; decide

example : ((firstFitPacker 41).run
    (List.replicate 6 6 ++ List.replicate 6 14 ++ List.replicate 6 21)).length = 10 := by
  rw [run_firstFitPacker]; decide

/-- Yao's bound applied to First Fit. -/
example : 3 * 1 ≤ 2 * ((firstFitPacker 41).run (List.replicate 6 6)).length ∨
    3 * 3 ≤ 2 * ((firstFitPacker 41).run (List.replicate 6 6 ++ List.replicate 6 14)).length ∨
    3 * 6 ≤ 2 * ((firstFitPacker 41).run
      (List.replicate 6 6 ++ List.replicate 6 14 ++ List.replicate 6 21)).length := by
  simpa using (firstFitPacker 41).yao_lower_bound 1

/-! ### 3. Tightness -/

/-- The online packer following the optimal solution of Yao's linear program for `m = 8`. It
puts the first `12` items of size `6` two to a bin into bins `0`–`5` and the next `36` six to a
bin into bins `6`–`11`; the first `12` items of size `14` two to a bin into bins `0`–`5`, the next
`12` one to a bin into new bins `12`–`23`, and the last `24` two to a bin into new bins; and the
first `12` items of size `21` into bins `12`–`23`, and the rest into new bins. -/
def lpPacker : OnlinePacker 41 where
  place hist _ a :=
    let k := hist.count a
    if a = 6 then
      if k < 12 then some (k / 2) else if k < 48 then some (6 + (k - 12) / 6) else none
    else if a = 14 then
      if k < 12 then some (k / 2) else if k < 24 then none
      else if k < 48 then some (24 + (k - 24) / 2) else none
    else if a = 21 then (if k < 12 then some (12 + k) else none)
    else none

example : (lpPacker.run (List.replicate 48 6)).length = 12 := by decide

example : (lpPacker.run (List.replicate 48 6 ++ List.replicate 48 14)).length = 36 := by decide

example : (lpPacker.run
    (List.replicate 48 6 ++ List.replicate 48 14 ++ List.replicate 48 21)).length = 72 := by
  decide +kernel

/-! ### 4. A rule that always opens a new bin -/

/-- The online packer that never reuses a bin. -/
def newBinPacker : OnlinePacker 41 := ⟨fun _ _ _ => none⟩

example : newBinPacker.run [6, 14, 21] = [[6], [14], [21]] := by decide

example : IsPacking 41 [6, 14, 21] (newBinPacker.run [6, 14, 21]) :=
  newBinPacker.isPacking_run (by decide)

/-! ### 5. The bracket `[3/2, 17/10]` -/

/-- An online upper bound: First Fit, run online, is within `17/10` of every packing, up to the
additive constant `4/5`. -/
example {l : List ℕ} {Q : List (List ℕ)} (hQ : IsPacking 41 l Q) :
    10 * ((firstFitPacker 41).run l).length ≤ 17 * Q.length + 8 := by
  rw [run_firstFitPacker]
  exact ten_mul_length_firstFit_le hQ

/-- The matching lower bound: no online packer is within `a / b < 3/2` with any additive
constant; here `a / b = 7/5`. -/
example (A : OnlinePacker 41) (c : ℕ) :
    ∃ (l : List ℕ) (Q : List (List ℕ)), IsPacking 41 l Q ∧
      (∀ Q', IsPacking 41 l Q' → Q.length ≤ Q'.length) ∧ 7 * Q.length + c < 5 * (A.run l).length :=
  A.exists_ratio_violation_of_lt (by decide) c

end ComplexityTests.BinPackingOnline
