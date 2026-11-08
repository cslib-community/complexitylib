/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.BinPacking.FirstFitWeight

/-!
# First Fit's `17/10` bound: examples

These kernel-checked examples (using no `native_decide`) exercise
`Complexity.Algorithms.Lean.BinPacking.FirstFitWeight`:

1. The weights: a full bin `[18, 41, 61]` of capacity `120` weighs exactly `17 * 120`, so the
   per-bin bound `sum_map_firstFitWeight_le` is attained, and First Fit's bins on that instance
   weigh at least `10 * 120` each.
2. The First Fit rule `pairwise_forall_lt_sum_add_firstFit` is stronger than the pairwise
   overfull property `pairwise_firstFit`: `[[5], [3, 3]]` has the second property but not the
   first, and First Fit never returns it.
3. The small instances of [Dósa and Sgall, Section 4][DosaSgall2013]: `i` items each of sizes
   `18`, `41` and `61` in nondecreasing order, with capacity `120`, so `OPT = i`. For `i = 3`
   First Fit uses `5` bins, exactly the bound `⌊(17 * 3 + 8) / 10⌋ = 5` of
   `ten_mul_length_firstFit_le`. For `i = 9` it uses `15` bins, a ratio `5/3 > 3/2` beyond the
   reach of any bound of the form `3/2 * OPT + c` with `c < 3/2`, and within `⌈17/10 * 9⌉ = 16`.
-/

public section

namespace ComplexityTests.BinPackingFirstFitWeight

open Cslib.Algorithms.Lean.BinPacking

/-! ### 1. The weights -/

/-- The bonuses at the breakpoints `C / 6`, `C / 3` and `C / 2` and just above `C / 2`. -/
example : firstFitBonus 120 20 = 0 ∧ firstFitBonus 120 30 = 60 ∧ firstFitBonus 120 40 = 120 ∧
    firstFitBonus 120 60 = 120 ∧ firstFitBonus 120 61 = 480 := by decide

/-- A full bin attains the per-bin bound `17 * C`. -/
example : ([18, 41, 61].map (firstFitWeight 120)).sum = 17 * 120 := by decide

/-- The per-bin bound applied to the same bin. -/
example : ([18, 41, 61].map (firstFitWeight 120)).sum ≤ 17 * 120 :=
  sum_map_firstFitWeight_le (by decide)

/-- On the `i = 3` instance every First Fit bin weighs at least `10 * C`. -/
example : ∀ b ∈ firstFit 120 [18, 18, 18, 41, 41, 41, 61, 61, 61],
    10 * 120 ≤ (b.map (firstFitWeight 120)).sum := by decide

/-! ### 2. The First Fit rule -/

/-- The bins `[[5], [3, 3]]` are jointly overfull but violate the First Fit rule: the items `3`
fit into the first bin. -/
example : [[5], [3, 3]].Pairwise (fun b b' => 8 < b.sum + b'.sum) ∧
    ¬ [[5], [3, 3]].Pairwise (fun b b' => ∀ c ∈ b', 8 < b.sum + c) := by decide

/-- First Fit packs the same items differently, and its bins satisfy the First Fit rule. -/
example : firstFit 8 [5, 3, 3] = [[5, 3], [3]] ∧
    (firstFit 8 [5, 3, 3]).Pairwise (fun b b' => ∀ c ∈ b', 8 < b.sum + c) :=
  ⟨by decide, pairwise_forall_lt_sum_add_firstFit 8 [5, 3, 3]⟩

/-! ### 3. Dósa and Sgall's small instances -/

/-- `OPT = 3`: three full bins. -/
example : IsPacking 120 [18, 18, 18, 41, 41, 41, 61, 61, 61]
    [[18, 41, 61], [18, 41, 61], [18, 41, 61]] := ⟨by decide, by decide⟩

/-- No packing of the `i = 3` instance has fewer than `3` bins (volume `360 = 3 * 120`). -/
example {Q : List (List ℕ)} (hQ : IsPacking 120 [18, 18, 18, 41, 41, 41, 61, 61, 61] Q) :
    3 ≤ Q.length := by
  have := hQ.sum_le_mul_length
  simp only [List.sum_cons, List.sum_nil] at this
  omega

/-- First Fit uses `5 = ⌊1.7 * 3⌋` bins. -/
example : firstFit 120 [18, 18, 18, 41, 41, 41, 61, 61, 61] =
    [[18, 18, 18, 41], [41, 41], [61], [61], [61]] := by decide

/-- The bound `10 * FF ≤ 17 * OPT + 8` is attained at `OPT = 3`: it allows `FF ≤ 5`. -/
example : 10 * (firstFit 120 [18, 18, 18, 41, 41, 41, 61, 61, 61]).length ≤ 17 * 3 + 8 ∧
    ¬ 10 * 6 ≤ 17 * 3 + 8 := by
  have hQ : IsPacking 120 [18, 18, 18, 41, 41, 41, 61, 61, 61]
      [[18, 41, 61], [18, 41, 61], [18, 41, 61]] := ⟨by decide, by decide⟩
  exact ⟨ten_mul_length_firstFit_le hQ, by decide⟩

/-- The `i = 9` instance. -/
abbrev inst9 : List ℕ := List.replicate 9 18 ++ List.replicate 9 41 ++ List.replicate 9 61

/-- `OPT = 9`: nine full bins. -/
example : IsPacking 120 inst9 (List.replicate 9 [18, 41, 61]) := ⟨by decide, by decide⟩

/-- First Fit uses `15` bins on `inst9`, so `FF / OPT = 5/3 > 3/2`. -/
example : (firstFit 120 inst9).length = 15 ∧ 3 * 9 < 2 * 15 := by decide

/-- The ceiling form of the bound allows `16 = ⌈17/10 * 9⌉` bins on `inst9`. -/
example : (firstFit 120 inst9).length ≤ 16 := by
  have hQ : IsPacking 120 inst9 (List.replicate 9 [18, 41, 61]) := ⟨by decide, by decide⟩
  have h := length_firstFit_le_ceil hQ
  have hc : ⌈(17 / 10 : ℚ) * (List.replicate 9 [18, 41, 61]).length⌉₊ = 16 := by
    rw [List.length_replicate, Nat.ceil_eq_iff (by norm_num)]
    norm_num
  omega

end ComplexityTests.BinPackingFirstFitWeight
