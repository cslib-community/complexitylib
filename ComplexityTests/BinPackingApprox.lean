/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.BinPacking.FirstFit
public import Complexity.Algorithms.Lean.BinPacking.NextFit
public import Complexity.Computability.PCP.Approximation.BinPacking

/-!
# Bin packing examples

These kernel-checked examples (using no `native_decide`) exercise:

1. Next Fit and First Fit on small instances, where First Fit packs better than Next Fit.
2. Packings that hold and fail (`IsPacking`), including a missing item and an overfull bin.
3. Tightness of the bounds `length_nextFit_lt` and `length_firstFit_lt`: instances with
   `NF = FF = 2 * OPT - 1`.
4. The hypotheses of `P_eq_NP_of_binPacking_approx`: an exact, not necessarily polynomial-time,
   algorithm satisfies them, while First Fit violates the ratio hypothesis. A polynomial-time
   algorithm satisfying them gives `P = NP`, so no unconditional witness is expected.
-/

public section

namespace ComplexityTests.BinPackingApprox

open Cslib.Algorithms.Lean.BinPacking

/-! ### 1. Next Fit and First Fit -/

example : nextFit 10 [6, 5, 4, 5] = [[6], [5, 4], [5]] := by decide

example : firstFit 10 [6, 5, 4, 5] = [[6, 4], [5, 5]] := by decide

example : nextFit 10 [] = [] ∧ firstFit 10 [] = [] := by decide

/-- Next Fit returns a packing. -/
example : IsPacking 10 [6, 5, 4, 5] (nextFit 10 [6, 5, 4, 5]) :=
  isPacking_nextFit (by decide)

/-- First Fit returns a packing. -/
example : IsPacking 10 [6, 5, 4, 5] (firstFit 10 [6, 5, 4, 5]) :=
  isPacking_firstFit (by decide)

/-! ### 2. Packings that hold and fail -/

example : IsPacking 10 [6, 5, 4, 5] [[5, 5], [6, 4]] :=
  ⟨by decide, by decide⟩

/-- A list of bins that misses an item is not a packing. -/
example : ¬ IsPacking 10 [6, 5, 4, 5] [[5, 5], [6]] := fun h => by
  have := h.perm.length_eq
  simp at this

/-- A list of bins with an overfull bin is not a packing. -/
example : ¬ IsPacking 10 [6, 5, 4, 5] [[6, 5], [4, 5]] := fun h => by
  have := h.sum_le [6, 5] (by simp)
  simp at this

/-- An item larger than the capacity has no packing. -/
example : ¬ ∃ bins, IsPacking 10 [11] bins := by
  rw [exists_isPacking_iff]
  simp

/-! ### 3. Tightness of the `2 * OPT - 1` bounds -/

/-- Next Fit uses `3 = 2 * 2 - 1` bins on an instance with a packing into `2` bins. -/
example : IsPacking 2 [1, 2, 1] [[1, 1], [2]] ∧ (nextFit 2 [1, 2, 1]).length = 3 :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-- First Fit uses `3 = 2 * 2 - 1` bins on an instance with a packing into `2` bins. -/
example : IsPacking 6 [1, 1, 5, 5] [[1, 5], [1, 5]] ∧ (firstFit 6 [1, 1, 5, 5]).length = 3 :=
  ⟨⟨by decide, by decide⟩, by decide⟩

/-! ### 4. The hypotheses of the hardness theorem -/

open Classical in
/-- An exact bin-packing algorithm: a packing with the fewest bins, when one exists. It is not
claimed to be polynomial-time. -/
noncomputable def exactPacking (x : List ℕ × ℕ) : List (List ℕ) :=
  if h : ∃ m bins, IsPacking x.2 x.1 bins ∧ bins.length = m then
    Classical.choose (Nat.find_spec h)
  else []

/-- The exact algorithm satisfies the validity and ratio hypotheses of
`Cslib.Complexity.P_eq_NP_of_binPacking_approx`, so they are consistent. -/
example : (∀ l C, (∀ a ∈ l, a ≤ C) → IsPacking C l (exactPacking (l, C))) ∧
    ∀ l C Q, l ≠ [] → IsPacking C l Q → 2 * (exactPacking (l, C)).length < 3 * Q.length := by
  classical
  have hspec : ∀ l C (h : ∃ m bins, IsPacking C l bins ∧ bins.length = m),
      IsPacking C l (exactPacking (l, C)) ∧ (exactPacking (l, C)).length = Nat.find h := by
    intro l C h
    unfold exactPacking
    split
    next h' => exact Classical.choose_spec (Nat.find_spec h')
    next h' => exact absurd h h'
  refine ⟨fun l C hl => ?_, fun l C Q hl hQ => ?_⟩
  · obtain ⟨bins, hbins⟩ := exists_isPacking_iff.2 hl
    exact (hspec l C ⟨_, bins, hbins, rfl⟩).1
  · have h : ∃ m bins, IsPacking C l bins ∧ bins.length = m := ⟨_, Q, hQ, rfl⟩
    have hmin : Nat.find h ≤ Q.length := Nat.find_min' h ⟨Q, hQ, rfl⟩
    have hQ0 : 0 < Q.length := List.length_pos_iff.2 (hQ.ne_nil hl)
    rw [(hspec l C h).2]
    omega

/-- First Fit violates the ratio hypothesis of `Cslib.Complexity.P_eq_NP_of_binPacking_approx`. -/
example : ¬ (2 * (firstFit 6 [1, 1, 5, 5]).length < 3 * [[1, 5], [1, 5]].length) := by decide

end ComplexityTests.BinPackingApprox
