/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Combination
import Mathlib.Data.List.Count

/-!
# Exact coverage of the executable combination decoder

The existing unranker is a bijection between fitting ranks and fixed-weight words, including
empty and impossible layers. The proof follows the actual false-first recursion; it introduces
no enumeration of the full Boolean cube.

## Main results

* `Cslib.BitString.unrankCombination_coverage`: every fixed-weight word has exactly one rank.
-/

public section

namespace Cslib.BitString

/-- Every fixed-weight word has exactly one fitting rank in the actual recursive decoder. -/
theorem unrankCombination_coverage (w : List Bool) :
    ∃! r : Fin (w.length.choose (w.count true)),
      unrankCombination w.length (w.count true) r = w := by
  have hex : ∃ r, r < w.length.choose (w.count true) ∧
      unrankCombination w.length (w.count true) r = w := by
    induction w with
    | nil => exact ⟨0, by decide, rfl⟩
    | cons b w ih =>
      obtain ⟨r, hr, he⟩ := ih
      cases b
      · refine ⟨r, ?_, ?_⟩
        · change r < (w.length + 1).choose (w.count true)
          cases hk : w.count true with
          | zero => simpa [hk] using hr
          | succ k =>
            rw [hk] at hr
            rw [Nat.choose_succ_succ']
            omega
        · simpa [unrankCombination, hr] using congrArg (false :: ·) he
      · refine ⟨w.length.choose (w.count true + 1) + r, ?_, ?_⟩
        · rw [List.length_cons, List.count_cons_self, Nat.choose_succ_succ']
          omega
        · simp [unrankCombination, he, Nat.not_lt.mpr (Nat.le_add_right _ _)]
  obtain ⟨r, hr, he⟩ := hex
  exact ⟨⟨r, hr⟩, he, fun s hs =>
    Fin.ext (unrankCombination_injective s.isLt hr (hs.trans he.symm))⟩

end Cslib.BitString
