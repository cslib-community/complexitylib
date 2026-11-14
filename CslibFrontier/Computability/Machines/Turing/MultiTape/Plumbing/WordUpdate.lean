/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Updating a cell of a word tape

The list update and the corresponding tape-cell update agree. This shared tape fact is used by
both alternating guessing machines and in-place deterministic word operations.
-/

public section

namespace Turing

/-- Setting a cell of a word sets the cell of its tape. -/
theorem tapeOfList_set {Symbol : Type*} (w : List Symbol) {i : ℕ} (hi : i < w.length)
    (s : Symbol) : tapeOfList (w.set i s) = Function.update (tapeOfList w) (i : ℤ) (some s) := by
  funext z
  cases z with
  | negSucc n => simp
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, tapeOfList_ofNat, Function.update_apply, Nat.cast_inj,
      List.getElem?_set]
    by_cases h : n = i
    · subst h
      simp [hi]
    · simp [h, Ne.symm h]

/-- Replacing the first cell after a fixed prefix preserves that prefix and the trailing suffix. -/
theorem update_tapeOfList_append_cons {Symbol : Type*} (pre suffix : List Symbol)
    (b b' : Symbol) :
    Function.update (tapeOfList (pre ++ b :: suffix)) (pre.length : ℤ) (some b') =
      tapeOfList (pre ++ b' :: suffix) := by
  rw [← tapeOfList_set _ (by simp), List.set_append_right _ _ le_rfl]
  simp

end Turing
