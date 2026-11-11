/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1138 @b1635b2e

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Cslib.Computability.Machines.Turing.MultiTape.Space

/-!
# Every work tape costs a cell

The additions of cslib PR #1138 to `Cslib.Computability.Machines.Turing.MultiTape.Space`: every
work head visits the cell it starts on, so a run path visits at least one cell per work tape, and a
space bound is at least the number of work tapes.

## Main results

* `Turing.MultiTapeNTM.RunPath.le_space`: a run path visits at least `k` cells.
* `Turing.MultiTapeNTM.RunsInSpace.le`: a space bound is at least the number of work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- Every work head visits at least the cell it starts on, so a path visits at least `k` cells. -/
lemma le_space (p : ntm.RunPath input) : k ≤ p.space :=
  calc k = ∑ _ : Fin k, 1 := by rw [← Finset.card_eq_sum_ones, Finset.card_univ, Fintype.card_fin]
    _ ≤ p.space := Finset.sum_le_sum fun _ _ =>
      Finset.card_pos.mpr (Finset.univ_nonempty.image _)

end RunPath

/-- A space bound leaves room for every work tape: already the computation path that has not
moved yet visits one cell per tape. -/
lemma RunsInSpace.le {s : ℕ} (h : ntm.RunsInSpace input s) : k ≤ s :=
  RunPath.le_space _ |>.trans <| h ⟨RelSeries.singleton _ (ntm.initCfg input), rfl⟩

end Turing.MultiTapeNTM
