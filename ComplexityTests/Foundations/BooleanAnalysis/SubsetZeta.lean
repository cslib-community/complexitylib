/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Foundations.BooleanAnalysis.SubsetZeta

/-!
# Tests for the subset zeta transform and Yates's passes

Concrete instances of `Complexity.Foundations.BooleanAnalysis.SubsetZeta`:

* kernel-computed zeta and Möbius transforms on the subsets of `Fin 2`, and their inversion;
* Yates's passes compared with the zeta transform, including a list with a repeated coordinate,
  for which the closed form `yatesTransform_apply` (which assumes `l.Nodup`) fails;
* the reversed passes with coefficient `-1` undoing the passes with coefficient `1`.
-/

@[expose] public section

namespace ComplexityTests.Foundations.BooleanAnalysis.SubsetZeta

open Cslib.BitString Finset

/-- The weight function `S ↦ #S ^ 2` on the subsets of `Fin 2`. -/
def w (S : Finset (Fin 2)) : ℤ := (#S : ℤ) ^ 2

/-- `∑_{T ⊆ {0, 1}} #T ^ 2 = 0 + 1 + 1 + 4`, computed by the kernel. -/
example : subsetZeta w {0, 1} = 6 := by decide +kernel

/-- The Möbius transform of the zeta transform, computed by the kernel. -/
example : subsetMobius (subsetZeta w) {0, 1} = 4 := by decide +kernel

/-- ... agrees with `subsetMobius_subsetZeta`. -/
example : subsetMobius (subsetZeta w) {0, 1} = w {0, 1} := by rw [subsetMobius_subsetZeta]

/-- The zeta transform of the Möbius transform, computed by the kernel. -/
example : subsetZeta (subsetMobius w) {0, 1} = 4 := by decide +kernel

/-- Yates's passes in coordinates `0, 1` compute the zeta transform at `{0, 1}`. -/
example : yatesTransform (1 : ℕ) [0, 1] w {0, 1} = 6 := by decide +kernel

/-- ... as `yatesTransform_one_apply` predicts. -/
example : yatesTransform (1 : ℕ) [0, 1] w {0, 1} = subsetZeta w {0, 1} :=
  yatesTransform_one_apply (by decide) w (by decide)

/-- With coefficient `-1` the passes compute the Möbius transform: `4 - 1 - 1 + 0`. -/
example : yatesTransform (-1 : ℤ) [1, 0] w {0, 1} = subsetMobius w {0, 1} :=
  yatesTransform_neg_one_apply (by decide) w (by decide)

example : subsetMobius w {0, 1} = 2 := by decide +kernel

/-- The indicator of the empty set. -/
def e (S : Finset (Fin 1)) : ℕ := if S = ∅ then 1 else 0

/-- Edge case: repeating a coordinate double-counts. With the list `[0, 0]` the value at `{0}`
is `2`, while the zeta transform is `1`; `yatesTransform_apply` assumes a duplicate-free list. -/
example : yatesTransform (1 : ℕ) [0, 0] e {0} = 2 ∧ subsetZeta e {0} = 1 := by decide +kernel

/-- The reversed passes with the negated coefficient restore the input. -/
example : yatesTransform (-1 : ℤ) [1, 0] (yatesTransform (1 : ℤ) [0, 1] w) = w := by
  rw [show ([1, 0] : List (Fin 2)) = [0, 1].reverse from rfl, yatesTransform_neg_reverse]

end ComplexityTests.Foundations.BooleanAnalysis.SubsetZeta
