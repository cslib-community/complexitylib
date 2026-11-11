/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.PMF.Bool

/-! # Boolean distributions

The masses of `true` and `false` under a Boolean distribution add to one. A point mass at `true`
puts no mass on `false`, and a coin that lands `true` with probability `1/4` lands `false` with
probability `3/4`, both in `ENNReal` and in `ℝ`.
-/

namespace CslibFrontierTests.PMFBool

open Cslib.Probability

-- A point mass at `true` puts no mass on `false`.
example : (PMF.pure true) false = 0 := by
  have hsum := PMF.apply_true_add_apply_false (PMF.pure true)
  rw [PMF.pure_apply_self] at hsum
  exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (hsum.trans (add_zero 1).symm)

-- The `ENNReal` identity recovers the mass of `false` from the mass of `true`.
example (p : PMF Bool) (h : p true = 1 / 4) : p false = 3 / 4 := by
  have hsum := PMF.apply_true_add_apply_false p
  have hq : (1 / 4 : ENNReal) + 3 / 4 = 1 := by
    rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 3 = 4 by norm_num,
      ENNReal.div_self (by norm_num) (by norm_num)]
  rw [h] at hsum
  exact (ENNReal.add_right_inj (by simp)).1 (hsum.trans hq.symm)

-- The real-valued form gives the same answer.
example (p : PMF Bool) (h : (p true).toReal = 1 / 4) : (p false).toReal = 3 / 4 := by
  rw [PMF.toReal_false_eq_one_sub, h]
  norm_num

end CslibFrontierTests.PMFBool
