/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.LinearCombination
import Mathlib.Algebra.Field.ZMod

/-!
# Direct client of finite-field random linear combinations

The difference of two independent uniform elements of `ZMod 5` is uniform, using only the shared
probability module rather than the polynomial-commitment or interactive-protocol modules.
-/

namespace CslibFrontierTests.LinearCombination

open Cslib.Probability

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : (PMF.uniformOfFintype (Fin 2 → ZMod 5)).map (fun r => r 0 - r 1) =
    PMF.uniformOfFintype (ZMod 5) := by
  have hd : (![1, -1] : Fin 2 → ZMod 5) 0 ≠ 0 := by decide
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using uniformOfFintype_map_linearComb hd

end CslibFrontierTests.LinearCombination
