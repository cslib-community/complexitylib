/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation
import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Bridge

/-! Clients for the superquadratic sensitivity separation. -/

namespace CslibFrontierTests.SensitivitySeparation

open Cslib Cslib.BitString Cslib.QueryComplexity

-- The headline separation, at a concrete constant.
example : ∃ (n : ℕ) (f : BooleanFunction n), 0 < n ∧ (∃ x y, f x ≠ f y) ∧
    1000 * (sensitivity f : ℝ) ^ 2 < (blockSensitivity f : ℝ) :=
  exists_mul_sensitivity_sq_lt_blockSensitivity 1000

-- No bound of the form `C · s(f)²` holds for decision-tree complexity either.
example (C : ℝ) : ¬ ∀ (n : ℕ) (f : BooleanFunction n),
    (DecisionTree.complexity f : ℝ) ≤ C * (sensitivity f : ℝ) ^ 2 := fun h => by
  obtain ⟨n, f, -, -, hf⟩ := DecisionTree.exists_mul_sensitivity_sq_lt_complexity C
  exact (h n f).not_gt hf

-- The internal measures agree with CSLib's on `Fin n`.
example {n : ℕ} (f : BooleanFunction n) :
    SensitivitySeparation.Internal.blockSensitivity f = blockSensitivity f :=
  SensitivitySeparation.Internal.blockSensitivity_eq_queryComplexity_blockSensitivity f

-- `flipOn` agrees with CSLib's `flipBlock` on `BitString n`.
example {n : ℕ} (S : Finset (Fin n)) (x : BitString n) : flipOn S x = flipBlock S x :=
  flipOn_eq_flipBlock S x

end CslibFrontierTests.SensitivitySeparation
