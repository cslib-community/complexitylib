/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Game.CloseTo.Statistical

/-!
# A finite source followed by an infinite-output continuation

The shared distance bridge suffices to bound every event after an arbitrary kernel into `ℕ`.
No lattice protocol, native sampler or finite output-type instance is needed.
-/

open Cslib.Interactive Cslib.Probability
open scoped ENNReal NNReal Cslib.Probability.PMF

example (next : Bool → PMF ℕ) :
    CloseTo ((PMF.pure true).bind next) ((PMF.uniformOfFintype Bool).bind next) (1 / 2) := by
  have h : dist (PMF.pure true) (PMF.uniformOfFintype Bool) ≤ (1 / 2 : ℝ≥0) := by
    norm_num [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, PMF.pure_apply,
      PMF.uniformOfFintype_apply]
  simpa using (closeTo_of_dist_le h).bind_left next
