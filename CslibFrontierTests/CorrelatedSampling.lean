/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Probability.CorrelatedSampling.Embedding
import CslibFrontier.Probability.StatisticalDistance.Coupling

/-! # Correlated sampling

Parties holding the same distribution always agree, and every party samples its own distribution.
For a point mass against a uniform bit, the agreement bound is `1/3`. When both parties already
know the target kernel, the local embedding is exact.
-/

namespace CslibFrontierTests.CorrelatedSampling

open Cslib.Probability.CorrelatedSampling
open scoped Cslib.Probability.PMF

/-- A point mass on `true` and a uniform bit. -/
noncomputable def P : Bool → PMF Bool
  | false => PMF.pure true
  | true => Cslib.Probability.PMF.uniformOfFintype Bool

-- Each party samples its own distribution.
example (i : Bool) : (shared P).map (sample P i) = P i := map_sample i

-- Parties with the same distribution agree with probability one.
example (i : Bool) : 1 ≤ ((shared P).toOuterMeasure {l | sample P i l = sample P i l}).toReal := by
  simpa using agree_ge (P := P) i i

-- The point mass and the uniform bit are at distance `1/2`, so they agree with probability at
-- least `(1 - 1/2) / (1 + 1/2) = 1/3`.
example : 1 / 3 ≤
    ((shared P).toOuterMeasure {l | sample P false l = sample P true l}).toReal := by
  have hd : dist (P false) (P true) = 1 / 2 := by
    rw [Cslib.Probability.PMF.dist_eq]
    simp [P, Cslib.Probability.PMF.uniformOfFintype_apply]
    norm_num
  have h := agree_ge (P := P) false true
  rw [hd] at h
  norm_num at h ⊢
  exact h

-- If both parties hold the target kernel, local sampling reproduces `(x, y, s, s)` exactly.
example {X Y S : Type} [Fintype X] [Fintype Y] [Fintype S] (P : PMF (X × Y)) (q : PMF S) :
    dist (P.bind fun xy => (localSample (fun _ => q) (fun _ => q) (fun _ => q) xy.1 xy.2).map
        (xy, ·))
      (P.bind fun xy => (q.map fun s => (s, s)).map (xy, ·)) = 0 := by
  refine le_antisymm ?_ dist_nonneg
  simpa using dist_embed_le P (fun _ => q) (fun _ => q) (fun _ => q)

-- The coupling inequality: a uniform bit and the constant `true` differ with probability `1/2`.
example : dist ((Cslib.Probability.PMF.uniformOfFintype Bool).map id)
    ((Cslib.Probability.PMF.uniformOfFintype Bool).map fun _ => true) ≤
      ((Cslib.Probability.PMF.uniformOfFintype Bool).toOuterMeasure {b | id b ≠ true}).toReal :=
  Cslib.Probability.PMF.dist_map_map_le _ _ _

end CslibFrontierTests.CorrelatedSampling
