/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntervalOrder

/-!
The generic interval topic alone exposes the original first-hit and port-rank API,
without the loop realization application. Concrete four-dart intervals check the new
anchor and cyclic laws in both directions.
-/

namespace CslibFrontierTests.RotationIntervalOrder

open Cslib.Complexity Cslib.Complexity.Graph

private abbrev G : Graph := ([9], [(9, 9), (9, 9)])

private def r : RotationSystem G where
  rotate := ((Dart.indexEquiv G).trans (finRotate 4)).trans (Dart.indexEquiv G).symm
  sameCycle_iff := by decide

private abbrev a : Dart G := (0, false)
private abbrev b : Dart G := (0, true)
private abbrev c : Dart G := (1, false)

private theorem ab_rank : r.rotationDistance a b = 1 := by
  apply r.rotationDistance_eq a b rfl 1 (by decide)
  intro k hk
  have hk0 : k = 0 := by omega
  subst k
  decide

private theorem ac_rank : r.rotationDistance a c = 2 := by
  apply r.rotationDistance_eq a c rfl 2 (by decide)
  intro k hk
  have hk' : k = 0 ∨ k = 1 := by omega
  rcases hk' with rfl | rfl <;> decide

private theorem interval : b ∈ r.rotationInterval a c := by
  apply (r.mem_rotationInterval_iff_lt_distance a b c rfl rfl (by decide)
    (by decide) (by decide)).mpr
  rw [ab_rank, ac_rank]
  decide

example : c ∈ r.rotationInterval b a :=
  (r.mem_rotationInterval_cyclic a b c rfl rfl (by decide) (by decide) (by decide)).mp interval

example : ¬c ∈ r.rotationInterval a b := by
  rw [r.mem_rotationInterval_iff_lt_distance a c b rfl rfl (by decide)
    (by decide) (by decide), ac_rank, ab_rank]
  decide

-- Original QNs and types remain directly usable from the lower topic.
example : r.rotationDistance a a = 0 := r.rotationDistance_self a

example : r.portRank a ≠ r.portRank b :=
  fun h => (by decide : a ≠ b) (r.portRank_injective a b rfl h)

end CslibFrontierTests.RotationIntervalOrder
