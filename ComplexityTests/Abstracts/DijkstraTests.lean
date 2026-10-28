/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.DijkstraAbstract

/-!
# Non-vacuity tests for `ComplexityAbstracts.DijkstraAbstract`

Instantiates both `dijkstra_logLinear` and `dijkstra_fibonacci` on a concrete weighted directed
graph with parallel edges and checks the encoded source distance and concrete instruction bounds.
-/

namespace ComplexityTests.Abstracts.DijkstraTests

open ComplexityAbstracts.DijkstraAbstract

/-- Concrete 3-vertex graph: `0 → 1` (weights `4`, `5`), `0 → 2` (weight `1`), `2 → 1` (weight `2`).
-/
def sampleGraph : Graph 3 := ![[(1, 4), (2, 1), (1, 5)], [], [(1, 2)]]

private theorem dist_source_zero : dist sampleGraph 0 0 = 0 := by
  unfold ComplexityAbstracts.DijkstraAbstract.dist
  exact le_antisymm (iInf₂_le [] (show IsWalk sampleGraph 0 [] 0 from rfl)) zero_le

/-- Non-vacuity of `dijkstra_logLinear` on `sampleGraph` at word size `10`. -/
example :
    ∃ r, ∃ p : Program r, ∃ K t steps,
      Runs 10 p (init (encode sampleGraph 0)) t steps ∧
      (∃ v, step 10 p t = .halt v) ∧
      steps + 1 ≤ K * 5 * 2 ∧
      t.mem (outAddr sampleGraph 0) = 1 := by
  obtain ⟨r, p, K, h⟩ := dijkstra_logLinear
  have hw : 8 * (3 + numEdges sampleGraph + 2) * (maxWeight sampleGraph + 2) < 2 ^ 10 := by decide
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := h 3 sampleGraph 0 10 hw
  have hm : numEdges sampleGraph = 4 := by decide
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog] at hle
  have hd0 : t.mem (outAddr sampleGraph 0) = 1 := by
    rw [hd 0, dist_source_zero]
    rfl
  exact ⟨r, p, K, t, steps, hr, hh, hle, hd0⟩

/-- Non-vacuity of `dijkstra_fibonacci` on `sampleGraph` at word size `10`. -/
example :
    ∃ r, ∃ p : Program r, ∃ K t steps,
      Runs 10 p (init (encode sampleGraph 0)) t steps ∧
      (∃ v, step 10 p t = .halt v) ∧
      steps + 1 ≤ K * (4 + 3 * 2) ∧
      t.mem (outAddr sampleGraph 0) = 1 := by
  obtain ⟨r, p, K, h⟩ := dijkstra_fibonacci
  have hw : 8 * (3 + numEdges sampleGraph + 2) * (maxWeight sampleGraph + 2) < 2 ^ 10 := by decide
  obtain ⟨t, steps, hr, hh, hle, hd⟩ := h 3 sampleGraph 0 10 hw
  have hm : numEdges sampleGraph = 4 := by decide
  have hlog : Nat.log 2 3 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  rw [hm, hlog] at hle
  have hd0 : t.mem (outAddr sampleGraph 0) = 1 := by
    rw [hd 0, dist_source_zero]
    rfl
  exact ⟨r, p, K, t, steps, hr, hh, hle, hd0⟩

end ComplexityTests.Abstracts.DijkstraTests
