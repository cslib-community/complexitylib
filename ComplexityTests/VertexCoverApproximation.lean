/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Problems.VertexCover.Approximation
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Worked maximal-matching vertex-cover examples

These kernel-checked examples (using no `native_decide`) exercise
`Cslib.Algorithms.Lean.VertexCover.matchingCover` and its `Graph` wrapper
`Cslib.Complexity.VertexCover.approxCover`:

1. The path `0 - 1 - 2 - 3`: the greedy matching keeps `(0, 1)` and `(2, 3)` and returns all four
   vertices, while `{1, 2}` is a cover. The 2-approximation theorem then pins the optimum at
   exactly `2`, so the factor `2` is attained.
2. The star with centre `0` and three leaves: the matching keeps one edge and returns `[0, 1]`
   against the optimum `{0}`, again attaining the factor `2`.
3. Edge cases: self-loops and repeated edges are skipped by the scan; edges with an undeclared
   endpoint are discarded by `approxCover`, so a graph whose edges are all loops or undeclared gets
   the empty cover; the empty graph gets the empty cover.
4. The polynomial-time certificate composes with list membership under `fun_prop`.
-/

public section

namespace ComplexityTests.VertexCoverApproximation

open Cslib.Complexity Cslib.Complexity.VertexCover Cslib.Algorithms.Lean.VertexCover
open Turing.MultiTapeTM

/-! ### 1. The path on four vertices attains the factor 2 -/

/-- The path `0 - 1 - 2 - 3`. -/
def path4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)])

example : greedyMatching path4.2 = [(0, 1), (2, 3)] := by decide +kernel

example : approxCover path4 = [0, 1, 2, 3] := by decide +kernel

/-- `{1, 2}` covers the path. -/
theorem path4_mem : (path4, 2) ∈ VertexCover := by
  refine mem_VertexCover_iff.2 ⟨{1, 2}, by decide +kernel, ?_, rfl⟩
  intro u hu v hv huv
  simp only [Graph.toSimpleGraph, SimpleGraph.fromRel_adj, path4, List.mem_cons,
    List.not_mem_nil, Prod.mk.injEq, or_false] at hu hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- The optimum of the path is exactly `2`: the cover `{1, 2}` gives `≤ 2`, and the
2-approximation theorem applied to the four returned vertices gives `≥ 2`. -/
theorem vertexCoverNum_path4 : path4.vertexCoverNum = 2 := by
  have hle := Graph.vertexCoverNum_le_of_mem_VertexCover path4_mem
  have hge := length_approxCover_le_two_mul_vertexCoverNum path4
  have hlen : (approxCover path4).length = 4 := by decide +kernel
  omega

/-- The factor `2` is attained on the path. -/
example : (approxCover path4).length = 2 * path4.vertexCoverNum := by
  rw [vertexCoverNum_path4]
  decide +kernel

/-! ### 2. The star attains the factor 2 -/

/-- The star with centre `0` and leaves `1`, `2`, `3`. -/
def star3 : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3)])

example : approxCover star3 = [0, 1] := by decide +kernel

/-- The centre covers the star. -/
theorem star3_mem : (star3, 1) ∈ VertexCover := by
  refine mem_VertexCover_iff.2 ⟨{0}, by decide +kernel, ?_, rfl⟩
  intro u hu v hv huv
  simp only [Graph.toSimpleGraph, SimpleGraph.fromRel_adj, star3, List.mem_cons,
    List.not_mem_nil, Prod.mk.injEq, or_false] at hu hv huv
  simp only [Finset.mem_singleton]
  omega

example : star3.vertexCoverNum = 1 ∧ (approxCover star3).length = 2 * star3.vertexCoverNum := by
  have hle := Graph.vertexCoverNum_le_of_mem_VertexCover star3_mem
  have hge := length_approxCover_le_two_mul_vertexCoverNum star3
  have hlen : (approxCover star3).length = 2 := by decide +kernel
  omega

/-! ### 3. Edge cases -/

/-- Self-loops and repeated edges are skipped by the scan. -/
example : matchingCover [(1, 1), (1, 2), (2, 1), (1, 2), (3, 3)] = [1, 2] := by decide +kernel

/-- A loop and an edge to the undeclared vertex `5` impose nothing; the cover is empty. -/
example : approxCover ([0, 1, 2], [(2, 2), (0, 5)]) = [] := by decide +kernel

/-- Undeclared edges are discarded before the scan, so they cannot block a declared edge. -/
example : approxCover ([0, 1, 2], [(0, 5), (0, 1)]) = [0, 1] := by decide +kernel

/-- The empty graph gets the empty cover. -/
example : approxCover ([], []) = [] := by decide +kernel

/-! ### 4. Polynomial time -/

/-- Whether vertex `0` is in the returned cover is polynomial-time decidable from the encoded
graph, by composing the certificate with list membership. -/
example : ComputableInPolyTime (fun G => decide (0 ∈ approxCover G)) encGraph encBool := by
  fun_prop

end ComplexityTests.VertexCoverApproximation
