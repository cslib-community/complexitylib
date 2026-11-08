/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.SpanningTrees
import CslibFrontier.Foundations.LinearAlgebra.Matrix.CauchyBinet

/-!
# Regression tests for the matrix-tree theorem and spanning-tree counting

The Cauchy–Binet formula is instantiated in its degenerate case (fewer columns than rows, an empty
sum). `Cslib.Complexity.Graph.spanningTreeCount` is evaluated by the kernel and compiled on small
graphs: triangles, `K₄` (Cayley's `4 ^ 2 = 16`), a `4`-cycle, a path, a disconnected graph, a single
vertex, no vertex, and an input with repeated vertices, a loop, a reversed edge and an undeclared
endpoint. Through `Cslib.Complexity.Graph.spanningTreeCount_eq_natCard` the kernel values count the
spanning trees of `SimpleGraph`s, Cayley's formula is instantiated at `n = 1, 2, 4`, and the
polynomial-time certificates are checked.
-/

namespace ComplexityTests.SpanningTrees

open Turing.MultiTapeTM Cslib.Complexity

/-! ### Cauchy–Binet -/

-- With fewer columns than rows, the sum over `3`-element subsets of `Fin 2` is empty.
example (A : Matrix (Fin 3) (Fin 2) ℤ) (B : Matrix (Fin 2) (Fin 3) ℤ) : (A * B).det = 0 := by
  rw [Matrix.det_mul_eq_sum_powersetCard]
  have : IsEmpty (Set.powersetCard (Fin 2) 3) := by
    rw [← not_nonempty_iff, Set.powersetCard.nonempty_iff]
    simp
  simp

/-! ### Concrete spanning-tree counts -/

/-- The triangle `K₃`. -/
def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

/-- The complete graph `K₄`. -/
def k4 : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])

/-- The `4`-cycle. -/
def cycle4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)])

/-- The path `0 - 1 - 2`. -/
def path3 : Graph := ([0, 1, 2], [(0, 1), (1, 2)])

/-- An edge and an isolated vertex. -/
def disconnected : Graph := ([0, 1, 2], [(0, 1)])

/-- The path `0 - 1 - 2`, with a repeated vertex, a loop, both orientations of an edge and an edge
to the undeclared vertex `5`. -/
def noisyPath : Graph := ([0, 1, 1, 2], [(0, 1), (1, 0), (1, 1), (1, 2), (2, 5)])

example : triangle.spanningTreeCount = 3 := by decide +kernel
example : k4.spanningTreeCount = 16 := by decide +kernel
example : cycle4.spanningTreeCount = 4 := by decide +kernel
example : path3.spanningTreeCount = 1 := by decide +kernel
example : disconnected.spanningTreeCount = 0 := by decide +kernel
-- A single vertex: the reduced Laplacian is empty, with determinant `1`.
example : Graph.spanningTreeCount ([7], []) = 1 := by decide +kernel
-- No vertex: no tree, since trees are nonempty.
example : Graph.spanningTreeCount ([], [(0, 1)]) = 0 := by decide +kernel
example : noisyPath.spanningTreeCount = 1 := by decide +kernel

/-- info: [3, 16, 4, 1, 0, 1, 0, 1] -/
#guard_msgs in
#eval [triangle, k4, cycle4, path3, disconnected, ([7], []), ([], [(0, 1)]), noisyPath].map
  Graph.spanningTreeCount

-- The reduced Laplacian of the triangle, on the vertices `1` and `2`.
example : triangle.reducedLaplacianRows = [[2, -1], [-1, 2]] := by decide +kernel

/-! ### Counting spanning trees of `SimpleGraph`s -/

/-- `K₄` has `16` spanning trees (Cayley's formula `n ^ (n - 2)`). -/
theorem natCard_isTree_k4 :
    Nat.card {T : SimpleGraph {v // v ∈ k4.1} // T ≤ k4.induced ∧ T.IsTree} = 16 := by
  have h := Graph.spanningTreeCount_eq_natCard k4
  rw [show k4.spanningTreeCount = 16 by decide +kernel] at h
  exact_mod_cast h.symm

-- A disconnected graph has no spanning tree.
example :
    Nat.card {T : SimpleGraph {v // v ∈ disconnected.1} //
      T ≤ disconnected.induced ∧ T.IsTree} = 0 := by
  have h := Graph.spanningTreeCount_eq_natCard disconnected
  rw [show disconnected.spanningTreeCount = 0 by decide +kernel] at h
  exact_mod_cast h.symm

-- The matrix-tree theorem over `ℚ`: every reduced Laplacian determinant of `K₄` is `16`.
example (r : {v // v ∈ k4.1}) :
    ((k4.induced.lapMatrix ℚ).submatrix (Subtype.val : {v // v ≠ r} → _) Subtype.val).det =
      16 := by
  rw [SimpleGraph.det_lapMatrix_submatrix_eq_natCard_isTree' ℚ, natCard_isTree_k4]
  norm_num

/-! ### Cayley's formula -/

-- `16` labelled trees on four vertices, agreeing with the kernel count for `K₄` above.
example : Nat.card {T : SimpleGraph (Fin 4) // T.IsTree} = 16 := by
  rw [SimpleGraph.natCard_isTree_eq_card_pow, Fintype.card_fin]
  rfl

-- One vertex: the single-vertex tree (`1 ^ (1 - 2) = 1` with truncated subtraction).
example : Nat.card {T : SimpleGraph (Fin 1) // T.IsTree} = 1 := by
  rw [SimpleGraph.natCard_isTree_eq_card_pow, Fintype.card_fin]
  rfl

-- Two vertices: the single edge.
example : Nat.card {T : SimpleGraph (Fin 2) // T.IsTree} = 1 := by
  rw [SimpleGraph.natCard_isTree_eq_card_pow, Fintype.card_fin]
  rfl

/-! ### Polynomial time -/

example : ComputableInPolyTime Graph.spanningTreeCount encGraph encIntBin :=
  Graph.computableInPolyTime_spanningTreeCount

example : ComputableInPolyTime
    (fun G : Graph => Nat.card {T : SimpleGraph {v // v ∈ G.1} // T ≤ G.induced ∧ T.IsTree})
    encGraph encNat :=
  Graph.computableInPolyTime_natCard_isTree

end ComplexityTests.SpanningTrees
