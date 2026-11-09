/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.ContractionMatching

/-! # Permanents and perfect matchings by tensor contraction: checked instances

Permanents of small `0/1` matrices (the all-ones `3 × 3` matrix, the identity, a matrix with an
empty row, a matrix given by rows of unequal length), perfect matchings of the cycle `C₆` and of
`K₃,₃`, the guard on instances with an empty scope, the edge list of a graph with repeated,
reversed and loop edges, and the values of the two counters on instances meeting their degree
promises. -/

namespace ComplexityTests.ContractionMatching

open Finset Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.ContractionMatching

/-! ### Permanents -/

/-- The all-ones `3 × 3` matrix. -/
def ones₃ : List (List Bool) := [[true, true, true], [true, true, true], [true, true, true]]

/-- The `3 × 3` identity matrix. -/
def id₃ : List (List Bool) := [[true, false, false], [false, true, false], [false, false, true]]

-- The all-ones matrix has permanent `3! = 6`, on both sides of the reduction.
example : (CSP.permanentInstance 3 (rowEntry ones₃)).partitionFunction CSP.exactlyOneWeight =
    6 := by
  decide +kernel

example : (rowsMatrix ones₃).permanent = 6 := by
  rw [rowsMatrix_eq, ← CSP.partitionFunction_permanentInstance]
  decide +kernel

-- The identity has permanent one.
example : (rowsMatrix id₃).permanent = 1 := by
  rw [rowsMatrix_eq, ← CSP.partitionFunction_permanentInstance]
  decide +kernel

-- Rows of unequal length are cut or padded with zeros: `[[1, 0], [1, 1]]` has permanent one.
example : rowsMatrix [[true], [true, true, true]] = !![1, 0; 1, 1] := by
  decide

example : (rowsMatrix [[true], [true, true, true]]).permanent = 1 := by
  rw [rowsMatrix_eq, ← CSP.partitionFunction_permanentInstance]
  decide +kernel

-- Each nonzero entry `(i, j)` is the variable `3 i + j`, in its row and its column.
example : (CSP.permanentInstance 3 (rowEntry id₃)) =
    [((), [0]), ((), [4]), ((), [8]), ((), [0]), ((), [4]), ((), [8])] := by
  decide

example : (CSP.permanentInstance 3 (rowEntry ones₃)).vars.count 5 = 2 := by
  decide

-- A matrix with an empty row: the row constraint has no variable, so the guard answers the zero
-- instance, and the permanent is zero.
example : guarded 2 (CSP.permanentInstance 2 (rowEntry [[true, true], [false, false]])) =
    zeroInstance := by
  decide

example : (rowsMatrix [[true, true], [false, false]]).permanent = 0 := by
  rw [rowsMatrix_eq, ← CSP.partitionFunction_permanentInstance]
  decide +kernel

-- Wide constraints are guarded out too.
example : guarded 2 (CSP.permanentInstance 3 (rowEntry ones₃)) = zeroInstance := by
  decide

/-- The counter for at most three nonzero entries per row and column outputs `6` on the all-ones
matrix, which meets the degree promise. -/
example : ∃ count : List (List Bool) → ℕ, count ones₃ = 6 := by
  obtain ⟨count, A, e, b, hcount, -⟩ := exists_permanentCounter 3
  refine ⟨count, ?_⟩
  rw [hcount ones₃ (by decide) (by decide), rowsMatrix_eq,
    ← CSP.partitionFunction_permanentInstance]
  decide +kernel

/-! ### Perfect matchings -/

/-- The cycle `0 - 1 - 2 - 3 - 4 - 5 - 0`. -/
def cycle₆ : Graph := (List.range 6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)])

/-- The complete bipartite graph `K₃,₃` with sides `{0, 1, 2}` and `{3, 4, 5}`. -/
def k₃₃ : Graph :=
  (List.range 6, (List.range 3).flatMap fun i => (List.range 3).map fun j => (i, j + 3))

-- The cycle `C₆` has two perfect matchings.
example : cycle₆.perfectMatchingInstance.partitionFunction CSP.exactlyOneWeight = 2 := by
  decide +kernel

-- `K₃,₃` has `3! = 6` perfect matchings.
example : k₃₃.perfectMatchingInstance.partitionFunction CSP.exactlyOneWeight = 6 := by
  decide +kernel

example : Nat.card {M : k₃₃.induced.Subgraph // M.IsPerfectMatching} = 6 := by
  rw [← Graph.partitionFunction_perfectMatchingInstance]
  decide +kernel

-- The edge list drops the loop `(1, 1)` and the edge `(2, 5)` to an undeclared vertex, and keeps
-- one copy of `0 - 1` among `(0, 1)`, `(1, 0)` and `(0, 1)`.
example : Graph.edgeList ([0, 1, 2, 1], [(0, 1), (1, 0), (1, 1), (1, 2), (2, 5), (0, 1)]) =
    [(0, 1), (1, 2)] := by
  decide

-- The path `0 - 1` with the isolated vertex `2`: the constraint of `2` has no variable, the guard
-- answers the zero instance, and there is no perfect matching.
example : guarded 2 (Graph.perfectMatchingInstance ([0, 1, 2], [(0, 1)])) = zeroInstance := by
  decide

example : Nat.card {M : Graph.induced ([0, 1, 2], [(0, 1)]) |>.Subgraph // M.IsPerfectMatching} =
    0 := by
  rw [← Graph.partitionFunction_perfectMatchingInstance]
  decide +kernel

/-- The counter for maximum degree three outputs `6` on `K₃,₃`, which meets the degree promise:
the degree bound is checked on the edge list. -/
example : ∃ count : Graph → ℕ, count k₃₃ = 6 := by
  obtain ⟨count, A, e, b, hcount, -⟩ := exists_perfectMatchingCounter 3
  refine ⟨count, ?_⟩
  rw [hcount k₃₃ fun v => (Graph.card_neighborSet_le v).trans (by revert v; decide),
    ← Graph.partitionFunction_perfectMatchingInstance]
  decide +kernel

end ComplexityTests.ContractionMatching
