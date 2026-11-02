/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceNetworkSize

/-!
# Tests for the incidence network of Lemma D.2

A system of three tests on three variables, in two groups on each side. The array `[1, 1, 0, 1]`
selects one incidence of the pairs `(0, 0)`, `(0, 1)` and `(1, 1)`. The pairs have `4, 2, 0, 1`
incidences, so `2, 1, 0, 0` index wires; padding to size `6` adds three edges. The network is
rows-first bipartite, and the hypotheses of the degree and wire bounds hold for it.
-/

@[expose] public section

namespace ComplexityTests.TensorNetworkIncidenceNetwork

open Cslib.Circuits.Frontier Cslib.Circuits.Frontier.IncidenceNetwork Cslib.Complexity

/-- Three tests on the variables `0, 1, 2`: `x₀ x₁ + x₂`, `x₁` and `x₀ + x₁ x₂`. -/
abbrev sys : List (List (List ℕ)) := [[[0, 1], [2]], [[1]], [[0], [1, 2]]]

/-- The network of the array `[1, 1, 0, 1]`: two groups, degree cap `4`, size `6`, precision and
truncation order `4`, three variables. -/
abbrev G : ℕ × DescribedNetwork Desc := network 4 4 2 4 6 3 sys [1, 1, 0, 1]

example : List.residueClass 2 3 0 = [0, 2] := by decide
example : pairInc 2 sys 0 0 = [(0, 0), (0, 2), (1, 0), (1, 2)] := by decide
example : pairInc 2 sys 0 1 = [(0, 1), (1, 1)] := by decide
example : pairInc 2 sys 1 0 = [] := by decide
example : pairInc 2 sys 1 1 = [(0, 1)] := by decide
example : numInc sys = 7 := by decide

example : live 2 4 [1, 1, 0, 1] = true := by decide
example : live 2 2 [1, 1, 0, 1] = false := by decide

example : numWires 2 sys [1, 1, 0, 1] = 3 := by decide
example : rowPorts 2 sys [1, 1, 0, 1] 0 = [0, 1, 2] := by decide
example : colPorts 2 sys [1, 1, 0, 1] 1 = [2] := by decide
example : G.1 = 5 := by decide
example : G.2.numEdges = 6 := by decide
example : G.2.vertices.length = 10 := by decide

-- The network is rows-first bipartite.
example : G.2.IsRowsFirstBipartite G.1 := isRowsFirstBipartite_network

-- A dead array gets the padding and one isolated row.
example : (network 4 4 2 2 6 3 sys [1, 1, 0, 1]).2.vertices.length = 13 := by
  rw [length_vertices_network]
  decide

/-! ### The bounds are not vacuous -/

-- Every scope has at most three variables, and every variable lies in at most three scopes.
example : (rowPorts 2 sys [1, 1, 0, 1] 0).length ≤ (3 / 2 + 1) * 3 :=
  length_rowPorts_le (by norm_num) 0 (S := 3) (by decide)

example : (colPorts 2 sys [1, 1, 0, 1] 0).length ≤ (3 / 2 + 1) * 3 :=
  length_colPorts_le (by norm_num) (by norm_num) (by decide) (D := 3) (by decide)

-- `N + K = 7 + 4 ≤ 3 K`, so the wire bound gives at most `4 + 4 ⌈log₂ 9⌉ = 20` wires.
example : numWires 2 sys [1, 1, 0, 1] ≤ 2 * 2 + 4 * Nat.clog 2 (3 * 3) :=
  numWires_le (by norm_num) (by decide) (R := 3) (by decide)

-- Stars and bars: `C(11, 4) = 330 ≤ 9 ^ 4`.
example : (7 + 4).choose 4 ≤ (3 * 3) ^ 4 := Nat.add_choose_le_three_mul_pow (by norm_num)

/-! ### The parameters of Lemma D.2 -/

-- `⌈16 ^ (1/4)⌉ = 2` and `⌈17 ^ (1/4)⌉ = 3`.
example : Nat.ceilQuarter 16 = 2 :=
  le_antisymm (Nat.find_min' _ (by norm_num)) (by
    by_contra h
    have := Nat.le_ceilQuarter_pow 16
    interval_cases (Nat.ceilQuarter 16) <;> simp_all)

-- `16 ≤ J ^ 4` and `J ² ≤ 4 · 16` at `J = ⌈16 ^ (1/4)⌉`.
example : 16 ≤ Nat.ceilQuarter 16 ^ 4 ∧ Nat.ceilQuarter 16 * Nat.ceilQuarter 16 ≤ 4 * 16 :=
  ⟨Nat.le_ceilQuarter_pow 16, Nat.ceilQuarter_mul_self_le (by norm_num)⟩

end ComplexityTests.TensorNetworkIncidenceNetwork
