/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.TSP
import Complexity.Tactic.PolyTime

/-!
# Traveling salesman tests

Concrete, boundary, `fun_prop`, and axiom checks for `TSP`, its verifier, and the reduction
`HamCycle.toTSP` from `HamCycle`.
-/

namespace ComplexityTests.NPCompleteGraphs.TSP

open Cslib.Complexity Turing.MultiTapeTM

/-! ### Headline results -/

example : TSP ∈ NP encTSP := TSP.mem_NP
example : NPComplete encTSP TSP := TSP_npComplete
example : PolyTimeReducible encGraph encTSP HamCycle TSP := polyTimeReducible_HamCycle_TSP

-- Certificates are quadratic in the encoded instance.
example : IsVerifier encTSP (Polynomial.X ^ 2) TSP.verifier TSP := TSP.isVerifier

/-! ### Compositional `fun_prop` synthesis -/

example : ComputableInPolyTime HamCycle.toTSP encGraph encTSP := by fun_prop

example : ComputableInPolyTime TSP.verifier (encPair encTSP encBits) encBool := by fun_prop

example : ComputableInPolyTime (fun x : List (List ℕ) × List ℕ => TSP.tourLength x.1 x.2)
    (encPair (encList (encList encNat)) (encList encNat)) encNat := by
  fun_prop

-- Tour lengths compose with the binary comparison and sum certificates.
example : ComputableInPolyTime
    (fun x : (List (List ℕ) × List ℕ) × ℕ => decide (TSP.tourLength x.1.1 x.1.2 + x.2 ≤ x.2 * 2))
    (encPair (encPair (encList (encList encNat)) (encList encNat)) encNat) encBool := by
  have htour := TSP.computableInPolyTime_tourLength.tidy
  refine .of_tidy ?_
  fun_prop

/-- Non-membership in `TSP`, checked over the permutations of the cities. -/
private theorem notMem_TSP {x : List (List ℕ) × ℕ}
    (h : ∀ p ∈ (List.range x.1.length).permutations', x.2 < TSP.tourLength x.1 p) :
    x ∉ TSP := fun ⟨p, hp, hlen⟩ =>
  absurd hlen (Nat.not_le.2 (h p (List.mem_permutations'.2 hp)))

/-! ### Distances and tour lengths -/

-- Four cities on a cycle of distance-`1` steps, with distance `5` across.
private def square : List (List ℕ) := [[0, 1, 5, 1], [1, 0, 1, 5], [5, 1, 0, 1], [1, 5, 1, 0]]

example : TSP.dist square 0 2 = 5 := rfl
example : TSP.tourLength square [0, 1, 2, 3] = 4 := rfl
example : TSP.tourLength square [1, 2, 3, 0] = 4 := rfl
example : TSP.tourLength square [0, 2, 1, 3] = 12 := rfl

-- Distances need not be symmetric: the direction of the tour matters.
private def oneWay : List (List ℕ) := [[0, 1, 9], [9, 0, 1], [1, 9, 0]]

example : TSP.tourLength oneWay [0, 1, 2] = 3 := rfl
example : TSP.tourLength oneWay [0, 2, 1] = 27 := rfl

-- The tour length as a sum over positions, the last one returning to the first city.
example : TSP.tourLength oneWay [0, 1, 2] =
    TSP.dist oneWay 0 1 + TSP.dist oneWay 1 2 + TSP.dist oneWay 2 0 := by
  rw [TSP.tourLength_eq_sum]
  rfl

-- The empty tour has length `0`; a tour of one city pays its diagonal entry.
example : TSP.tourLength square [] = 0 := rfl
example : TSP.tourLength [[7]] [0] = 7 := rfl

-- Entries missing from ragged rows, or from missing rows, read `0`.
example : TSP.dist [[3], []] 0 0 = 3 := rfl
example : TSP.dist [[3], []] 0 1 = 0 := rfl
example : TSP.dist [[3], []] 5 0 = 0 := rfl
example : TSP.tourLength [[3], []] [0, 1] = 0 := rfl

/-! ### Membership in `TSP` -/

example : (square, 4) ∈ TSP := ⟨[0, 1, 2, 3], by decide, by decide⟩
example : (square, 3) ∉ TSP := notMem_TSP (by decide)
example : (oneWay, 3) ∈ TSP := ⟨[0, 1, 2], by decide, by decide⟩
example : (oneWay, 2) ∉ TSP := notMem_TSP (by decide)

-- The matrix without rows is a yes-instance, through the empty tour.
example : (([] : List (List ℕ)), 0) ∈ TSP := ⟨[], by decide, by decide⟩

-- One city: the tour pays the diagonal entry.
example : ([[0]], 0) ∈ TSP := ⟨[0], by decide, by decide⟩
example : ([[1]], 0) ∉ TSP := notMem_TSP (by decide)

-- Ragged matrices: missing entries read `0`, so here every tour has length `0`.
example : ([[3], []], 0) ∈ TSP := ⟨[0, 1], by decide, by decide⟩

-- Rows of different lengths: the tour `[0, 2, 1]` pays `0 + 7 + 1`, and `[0, 1, 2]` pays
-- `2 + 0 + 7`.
private def ragged : List (List ℕ) := [[0, 2], [1], [7, 7, 7]]

example : (ragged, 8) ∈ TSP := ⟨[0, 2, 1], by decide, by decide⟩
example : (ragged, 7) ∉ TSP := notMem_TSP (by decide)

-- The budget is a natural number of any size; the binary encoding stays short.
example : (square, 2 ^ 100) ∈ TSP := ⟨[0, 1, 2, 3], by decide, by decide⟩
example : (encNat (2 ^ 100)).length = 101 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]

/-! ### The verifier -/

-- A certificate naming the tour `p` of `n` cities: one block of `n` bits for each city of `p`,
-- whose number of set bits is that city.
private def tour (n : ℕ) (p : List ℕ) : List Bool :=
  p.flatMap fun c => (List.range n).map fun i => decide (i < c)

example : Graph.decodeVertexList (List.range 4) (tour 4 [0, 2, 1, 3]) = [0, 2, 1, 3] := rfl

-- The cheapest tour of `square` is accepted at budget `4` and rejected at budget `3`; a costlier
-- tour needs a larger budget.
example : TSP.verifier ((square, 4), tour 4 [0, 1, 2, 3]) = true := rfl
example : TSP.verifier ((square, 3), tour 4 [0, 1, 2, 3]) = false := rfl
example : TSP.verifier ((square, 12), tour 4 [0, 2, 1, 3]) = true := rfl
example : TSP.verifier ((square, 11), tour 4 [0, 2, 1, 3]) = false := rfl

-- An ordering that repeats or omits a city is rejected whatever the budget.
example : TSP.verifier ((square, 100), tour 4 [0, 0, 1, 2]) = false := rfl
example : TSP.verifier ((square, 100), []) = false := rfl

-- The direction of the tour matters for asymmetric distances.
example : TSP.verifier ((oneWay, 3), tour 3 [0, 1, 2]) = true := rfl
example : TSP.verifier ((oneWay, 3), tour 3 [0, 2, 1]) = false := rfl

-- Boundaries: the matrix without rows is accepted with the empty certificate, and a single city
-- pays its diagonal entry.
example : TSP.verifier ((([] : List (List ℕ)), 0), []) = true := rfl
example : TSP.verifier (([[1]], 0), tour 1 [0]) = false := rfl
example : TSP.verifier (([[1]], 1), tour 1 [0]) = true := rfl

-- Ragged matrices: missing entries read `0`.
example : TSP.verifier ((ragged, 8), tour 3 [0, 2, 1]) = true := rfl
example : TSP.verifier ((ragged, 7), tour 3 [0, 2, 1]) = false := rfl

-- Binary distances and budgets: distances `2 ^ 100` are added and compared without unary
-- expansion.
example : TSP.verifier (([[0, 2 ^ 100], [2 ^ 100, 0]], 2 ^ 101), tour 2 [0, 1]) = true := by
  decide
example : TSP.verifier (([[0, 2 ^ 100], [2 ^ 100, 0]], 2 ^ 101 - 1), tour 2 [1, 0]) = false := by
  decide

/-! ### The reduction from `HamCycle` -/

-- The cycle on four vertices: distance `1` along the cycle, `2` across and on the diagonal.
private def c4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3), (3, 0)])

example : HamCycle.toTSP c4 =
    ([[2, 1, 2, 1], [1, 2, 1, 2], [2, 1, 2, 1], [1, 2, 1, 2]], 4) := by decide

example : HamCycle.toTSP c4 ∈ TSP := ⟨[0, 1, 2, 3], by decide, by decide⟩
example : c4 ∈ HamCycle := (HamCycle.toTSP_mem_iff c4).1 ⟨[0, 1, 2, 3], by decide, by decide⟩

-- The path on four vertices has no Hamiltonian cycle: every tour pays `2` for a missing edge.
private def p4 : Graph := ([0, 1, 2, 3], [(0, 1), (1, 2), (2, 3)])

example : p4 ∉ HamCycle := fun h => notMem_TSP (by decide) ((HamCycle.toTSP_mem_iff p4).2 h)

-- Cities are the distinct declared vertices in the order of their first occurrences; labels
-- need not be contiguous, and self-loops are ignored.
private def triangle : Graph := ([10, 20, 10, 30], [(10, 20), (20, 30), (30, 10), (10, 10)])

example : triangle.distinctVertices = [10, 20, 30] := by decide
example : HamCycle.toTSP triangle = ([[2, 1, 1], [1, 2, 1], [1, 1, 2]], 3) := by decide
example : triangle ∈ HamCycle :=
  (HamCycle.toTSP_mem_iff triangle).1 ⟨[0, 1, 2], by decide, by decide⟩

-- Edges with an undeclared endpoint are never used: `0 - 7 - 2` does not close the path.
private def detour : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 7), (7, 0)])

example : HamCycle.toTSP detour = ([[2, 1, 2], [1, 2, 1], [2, 1, 2]], 3) := by decide
example : detour ∉ HamCycle :=
  fun h => notMem_TSP (by decide) ((HamCycle.toTSP_mem_iff detour).2 h)

-- Graphs with fewer than three distinct vertices map to a fixed no-instance.
example : HamCycle.toTSP ([0, 1, 0], [(0, 1)]) = ([[1]], 0) := by decide
example : HamCycle.toTSP ([], []) = ([[1]], 0) := by decide
example : (([0, 1, 0], [(0, 1)]) : Graph) ∉ HamCycle :=
  fun h => notMem_TSP (by decide) ((HamCycle.toTSP_mem_iff _).2 h)
example : (([], []) : Graph) ∉ HamCycle :=
  fun h => notMem_TSP (by decide) ((HamCycle.toTSP_mem_iff _).2 h)

/-! ### Axiom checks for headline theorems -/

/--
info: 'Cslib.Complexity.TSP.computableInPolyTime_tourLength' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TSP.computableInPolyTime_tourLength

/--
info: 'Cslib.Complexity.TSP.isVerifier' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TSP.isVerifier

/--
info: 'Cslib.Complexity.TSP.computableInPolyTime_verifier' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TSP.computableInPolyTime_verifier

/--
info: 'Cslib.Complexity.TSP.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.TSP.mem_NP

/--
info: 'Cslib.Complexity.HamCycle.toTSP_mem_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HamCycle.toTSP_mem_iff

/--
info: 'Cslib.Complexity.HamCycle.computableInPolyTime_toTSP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.HamCycle.computableInPolyTime_toTSP

/--
info: 'Cslib.Complexity.polyTimeReducible_HamCycle_TSP' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.polyTimeReducible_HamCycle_TSP

end ComplexityTests.NPCompleteGraphs.TSP
