/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.PerfectMatchingCut
public import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend
meta import CslibFrontier.Computability.PolyTime.CNF.PerfectMatchingCut
meta import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
meta import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend

/-! # Actual perfect matching cut execution, labeled counts and sharp resources

Small query counting is only a test oracle. Production uses the proved sharp native counter.
The whole crossing graph must be a perfect matching; neither empty nor one-sided cuts qualify.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDomination

namespace PerfectMatchingCutTests

open PerfectMatchingCut

set_option linter.hashCommand false

/-- Test-only exhaustive oracle for tiny actual ordinary queries. -/
@[expose] def smallCounter (x : TwoBoundary.BinaryFrontend.Input) : ℕ :=
  TwoBoundary.BinaryFrontend.execute dnfTestCounter (TwoBoundary.BinaryFrontend.compile x)

/-- Execute the real constructor and its direct empty branch, using the small test oracle. -/
@[expose] def count (x : Input) : ℕ := PerfectMatchingCut.run smallCounter x

/-- Original side assignments satisfying actual upper clauses and both neighborhood tests. -/
@[expose] def selections (x : Input) : List (List ℕ) :=
  if PerfectMatchingCut.isEmpty x then [] else
    let (_, side, conditions) := PerfectMatchingCut.build x
    ((List.range (2 ^ order x)).filter fun seed =>
      side.eval (Nat.testBit seed) && conditions.all (DNF.eval (Nat.testBit seed))).map fun seed =>
        (List.range (order x)).filter (Nat.testBit seed)

/- Empty graph, isolate, one edge, odd path, and two disjoint edges. -/
/-- info: (0, 0, 2, 0, 4) -/
#guard_msgs in
#eval (count (0, []), count (1, [[false]]), count (2, [[false, true], [true, false]]),
  count (3, [[false, true, false], [true, false, true], [false, true, false]]),
  count (4, [[false, true, false, false], [true, false, false, false],
    [false, false, false, true], [false, false, true, false]]))

/- The two labels are distinct, and both sides are nonempty. -/
/-- info: ([[0], [1]], [[1, 2], [0, 3]]) -/
#guard_msgs in
#eval (selections (2, [[false, true], [true, false]]),
  selections (4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]]))

/- Four-cycle, complete graph on four vertices, and a graph with an isolated vertex. -/
/-- info: (4, 0, 0) -/
#guard_msgs in
#eval (count (4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]),
  count (4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]),
  count (3, [[false, true, false], [true, false, false], [false, false, false]]))

/- A six-cycle has perfect matchings but no perfect matching cut; enumerate only original bits. -/
/-- info: [] -/
#guard_msgs in
#eval selections (6, [[false, true, false, false, false, true],
  [true, false, true, false, false, false], [false, true, false, true, false, false],
  [false, false, true, false, true, false], [false, false, false, true, false, true],
  [true, false, false, false, true, false]])

/- Empty input bypasses its continuation. Large-declaration writing does not enumerate the cube. -/
/-- info: (0, 2, true, true) -/
#guard_msgs in
#eval let x : Input := (32, [])
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (PerfectMatchingCut.build x))
  (PerfectMatchingCut.run (fun _ => 999) (0, []), qs.length,
    qs.all fun (n, _) => n == 95,
    qs.all fun (_, q) => q.length ≤ 10 * 32 ^ 3 && q.all fun c => c.length ≤ 3)

/-- The single undirected edge, represented by a conventional simple graph. -/
@[expose] def oneEdge : SimpleGraph (Fin 2) := ⊤

example : oneEdge.IsPerfectMatchingCut (fun i => decide (i = 1)) := by
  rw [SimpleGraph.isPerfectMatchingCut_iff]
  simp only [oneEdge, SimpleGraph.top_adj, ExistsUnique]
  decide

example : ¬oneEdge.IsPerfectMatchingCut (fun _ => true) := by
  rw [SimpleGraph.isPerfectMatchingCut_iff]
  simp only [oneEdge, SimpleGraph.top_adj, ExistsUnique]
  decide

example : ComputableInPolyTime PerfectMatchingCut.build encInput
    TwoBoundary.BinaryFrontend.encInput :=
  PerfectMatchingCut.build_polytime

open Classical in
/-- Actual original-input labeled-cut count, including empty inputs, with source clock and space. -/
example : ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
    (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      count (ofGraph G) = Fintype.card {side : Fin n → Bool // G.IsPerfectMatchingCut side} ∧
      cs.time (ofGraph G) ≤ C * ((encInput (ofGraph G)).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale n) := PerfectMatchingCut.exists_count_sharp_certificate

end PerfectMatchingCutTests
