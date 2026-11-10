/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.DominatingInducedMatching
public import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend
meta import CslibFrontier.Computability.PolyTime.CNF.DominatingInducedMatching
meta import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
meta import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend

/-! # Actual dominating induced matching counts, endpoint uniqueness and source budgets

The tiny exhaustive query oracle is a test instrument. Production uses the proved sharp counter.
Each matching is an unordered-edge Mathlib subgraph; no label, orientation or marking is counted.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDomination

namespace DominatingInducedMatchingTests

open DominatingInducedMatching

set_option linter.hashCommand false

/-- Test-only ordinary-query execution of the actual constructed graph plan. -/
@[expose] def count (x : Input) : ℕ :=
  TwoBoundary.BinaryFrontend.execute dnfTestCounter
    (TwoBoundary.BinaryFrontend.compile (DominatingInducedMatching.build x))

/-- Original support selections passing the actual upper/cover/neighborhood constraints. -/
@[expose] def selections (x : Input) : List (List ℕ) :=
  let (_, side, conditions) := DominatingInducedMatching.build x
  ((List.range (2 ^ order x)).filter fun seed =>
    side.eval (Nat.testBit seed) && conditions.all (DNF.eval (Nat.testBit seed))).map fun seed =>
      (List.range (order x)).filter (Nat.testBit seed)

/- Empty graph, isolates, edge, three/four-vertex paths and two disjoint edges. -/
/-- info: (1, 1, 1, 2, 1, 1) -/
#guard_msgs in
#eval (count (0, []), count (3, List.replicate 3 (List.replicate 3 false)),
  count (2, [[false, true], [true, false]]),
  count (3, [[false, true, false], [true, false, true], [false, true, false]]),
  count (4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]]),
  count (4, [[false, true, false, false], [true, false, false, false],
    [false, false, false, true], [false, false, true, false]]))

/- Isolates are fixed unselected; an edge has one support, and only the middle edge works on P4. -/
/-- info: ([[]], [[0, 1]], [[1, 2]]) -/
#guard_msgs in
#eval (selections (3, List.replicate 3 (List.replicate 3 false)),
  selections (2, [[false, true], [true, false]]),
  selections (4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]]))

/- A triangle has three choices, a star three, but C4 and K4 have no efficient edge domination. -/
/-- info: (3, 3, 0, 0) -/
#guard_msgs in
#eval (count (3, [[false, true, true], [true, false, true], [true, true, false]]),
  count (4, [[false, true, true, true], [true, false, false, false],
    [true, false, false, false], [true, false, false, false]]),
  count (4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]),
  count (4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]))

/-- info: 3 -/
#guard_msgs in
#eval count (6, [[false, true, false, false, false, true],
  [true, false, true, false, false, false], [false, true, false, true, false, false],
  [false, false, true, false, true, false], [false, false, false, true, false, true],
  [true, false, false, false, true, false]])

/- Actual construction at 32 declared vertices, without enumerating endpoint selections. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval Id.run do
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (DominatingInducedMatching.build (32, [])))
  return (qs.length, qs.all fun (n, _) => n == 63,
    qs.all fun (_, q) => q.length ≤ 6 * 32 ^ 3 && q.all fun c => c.length ≤ 3)

/-- info: [(0, 0)] -/
#guard_msgs in
#eval (TwoBoundary.BinaryFrontend.queries
  (TwoBoundary.BinaryFrontend.compile (DominatingInducedMatching.build (0, [])))).map
    fun (n, q) => (n, q.length)

/-- The conventional two-vertex graph with its one unordered edge. -/
@[expose] def oneEdge : SimpleGraph (Fin 2) := ⊤

example : (⊤ : oneEdge.Subgraph).IsDominatingInducedMatching := by
  rw [SimpleGraph.Subgraph.isDominatingInducedMatching_iff]
  refine ⟨?_, SimpleGraph.Subgraph.IsInduced.top, fun _ _ _ => Or.inl (Set.mem_univ _)⟩
  intro u _
  change ∃! v, oneEdge.Adj u v
  simp only [oneEdge, SimpleGraph.top_adj, ExistsUnique]
  fin_cases u <;> decide

example : ¬(⊥ : oneEdge.Subgraph).IsDominatingInducedMatching := by
  intro h
  obtain ⟨_, _, hc⟩ := (SimpleGraph.Subgraph.isDominatingInducedMatching_iff _).mp h
  have ha : oneEdge.Adj 0 1 := by simp [oneEdge]
  rcases hc 0 1 ha with h | h <;> exact h

example : ComputableInPolyTime DominatingInducedMatching.build encInput
    TwoBoundary.BinaryFrontend.encInput := DominatingInducedMatching.build_polytime

open Classical in
/-- The actual counter's output counts matching objects, rather than unproved support witnesses. -/
example : ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
    (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
    ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      count (ofGraph G) = Fintype.card {M : G.Subgraph // M.IsDominatingInducedMatching} ∧
      cs.time (ofGraph G) ≤ C * ((encInput (ofGraph G)).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale n) :=
  DominatingInducedMatching.exists_count_sharp_certificate

end DominatingInducedMatchingTests
