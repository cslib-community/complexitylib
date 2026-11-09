/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingDistribution
public import CslibFrontierTests.PaperEndpoints.InducedMatchingInterval
public import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend
meta import CslibFrontier.Computability.Complexity.FineGrained.InducedMatchingDistribution
meta import CslibFrontier.Computability.PolyTime.CNF.InducedMatching
meta import CslibFrontierTests.PaperEndpoints.InducedMatchingInterval
meta import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend

/-! # Actual induced matching total and size-list execution

The tiny no-size query oracle exhausts written ordinary queries. The exact-size oracle computes
unique circuit traces for original selections. These are tests; production uses the certified
unrestricted-density native counter and the actual sequential coefficient loop.
-/

public section

namespace InducedMatchingDistributionTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM

set_option linter.hashCommand false

/-- Test-only execution of the actual no-size-test query plan. -/
@[expose] def total (g : IndependentDomination.Input) : ℕ :=
  TwoBoundary.BinaryFrontend.execute dnfTestCounter
    (TwoBoundary.BinaryFrontend.compile (InducedMatching.build g))

/-- Actual coefficient traversal with a tiny oracle evaluating the actual exact-size constructor. -/
@[expose] def distribution (g : IndependentDomination.Input) : List ℕ :=
  InducedMatching.Distribution.run InducedMatchingIntervalTests.intervalCount g

/- The empty coefficient is retained; declared isolates add no selected endpoint multiplicity. -/
/-- info: ([1], [1, 0], [1, 1], [1, 3]) -/
#guard_msgs in
#eval (distribution (0, []), distribution (3, List.replicate 3 (List.replicate 3 false)),
  distribution (2, [[false, true], [true, false]]),
  distribution (3, [[false, true, true], [true, false, true], [true, true, false]]))

/- Zero coefficients and increasing edge-size order are part of the actual output. -/
/-- info: ([1, 3, 0], [1, 2, 1], [1, 6, 0], [1, 1]) -/
#guard_msgs in
#eval (distribution InducedMatchingIntervalTests.pathFour,
  distribution InducedMatchingIntervalTests.disjointEdges,
  distribution (4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]),
  distribution (3, [[false, true, false], [true, false, false], [false, false, false]]))

/-- info: [1, 4, 1] -/
#guard_msgs in
#eval distribution (5, [[false, true, false, false, false], [true, false, true, false, false],
  [false, true, false, true, false], [false, false, true, false, true],
  [false, false, false, true, false]])

/-- info: [1, 6, 3, 0] -/
#guard_msgs in
#eval distribution (6, [[false, true, false, false, false, true],
  [true, false, true, false, false, false], [false, true, false, true, false, false],
  [false, false, true, false, true, false], [false, false, false, true, false, true],
  [true, false, false, false, true, false]])

/- Independent actual no-size query execution agrees with the complete coefficient sum. -/
/-- info: [(1, 1), (1, 1), (2, 2), (4, 4), (4, 4), (4, 4)] -/
#guard_msgs in
#eval ([(0, []), (3, List.replicate 3 (List.replicate 3 false)),
  (2, [[false, true], [true, false]]), InducedMatchingIntervalTests.pathFour,
  InducedMatchingIntervalTests.disjointEdges,
  (3, [[false, true, true], [true, false, true], [true, true, false]])].map fun g =>
    (total g, (distribution g).sum))

/- No cardinality gates: the 32-vertex total-count plan uses exactly 63 variables per query. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval Id.run do
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (InducedMatching.build (32, [])))
  return (qs.length, qs.all fun (n, _) => n == 63,
    qs.all fun (n, q) => q.length ≤ 6 * 32 ^ 3 &&
      q.all fun c => c.length ≤ 3 && c.all fun l => l.1 < n)

example : InducedMatching.Distribution.rounds (0, []) = 1 := rfl

open Classical in
/-- A client pins the complete list, binary output bound and actual native resources together. -/
example : ∃ distribution : IndependentDomination.Input → List ℕ,
    ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encNat),
      ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          distribution (IndependentDomination.ofGraph G) =
            (List.range (n / 2 + 1)).map (fun k => Nat.card {M : G.Subgraph //
              M.IsMatching ∧ M.IsInduced ∧ Nat.card M.edgeSet = k}) ∧
          (encList encNat (distribution (IndependentDomination.ofGraph G))).length ≤
            (n / 2 + 1) * (2 * (n + 1) + 1) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput
              (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
                (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  InducedMatching.Distribution.exists_distribution_realEta_certificate

end InducedMatchingDistributionTests
