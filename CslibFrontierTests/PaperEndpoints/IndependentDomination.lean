/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.IndependentDomination
public import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend
meta import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
meta import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
meta import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend

/-! # Original graph counts, empty/isolated/dense graphs and sharp resource clients -/

public section

open Cslib.Logic.PL Turing.MultiTapeTM
open IndependentDomination

set_option linter.hashCommand false

/-- Test-only graph execution, using the small exhaustive oracle. -/
@[expose] def graphTestCount (x : Input) : ℕ :=
  TwoBoundary.BinaryFrontend.execute dnfTestCounter (TwoBoundary.BinaryFrontend.compile (build x))

/- Empty graph, three isolated vertices, a single edge, and a three-vertex path. -/
/-- info: (1, 1, 2, 2) -/
#guard_msgs in
#eval (graphTestCount (0, []),
  graphTestCount (3, List.replicate 3 (List.replicate 3 false)),
  graphTestCount (2, [[false, true], [true, false]]),
  graphTestCount (3, [[false, true, false], [true, false, true], [false, true, false]]))

/- Triangle and four-vertex star: original selections, with no marking multiplicity. -/
/-- info: (3, 2) -/
#guard_msgs in
#eval (graphTestCount (3, [[false, true, true], [true, false, true], [true, true, false]]),
  graphTestCount (4, [[false, true, true, true], [true, false, false, false],
    [true, false, false, false], [true, false, false, false]]))

/-- info: [(5, 14), (5, 14)] -/
#guard_msgs in
#eval (TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile
  (build (3, [[false, true, false], [true, false, true], [false, true, false]])))).map
    fun (N, q) => (N, q.length)

example : ComputableInPolyTime build encInput TwoBoundary.BinaryFrontend.encInput := build_polytime

open Classical in
example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (TwoBoundary.BinaryFrontend.compile (build (ofGraph G))) =
      Fintype.card {σ : Fin n → Bool // G.IsIndepSet {u | σ u = true} ∧
        ∀ u, σ u = true ∨ ∃ v, G.Adj u v ∧ σ v = true} := plan_count G

example {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (N : ℕ) (q : CNF ℕ)
    (hq : (N, q) ∈ TwoBoundary.BinaryFrontend.queries
      (TwoBoundary.BinaryFrontend.compile (build (ofGraph G)))) :
    N = 2 * n - 1 ∧ q.length ≤ 3 * n ^ 2 ∧
      ∀ c ∈ q, c.length ≤ 3 ∧ ∀ l ∈ c, l.1 < N := plan_budget G N q hq
