/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.InducedMatchingInterval
public import ComplexityTests.PaperEndpoints.CardinalityInterval
meta import Complexity.Computability.PolyTime.CNF.InducedMatchingInterval
meta import ComplexityTests.PaperEndpoints.CardinalityInterval

/-! # Actual size-constrained induced matching construction

The small oracle enumerates original vertex selections and computes their unique gate traces.
It never enumerates auxiliary assignments. Production uses the proved sharp native counter.
-/

public section

namespace InducedMatchingIntervalTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDominationInterval

set_option linter.hashCommand false

/-- Test-only evaluation of the actual degree-one/functional size-test/neighbor construction. -/
@[expose] def intervalCount (x : Input) : ℕ :=
  let n := IndependentDomination.order (graph x)
  let (_, side, conditions) := InducedMatchingInterval.build x
  (List.range (2 ^ n)).countP fun seed =>
    let vals := intervalTestValues n (lower x) (upper x) seed
    let σ := (vals.getD · false)
    side.eval σ && conditions.all (DNF.eval σ)

/-- Execute actual signed binary edge-threshold preparation before the original-input oracle. -/
@[expose] def count (x : InducedMatchingInterval.Maximum.Input) : ℕ :=
  intervalCount (InducedMatchingInterval.Maximum.prepare x)

/-- A path whose first and last edges are not an induced pair. -/
@[expose] def pathFour : IndependentDomination.Input :=
  (4, [[false, true, false, false], [true, false, true, false],
    [false, true, false, true], [false, false, true, false]])

/-- Two disjoint edges, admitting an induced pair. -/
@[expose] def disjointEdges : IndependentDomination.Input :=
  (4, [[false, true, false, false], [true, false, false, false],
    [false, false, false, true], [false, false, true, false]])

/- Empty support is always an induced matching. Isolated declared vertices cannot be marked. -/
/-- info: (1, 0, 1, 1, 0, 2, 1, 0) -/
#guard_msgs in
#eval (count ((0, []), 0), count ((0, []), 1), count ((0, []), -100),
  count ((3, List.replicate 3 (List.replicate 3 false)), 0),
  count ((3, List.replicate 3 (List.replicate 3 false)), 1),
  count ((2, [[false, true], [true, false]]), 0),
  count ((2, [[false, true], [true, false]]), 1),
  count ((2, [[false, true], [true, false]]), 2))

/- A lower bound on edges is twice that bound on selected endpoints, without domination. -/
/-- info: (4, 3, 0, 4, 3, 1, 4, 0) -/
#guard_msgs in
#eval (count (pathFour, 0), count (pathFour, 1), count (pathFour, 2),
  count (disjointEdges, 0), count (disjointEdges, 1), count (disjointEdges, 2),
  count (disjointEdges, -(2 ^ 512)), count (disjointEdges, 2 ^ 512))

/- Triangle, C4 and K4 have respectively three, four and six nonempty induced matchings. -/
/-- info: (4, 3, 5, 4, 7, 6) -/
#guard_msgs in
#eval (count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 0),
  count ((3, [[false, true, true], [true, false, true], [true, true, false]]), 1),
  count ((4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]), 0),
  count ((4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]), 1),
  count ((4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]), 0),
  count ((4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]), 1))

/- Exact edge-size coefficients use endpoint equality, including the empty matching. -/
/-- info: (1, 2, 1, 0) -/
#guard_msgs in
#eval (intervalCount (disjointEdges, 0, 0), intervalCount (disjointEdges, 2, 2),
  intervalCount (disjointEdges, 4, 4), intervalCount (disjointEdges, 3, 3))

/- Actual ordinary query writing, including generated auxiliary variables and literal bounds. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval let x := InducedMatchingInterval.Maximum.prepare (pathFour, 1)
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (InducedMatchingInterval.build x))
  (qs.length, qs.all fun (n, _) => n == 2 * IndependentDomination.order pathFour + auxiliary x - 1,
    qs.all fun (n, q) => q.all fun c => c.length ≤ 3 && c.all fun l => l.1 < n)

example : ComputableInPolyTime InducedMatchingInterval.Maximum.prepare
    InducedMatchingInterval.Maximum.encInput encInput :=
  InducedMatchingInterval.Maximum.prepare_polytime

/- Nonpositive edge thresholds compute a zero lower endpoint bound, including empty graphs. -/
example : InducedMatchingInterval.Maximum.prepare ((0, []), -10) = ((0, []), 0, 0) := rfl

/- A nonvacuous conventional matching, with a genuine unordered edge rather than endpoint marks. -/
example : (⊤ : (⊤ : SimpleGraph (Fin 2)).Subgraph).IsMatching := by
  intro u _
  change ∃! v : Fin 2, u ≠ v
  simp only [ExistsUnique]
  fin_cases u <;> decide

open Classical in
/-- A client states actual matching-object counts, signed input thresholds and the original-vertex
single-loglog clock, rather than merely asserting the constructor's output size. -/
example : ∃ count : InducedMatchingInterval.Maximum.Input → ℕ,
    ∃ cs : NativeCertificate count InducedMatchingInterval.Maximum.encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C *
        ((InducedMatchingInterval.Maximum.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℤ),
        count (InducedMatchingInterval.Maximum.ofGraph G k) =
          Nat.card {M : G.Subgraph // M.IsMatching ∧ M.IsInduced ∧
            k ≤ (Nat.card M.edgeSet : ℤ)} ∧
        (16 ≤ n → (cs.time (InducedMatchingInterval.Maximum.ofGraph G k) : ℝ) ≤ (C : ℝ) *
          ((InducedMatchingInterval.Maximum.encInput
            (InducedMatchingInterval.Maximum.ofGraph G k)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  InducedMatchingInterval.Maximum.exists_count_realEta_certificate

end InducedMatchingIntervalTests
