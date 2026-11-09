/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.InducedMatchingWitness
public import ComplexityTests.PaperEndpoints.InducedMatchingInterval
meta import Complexity.Computability.Complexity.FineGrained.InducedMatchingWitness
meta import Complexity.Computability.Complexity.FineGrained.InducedMatchingOptimum
meta import ComplexityTests.PaperEndpoints.InducedMatchingInterval

/-! # Actual optimum and original matching output on small graphs

The test threshold oracle evaluates the actual approved cardinality/degree-one construction on
small original selections and their unique circuit traces. Production instantiates the proved
sharp native decider; neither pass enumerates matchings or auxiliary assignments.
-/

public section

namespace InducedMatchingOptimumTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open InducedMatchingInterval.Maximum

set_option linter.hashCommand false

/-- Test-only threshold evaluation through the actual original-input constructor. -/
@[expose] def test (x : Input) : Bool := decide (0 < InducedMatchingIntervalTests.count x)

/-- The actual two-pass traversal, using the tiny test threshold oracle. -/
@[expose] def optimize (g : IndependentDomination.Input) : Witness.Output :=
  Witness.solve (Optimum.run test) (Witness.run test) g

/- The returned binary value is an edge count, and every declared bit position is present. -/
/-- info: ((0, []), (0, [false, false, false]), 1, [true, true]) -/
#guard_msgs in
#eval (optimize (0, []), optimize (3, List.replicate 3 (List.replicate 3 false)),
  optimize (2, [[false, true], [true, false]]))

/- P4 cannot use its two outer edges; disjoint edges attain size two. -/
/-- info: ((1, [false, false, true, true]), 2, [true, true, true, true]) -/
#guard_msgs in
#eval (optimize InducedMatchingIntervalTests.pathFour,
  optimize InducedMatchingIntervalTests.disjointEdges)

/- Deleting the middle vertex of P5 recovers both outer matching edges. -/
/-- info: (2, [true, true, false, true, true]) -/
#guard_msgs in
#eval optimize (5, [[false, true, false, false, false], [true, false, true, false, false],
  [false, true, false, true, false], [false, false, true, false, true],
  [false, false, false, true, false]])

/- Triangle, dense graph and an edge with an unused declared isolate. -/
/-- info: ((1, [false, true, true]), (1, [false, false, true, true]), 1, [true, true, false]) -/
#guard_msgs in
#eval (optimize (3, [[false, true, true], [true, false, true], [true, true, false]]),
  optimize (4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]),
  optimize (3, [[false, true, false], [true, false, false], [false, false, false]]))

/- Vertex restriction keeps all rows/columns and clears incident edges, without new vertices. -/
example : Witness.restrict (2, [[false, true], [true, false]]) [true, false] =
    (2, [[false, false], [false, false]]) := rfl

open Classical in
/-- The public endpoint pins actual returned matching optimality and native resources together. -/
example : ∃ optimize : IndependentDomination.Input → Witness.Output,
    ∃ cs : NativeCertificate optimize IndependentDomination.encInput Witness.encOutput,
      ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (let out := optimize (IndependentDomination.ofGraph G)
           let M := Witness.decode G (Witness.vertices out)
           (Witness.vertices out).length = n ∧ M.IsMatching ∧ M.IsInduced ∧
             Nat.card M.edgeSet = Witness.value out ∧
               ∀ Q : G.Subgraph, Q.IsMatching → Q.IsInduced →
                 Nat.card Q.edgeSet ≤ Witness.value out) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput
              (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  Witness.exists_optimalWitness_realEta_certificate

end InducedMatchingOptimumTests
