/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.UpperDominationOptimum
public import CslibFrontierTests.PaperEndpoints.UpperDomination
meta import CslibFrontier.Computability.Complexity.FineGrained.UpperDominationOptimum
meta import CslibFrontierTests.PaperEndpoints.UpperDomination

/-!
# Computed original Upper Dominating Set optimum values

The tiny threshold oracle evaluates the approved actual graph/cardinality/private-mark writer.
Production instantiates the proved sharp native decider, not this test-only enumeration.
The returned value counts original selected vertices, independently of marking multiplicity.
-/

public section

namespace UpperDominationOptimumTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM

set_option linter.hashCommand false

/-- Test-only threshold decision through the actual selection/marking clauses and unique gates. -/
@[expose] def test (x : UpperDomination.Input) : Bool :=
  decide (0 < UpperDominationTests.count x)

/-- The production bounded threshold traversal, with the tiny test oracle substituted. -/
@[expose] def optimum (g : IndependentDomination.Input) : ℕ :=
  UpperDomination.Optimum.run test g

/- Empty/edgeless inputs retain the complete declared vertex count. -/
/-- info: (0, 1, 3) -/
#guard_msgs in
#eval (optimum (0, []), optimum (1, [[false]]),
  optimum (3, List.replicate 3 (List.replicate 3 false)))

/- One edge gives value one, not its six valid selection/marking pairs. -/
/-- info: (1, 6, false) -/
#guard_msgs in
#eval (optimum (2, [[false, true], [true, false]]),
  UpperDominationTests.count ((2, [[false, true], [true, false]]), 0),
  test ((2, [[false, true], [true, false]]), 2))

/- P3 has upper domination two although its minimum dominating set has size one. -/
/-- info: (2, true, false) -/
#guard_msgs in
#eval Id.run do
  let g := (3, [[false, true, false], [true, false, true], [false, true, false]])
  let k := optimum g
  return (k, test (g, (k : ℤ)), test (g, ((k + 1 : ℕ) : ℤ)))

/- A star returns its three leaves; complete graphs return one. -/
/-- info: (3, 1) -/
#guard_msgs in
#eval (optimum (4, [[false, true, true, true], [true, false, false, false],
  [true, false, false, false], [true, false, false, false]]),
  optimum (4, [[false, true, true, true], [true, false, true, true],
    [true, true, false, true], [true, true, true, false]]))

/- P4 and C4 retain the original graph, including possible adjacent selected vertices. -/
/-- info: (2, 2, 2) -/
#guard_msgs in
#eval (optimum (4, [[false, true, false, false], [true, false, true, false],
  [false, true, false, true], [false, false, true, false]]),
  optimum (4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]),
  optimum (3, [[false, true, false], [true, false, false], [false, false, false]]))

open Classical in
/-- The original-input endpoint returns an attained global optimum with the real source bound.
This asserts existence of an attaining set, not output of that set by a witness machine. -/
example : ∃ optimum : IndependentDomination.Input → ℕ,
    ∃ cs : NativeCertificate optimum IndependentDomination.encInput encNat, ∃ C e A : ℕ,
      (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((∃ S : Set (Fin n), Minimal G.IsDominatingSet S ∧
          Nat.card S = optimum (IndependentDomination.ofGraph G)) ∧
          ∀ S : Set (Fin n), Minimal G.IsDominatingSet S →
            Nat.card S ≤ optimum (IndependentDomination.ofGraph G)) ∧
        (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  UpperDomination.Optimum.exists_optimum_realEta_certificate

end UpperDominationOptimumTests
