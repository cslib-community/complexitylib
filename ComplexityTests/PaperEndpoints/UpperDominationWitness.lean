/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.UpperDominationWitness
public import ComplexityTests.PaperEndpoints.UpperDominationOptimum
meta import Complexity.Computability.Complexity.FineGrained.UpperDominationWitness
meta import Complexity.Computability.Complexity.FineGrained.TwoBoundaryWitness
meta import ComplexityTests.PaperEndpoints.UpperDominationOptimum

/-!
# Actual original upper-domination witness output on small graphs

The tiny oracle caches only original selection/mark words with their computed unique gate traces.
Each real trial writes unit clauses on the original formula; the oracle inspects those actual
clauses against the cached valid traces. No gate cube is enumerated. Production instantiates the
proved sharp counter, not this tiny test-only enumeration.
-/

public section

namespace UpperDominationWitnessTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open UpperDomination

set_option linter.hashCommand false

/-- Test-only original selection/mark enumeration with computed unique gate traces. -/
@[expose] def traces (x : Input) : List (List Bool) :=
  let n := IndependentDomination.order (graph x)
  let base := build x
  ((List.range (2 ^ n)).flatMap fun seed =>
    let trace := intervalTestValues n (threshold x).toNat n seed
    (List.range (2 ^ n)).map fun marks =>
      trace ++ (List.range n).map (Nat.testBit marks)).filter fun bits =>
        let y := (bits.getD · false)
        (TwoBoundary.BinaryFrontend.side base).eval y &&
          (TwoBoundary.BinaryFrontend.conditions base).all (DNF.eval y)

/-- Actual unit-clause traversal, with a tiny trace-based oracle for its exact trial family. -/
@[expose] def recover (x : Input) : List Bool :=
  let base := build x
  let words := traces x
  let offset := (TwoBoundary.BinaryFrontend.side base).length
  TwoBoundary.BinaryFrontend.Witness.run
    (fun q => words.any fun bits =>
      CNF.eval (bits.getD · false) ((TwoBoundary.BinaryFrontend.side q).drop offset)) base

/-- Both actual passes and original-prefix output writing, with tiny test oracles substituted. -/
@[expose] def optimize (g : IndependentDomination.Input) : Witness.Output :=
  Witness.solve UpperDominationOptimumTests.optimum recover g

/- Every declared original position is returned, with no mark/gate bits in the output. -/
/-- info: ((0, []), (1, [true]), 2, [true, true]) -/
#guard_msgs in
#eval (optimize (0, []), optimize (1, [[false]]),
  optimize (2, [[false, false], [false, false]]))

/- An edge returns one actual vertex, not its nonunique private marks. -/
/-- info: (1, [false, true]) -/
#guard_msgs in
#eval optimize (2, [[false, true], [true, false]])

/- P3 returns its two leaves, proving maximum rather than minimum domination is intended. -/
/-- info: (2, [true, false, true]) -/
#guard_msgs in
#eval optimize (3, [[false, true, false], [true, false, true], [false, true, false]])

/- A triangle returns its last vertex; an original declared isolate must remain selected. -/
/-- info: ((1, [false, false, true]), 2, [false, true, true]) -/
#guard_msgs in
#eval (optimize (3, [[false, true, true], [true, false, true], [true, true, false]]),
  optimize (3, [[false, true, false], [true, false, false], [false, false, false]]))

/- A star returns its leaves. C4 admits an optimal adjacent pair, unlike independent domination. -/
/-- info: ((3, [false, true, true, true]), 2, [false, false, true, true]) -/
#guard_msgs in
#eval (optimize (4, [[false, true, true, true], [true, false, false, false],
  [true, false, false, false], [true, false, false, false]]),
  optimize (4, [[false, true, false, true], [true, false, true, false],
    [false, true, false, true], [true, false, true, false]]))

/-- Independently check the returned bits using the original closed-neighborhood predicate. -/
@[expose] def verify (g : IndependentDomination.Input) : Bool :=
  let out := optimize g
  let bits := Witness.vertices out
  let indices := List.range (IndependentDomination.order g)
  let chosen := indices.filter fun u => bits.getD u false
  bits.length == IndependentDomination.order g && chosen.length == Witness.value out &&
    indices.all (fun w => chosen.any (closed g w)) &&
    chosen.all (fun u => indices.any fun w => closed g w u &&
      chosen.all fun v => !closed g w v || v == u)

/-- info: (true, true, true) -/
#guard_msgs in
#eval (verify (0, []), verify (2, [[false, true], [true, false]]),
  verify (3, [[false, true, false], [true, false, true], [false, true, false]]))

/- Full-width ordinary CNF/DNF self-reduction also handles a free unused original variable. -/
/-- info: [false, true, false] -/
#guard_msgs in
#eval TwoBoundary.BinaryFrontend.Witness.run
  (fun q => (List.range (2 ^ TwoBoundary.BinaryFrontend.declared q)).any fun seed =>
    let y := Nat.testBit seed
    (TwoBoundary.BinaryFrontend.side q).eval y &&
      (TwoBoundary.BinaryFrontend.conditions q).all (DNF.eval y))
  (3, [], [[[(0, true)], [(1, true)]]])

open Classical in
/-- The complete native endpoint returns the set itself, its exact value and global optimality. -/
example : ∃ optimize : IndependentDomination.Input → Witness.Output,
    ∃ cs : NativeCertificate optimize IndependentDomination.encInput Witness.encOutput,
      ∃ C e A : ℕ, (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (let out := optimize (IndependentDomination.ofGraph G)
         (Witness.vertices out).length = n ∧
           Minimal G.IsDominatingSet (Witness.selected (Witness.vertices out)) ∧
           Nat.card (Witness.selected (n := n) (Witness.vertices out)) = Witness.value out ∧
             ∀ S : Set (Fin n), Minimal G.IsDominatingSet S → Nat.card S ≤ Witness.value out) ∧
        (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  Witness.exists_optimalWitness_realEta_certificate

end UpperDominationWitnessTests
