/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationMinimumResources
public import CslibFrontierTests.PaperEndpoints.CardinalityInterval
meta import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryWitness
meta import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundarySolver
meta import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundarySourceSolver
meta import CslibFrontier.Computability.Complexity.FineGrained.GraphWitness
meta import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationWitness
meta import CslibFrontier.Computability.Complexity.FineGrained.IndependentDominationMinimumResources
meta import CslibFrontierTests.PaperEndpoints.CardinalityInterval

/-!
# Actual checked graph solution output

These tiny oracles enumerate original selections only. For cardinality gates they compute the
unique trace and cache the valid full words. Each actual self-reduction query appends units to
the same base formula; the oracle checks those units against the cached words. Production uses
the instantiated native counter, rather than this enumeration or a supplied solution.
-/

public section

namespace GraphWitnessTests

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDomination GraphWitness

set_option linter.hashCommand false

/-- Actual unit-clause traversal, actual full-word check and actual original-prefix output. -/
@[expose] def recover (n : ℕ) (x : TwoBoundary.BinaryFrontend.Input)
    (words : List (List Bool)) : TwoBoundary.BinaryFrontend.Witness.Output :=
  let good := words.filter fun bits => TwoBoundary.BinaryFrontend.Witness.check (x, bits)
  let offset := (TwoBoundary.BinaryFrontend.side x).length
  let full := TwoBoundary.BinaryFrontend.Witness.run
    (fun q => good.any fun bits =>
      CNF.eval (bits.getD · false) ((TwoBoundary.BinaryFrontend.side q).drop offset)) x
  TwoBoundary.BinaryFrontend.Witness.keepPrefix
    (n, TwoBoundary.BinaryFrontend.Witness.finish (x, full))

/-- Tiny original-selection words, for the four gate-free graph constructors. -/
@[expose] def words (n : ℕ) : List (List Bool) :=
  (List.range (2 ^ n)).map fun seed => (List.range n).map (Nat.testBit seed)

/-- Execute the actual source graph constructor with the tiny oracle. -/
@[expose] def graphSolve (build : IndependentDomination.Input → TwoBoundary.BinaryFrontend.Input)
    (g : IndependentDomination.Input) : TwoBoundary.BinaryFrontend.Witness.Output :=
  recover (IndependentDomination.order g) (build g) (words (IndependentDomination.order g))

/-- The bounded constructor retains computed gate traces, never a gate-cube enumeration. -/
@[expose] def bounded (g : IndependentDomination.Input) (lo hi : ℤ) :
    TwoBoundary.BinaryFrontend.Witness.Output :=
  let low := IndependentDominationInterval.Signed.lowerNat lo hi
  let high := IndependentDominationInterval.Signed.upperNat hi
  let n := IndependentDomination.order g
  recover n (IndependentDominationInterval.Signed.Witness.construct (g, lo, hi))
    ((List.range (2 ^ n)).map (intervalTestValues n low high))

/-- Original three-vertex path with overlapping closed neighborhoods. -/
@[expose] def path : IndependentDomination.Input :=
  (3, [[false, true, false], [true, false, true], [false, true, false]])

/- Actual independent dominating sets, including empty and declared isolated vertices. -/
/-- info: (some [], some [true], some [false, true, false], some [true, true]) -/
#guard_msgs in
#eval (graphSolve IndependentDomination.build (0, []),
  graphSolve IndependentDomination.build (1, [[false]]),
  graphSolve IndependentDomination.build path,
  graphSolve IndependentDomination.build (2, [[false, false], [false, false]]))

/- One arc absorbs toward its head; reversing it reverses the returned singleton. -/
/-- info: (some [false, true], some [true, false], none, some []) -/
#guard_msgs in
#eval (graphSolve IndependentDomination.build (2, [[false, true], [false, false]]),
  graphSolve IndependentDomination.build (2, [[false, false], [true, false]]),
  graphSolve IndependentDomination.build
    (3, [[false, true, false], [false, false, true], [true, false, false]]),
  graphSolve IndependentDomination.build (0, []))

/- Actual perfect matching cut side labels; the vacuous empty cut is rejected. -/
/-- info: (none, some [false, true], none, some [false, false, true, true]) -/
#guard_msgs in
#eval (graphSolve PerfectMatchingCut.Witness.construct (0, []),
  graphSolve PerfectMatchingCut.Witness.construct (2, [[false, true], [true, false]]),
  graphSolve PerfectMatchingCut.Witness.construct path,
  graphSolve PerfectMatchingCut.Witness.construct
    (4, [[false, true, false, true], [true, false, true, false],
      [false, true, false, true], [true, false, true, false]]))

/- Endpoint bits of actual dominating induced matchings; an isolate stays unselected. -/
/-- info: (some [], some [false], some [false, true, true], none) -/
#guard_msgs in
#eval (graphSolve DominatingInducedMatching.build (0, []),
  graphSolve DominatingInducedMatching.build (1, [[false]]),
  graphSolve DominatingInducedMatching.build path,
  graphSolve DominatingInducedMatching.build
    (4, [[false, true, false, true], [true, false, true, false],
      [false, true, false, true], [true, false, true, false]]))

/- Original size bounds select the center or both leaves; no auxiliary output survives. -/
/-- info: (some [false, true, false], some [true, false, true], none, none) -/
#guard_msgs in
#eval (bounded path 1 1, bounded path 2 2, bounded path 0 0, bounded path 2 1)

/- Empty, negative and huge binary cutoffs use the same actual checked cardinality writer. -/
/-- info: (some [], none, none, some [false, true, false]) -/
#guard_msgs in
#eval (bounded (0, []) (-10) 10, bounded (0, []) 0 (-1),
  bounded path (-10) (-1), bounded path (-(2 ^ 512)) (2 ^ 512))

/- Unused declared bits survive; a wrong full word is rejected, rather than reported as success. -/
/-- info: (some [false, true, false], none, some []) -/
#guard_msgs in
#eval (recover 3 (3, [], [[[(0, true)], [(1, true)]]]) (words 3),
  TwoBoundary.BinaryFrontend.Witness.finish ((1, [[(0, true)]], []), [false]),
  recover 0 (0, [], []) [[]])

open DigraphKernel DigraphKernel.Witness in
open Classical in
/-- Full source-output correspondence and native resources, rather than only existence. -/
example :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofDigraph G)).isSome = true ↔ ∃ S : Set (Fin n), G.IsKernel S) ∧
        (∀ bits, solver (ofDigraph G) = some bits → bits.length = n ∧ G.IsKernel (selected bits)) ∧
        (16 ≤ n → (cs.time (ofDigraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofDigraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DigraphKernel.Witness.exists_solver_realEta_certificate

open PerfectMatchingCut PerfectMatchingCut.Witness in
open Classical in
/-- Full source-output correspondence and native resources, rather than only existence. -/
example :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofGraph G)).isSome = true ↔ ∃ σ : Fin n → Bool, G.IsPerfectMatchingCut σ) ∧
        (∀ bits, solver (ofGraph G) = some bits → bits.length = n ∧
          G.IsPerfectMatchingCut (fun u => bits.getD u.val false)) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  PerfectMatchingCut.Witness.exists_solver_realEta_certificate

open DominatingInducedMatching DominatingInducedMatching.Witness in
open Classical in
/-- Full source-output correspondence and native resources, rather than only existence. -/
example :
    ∃ solver : Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ((solver (ofGraph G)).isSome = true ↔
          ∃ M : G.Subgraph, M.IsDominatingInducedMatching) ∧
        (∀ bits, solver (ofGraph G) = some bits → bits.length = n ∧
          (decodeMatching G bits).IsDominatingInducedMatching) ∧
        (16 ≤ n → (cs.time (ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DominatingInducedMatching.Witness.exists_solver_realEta_certificate

open IndependentDominationInterval in
open IndependentDominationInterval.Signed in
open IndependentDominationInterval.Signed.Witness in
open Classical in
/-- Arbitrary runtime signed size bounds, checked original output and full native resources. -/
example :
    ∃ solver : Signed.Input → TwoBoundary.BinaryFrontend.Witness.Output,
      ∃ cs : NativeCertificate solver Signed.encInput TwoBoundary.BinaryFrontend.Witness.encOutput,
      ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        ((solver (Signed.ofGraph G lo hi)).isSome = true ↔ ∃ σ, Feasible G lo hi σ) ∧
        (∀ bits, solver (Signed.ofGraph G lo hi) = some bits → bits.length = n ∧
          Feasible G lo hi (fun u => bits.getD u.val false)) ∧
        (16 ≤ n → (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  IndependentDominationInterval.Signed.Witness.exists_solver_realEta_certificate

/-- Execute the real ascending search with the existing tiny checked-gate test solver. -/
@[expose] def minimum (g : IndependentDomination.Input) : Option (ℕ × List Bool) :=
  IndependentDominationInterval.Signed.Witness.Minimum.run
    (fun (g, lo, hi) => bounded g lo hi) g

/- Empty, isolated and path cases return the least attainable size and the actual vertices. -/
/-- info: (some (0, []), some (1, [true]), some (1, [false, true, false])) -/
#guard_msgs in
#eval (minimum (0, []), minimum (1, [[false]]), minimum path)

/- A star's minimum is its center, unlike the already implemented maximum upper domination. -/
/-- info: (some (1, [true, false, false, false]), some (3, [true, true, true])) -/
#guard_msgs in
#eval (minimum (4, [[false, true, true, true], [true, false, false, false],
  [true, false, false, false], [true, false, false, false]]),
  minimum (3, List.replicate 3 (List.replicate 3 false)))

/- A complete graph has optimum one, with an actual singleton output. -/
/-- info: some (1, [false, false, true]) -/
#guard_msgs in
#eval minimum (3, [[false, true, true], [true, false, true], [true, true, false]])

/- The native iterator writes the same actual minimum value and word as recursive search. -/
/-- info: (some (1, [false, false, true]), some (0, [])) -/
#guard_msgs in
#eval (IndependentDominationInterval.Signed.Witness.Minimum.execute
  (fun (g, lo, hi) => bounded g lo hi)
    (3, [[false, true, true], [true, false, true], [true, true, false]]),
  IndependentDominationInterval.Signed.Witness.Minimum.execute
    (fun (g, lo, hi) => bounded g lo hi) (0, []))

open IndependentDominationInterval.Signed in
open IndependentDominationInterval.Signed.Witness in
open IndependentDominationInterval.Signed.Witness.Minimum in
open Classical in
/-- Full attaining-output and source-time/global-workspace endpoint, with no runtime premise. -/
example :
    ∃ optimize : IndependentDomination.Input → Option (ℕ × List Bool),
      ∃ cs : NativeCertificate optimize IndependentDomination.encInput encOutput, ∃ C e A : ℕ,
        (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
        ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
          (∃ k bits, optimize (IndependentDomination.ofGraph G) = some (k, bits) ∧
            bits.length = n ∧ Feasible G k k (fun u => bits.getD u.val false) ∧
              ∀ σ : Fin n → Bool, G.IsIndepSet {u | σ u = true} →
                G.IsDominatingSet {u | σ u = true} → k ≤ Cslib.BitString.weight σ) ∧
          (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
            ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
              e *
              (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  IndependentDominationInterval.Signed.Witness.Minimum.exists_optimal_realEta_certificate

/- Explicit decision tags agree with the actual checked size-bounded recovery. -/
/-- info: (true, false, false, true, false) -/
#guard_msgs in
#eval let test : IndependentDominationInterval.Signed.Input → Bool :=
    IndependentDominationInterval.Signed.decideWith (fun (g, lo, hi) => bounded g lo hi);
  (test (path, 1, 1), test (path, 0, 0), test (path, 2, 1),
    test ((0, []), 0, 0), test ((0, []), 0, -1))

open IndependentDominationInterval in
open IndependentDominationInterval.Signed in
open Classical in
/-- Separate Boolean native decision with varying signed bounds and source resources. -/
example :
    ∃ test : Signed.Input → Bool, ∃ cs : NativeCertificate test Signed.encInput encBool,
      ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((Signed.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℤ),
        (test (Signed.ofGraph G lo hi) = true ↔ ∃ σ, Witness.Feasible G lo hi σ) ∧
        (16 ≤ n → (cs.time (Signed.ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((Signed.encInput (Signed.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  Signed.exists_decide_realEta_certificate

end GraphWitnessTests
