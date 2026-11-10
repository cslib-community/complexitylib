/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.DigraphKernel
public import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend
meta import CslibFrontier.Computability.PolyTime.CNF.DigraphKernel
meta import CslibFrontier.Computability.PolyTime.CNF.IndependentDomination
meta import CslibFrontierTests.PaperEndpoints.TwoBoundaryFrontend

/-! # Directed kernel counts, orientation and complete source-resource clients

The tiny exhaustive CNF oracle checks actual written queries. Production certificates use the
proved sharp counter. Original-selection tests expose the direction of absorption explicitly.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open IndependentDomination DigraphKernel

set_option linter.hashCommand false

/-- Test-only execution of the actual one/two-query kernel plan. -/
@[expose] def kernelTestCount (x : Input) : ℕ :=
  TwoBoundary.BinaryFrontend.execute dnfTestCounter (plan x)

/-- Test-only original selections satisfying the actual arc and outgoing coverage formulas. -/
@[expose] def kernelTestSelections (x : Input) : List (List ℕ) :=
  let (_, side, conditions) := build x
  ((List.range (2 ^ order x)).filter fun seed =>
    side.eval (Nat.testBit seed) && conditions.all (DNF.eval (Nat.testBit seed))).map fun seed =>
      (List.range (order x)).filter (Nat.testBit seed)

/-- info: (1, 1, 1, 2, 0, 2) -/
#guard_msgs in
#eval (kernelTestCount (0, []), kernelTestCount (1, [[false]]),
  kernelTestCount (3, List.replicate 3 (List.replicate 3 false)),
  kernelTestCount (2, [[false, true], [true, false]]),
  kernelTestCount (3, [[false, true, false], [false, false, true], [true, false, false]]),
  kernelTestCount (4, [[false, true, false, false], [false, false, true, false],
    [false, false, false, true], [true, false, false, false]]))

/- A single arc absorbs toward its head, not its tail; star orientation changes the kernel. -/
/-- info: ([[1]], [[0]], [[1, 2]], [[0]]) -/
#guard_msgs in
#eval (kernelTestSelections (2, [[false, true], [false, false]]),
  kernelTestSelections (2, [[false, false], [true, false]]),
  kernelTestSelections (3, [[false, true, true], [false, false, false], [false, false, false]]),
  kernelTestSelections (3, [[false, false, false], [true, false, false], [true, false, false]]))

/- Dense symmetric graph, transitive orientation, symmetric path, and the stronger loop case. -/
/-- info: (3, 1, 2, 0) -/
#guard_msgs in
#eval (kernelTestCount (3, [[false, true, true], [true, false, true], [true, true, false]]),
  kernelTestCount (3, [[false, true, true], [false, false, true], [false, false, false]]),
  kernelTestCount (3, [[false, true, false], [true, false, true], [false, true, false]]),
  kernelTestCount (1, [[true]]))

/- Actual construction at 64 declared vertices writes queries, without enumerating selections. -/
/-- info: (2, true, true) -/
#guard_msgs in
#eval let qs := TwoBoundary.BinaryFrontend.queries (plan (64, []))
  (qs.length, qs.all fun (n, _) => n == 127,
    qs.all fun (_, q) => q.length ≤ 3 * 64 ^ 2 && q.all fun c => c.length ≤ 3)

/-- info: [(0, 0)] -/
#guard_msgs in
#eval (TwoBoundary.BinaryFrontend.queries (plan (0, []))).map fun (n, q) => (n, q.length)

/-- The graph has one directed arc, without its reverse. -/
@[expose] def kernelOneArc : Digraph (Fin 2) :=
  Digraph.mk' fun u v => decide (u = 0 ∧ v = 1)

example : kernelOneArc.IsKernel {u | u = 1} := by unfold Digraph.IsKernel kernelOneArc; decide
example : ¬kernelOneArc.IsKernel {u | u = 0} := by unfold Digraph.IsKernel kernelOneArc; decide

example : ComputableInPolyTime plan encInput TwoBoundary.BinaryFrontend.encOutput := plan_polytime

open Classical in
/-- The counter counts vertex sets, rather than multiple encodings or certificates. -/
example {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj] :
    TwoBoundary.BinaryFrontend.value (plan (ofDigraph G)) =
      Fintype.card {S : Set (Fin n) // G.IsKernel S} := DigraphKernel.plan_count G

/-- Full input-matrix kernel decision with global workspace and the sharp rounded clock. -/
example : ∃ decideKernel : Input → Bool, ∃ cs : NativeCertificate decideKernel encInput encBool,
    ∃ C e A : ℕ, (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
    ∀ {n : ℕ} (G : Digraph (Fin n)) [DecidableRel G.Adj],
      (decideKernel (ofDigraph G) = true ↔ ∃ S : Set (Fin n), G.IsKernel S) ∧
      cs.time (ofDigraph G) ≤ C * ((encInput (ofDigraph G)).length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale n) := exists_decide_sharp_certificate
