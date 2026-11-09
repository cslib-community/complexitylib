/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.SigmaRhoCountingResources
public import CslibFrontierTests.PaperEndpoints.CardinalityInterval
meta import CslibFrontier.Computability.PolyTime.CNF.SigmaRhoInput
meta import CslibFrontier.Computability.Complexity.FineGrained.TwoBoundaryFrontend
meta import CslibFrontierTests.PaperEndpoints.CardinalityInterval

/-!
# Actual general degree-rule construction

Enumerate only original selections on small graphs, then compute the unique gate/threshold trace.
These tests check original open-neighbor counts, fixed finite/cofinite tails, contradictory binary
bounds, empty graphs and actual two-query writing. The production algorithm never performs this
original-cube test enumeration.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM
open SigmaRho.BinaryFrontend

set_option linter.hashCommand false

/-- Test-only original-selection enumeration with deterministic auxiliary materialization. -/
@[expose] def degreeRuleTestCount (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool)
    (x : Input) : ℕ :=
  let g := original x
  let n := IndependentDomination.order g
  let (_, side, conditions) := build D σ ρ active x
  (List.range (2 ^ n)).countP fun seed =>
    let initialValues := if active then intervalTestValues n (lower x) (upper x) seed
      else (List.range n).map (Nat.testBit seed)
    let bits := (List.range D).flatMap fun j => (List.range n).map fun u =>
      decide (j + 1 ≤ ((DegreeThreshold.neighbors g u).filter (Nat.testBit seed)).length)
    let vals := initialValues ++ bits
    side.eval (vals.getD · false) && conditions.all (DNF.eval (vals.getD · false))

/-- Small path with overlapping open neighborhoods. -/
@[expose] def degreeRulePath : IndependentDomination.Input :=
  (3, [[false, true, false], [true, false, true], [false, true, false]])

/-- Four-vertex complete graph, distinguishing exact degree two from the entire tail. -/
@[expose] def degreeRuleClique : IndependentDomination.Input :=
  (4, (List.range 4).map fun u => (List.range 4).map fun v => u != v)

/- D=1 gives independence on selected vertices and domination on the complement. -/
/-- info: (2, 1, 1, 0, 0, 2) -/
#guard_msgs in
#eval (degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) false
    (degreeRulePath, 100, 0),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true
    (degreeRulePath, 1, 1),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true
    (degreeRulePath, 2, 2),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true
    (degreeRulePath, 0, 0),
  degreeRuleTestCount 1 (fun _ => true) (fun _ => true) true (degreeRulePath, 3, 2),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true
    (degreeRulePath, 0, 2 ^ 512))

/- With cutoff 3 the selected rule is exactly {2}; with cutoff 2 it is the tail [2,infinity). -/
/-- info: (5, 6, 16, 0) -/
#guard_msgs in
#eval (degreeRuleTestCount 3 (fun s => s.val == 2) (fun _ => true) false
    (degreeRuleClique, 0, 0),
  degreeRuleTestCount 2 (fun s => s.val == 2) (fun _ => true) false
    (degreeRuleClique, 0, 0),
  degreeRuleTestCount 2 (fun _ => true) (fun _ => true) false (degreeRuleClique, 0, 0),
  degreeRuleTestCount 2 (fun _ => false) (fun _ => false) false (degreeRuleClique, 0, 0))

/-- info: (1, 0, 1, 1, 0) -/
#guard_msgs in
#eval (degreeRuleTestCount 2 (fun _ => false) (fun _ => false) true ((0, []), 0, 0),
  degreeRuleTestCount 2 (fun _ => true) (fun _ => true) true ((0, []), 1, 100),
  degreeRuleTestCount 2 (fun _ => false) (fun _ => false) false ((0, []), 100, 0),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) false
    ((3, List.replicate 3 (List.replicate 3 false)), 0, 0),
  degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true
    ((3, List.replicate 3 (List.replicate 3 false)), 0, 2))

/-- info: (2, true, true) -/
#guard_msgs in
#eval let x : Input := (degreeRulePath, 1, 2)
  let qs := TwoBoundary.BinaryFrontend.queries
    (TwoBoundary.BinaryFrontend.compile (build 2 (fun _ => true) (fun _ => true) true x))
  (qs.length,
    qs.all fun (n, _) => n == 5 * IndependentDomination.order degreeRulePath + auxiliary true x - 1,
    qs.all fun (_, q) => q.all fun c => c.length ≤ 4)

example (D : ℕ) (σ ρ : SimpleGraph.DegreeRule D) (active : Bool) :
    ComputableInPolyTime (build D σ ρ active) encInput TwoBoundary.BinaryFrontend.encInput :=
  build_polytime D σ ρ active

open Classical in
/-- Arbitrary fixed finite/cofinite rules, varying binary bounds, exact original counts and
complete sharp native resources, rather than a supplied fast-counter contract. -/
example (σ ρ : Set ℕ) (hσ : σ.Finite ∨ σᶜ.Finite) (hρ : ρ.Finite ∨ ρᶜ.Finite) :
    ∃ count : Input → ℕ, ∃ cs : NativeCertificate count encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : ℕ),
        count (ofGraph G lo hi) = Fintype.card {S : Set (Fin n) //
          G.IsSigmaRhoSet σ ρ S ∧ InBounds true lo hi (Nat.card S)} ∧
        (16 ≤ n → (cs.time (ofGraph G lo hi) : ℝ) ≤ (C : ℝ) *
          ((encInput (ofGraph G lo hi)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  exists_count_finiteCofinite_certificate σ ρ hσ hρ true
