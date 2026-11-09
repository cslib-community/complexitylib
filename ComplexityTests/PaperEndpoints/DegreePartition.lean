/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.DegreePartitionCountingResources
public import Complexity.Computability.Complexity.FineGrained.SigmaRhoDistribution
public import ComplexityTests.PaperEndpoints.SigmaRho
meta import Complexity.Computability.PolyTime.CNF.DegreePartition
meta import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
meta import Complexity.Computability.Complexity.FineGrained.SigmaRhoDistribution
meta import ComplexityTests.PaperEndpoints.SigmaRho

/-!
# General labeled matrices and complete original-set distributions

Tiny tests enumerate original labels, deriving thresholds rather than searching an auxiliary cube.
The actual production theorems instantiate the proved native counter, not this test enumerator.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM

set_option linter.hashCommand false

/-- Tiny test-only label enumeration, preserving labels and permitting empty classes. -/
@[expose] def degreePartitionTestCount {q D : ℕ}
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D) (g : IndependentDomination.Input) : ℕ :=
  let n := IndependentDomination.order g
  let (_, side, conditions) := DegreePartition.BinaryFrontend.build M g
  (List.range (q ^ n)).countP fun seed =>
    let belongs (i u : ℕ) := seed / q ^ u % q == i
    let vals := (List.range q).flatMap fun i =>
      (List.range n).map (belongs i) ++
        (List.range D).flatMap fun j => (List.range n).map fun u =>
          decide (j + 1 ≤ ((DegreeThreshold.neighbors g u).filter (belongs i)).length)
    side.eval (vals.getD · false) && conditions.all (DNF.eval (vals.getD · false))

/- Universal matrices count q^v, not unlabeled partitions or binary membership arrays. -/
/-- info: (1, 4, 9, 27, 1) -/
#guard_msgs in
#eval (degreePartitionTestCount (q := 1) (D := 1) (fun _ _ _ => true) degreeRulePath,
  degreePartitionTestCount (q := 2) (D := 2) (fun _ _ _ => true)
    (2, [[false, true], [true, false]]),
  degreePartitionTestCount (q := 3) (D := 1) (fun _ _ _ => true)
    (2, [[false, true], [true, false]]),
  degreePartitionTestCount (q := 3) (D := 2) (fun _ _ _ => true) degreeRulePath,
  degreePartitionTestCount (q := 3) (D := 2) (fun _ _ _ => false) (0, []))

/- Off-diagonal exact-one rules impose opposite-neighbor degrees; no side names are identified. -/
/-- info: (2, 0, 0, 0, 1) -/
#guard_msgs in
#eval (degreePartitionTestCount (q := 2) (D := 2)
    (fun i j s => i == j || s.val == 1) (2, [[false, true], [true, false]]),
  degreePartitionTestCount (q := 2) (D := 2)
    (fun i j s => i == j || s.val == 1) (1, [[false]]),
  degreePartitionTestCount (q := 2) (D := 1) (fun _ _ _ => false) degreeRulePath,
  degreePartitionTestCount (q := 0) (D := 1) (fun i => Fin.elim0 i) degreeRulePath,
  degreePartitionTestCount (q := 0) (D := 1) (fun i => Fin.elim0 i) (0, []))

/-- info: (2, true, true) -/
#guard_msgs in
#eval let qs := TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile
    (DegreePartition.BinaryFrontend.build (q := 3) (D := 2) (fun _ _ _ => true) degreeRulePath))
  (qs.length, qs.all (fun (n, _) => n == 44),
    qs.all (fun (_, f) => f.all fun c => c.length ≤ 4))

/- Actual sequential traversal, including all zero coefficients and size-zero empty input. -/
/-- info: ([0, 1, 1, 0], [1, 0, 0, 4, 0], [1, 0, 0, 4, 1], [1]) -/
#guard_msgs in
#eval (SigmaRho.Distribution.run
    (degreeRuleTestCount 1 (fun s => s.val == 0) (fun s => s.val == 1) true) degreeRulePath,
  SigmaRho.Distribution.run (degreeRuleTestCount 3 (fun s => s.val == 2) (fun _ => true) true)
    degreeRuleClique,
  SigmaRho.Distribution.run (degreeRuleTestCount 2 (fun s => s.val == 2) (fun _ => true) true)
    degreeRuleClique,
  SigmaRho.Distribution.run (degreeRuleTestCount 2 (fun _ => false) (fun _ => false) true) (0, []))

/- Semantic bound boundaries only: the encoded per-class-bound frontend remains separate. -/
example : SimpleGraph.InClassBounds (n := 0) (q := 2) (fun _ => 0) (fun _ => 0)
    (fun _ => ∅) := by simp [SimpleGraph.InClassBounds]

example : ¬ SimpleGraph.InClassBounds (n := 0) (q := 2) (fun _ => 1) (fun _ => 0)
    (fun _ => ∅) := by simp [SimpleGraph.InClassBounds]

example {q D : ℕ} (M : Fin q → Fin q → SimpleGraph.DegreeRule D) :
    ComputableInPolyTime (DegreePartition.BinaryFrontend.build M) IndependentDomination.encInput
      TwoBoundary.BinaryFrontend.encInput := DegreePartition.BinaryFrontend.build_polytime M

open Classical in
/-- Arbitrary fixed finite/cofinite matrices, exact ordinary labeled counts and complete actual
sharp resources, without assuming a supplied conversion or fast counter. -/
example {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ count : IndependentDomination.Input → ℕ,
      ∃ cs : NativeCertificate count IndependentDomination.encInput encNat, ∃ C e A : ℕ,
      (∀ x, cs.space x ≤ C * ((IndependentDomination.encInput x).length + 1) ^ e) ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        count (IndependentDomination.ofGraph G) = Fintype.card {S : Fin q → Set (Fin n) //
          G.IsDegreePartition M S} ∧
        (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
          ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^ e *
            (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DegreePartition.BinaryFrontend.exists_count_finiteCofinite_certificate M hM
