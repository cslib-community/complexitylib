/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import Complexity.Computability.Complexity.FineGrained.DegreePartitionDistribution
public import ComplexityTests.PaperEndpoints.DegreePartition
meta import Complexity.Computability.PolyTime.CNF.BoundedDegreePartition
meta import Complexity.Computability.Complexity.FineGrained.DegreePartitionDistribution
meta import Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend
meta import Complexity.Computability.PolyTime.CNF.CardinalityInterval
meta import Complexity.Computability.Circuit.Boolean.FunctionalCNF

/-!
# Actual bounded labeled counts and complete size-vector output

Enumerate only tiny original labelings and compute their actual circuit/threshold traces. Padded
slots are fixed zeros, never enumerated. Production theorems instantiate the actual native counter.
-/

public section

open Cslib.Logic.PL Turing.MultiTapeTM Cslib.GenericRAM Cslib.Circuits.Boolean

set_option linter.hashCommand false

/-- Tiny actual-writer oracle, with all auxiliary bits derived from the original labels. -/
@[expose] def boundedPartitionTestCount {q D : ℕ}
    (M : Fin q → Fin q → SimpleGraph.DegreeRule D)
    (x : DegreePartition.Bounded.BinaryFrontend.Input) :
    ℕ :=
  let g := DegreePartition.Bounded.BinaryFrontend.original x
  let n := IndependentDomination.order g
  let (_, side, conditions) := DegreePartition.Bounded.BinaryFrontend.build M x
  (List.range (q ^ n)).countP fun seed =>
    let belongs (i u : ℕ) := seed / q ^ u % q == i
    let vals := (List.range q).flatMap fun i =>
      let bits := (List.range n).map (belongs i)
      let (gs, _) := CardinalityInterval.generate
        (DegreePartition.Bounded.BinaryFrontend.interval i x)
      let trace := Cslib.Circuits.evalCode interpretation false bits gs
      trace ++ List.replicate (PaddedCardinality.capacity n - gs.length) false ++
        (List.range D).flatMap fun j => (List.range n).map fun u =>
          decide (j + 1 ≤ ((DegreeThreshold.neighbors g u).filter (belongs i)).length)
    let a := vals.toArray
    side.eval (fun j => a[j]?.getD false) && conditions.all (DNF.eval (fun j => a[j]?.getD false))

/-- Two original adjacent vertices; labels remain distinct. -/
@[expose] def boundedPartitionEdge : IndependentDomination.Input :=
  (2, [[false, true], [true, false]])

/-- info: (4, 1, 2, 1, 0) -/
#guard_msgs in
#eval (boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(0, 2), (0, 2)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(0, 0), (0, 2)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(1, 1), (1, 1)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(2, 2), (0, 0)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(1, 0), (0, 2)]))

/-- info: (2, 0, 1, 0, 1, 0) -/
#guard_msgs in
#eval (boundedPartitionTestCount (q := 2) (D := 2)
    (fun i j s => i == j || s.val == 1) (boundedPartitionEdge, [(1, 1), (1, 1)]),
  boundedPartitionTestCount (q := 2) (D := 2)
    (fun i j s => i == j || s.val == 1) (boundedPartitionEdge, [(0, 0), (2, 2)]),
  boundedPartitionTestCount (q := 3) (D := 1) (fun _ _ _ => true)
    ((1, [[false]]), [(0, 0), (1, 1), (0, 0)]),
  boundedPartitionTestCount (q := 3) (D := 1) (fun _ _ _ => true)
    ((1, [[false]]), [(0, 0), (0, 0), (0, 0)]),
  boundedPartitionTestCount (q := 1) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(2, 2)]),
  boundedPartitionTestCount (q := 1) (D := 1) (fun _ _ _ => true)
    (boundedPartitionEdge, [(1, 1)]))

/- Asymmetric source-label rules detect swapped bound positions or quotiented labels. -/
/-- info: (1, 0) -/
#guard_msgs in
#eval (boundedPartitionTestCount (q := 2) (D := 1) (fun i _ _ => i.val == 0)
    ((1, [[false]]), [(1, 1), (0, 0)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun i _ _ => i.val == 0)
    ((1, [[false]]), [(0, 0), (1, 1)]))

/-- info: (1, 0, 1, 0) -/
#guard_msgs in
#eval (boundedPartitionTestCount (q := 3) (D := 1) (fun _ _ _ => false)
    ((0, []), [(0, 0), (0, 0), (0, 0)]),
  boundedPartitionTestCount (q := 3) (D := 1) (fun _ _ _ => true)
    ((0, []), [(0, 0), (1, 100), (0, 0)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    ((1, [[false]]), [(0, 2 ^ 512), (1, 1)]),
  boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)
    ((1, [[false]]), [(2 ^ 512, 2 ^ 1024), (0, 1)]))

/- All vectors are emitted in class order, including impossible totals with coefficient zero. -/
/-- info: [([0, 0], 0), ([0, 1], 1), ([1, 0], 1), ([1, 1], 0)] -/
#guard_msgs in
#eval DegreePartition.Distribution.run 2
  (boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)) (1, [[false]])

/-- info: [0, 0, 1, 0, 2, 0, 1, 0, 0] -/
#guard_msgs in
#eval (DegreePartition.Distribution.run 2
  (boundedPartitionTestCount (q := 2) (D := 1) (fun _ _ _ => true)) boundedPartitionEdge).map
    (fun p => p.2)

/-- info: [([0, 0, 0], 1)] -/
#guard_msgs in
#eval DegreePartition.Distribution.run 3
  (boundedPartitionTestCount (q := 3) (D := 1) (fun _ _ _ => false)) (0, [])

/-- info: (2, true, true) -/
#guard_msgs in
#eval let x : DegreePartition.Bounded.BinaryFrontend.Input :=
    (boundedPartitionEdge, [(1, 1), (1, 1)])
  let qs := TwoBoundary.BinaryFrontend.queries (TwoBoundary.BinaryFrontend.compile
    (DegreePartition.Bounded.BinaryFrontend.build (q := 2) (D := 1) (fun _ _ _ => true) x))
  (qs.length, qs.all (fun (n, _) => n == 5723),
    qs.all (fun (_, f) => f.all fun c => c.length ≤ 3))

example (q n : ℕ) : (DegreePartition.SizeVectors.vectors q n).length = (n + 1) ^ q :=
  DegreePartition.SizeVectors.length_vectors q n

open Classical in
/-- Arbitrary fixed finite/cofinite matrices and input-varying binary bounds have complete
ordinary original-partition correctness and actual sharp native time/global space. -/
example {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ count : DegreePartition.Bounded.BinaryFrontend.Input → ℕ,
      ∃ cs : NativeCertificate count DegreePartition.Bounded.BinaryFrontend.encInput encNat,
        ∃ C e A : ℕ,
          (∀ x, cs.space x ≤ C *
            ((DegreePartition.Bounded.BinaryFrontend.encInput x).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (lo hi : Fin q → ℕ),
            count (DegreePartition.Bounded.BinaryFrontend.ofGraph G lo hi) =
              Fintype.card {S : Fin q → Set (Fin n) //
                G.IsDegreePartition M S ∧ SimpleGraph.InClassBounds lo hi S} ∧
            (16 ≤ n → (cs.time (DegreePartition.Bounded.BinaryFrontend.ofGraph G lo hi) : ℝ) ≤
              (C : ℝ) * ((DegreePartition.Bounded.BinaryFrontend.encInput
                (DegreePartition.Bounded.BinaryFrontend.ofGraph G lo hi)).length + 1 : ℕ) ^ e *
                  (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  DegreePartition.Bounded.BinaryFrontend.exists_count_finiteCofinite_certificate M hM

open Classical in
open DegreePartition.Distribution in
/-- Full vector tags, order, original counts, output bytes and actual native resources are
available together, with no supplied output or counter contract. -/
example {q : ℕ} (M : Fin q → Fin q → Set ℕ)
    (hM : ∀ i j, (M i j).Finite ∨ (M i j)ᶜ.Finite) :
    ∃ distribution : IndependentDomination.Input → List Entry,
      ∃ cs : NativeCertificate distribution IndependentDomination.encInput (encList encEntry),
        ∃ C e A : ℕ,
          (∀ g, cs.space g ≤ C * ((IndependentDomination.encInput g).length + 1) ^ e) ∧
          ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            distribution (IndependentDomination.ofGraph G) =
              (DegreePartition.SizeVectors.vectors q n).map
                (fun v => (v, countForVector G M v)) ∧
            ((encList encEntry) (distribution (IndependentDomination.ofGraph G))).length ≤
              (n + 1) ^ q * (2 * (2 * q * (2 * (n + 1) + 1) + n * q + 2) + 1) ∧
            (16 ≤ n → (cs.time (IndependentDomination.ofGraph G) : ℝ) ≤ (C : ℝ) *
              ((IndependentDomination.encInput (IndependentDomination.ofGraph G)).length + 1 : ℕ) ^
                e * (2 : ℝ) ^ ((A : ℝ) * Real.logLogSqrtLogScale n)) :=
  exists_distribution_finiteCofinite_certificate M hM
