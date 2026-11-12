/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.TrinomialParameters
public import CslibFrontier.Foundations.Combinatorics.SeededPackingRank
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Native seeded predecessor tests with explicit endpoint keys

One fixed seed evaluates all four endpoint labels. This module implements the Boolean leaf of
the rank count. Endpoint keys are supplied input data: obtaining them from a recursive graph
representation, and summing these predicates, remain separate computations.
-/

public section

namespace Cslib.SeededPredecessor

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Complete local input for one seeded predecessor comparison. -/
structure Input where
  /-- Cardinality of the tagged vertex universe. -/
  universeSize : ℕ
  /-- Number of alphabet-64 coordinates per label, charged in unary. -/
  labelLength : ℕ
  /-- Constant seed coefficient. -/
  c0 : ℕ
  /-- Linear seed coefficient. -/
  c1 : ℕ
  /-- Quadratic seed coefficient. -/
  c2 : ℕ
  /-- Cubic seed coefficient. -/
  c3 : ℕ
  /-- Index of the edge whose class rank is being queried. -/
  edge : ℕ
  /-- Index of the candidate predecessor edge. -/
  candidate : ℕ
  /-- Tagged row key of the queried edge. -/
  edgeRow : ℕ
  /-- Tagged column key of the queried edge. -/
  edgeCol : ℕ
  /-- Tagged row key of the candidate. -/
  candidateRow : ℕ
  /-- Tagged column key of the candidate. -/
  candidateCol : ℕ

/-- All numeric data are binary except the label length. -/
enc_structure encInput : Input where
  universeSize : encNat, labelLength : encUnary, c0 : encNat, c1 : encNat,
  c2 : encNat, c3 : encNat, edge : encNat, candidate : encNat,
  edgeRow : encNat, edgeCol : encNat, candidateRow : encNat, candidateCol : encNat

/-- Evaluate one key with this input's shared seed. -/
@[expose] def hash (p : Input) (key : ℕ) : ℕ :=
  TrinomialArithmetic.runSelected
    ⟨p.universeSize, 6 * p.labelLength, p.c0, p.c1, p.c2, p.c3, key⟩

/-- Test strict precedence and membership in the same pair-label class. -/
@[expose] def test (p : Input) : Bool :=
  decide (p.candidate < p.edge ∧ hash p p.candidateRow = hash p p.edgeRow ∧
    hash p p.candidateCol = hash p p.edgeCol)

/-- Shared-seed hashing remains native polynomial-time for any computed binary key. -/
theorem computableInPolyTime_hash {key : Input → ℕ}
    (hkey : ComputableInPolyTime key encInput encNat) :
    ComputableInPolyTime (fun p => hash p (key p)) encInput encNat := by
  unfold hash TrinomialArithmetic.runSelected
  apply TrinomialArithmetic.computableInPolyTime_hash4
  · apply TrinomialArithmetic.computableInPolyTime_limb <;> fun_prop
  all_goals fun_prop

/-- The local predecessor leaf is computed by a uniform native polynomial-time machine. -/
theorem computableInPolyTime_test : ComputableInPolyTime test encInput encBool := by
  have hr := decide_eq' (computableInPolyTime_hash (key := Input.candidateRow) (by fun_prop))
    (computableInPolyTime_hash (key := Input.edgeRow) (by fun_prop))
  have hc := decide_eq' (computableInPolyTime_hash (key := Input.candidateCol) (by fun_prop))
    (computableInPolyTime_hash (key := Input.edgeCol) (by fun_prop))
  have ho := binary_lt' (left := Input.candidate) (right := Input.edge)
    (by fun_prop) (by fun_prop)
  exact of_tidy (ComputableTidilyInPolyTime.decide_and ho.tidy
    (ComputableTidilyInPolyTime.decide_and hr.tidy hc.tidy))

/-- Construct the supplied local data from actual edge endpoints and a valid shared seed.
This mathematical constructor makes no claim about the cost of computing the endpoints. -/
def ofEdges {R C : Type*} {n : ℕ} (U a : ℕ) (vertex : R ⊕ C ↪ Fin U)
    (rowOf : Fin n → R) (colOf : Fin n → C)
    (seed : BalancedSchedules.SeededLabels.Seed U (6 * a)) (e candidate : Fin n) : Input where
  universeSize := U
  labelLength := a
  c0 := (seed 0).val
  c1 := (seed 1).val
  c2 := (seed 2).val
  c3 := (seed 3).val
  edge := e.val
  candidate := candidate.val
  edgeRow := (vertex (.inl (rowOf e))).val
  edgeCol := (vertex (.inr (colOf e))).val
  candidateRow := (vertex (.inl (rowOf candidate))).val
  candidateCol := (vertex (.inr (colOf candidate))).val

/-- The executable comparison equals the actual seeded-packing predecessor predicate. -/
theorem test_ofEdges {R C : Type*} {n : ℕ} (U a : ℕ) (vertex : R ⊕ C ↪ Fin U)
    (rowOf : Fin n → R) (colOf : Fin n → C)
    (seed : BalancedSchedules.SeededLabels.Seed U (6 * a)) (e candidate : Fin n) :
    test (ofEdges U a vertex rowOf colOf seed e candidate) =
      PacketPacking.Seeded.predecessor U a vertex rowOf colOf seed e candidate := by
  simp only [test, ofEdges, PacketPacking.Seeded.predecessor,
    PacketPacking.Seeded.label, Equiv.apply_eq_iff_eq, ← Fin.val_inj]
  simp only [hash, TrinomialArithmetic.runSelected_eq]
  rfl

end Cslib.SeededPredecessor
