/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.ObliviousSequence
public import Complexity.Probability.PMF.Event
public import Mathlib.Data.Finset.Card

/-!
# Dynamic Approximate-Membership Filter Specification

This file defines an algorithm-independent oblivious-sequence specification
(`Cslib.DataStructure.ApproximateMembership.spec`) for a dynamic approximate-membership filter
(supporting insertions, deletions of present keys, and membership queries) over a finite universe
`Fin U` with capacity `n` and per-query false-positive probability bound `ε : ℝ≥0∞`.

## Semantic design and duplicate-insertion convention

At any point in an operation sequence `ops : List (Op U)`, the filter represents a dynamic set
`S : Finset (Fin U)` of at most `n` keys, starting from `∅`:
* `Op.insert u` is admissible when `u ∉ S` and `#S < n`, transitioning to `insert u S`;
* `Op.delete u` is admissible when `u ∈ S`, transitioning to `S.erase u`;
* `Op.query u` is always admissible and leaves `S` unchanged.

Excluding duplicate insertions of an already-present key (`u ∉ S`) at the specification level is
essential for achieving $O(1)$ per-operation expected time in fingerprint-based filters such as the
quotient filter [Pagh, Pagh and Rao][PaghPaghRao2005]; [Bender et al.][BenderEtAl2012]: if an
operation sequence could insert the same key `u` `n` times, all `n` copies would share the same
quotient and remainder on every random branch, forming a deterministic run of length `n` and
forcing $\Omega(n)$ probe time. Internally, the quotient filter still maintains the **multiset** of
fingerprints `S.val.map fp` so that when two distinct present keys `x ≠ y` in `S` collide in both
quotient and remainder, deleting `x` removes only one copy of their shared fingerprint and preserves
zero false negatives for `y`.

## Main definitions

* `Cslib.DataStructure.ApproximateMembership.Op`,
  `Cslib.DataStructure.ApproximateMembership.Result`,
  `Cslib.DataStructure.ApproximateMembership.Label`: filter operations (`insert`, `delete`,
  `query`), return types (`PUnit` and `Bool`), and transcript labels.
* `Cslib.DataStructure.ApproximateMembership.stepSet`,
  `Cslib.DataStructure.ApproximateMembership.activeSetFrom`,
  `Cslib.DataStructure.ApproximateMembership.activeSet`,
  `Cslib.DataStructure.ApproximateMembership.activeSetBefore`: evolution of the present key set
  along an operation sequence.
* `Cslib.DataStructure.ApproximateMembership.ValidOp`,
  `Cslib.DataStructure.ApproximateMembership.ValidOpSeqFrom`,
  `Cslib.DataStructure.ApproximateMembership.ValidOpSeq`: operation-sequence admissibility under
  capacity `n`.
* `Cslib.DataStructure.ApproximateMembership.NoFalseNegatives`,
  `Cslib.DataStructure.ApproximateMembership.FalsePositiveAt`,
  `Cslib.DataStructure.ApproximateMembership.spec`: pathwise zero-false-negative invariant,
  per-query false-positive event, and `ObliviousSequenceSpec`.

## Main results

* `Cslib.DataStructure.ApproximateMembership.card_activeSetFrom_le`,
  `Cslib.DataStructure.ApproximateMembership.card_activeSet_le`,
  `Cslib.DataStructure.ApproximateMembership.card_activeSetBefore_le`: any admissible operation
  sequence maintains `#S ≤ n` at every step.
* `Cslib.DataStructure.ApproximateMembership.spec_weaken`: monotonicity of `spec U n ε` in the
  false-positive bound `ε`.

## References

* [B. H. Bloom, *Space/time trade-offs in hash coding with allowable errors*][Bloom1970]
* [L. Carter, R. Floyd, J. Gill, G. Markowsky and M. Wegman, *Exact and approximate membership
  testers*][CarterFloydGillMarkowskyWegman1978]
* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership

open Finset
open scoped ENNReal

/-- Operations on a dynamic approximate-membership filter over universe `Fin U`. -/
inductive Op (U : ℕ) : Type where
  /-- Insert key `u` into the represented set. -/
  | insert (u : Fin U) : Op U
  /-- Delete key `u` from the represented set (valid when `u` is currently present). -/
  | delete (u : Fin U) : Op U
  /-- Query whether key `u` is currently in the represented set. -/
  | query (u : Fin U) : Op U
  deriving DecidableEq, Repr

/-- Return type of each filter operation: `PUnit` for `insert` and `delete`, `Bool` for `query`. -/
abbrev Result {U : ℕ} : Op U → Type
  | .insert _ => PUnit
  | .delete _ => PUnit
  | .query _ => Bool

/-- Transcript entry pairing a filter operation with its observation. -/
abbrev Label (U : ℕ) : Type := Sigma (@Result U)

/-- Single-step update of the currently present key set `S : Finset (Fin U)`. -/
@[expose] def stepSet {U : ℕ} (S : Finset (Fin U)) : Op U → Finset (Fin U)
  | .insert u => insert u S
  | .delete u => S.erase u
  | .query _ => S

@[simp]
theorem stepSet_insert {U : ℕ} (S : Finset (Fin U)) (u : Fin U) :
    stepSet S (.insert u) = insert u S := rfl

@[simp]
theorem stepSet_delete {U : ℕ} (S : Finset (Fin U)) (u : Fin U) :
    stepSet S (.delete u) = S.erase u := rfl

@[simp]
theorem stepSet_query {U : ℕ} (S : Finset (Fin U)) (u : Fin U) :
    stepSet S (.query u) = S := rfl

/-- The set of keys present after executing `ops` starting from `S`. -/
@[expose] def activeSetFrom {U : ℕ} (S : Finset (Fin U)) (ops : List (Op U)) : Finset (Fin U) :=
  ops.foldl stepSet S

@[simp]
theorem activeSetFrom_nil {U : ℕ} (S : Finset (Fin U)) :
    activeSetFrom S [] = S := rfl

@[simp]
theorem activeSetFrom_cons {U : ℕ} (S : Finset (Fin U)) (o : Op U) (ops : List (Op U)) :
    activeSetFrom S (o :: ops) = activeSetFrom (stepSet S o) ops := rfl

theorem activeSetFrom_append {U : ℕ} (S : Finset (Fin U)) (ops₁ ops₂ : List (Op U)) :
    activeSetFrom S (ops₁ ++ ops₂) = activeSetFrom (activeSetFrom S ops₁) ops₂ := by
  simp only [activeSetFrom, List.foldl_append]

/-- The set of keys present after executing `ops` starting from the empty set `∅`. -/
@[expose] def activeSet {U : ℕ} (ops : List (Op U)) : Finset (Fin U) :=
  activeSetFrom ∅ ops

@[simp]
theorem activeSet_nil {U : ℕ} : activeSet ([] : List (Op U)) = ∅ := rfl

/-- The set of keys present immediately before step `idx` in `ops`. -/
@[expose] def activeSetBefore {U : ℕ} (ops : List (Op U)) (idx : ℕ) : Finset (Fin U) :=
  activeSet (ops.take idx)

@[simp]
theorem activeSetBefore_zero {U : ℕ} (ops : List (Op U)) :
    activeSetBefore ops 0 = ∅ := rfl

/-- Single-step admissibility of operation `o` from current key set `S` under capacity `n`:
* `insert u` is valid when `u ∉ S` and `#S < n`;
* `delete u` is valid when `u ∈ S`;
* `query u` is always valid. -/
@[expose] def ValidOp {U : ℕ} (n : ℕ) (S : Finset (Fin U)) : Op U → Prop
  | .insert u => u ∉ S ∧ #S < n
  | .delete u => u ∈ S
  | .query _ => True

/-- Multi-step admissibility of `ops : List (Op U)` starting from key set `S` under capacity `n`. -/
@[expose] def ValidOpSeqFrom {U : ℕ} (n : ℕ) : Finset (Fin U) → List (Op U) → Prop
  | _, [] => True
  | S, o :: rest => ValidOp n S o ∧ ValidOpSeqFrom n (stepSet S o) rest

@[simp]
theorem validOpSeqFrom_nil {U : ℕ} (n : ℕ) (S : Finset (Fin U)) :
    ValidOpSeqFrom n S [] := trivial

@[simp]
theorem validOpSeqFrom_cons {U : ℕ} (n : ℕ) (S : Finset (Fin U)) (o : Op U) (rest : List (Op U)) :
    ValidOpSeqFrom n S (o :: rest) ↔ ValidOp n S o ∧ ValidOpSeqFrom n (stepSet S o) rest :=
  Iff.rfl

/-- Multi-step admissibility of `ops : List (Op U)` starting from `∅` under capacity `n`. -/
@[expose] def ValidOpSeq {U : ℕ} (n : ℕ) (ops : List (Op U)) : Prop :=
  ValidOpSeqFrom n ∅ ops

@[simp]
theorem validOpSeq_nil {U : ℕ} (n : ℕ) : ValidOpSeq n ([] : List (Op U)) := trivial

theorem card_stepSet_le {U : ℕ} {n : ℕ} {S : Finset (Fin U)} {o : Op U}
    (hS : #S ≤ n) (ho : ValidOp n S o) : #(stepSet S o) ≤ n := by
  cases o with
  | insert u =>
    dsimp only [stepSet]
    rw [Finset.card_insert_of_notMem ho.1]
    exact Nat.succ_le_of_lt ho.2
  | delete u =>
    dsimp only [stepSet]
    exact (Finset.card_erase_le).trans hS
  | query u => exact hS

theorem card_activeSetFrom_le {U : ℕ} {n : ℕ} {S : Finset (Fin U)} {ops : List (Op U)}
    (hS : #S ≤ n) (hv : ValidOpSeqFrom n S ops) :
    #(activeSetFrom S ops) ≤ n := by
  induction ops generalizing S with
  | nil => exact hS
  | cons o rest ih =>
    exact ih (card_stepSet_le hS hv.1) hv.2

theorem card_activeSet_le {U : ℕ} {n : ℕ} {ops : List (Op U)}
    (hv : ValidOpSeq n ops) : #(activeSet ops) ≤ n :=
  card_activeSetFrom_le (by simp) hv

theorem validOpSeqFrom_take {U : ℕ} {n : ℕ} {S : Finset (Fin U)} {ops : List (Op U)}
    (hv : ValidOpSeqFrom n S ops) (idx : ℕ) :
    ValidOpSeqFrom n S (ops.take idx) := by
  induction ops generalizing S idx with
  | nil => simp
  | cons o rest ih =>
    cases idx with
    | zero => simp
    | succ idx =>
      simp only [List.take_succ_cons, validOpSeqFrom_cons]
      exact ⟨hv.1, ih hv.2 idx⟩

theorem card_activeSetBefore_le {U : ℕ} {n : ℕ} {ops : List (Op U)}
    (hv : ValidOpSeq n ops) (idx : ℕ) : #(activeSetBefore ops idx) ≤ n :=
  card_activeSet_le (validOpSeqFrom_take hv idx)

/-- Pathwise zero-false-negative invariant: whenever `u ∈ activeSetBefore ops idx` and step `idx`
is `.query u`, the transcript entry at `idx` is `⟨.query u, true⟩`. -/
@[expose] def NoFalseNegatives {U : ℕ} (ops : List (Op U)) (tr : List (Label U)) : Prop :=
  ∀ idx < ops.length, ∀ u : Fin U,
    ops[idx]? = some (.query u) →
    u ∈ activeSetBefore ops idx →
    tr[idx]? = some ⟨.query u, true⟩

/-- Event that transcript `tr` outputs `true` at step `idx` for query `u`. -/
@[expose] def FalsePositiveAt {U : ℕ} (tr : List (Label U)) (idx : ℕ) (u : Fin U) : Prop :=
  tr[idx]? = some ⟨.query u, true⟩

/-- Oblivious-sequence specification of a dynamic approximate-membership filter over universe
`Fin U` with capacity `n` and per-query false-positive probability bound `ε : ℝ≥0∞`:
1. Every transcript in `μ.support` matches `ops` and has zero false negatives on every query of a
   currently present key (`u ∈ activeSetBefore ops idx`).
2. At every query of a currently absent key (`ops[idx]? = some (.query u)` with
   `u ∉ activeSetBefore ops idx`), the probability of returning `true` is at most `ε`. -/
abbrev spec (U n : ℕ) (ε : ℝ≥0∞) : ObliviousSequenceSpec where
  Op := Op U
  Result := Result
  ValidOpSeq := ValidOpSeq n
  Contract ops μ :=
    (∀ tr ∈ μ.support,
      TranscriptMatches ops tr ∧
      NoFalseNegatives ops tr) ∧
    (∀ idx < ops.length, ∀ u : Fin U,
      ops[idx]? = some (.query u) →
      u ∉ activeSetBefore ops idx →
      μ.toOuterMeasure {tr | FalsePositiveAt tr idx u} ≤ ε)

/-- Monotonicity of `spec` in the false-positive bound `ε₁ ≤ ε₂`. -/
theorem spec_weaken {U n : ℕ} {ε₁ ε₂ : ℝ≥0∞} (hε : ε₁ ≤ ε₂)
    {ops : List (Op U)} {μ : PMF (List (Label U))}
    (h : (spec U n ε₁).Contract ops μ) :
    (spec U n ε₂).Contract ops μ :=
  ⟨h.1, fun idx hidx u hop hnotMem => (h.2 idx hidx u hop hnotMem).trans hε⟩

end Cslib.DataStructure.ApproximateMembership
