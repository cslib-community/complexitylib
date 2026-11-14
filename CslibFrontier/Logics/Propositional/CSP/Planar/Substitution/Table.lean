/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement
public import CslibFrontier.Foundations.GroupTheory.Perm.ListCycles
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Mathlib.Data.List.GetD

/-!
# Positional rotation tables for fixed-gadget replacement

The target body is exactly `replaceGadgets`, with its existing even/odd fresh namespaces.
Local rotation blocks use local **occurrence positions**. At each original variable, its
source successor cycle orders the blocks of its distinct source incidences, even when the
same variable occurs repeatedly in one constraint. Target argument rotations are built
from the target's actual ordered scope lists, so no relation is reflected.

Every loop is funded by a source, template, or target list. Binary source names and invalid
binary successor entries are lookup data, not loop bounds. Fixed template preprocessing is
nonuniform in the language. This module defines the executed positional table construction;
its vertex-fiber and componentwise numerical Euler properties are separate proof obligations.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP Turing.MultiTapeTM

variable {Src Rel : Type}

/-- Number of target occurrences contributed by the actual preceding source constraints. -/
@[expose] def occurrencePrefix (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) (index : ℕ) : ℕ :=
  ((F.take index).flatMap fun c => (templates c.rel).vars).length

/-- Shift one local occurrence block into its literal position in the flat-mapped body. -/
@[expose] def shiftBlock (offset : ℕ) (block : List ℕ) : List ℕ :=
  block.map (offset + ·)

/-- Expand one recorded source incidence by scanning actual constraint positions. The
record's indices are unary positions; relation symbols are read from the original body. -/
@[expose] def blockAtRecord (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (record : ℕ × ℕ) : List ℕ :=
  F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
    if i = record.1 then
      shiftBlock (occurrencePrefix templates F i)
        ((freeBlocks relation).getD record.2 [])
    else []

/-- The block for a single original incidence position. Oversized supplied successor values
are only used in the bounded lookup of the original occurrence record. -/
@[expose] def incidenceBlock (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ) (dart : ℕ) : List ℕ :=
  let ⟨row, argument, _⟩ := F.occurrences.getD (dart / 2) (0, 0, 0)
  blockAtRecord templates freeBlocks F (row, argument)

/-- Splice blocks in the actual source rotation at one appearing variable. The start is its
first positional occurrence, with no enumeration up to the numeric variable name. -/
@[expose] def variableBlock (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (c : Graph.RotationCertificate) (v : ℕ) : List ℕ :=
  (Graph.RotationCertificate.cycleWord c
    (2 * (F.occurrences.map fun ⟨_, _, name⟩ => name).idxOf v)).flatMap
    (incidenceBlock templates freeBlocks F)

/-- All variable-side target cycles: source-variable blocks first, followed by each copy's
private auxiliary-variable cycles in constraint-list order. Empty blocks are harmless. -/
@[expose] def replacementCycles (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (c : Graph.RotationCertificate) : List (List ℕ) :=
  F.distinctVars.map (variableBlock templates freeBlocks F c) ++
    F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
      (auxiliaryBlocks relation).map (shiftBlock (occurrencePrefix templates F i))

/-- Each emitted word is either one actual source-variable splice or one auxiliary block
at an actual indexed source row. Duplicate source records retain separate copy indices. -/
theorem mem_replacementCycles_iff (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (c : Graph.RotationCertificate) (word : List ℕ) :
    word ∈ replacementCycles templates freeBlocks auxiliaryBlocks F c ↔
      (∃ v ∈ F.distinctVars, variableBlock templates freeBlocks F c v = word) ∨
        ∃ i : Fin F.length, ∃ block ∈ auxiliaryBlocks F[i.val].rel,
          shiftBlock (occurrencePrefix templates F i.val) block = word := by
  simp only [replacementCycles, List.mem_append, List.mem_map, List.mem_flatMap]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨⟨row, i⟩, he, block, hb, hword⟩
    obtain ⟨hi, hrow⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
    change i < F.length at hi
    change F[i] = row at hrow
    subst row
    exact ⟨⟨i, hi⟩, block, hb, hword⟩
  · rintro ⟨i, block, hb, hword⟩
    exact ⟨(F[i.val], i.val), List.mem_zipIdx_iff_getElem?.mpr
      (List.getElem?_eq_some_iff.mpr ⟨i.isLt, rfl⟩), block, hb, hword⟩

/-- Successor pairs for each actual target occurrence. The second entry always follows
its original target constraint's cyclic argument order. -/
@[expose] def successorPairs (F : CSP Rel ℕ) (cycles : List (List ℕ)) : List (ℕ × ℕ) :=
  F.occurrences.zipIdx.map fun ⟨⟨row, argument, _⟩, i⟩ =>
    (2 * List.nextInCycles cycles i, 2 * argumentNextIndex F row argument + 1)

/-- Emit one even variable successor and one odd argument successor per target occurrence. -/
@[expose] def certificate (F : CSP Rel ℕ) (cycles : List (List ℕ)) :
    Graph.RotationCertificate :=
  ⟨(successorPairs F cycles).flatMap fun p => [p.1, p.2]⟩

/-- The produced table has exactly two entries per actual target occurrence on all inputs. -/
theorem length_certificate (F : CSP Rel ℕ) (cycles : List (List ℕ)) :
    (certificate F cycles).successor.length = 2 * F.occurrences.length := by
  change (Graph.incidenceVertices ⟨[], successorPairs F cycles⟩).length = _
  rw [Graph.incidenceVertices_length]
  simp [successorPairs]

/-- The emitted constraint-side rotation has exactly the target's literal argument order,
independently of the candidate variable cycles. This is an executed checker equality. -/
theorem verifyArgumentOrder_certificate (F : CSP Rel ℕ) (cycles : List (List ℕ)) :
    verifyArgumentOrder F (certificate F cycles) = true := by
  rw [verifyArgumentOrder, List.all_eq_true]
  intro entry he
  obtain ⟨hi, hentry⟩ := List.getElem?_eq_some_iff.mp
    (List.mem_zipIdx_iff_getElem?.mp he)
  apply decide_eq_true
  change (Graph.incidenceVertices ⟨[], successorPairs F cycles⟩).getD
    (2 * entry.2 + 1) 0 = _
  rw [Graph.getD_incidenceVertices_odd]
  have hp : entry.2 < (successorPairs F cycles).length := by
    simpa only [successorPairs, List.length_map, List.length_zipIdx] using hi
  rw [List.getD_eq_getElem _ _ hp]
  simp only [successorPairs, List.getElem_map, List.getElem_zipIdx]
  rw [hentry]

private theorem getD_successorPairs_occurrence (F : CSP Rel ℕ) (cycles : List (List ℕ))
    (o : F.Occurrence) :
    (successorPairs F cycles).getD (incidenceEdgeIndex o) (0, 0) =
      (2 * List.nextInCycles cycles (incidenceEdgeIndex o),
        2 * incidenceEdgeIndex (argumentSuccessor o) + 1) := by
  rw [List.getD_eq_getElem _ _ (by
    simpa only [successorPairs, List.length_map, List.length_zipIdx, incidenceGraph_edges]
      using incidenceEdgeIndex_lt o)]
  simp only [successorPairs, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  unfold incidenceEdgeIndex
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  change (_, 2 * argumentNextIndex F o.1 o.2 + 1) = _
  rw [argumentNextIndex_occurrence]
  rfl

/-- Every emitted raw successor is its exact variable-cycle or original argument successor.
This inspects the actual indexed body, retaining duplicate rows and repeated variable names. -/
theorem getD_certificate_incidenceDart (F : CSP Rel ℕ) (cycles : List (List ℕ))
    (o : F.Occurrence) (side : Bool) :
    (certificate F cycles).successor.getD (incidenceDart o side).index 0 =
      if side then 2 * incidenceEdgeIndex (argumentSuccessor o) + 1
      else 2 * List.nextInCycles cycles (incidenceEdgeIndex o) := by
  cases side
  · change (Graph.incidenceVertices ⟨[], successorPairs F cycles⟩).getD
      (2 * incidenceEdgeIndex o) 0 = _
    rw [Graph.getD_incidenceVertices_even, getD_successorPairs_occurrence]
    rfl
  · change (Graph.incidenceVertices ⟨[], successorPairs F cycles⟩).getD
      (2 * incidenceEdgeIndex o + 1) 0 = _
    rw [Graph.getD_incidenceVertices_odd, getD_successorPairs_occurrence]
    rfl

/-- The candidate certificate is computed from the literal replacement body and positional
source/template blocks. No rotation search is performed. -/
@[expose] def replacementCertificate (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (c : Graph.RotationCertificate) : Graph.RotationCertificate :=
  certificate (replaceGadgets B templates F)
    (replacementCycles templates freeBlocks auxiliaryBlocks F c)

/-- Every target scope order is preserved by the generated table, including repeated
variables and duplicate constraint records. -/
theorem verifyArgumentOrder_replacementCertificate (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ))
    (freeBlocks auxiliaryBlocks : Src → List (List ℕ)) (F : CSP Src ℕ)
    (c : Graph.RotationCertificate) :
    verifyArgumentOrder (replaceGadgets B templates F)
      (replacementCertificate B templates freeBlocks auxiliaryBlocks F c) = true :=
  verifyArgumentOrder_certificate _ _

end Cslib.Complexity.CSP.GadgetRotation
