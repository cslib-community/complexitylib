/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem
public import Complexity.Logics.Propositional.CSP.Occurrence.AppendScope

/-!
# Literal edge positions of appended-scope occurrences

An appended argument occupies the old occurrence count plus its original argument position.
The formula is independent of repeated variable labels and duplicate constraint tuples. This
original coordinate identity uses the existing actual occurrence type and incidence edge list.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

/-- The appended argument's incidence edge is the body-prefix length plus its actual slot.
The empty-scope case has no argument to select. Variable names need not be distinct. -/
theorem incidenceEdgeIndex_appendOfFnOccurrenceEquiv_inr {Rel V : Type} [DecidableEq V]
    (F : CSP Rel V) (r : Rel) {n : ℕ} (scope : Fin n → V) (j : Fin n) :
    incidenceEdgeIndex (appendOfFnOccurrenceEquiv F r scope (Sum.inr j)) =
      F.occurrences.length + j.val := by
  have hi : F.occurrences.length + j.val < (F ++ [(r, List.ofFn scope)]).occurrences.length := by
    rw [occurrences_append_scope, List.length_append, List.length_map, List.length_zipIdx,
      List.length_ofFn]
    omega
  have he : (F ++ [(r, List.ofFn scope)]).occurrences[F.occurrences.length + j.val] =
      (F.length, j.val, scope j) := by
    simp only [occurrences_append_scope,
      List.getElem_append_right (show F.occurrences.length ≤ F.occurrences.length + j.val by omega),
      Nat.add_sub_cancel_left, List.getElem_map, List.getElem_zipIdx, List.getElem_ofFn,
      Nat.zero_add, Fin.eta]
  unfold incidenceEdgeIndex
  rw [record_appendOfFnOccurrenceEquiv_inr, ← he]
  exact (F ++ [(r, List.ofFn scope)]).occurrences_nodup.idxOf_getElem _ hi

end Cslib.Complexity.CSP
