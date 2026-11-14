/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeOccurrences
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Literal edge labels on a probe-augmented body

The original body prefix keeps its supplied edge labels. The structural probe suffix receives
the supplied port tuple in exactly the reversed scope order. Zero arities and empty bodies need
no selected edge or corner. These labels are mathematical data, independent of any rotation.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

/-- Extend body edge labels by the literal reverse-ordered structural marker tuple. -/
@[expose] def probeEdgeLabels (F : CSP Rel V) (ports : List V) (t : Fin ports.length → Bool)
    (x : Fin (incidenceGraph F).edges.length → Bool) :
    Fin (incidenceGraph (probeBody F ports)).edges.length → Bool :=
  fun j => if j.val < F.occurrences.length then (List.ofFn x).getD j.val false
    else (List.ofFn t).getD (ports.length - 1 - (j.val - F.occurrences.length)) false

/-- Every retained original body occurrence reads exactly its supplied body edge bit. -/
theorem probeEdgeLabels_bodyOccurrence (F : CSP Rel V) (ports : List V)
    (t : Fin ports.length → Bool) (x : Fin (incidenceGraph F).edges.length → Bool)
    (o : F.Occurrence) (side : Bool) :
    probeEdgeLabels F ports t x (incidenceDart (bodyOccurrence F ports o) side).1 =
      x (incidenceDart o side).1 := by
  have ho : incidenceEdgeIndex o < F.occurrences.length := by
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
  unfold probeEdgeLabels
  simp only [incidenceDart]
  simp only [incidenceEdgeIndex_bodyOccurrence, ite_eq_left ho]
  exact List.getD_ofFn x (incidenceDart o side).1 false

/-- Each actual probe occurrence reads its original port coordinate, despite the reversed
scope. The finite coordinate supplies the bounds, including at arities zero and one. -/
theorem probeEdgeLabels_probeOccurrence (F : CSP Rel V) (ports : List V)
    (t : Fin ports.length → Bool) (x : Fin (incidenceGraph F).edges.length → Bool)
    (i : Fin ports.length) (side : Bool) :
    probeEdgeLabels F ports t x (incidenceDart (probeOccurrence F ports i) side).1 = t i := by
  unfold probeEdgeLabels
  simp only [incidenceDart]
  have hnot : ¬ F.occurrences.length + (ports.length - 1 - i.val) < F.occurrences.length := by omega
  simp only [incidenceEdgeIndex_probeOccurrence, ite_eq_right hnot]
  have he : ports.length - 1 -
      (F.occurrences.length + (ports.length - 1 - i.val) - F.occurrences.length) = i.val := by
    omega
  rw [he]
  exact List.getD_ofFn t i false

end Cslib.Complexity.CSP.OrderedBoundary
