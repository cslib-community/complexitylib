/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Relabel
import Mathlib.Data.List.GetD

/-!
# Positional incidence darts under arbitrary variable maps

An arbitrary variable map retains every original constraint/argument position and both
indexed edge ends. Its endpoint formula uses the target's actual dense names. Noninjective
maps can change vertex fibers, so this coordinate equivalence alone supplies no rotation
or numerical-genus claim. These original identities support actual variable identification.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V W : Type} [DecidableEq V] [DecidableEq W]

/-- Variable maps keep edge/end positions even when they identify source variable names. -/
@[expose] def relabelDartEquiv (F : CSP Rel V) (f : V → W) :
    Dart (incidenceGraph F) ≃ Dart (incidenceGraph (F.relabel f)) :=
  (finCongr (by simp [incidenceGraph_edges, CSP.occurrences_relabel])).prodCongr (Equiv.refl Bool)

/-- The target endpoint is its actual dense variable name or unchanged constraint position. -/
theorem vertex_relabelDartEquiv (F : CSP Rel V) (f : V → W)
    (o : F.Occurrence) (side : Bool) :
    (relabelDartEquiv F f (incidenceDart o side)).vertex =
      if side then (F.relabel f).numVars + o.1
      else (F.relabel f).distinctVars.idxOf (f o.var) := by
  have hi : incidenceEdgeIndex o < F.occurrences.length := by
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
  have hidx : F.occurrences.idxOf o.record < F.occurrences.length :=
    List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩)
  have he : (incidenceGraph (F.relabel f)).2.getD (incidenceEdgeIndex o) (0, 0) =
      ((F.relabel f).distinctVars.idxOf (f o.var), (F.relabel f).numVars + o.1) := by
    rw [incidenceGraph_edges, CSP.occurrences_relabel, List.map_map]
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi), List.getElem_map]
    change ((F.relabel f).distinctVars.idxOf
      (f (F.occurrences[F.occurrences.idxOf o.record]'hidx).2.2),
        (F.relabel f).numVars + (F.occurrences[F.occurrences.idxOf o.record]'hidx).1) = _
    rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
    rfl
  change (if side then ((incidenceGraph (F.relabel f)).2.getD
    (incidenceEdgeIndex o) (0, 0)).2 else ((incidenceGraph (F.relabel f)).2.getD
      (incidenceEdgeIndex o) (0, 0)).1) = _
  rw [he]

/-- The literal binary index is unchanged by the variable map. -/
theorem index_relabelDartEquiv (F : CSP Rel V) (f : V → W) (d : Dart (incidenceGraph F)) :
    (relabelDartEquiv F f d).index = d.index := rfl

/-- Positional variable maps retain the two opposite ends of every actual edge occurrence. -/
theorem reverse_relabelDartEquiv (F : CSP Rel V) (f : V → W) (d : Dart (incidenceGraph F)) :
    relabelDartEquiv F f d.reverse = (relabelDartEquiv F f d).reverse := rfl

end Cslib.Complexity.CSP
