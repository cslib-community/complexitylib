/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeOccurrences
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryRotation
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Restriction

/-!
# Literal body successors away from boundary ports

A body variable outside the probe tuple has no marker in its actual endpoint fiber. Its
accepted probe successor therefore remains in the body prefix, so the existing bounded
prefix restriction leaves that successor literally unchanged. No genus or degree shortcut
is used, and the probe tuple may be empty or contain repeated names.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

/-- Restricting the accepted table to the original body does not change a variable
successor outside the boundary tuple. The unchanged successor is an actual body dart. -/
theorem getD_bodyCertificate_of_variable_not_mem_ports {F : CSP Rel V} {ports : List V}
    (w : Witness F ports) (o : F.Occurrence) (ho : o.var ∉ ports) :
    (bodyCertificate F w.certificate).successor.getD (incidenceDart o false).index 0 =
      w.certificate.successor.getD (incidenceDart o false).index 0 := by
  let d := w.probeRotation.rotate (incidenceDart (bodyOccurrence F ports o) false)
  have hc := ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).1
  have hv := w.probeRotation.vertex_rotate (incidenceDart (bodyOccurrence F ports o) false)
  have hv' : d.vertex = (incidenceDart (bodyOccurrence F ports o) false).vertex := hv
  obtain ⟨p, hp⟩ := exists_incidenceDart d
  have hf := (vertex_incidenceDart_eq_iff p (bodyOccurrence F ports o) d.2 false).mp
    ((congrArg Dart.vertex hp).trans hv')
  have hvar : p.var = o.var := by
    simpa only [hf.1, Bool.false_eq_true, ite_false, var_bodyOccurrence] using hf.2
  have hpre : incidenceEdgeIndex p < F.occurrences.length := by
    rcases exists_bodyOccurrence_or_probeOccurrence F ports p with ⟨q, rfl⟩ | ⟨j, rfl⟩
    · rw [incidenceEdgeIndex_bodyOccurrence]
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt q
    · have hm : (probeOccurrence F ports j).var ∈ ports := by
        rw [var_probeOccurrence]
        exact List.getElem_mem j.isLt
      exact (ho (hvar ▸ hm)).elim
  have hindex : (incidenceDart (bodyOccurrence F ports o) false).index =
      (incidenceDart o false).index := by
    change 2 * incidenceEdgeIndex (bodyOccurrence F ports o) + 0 = 2 * incidenceEdgeIndex o + 0
    rw [incidenceEdgeIndex_bodyOccurrence]
  have hnext : w.certificate.successor.getD (incidenceDart o false).index 0 = d.index := by
    have h := RotationCertificate.index_decode_rotate hc
      (incidenceDart (bodyOccurrence F ports o) false)
    rw [hindex] at h
    exact h.symm
  have hnextlt : w.certificate.successor.getD (incidenceDart o false).index 0 <
      2 * F.occurrences.length := by
    have hp' : incidenceDart p false = d := hf.1 ▸ hp
    rw [hnext, ← hp']
    change 2 * incidenceEdgeIndex p + 0 < _
    omega
  have hi : (incidenceDart o false).index < 2 * F.occurrences.length := by
    have he : incidenceEdgeIndex o < F.occurrences.length := by
      simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
    change 2 * incidenceEdgeIndex o + 0 < _
    omega
  have hpos : 0 < w.certificate.successor.length := by
    have hi' : (incidenceDart o false).index < w.certificate.successor.length := by
      rw [RotationCertificate.length_of_verifyRotation hc, ← hindex]
      exact (Dart.indexEquiv _ (incidenceDart (bodyOccurrence F ports o) false)).isLt
    omega
  exact getD_restrictPrefix_one w.certificate _ _ hi hpos hnextlt

end Cslib.Complexity.CSP.OrderedBoundary
