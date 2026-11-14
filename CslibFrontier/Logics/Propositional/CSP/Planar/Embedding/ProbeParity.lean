/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeEdgeLabels
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ConstraintParity
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryRotation
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev

/-!
# Actual body-constraint parity under structural probe extension

Appending the probe preserves the complete indexed fiber at every original constraint.
Consequently its parity reads exactly the original body edge labels, independent of the
marker tuple, boundary distinctness, sparse names or any rotation.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

/-- The probe extension preserves actual original-body constraint parity. -/
theorem vertexParity_probeEdgeLabels_body_constraint (F : CSP Rel V) (ports : List V)
    (t : Fin ports.length → Bool) (x : Fin (incidenceGraph F).edges.length → Bool)
    (o : F.Occurrence) :
    (incidenceGraph (probeBody F ports)).vertexParity (probeEdgeLabels F ports t x)
        (incidenceDart (bodyOccurrence F ports o) true).vertex =
      (incidenceGraph F).vertexParity x (incidenceDart o true).vertex := by
  rw [vertexParity_eq_sum_scope, vertexParity_eq_sum_scope]
  have hlen := congrArg List.length (scope_bodyOccurrence F ports o)
  rw [List.ofFn_congr hlen]
  congr 1
  apply congrArg List.ofFn
  funext j
  have he : (⟨(bodyOccurrence F ports o).1, Fin.cast hlen.symm j⟩ :
      (probeBody F ports).Occurrence) = bodyOccurrence F ports (⟨o.1, j⟩ : F.Occurrence) := by
    apply CSP.Occurrence.eq_of_positions
    · exact (congrArg Prod.fst (record_bodyOccurrence F ports o)).trans
        (congrArg Prod.fst (record_bodyOccurrence F ports (⟨o.1, j⟩ : F.Occurrence))).symm
    · exact (congrArg (fun record : ℕ × ℕ × V => record.2.1)
        (record_bodyOccurrence F ports (⟨o.1, j⟩ : F.Occurrence))).symm
  rw [he, probeEdgeLabels_bodyOccurrence]

/-- A body variable outside the boundary tuple keeps exactly its original parity. No marker
is incident there, even if other port names occur repeatedly in the tuple. -/
theorem vertexParity_probeEdgeLabels_variable_of_not_mem (F : CSP Rel V) (ports : List V)
    (t : Fin ports.length → Bool) (x : Fin (incidenceGraph F).edges.length → Bool)
    (o : F.Occurrence) (ho : o.var ∉ ports) :
    (incidenceGraph (probeBody F ports)).vertexParity (probeEdgeLabels F ports t x)
        (incidenceDart (bodyOccurrence F ports o) false).vertex =
      (incidenceGraph F).vertexParity x (incidenceDart o false).vertex := by
  let selected := (CSP.incidenceList F).filter fun p => decide (p.var = o.var)
  let word := selected.map fun p => incidenceDart (bodyOccurrence F ports p) false
  have hn : word.Nodup := ((CSP.incidenceList_nodup F).filter _).map
    ((incidenceDart_injective false).comp (bodyOccurrence_injective F ports))
  have hw (d : Dart (incidenceGraph (probeBody F ports))) : d ∈ word ↔
      d.vertex = (incidenceDart (bodyOccurrence F ports o) false).vertex := by
    constructor
    · intro hd
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
      apply (vertex_incidenceDart_eq_iff _ _ false false).mpr
      exact ⟨rfl, by
        rw [var_bodyOccurrence, var_bodyOccurrence]
        exact of_decide_eq_true (List.mem_filter.mp hp).2⟩
    · intro hd
      obtain ⟨p, hp⟩ := exists_incidenceDart d
      have hv := (vertex_incidenceDart_eq_iff p (bodyOccurrence F ports o) d.2 false).mp (hp ▸ hd)
      have hvar : p.var = o.var := by
        simpa only [hv.1, Bool.false_eq_true, ite_false, var_bodyOccurrence] using hv.2
      rcases exists_bodyOccurrence_or_probeOccurrence F ports p with ⟨q, rfl⟩ | ⟨j, rfl⟩
      · refine List.mem_map.mpr ⟨q, ?_, hv.1 ▸ hp⟩
        exact List.mem_filter.mpr ⟨CSP.mem_incidenceList q,
          decide_eq_true ((var_bodyOccurrence F ports q).symm.trans hvar)⟩
      · have hm : (probeOccurrence F ports j).var ∈ ports := by
          rw [var_probeOccurrence]
          exact List.getElem_mem j.isLt
        exact (ho (hvar ▸ hm)).elim
  rw [(incidenceGraph (probeBody F ports)).vertexParity_eq_sum_word _ _ word hn hw,
    vertexParity_incidenceDart]
  simp only [word, selected, List.map_map, Function.comp_def, probeEdgeLabels_bodyOccurrence,
    Bool.false_eq_true, ite_false]

/-- At a distinct boundary marker, actual variable parity is its marker bit plus the edge
sum along the exact computed body tail. Empty tails contribute zero without selecting a dart. -/
theorem vertexParity_probeEdgeLabels_marker_variable (F : CSP Rel V) (ports : List V)
    (hn : ports.Nodup) (w : Witness F ports) (t : Fin ports.length → Bool)
    (x : Fin (incidenceGraph F).edges.length → Bool) (i : Fin ports.length) :
    (incidenceGraph (probeBody F ports)).vertexParity (probeEdgeLabels F ports t x)
        (incidenceDart (probeOccurrence F ports i) false).vertex =
      t i + (((RotationCertificate.cycleWord w.certificate
        (incidenceDart (probeOccurrence F ports i) false).index).tail.map (· / 2)).map
          fun j => (List.ofFn x).getD j false).sum := by
  let p := probeOccurrence F ports i
  let y := probeEdgeLabels F ports t x
  have hc := ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).1
  have hp : F.occurrences.length ≤ incidenceEdgeIndex p := by
    rw [incidenceEdgeIndex_probeOccurrence]
    omega
  have hword := vertexParity_eq_sum_incidenceWord y p
    ((RotationCertificate.cycleWord w.certificate (incidenceDart p false).index).map (· / 2))
    (nodup_variable_cycleBlock hc p) (mem_variable_cycleBlock_iff hc p)
  rw [hword]
  have hhead : RotationCertificate.cycleWord w.certificate (incidenceDart p false).index =
      (incidenceDart p false).index ::
        (RotationCertificate.cycleWord w.certificate (incidenceDart p false).index).tail := rfl
  rw [hhead, List.map_cons, List.map_cons, List.sum_cons]
  have hindex : (incidenceDart p false).index / 2 = incidenceEdgeIndex p := by
    change (2 * incidenceEdgeIndex p + 0) / 2 = _
    omega
  rw [hindex]
  have hbit : (List.ofFn y).getD (incidenceEdgeIndex p) false = t i :=
    (List.getD_ofFn y (incidenceDart p false).1 false).trans
      (probeEdgeLabels_probeOccurrence F ports t x i false)
  rw [hbit]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨q, hq, _, hpre⟩ := (mem_probe_cycleBlock_iff F ports hn w.certificate hc p hp j).mp hj
  obtain ⟨o, ho⟩ := exists_bodyOccurrence_of_prefix F ports q hpre
  calc
    (List.ofFn y).getD j false = y (incidenceDart q false).1 := by
      rw [← hq]
      exact List.getD_ofFn y (incidenceDart q false).1 false
    _ = x (incidenceDart o false).1 := by
      rw [← ho]
      exact probeEdgeLabels_bodyOccurrence F ports t x o false
    _ = (List.ofFn x).getD j false := by
      rw [← hq, ← ho, incidenceEdgeIndex_bodyOccurrence]
      exact (List.getD_ofFn x (incidenceDart o false).1 false).symm

/-- The actual appended probe-center parity is the sum of the complete original marker
tuple. Its reversed scope affects order, but retains every indexed marker exactly once. -/
theorem vertexParity_probeEdgeLabels_probe_constraint (F : CSP Rel V) (ports : List V)
    (t : Fin ports.length → Bool) (x : Fin (incidenceGraph F).edges.length → Bool)
    (i : Fin ports.length) :
    (incidenceGraph (probeBody F ports)).vertexParity (probeEdgeLabels F ports t x)
      (incidenceDart (probeOccurrence F ports i) true).vertex = (List.ofFn t).sum := by
  rw [vertexParity_eq_sum_scope]
  have hlen := length_scope_probeOccurrence F ports i
  change (probeBody F ports)[(probeOccurrence F ports i).1.val].2.length = ports.length at hlen
  rw [List.ofFn_congr hlen]
  have he (j : Fin ports.length) :
      probeEdgeLabels F ports t x
        (incidenceDart (⟨(probeOccurrence F ports i).1, Fin.cast hlen.symm j⟩ :
          (probeBody F ports).Occurrence) true).1 = t j.rev := by
    have hocc : (⟨(probeOccurrence F ports i).1, Fin.cast hlen.symm j⟩ :
        (probeBody F ports).Occurrence) = probeOccurrence F ports j.rev := by
      apply CSP.Occurrence.eq_of_positions
      · exact (probeOccurrence_constraint F ports i).trans
          (probeOccurrence_constraint F ports j.rev).symm
      · rw [probeOccurrence_argument]
        simp only [Fin.val_cast, Fin.val_rev]
        omega
    rw [hocc, probeEdgeLabels_probeOccurrence]
  rw [congrArg List.ofFn (funext he), List.sum_ofFn, List.sum_ofFn]
  exact Equiv.sum_comp Fin.revPerm t

end Cslib.Complexity.CSP.OrderedBoundary
