/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexFibers
public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceEnumeration
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateCycles

/-!
# Variable cycle words retain exactly the indexed occurrences of their label

The variable-side cycle of an accepted raw table contains only even dart indices. Dividing
these indices by two gives a duplicate-free word of occurrence positions. Variable names
may repeat in scopes and constraints; only the occurrence positions are distinct.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V} {c : RotationCertificate}

/-- Every entry of a rooted variable cycle is a variable-side dart at that same original
label, with its actual indexed occurrence retained. -/
theorem mem_variable_cycleWord_iff
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (o : F.Occurrence) (index : ℕ) :
    index ∈ RotationCertificate.cycleWord c (incidenceDart o false).index ↔
      ∃ p : F.Occurrence, index = 2 * incidenceEdgeIndex p ∧ p.var = o.var := by
  rw [RotationCertificate.mem_cycleWord_iff_exists_dart hc]
  constructor
  · rintro ⟨d, hd, hv⟩
    obtain ⟨p, hp⟩ := exists_incidenceDart d
    have hf := (vertex_incidenceDart_eq_iff p o d.2 false).mp (by rw [hp]; exact hv)
    have hside : d.2 = false := hf.1
    refine ⟨p, ?_, ?_⟩
    · rw [← hd, ← hp, hside]
      rfl
    · simpa only [hside, Bool.false_eq_true, ite_false] using hf.2
  · rintro ⟨p, rfl, hv⟩
    exact ⟨incidenceDart p false, rfl,
      (vertex_incidenceDart_eq_iff p o false false).mpr ⟨rfl, hv⟩⟩

/-- Dividing the actual variable darts by two gives exactly the occurrence positions at
the selected variable, including parallel incidences and repeated relation records. -/
theorem mem_variable_cycleBlock_iff
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (o : F.Occurrence) (index : ℕ) :
    index ∈ (RotationCertificate.cycleWord c (incidenceDart o false).index).map (· / 2) ↔
      ∃ p : F.Occurrence, incidenceEdgeIndex p = index ∧ p.var = o.var := by
  simp only [List.mem_map, mem_variable_cycleWord_iff hc]
  constructor
  · rintro ⟨j, ⟨p, rfl, hv⟩, hj⟩
    exact ⟨p, by omega, hv⟩
  · rintro ⟨p, rfl, hv⟩
    exact ⟨2 * incidenceEdgeIndex p, ⟨p, rfl, hv⟩, by omega⟩

/-- The occurrence-position word of a variable cycle is duplicate-free. -/
theorem nodup_variable_cycleBlock
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (o : F.Occurrence) :
    ((RotationCertificate.cycleWord c (incidenceDart o false).index).map (· / 2)).Nodup := by
  apply (RotationCertificate.nodup_cycleWord hc _).map_on
  intro i hi j hj he
  obtain ⟨p, hp, _⟩ := (mem_variable_cycleWord_iff hc o i).mp hi
  obtain ⟨q, hq, _⟩ := (mem_variable_cycleWord_iff hc o j).mp hj
  omega

/-- The runtime first-occurrence root has exactly the original variable's indexed darts.
An occurring-name premise justifies this particular root, not a degree or injectivity premise. -/
theorem mem_first_variable_cycleWord_iff
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (v : V) (hv : v ∈ F.vars) (index : ℕ) :
    index ∈ RotationCertificate.cycleWord c (2 * F.vars.idxOf v) ↔
      ∃ p : F.Occurrence, index = 2 * incidenceEdgeIndex p ∧ p.var = v := by
  obtain ⟨o, ho, hvar⟩ := exists_occurrence_at_first_index v hv
  have hstart : (incidenceDart o false).index = 2 * F.vars.idxOf v := by
    change 2 * incidenceEdgeIndex o + 0 = _
    rw [ho, Nat.add_zero]
  rw [← hstart, mem_variable_cycleWord_iff hc, hvar]

/-- The actual bounded scan at an occurring variable's first position has no repeated darts. -/
theorem nodup_first_variable_cycleWord
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (v : V) (hv : v ∈ F.vars) :
    (RotationCertificate.cycleWord c (2 * F.vars.idxOf v)).Nodup := by
  obtain ⟨o, ho, _⟩ := exists_occurrence_at_first_index v hv
  have hstart : (incidenceDart o false).index = 2 * F.vars.idxOf v := by
    change 2 * incidenceEdgeIndex o + 0 = _
    rw [ho, Nat.add_zero]
  rw [← hstart]
  exact RotationCertificate.nodup_cycleWord hc _

end Cslib.Complexity.CSP
