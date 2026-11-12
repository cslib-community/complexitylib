/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.LastArgument
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Symbols
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Nullary
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
import CslibFrontier.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.Nodup

/-!
# Removing the structural boundary probe

The probe contributes a suffix of positional occurrences. Its nullary case is a declared
point and leaves the exact supplied body table unchanged. These original structural facts
keep all original-language constraints and their argument orders intact.

## Main results

* `Cslib.Complexity.CSP.OrderedBoundary.bodyCertificate_accepted_of_probe`: actual body acceptance
  extracted internally from a supplied probe certificate, with the explicit `ports.Nodup` guard.
* `Cslib.Complexity.CSP.OrderedBoundary.Witness.ofProbe`: constructs the complete checked witness.
* `Cslib.Complexity.CSP.OrderedBoundary.Witness.forgetHead`: deletes one actual boundary marker.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- The probe's reversed scope contributes a literal suffix of indexed argument records. -/
theorem occurrences_probeBody (F : CSP Rel V) (ports : List V) :
    (probeBody F ports).occurrences = F.occurrences ++
      (ports.reverse.zipIdx.map fun (v, j) => (F.length, j, v)) := by
  simp [probeBody, CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences,
    List.zipIdx_append, List.zipIdx_map, List.flatMap_append, List.map_flatMap,
    List.map_map, Function.comp_def, -List.map_reverse]

omit [DecidableEq V] in
/-- Probe edge counts use the actual boundary word, even when names repeat. -/
theorem length_occurrences_probeBody (F : CSP Rel V) (ports : List V) :
    (probeBody F ports).occurrences.length = F.occurrences.length + ports.length := by
  simp only [occurrences_probeBody, List.length_append, List.length_map,
    List.length_zipIdx, List.length_reverse]

/-- A source occurrence belongs to the body prefix exactly when its constraint position
precedes the structural probe center. This concerns positions, not distinct scope records. -/
theorem incidenceEdgeIndex_probeBody_lt_iff (F : CSP Rel V) (ports : List V)
    (o : (probeBody F ports).Occurrence) :
    incidenceEdgeIndex o < F.occurrences.length ↔ o.1.val < F.length := by
  have hprefix : F.occurrences <+: (probeBody F ports).occurrences := by
    rw [occurrences_probeBody]
    exact List.prefix_append _ _
  change (probeBody F ports).occurrences.idxOf o.record < F.occurrences.length ↔ _
  rw [← hprefix.mem_iff_idxOf_lt_length]
  constructor
  · intro hm
    obtain ⟨p, hp⟩ := CSP.mem_occurrences.mp hm
    have he := congrArg Prod.fst hp
    change p.1.val = o.1.val at he
    rw [← he]
    exact p.1.isLt
  · intro hi
    have hm := CSP.mem_occurrences.mpr ⟨o, rfl⟩
    rw [occurrences_probeBody, List.mem_append] at hm
    rcases hm with hm | hm
    · exact hm
    · obtain ⟨⟨v, j⟩, -, he⟩ := List.mem_map.mp hm
      have hc := congrArg Prod.fst he
      change F.length = o.1.val at hc
      omega

/-- A deleted probe occurrence lies at the one appended constraint center. -/
theorem constraint_of_probe_occurrence (F : CSP Rel V) (ports : List V)
    (o : (probeBody F ports).Occurrence) (ho : F.occurrences.length ≤ incidenceEdgeIndex o) :
    o.1.val = F.length := by
  have hnot := (incidenceEdgeIndex_probeBody_lt_iff F ports o).not.mp (Nat.not_lt.mpr ho)
  have hbound := o.1.isLt
  have hlen : (probeBody F ports).length = F.length + 1 := by simp [probeBody]
  have hbound' : o.1.val < F.length + 1 := by simpa only [hlen] using hbound
  omega

/-- Distinct named boundary ports supply at most one probe occurrence at each variable.
Body occurrences may repeat labels and constraint records arbitrarily. -/
theorem probe_occurrence_eq_of_var_eq (F : CSP Rel V) (ports : List V)
    (hn : ports.Nodup) (o p : (probeBody F ports).Occurrence)
    (ho : F.occurrences.length ≤ incidenceEdgeIndex o)
    (hp : F.occurrences.length ≤ incidenceEdgeIndex p) (hv : o.var = p.var) : o = p := by
  have suffix (a : (probeBody F ports).Occurrence)
      (ha : F.occurrences.length ≤ incidenceEdgeIndex a) :
      a.record ∈ ports.reverse.zipIdx.map (fun (v, j) => (F.length, j, v)) := by
    have hm := CSP.mem_occurrences.mpr ⟨a, rfl⟩
    rw [occurrences_probeBody, List.mem_append] at hm
    rcases hm with hm | hm
    · have hlt : incidenceEdgeIndex a < F.occurrences.length := by
        change (probeBody F ports).occurrences.idxOf a.record < _
        rw [occurrences_probeBody, List.idxOf_append_of_mem hm]
        exact List.idxOf_lt_length_of_mem hm
      omega
    · exact hm
  obtain ⟨⟨v, j⟩, hj, he⟩ := List.mem_map.mp (suffix o ho)
  obtain ⟨⟨w, k⟩, hk, hf⟩ := List.mem_map.mp (suffix p hp)
  obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hj)
  obtain ⟨hkl, hkw⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hk)
  have hvw : v = w := by
    have he' := congrArg (fun a : ℕ × ℕ × V => a.2.2) he
    have hf' := congrArg (fun a : ℕ × ℕ × V => a.2.2) hf
    exact he'.trans (hv.trans hf'.symm)
  have hjk : j = k := ((List.nodup_reverse.mpr hn).getElem_inj_iff).mp
    (hjv.trans (hvw.trans hkw.symm))
  apply CSP.Occurrence.record_injective
  exact he.symm.trans (hjk ▸ hvw ▸ hf)

private theorem side_probe_dart_of_body_vertex (F : CSP Rel V) (ports : List V)
    (d a : Dart (incidenceGraph (probeBody F ports)))
    (hd : d.1.val < F.occurrences.length) (ha : F.occurrences.length ≤ a.1.val)
    (hv : a.vertex = d.vertex) : a.2 = false := by
  obtain ⟨o, ho⟩ := exists_incidenceDart d
  obtain ⟨p, hp⟩ := exists_incidenceDart a
  have hod : incidenceEdgeIndex o < F.occurrences.length := by
    have he : incidenceEdgeIndex o = d.1.val := congrArg (fun a => a.1.val) ho
    omega
  have hpa : F.occurrences.length ≤ incidenceEdgeIndex p := by
    have he : incidenceEdgeIndex p = a.1.val := congrArg (fun d => d.1.val) hp
    omega
  have hoc := (incidenceEdgeIndex_probeBody_lt_iff F ports o).mp hod
  have hpc := constraint_of_probe_occurrence F ports p hpa
  have hvar (q : (probeBody F ports).Occurrence) :
      (probeBody F ports).distinctVars.idxOf q.var < (probeBody F ports).numVars := by
    rw [← CSP.length_distinctVars]
    exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr q.var_mem)
  have hvo := hvar o
  have hvp := hvar p
  rw [← ho, ← hp, vertex_incidenceDart, vertex_incidenceDart] at hv
  cases hds : d.2 <;> cases has : a.2 <;>
    simp only [hds, has, Bool.false_eq_true, ite_false, ite_true] at hv ⊢ <;> omega

/-- At a vertex touched by a body dart, distinct boundary names leave at most one probe
dart. Repeated body visits and cutvertices are unrestricted. The probe center is excluded
by its actual constraint position, rather than by an assumed free-port injection. -/
theorem probe_dart_eq_of_body_vertex (F : CSP Rel V) (ports : List V) (hn : ports.Nodup)
    (d a b : Dart (incidenceGraph (probeBody F ports)))
    (hd : d.1.val < F.occurrences.length)
    (ha : F.occurrences.length ≤ a.1.val) (hb : F.occurrences.length ≤ b.1.val)
    (hav : a.vertex = d.vertex) (hbv : b.vertex = d.vertex) : a = b := by
  have hsa := side_probe_dart_of_body_vertex F ports d a hd ha hav
  have hsb := side_probe_dart_of_body_vertex F ports d b hd hb hbv
  obtain ⟨o, ho⟩ := exists_incidenceDart a
  obtain ⟨p, hp⟩ := exists_incidenceDart b
  have hoa : F.occurrences.length ≤ incidenceEdgeIndex o := by
    have he : incidenceEdgeIndex o = a.1.val := congrArg (fun d => d.1.val) ho
    omega
  have hpb : F.occurrences.length ≤ incidenceEdgeIndex p := by
    have he : incidenceEdgeIndex p = b.1.val := congrArg (fun d => d.1.val) hp
    omega
  have hv := hav.trans hbv.symm
  rw [← ho, ← hp, hsa, hsb, vertex_incidenceDart, vertex_incidenceDart] at hv
  have hm : o.var ∈ (probeBody F ports).distinctVars := CSP.mem_distinctVars.mpr o.var_mem
  have he : o = p := probe_occurrence_eq_of_var_eq F ports hn o p hoa hpb
    ((List.idxOf_inj hm).mp hv)
  rw [← ho, ← hp, hsa, hsb, he]

/-- A body dart returns to the body within two clockwise rotation steps when the named
boundary word is duplicate-free. No face/genus premise or body-degree bound is needed. -/
theorem rotate_probeBody_short_returns (F : CSP Rel V) (ports : List V) (hn : ports.Nodup)
    (r : RotationSystem (incidenceGraph (probeBody F ports)))
    (d : Dart (incidenceGraph (probeBody F ports))) (hd : d.1.val < F.occurrences.length) :
    (r.rotate d).1.val < F.occurrences.length ∨
      (r.rotate (r.rotate d)).1.val < F.occurrences.length := by
  by_cases ha : (r.rotate d).1.val < F.occurrences.length
  · exact Or.inl ha
  · apply Or.inr
    by_contra hb
    have he := probe_dart_eq_of_body_vertex F ports hn d (r.rotate d) (r.rotate (r.rotate d))
      hd (Nat.le_of_not_gt ha) (Nat.le_of_not_gt hb) (r.vertex_rotate d)
      ((r.vertex_rotate (r.rotate d)).trans (r.vertex_rotate d))
    have hd' := congrArg (fun a => a.1.val) (r.rotate.injective he)
    omega

/-- The supplied accepted table has the same two-step first-return property, at its actual
body dart prefix. The length comes from occurrences, not encoded labels or successor entries. -/
theorem probeBody_certificate_short_returns (F : CSP Rel V) (ports : List V)
    (hn : ports.Nodup) (c : RotationCertificate)
    (h : RotationCertificate.verifyRotation (incidenceGraph (probeBody F ports)) c = true) :
    ∀ i < 2 * F.occurrences.length,
      c.successor.getD i 0 < 2 * F.occurrences.length ∨
        c.successor.getD (c.successor.getD i 0) 0 < 2 * F.occurrences.length := by
  intro i hi
  have hb : i < 2 * (incidenceGraph (probeBody F ports)).2.length := by
    rw [incidenceGraph_edges, List.length_map, length_occurrences_probeBody]
    omega
  let r := RotationCertificate.decode (incidenceGraph (probeBody F ports)) c h
  let d := (Dart.indexEquiv (incidenceGraph (probeBody F ports))).symm ⟨i, hb⟩
  have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv _).apply_symm_apply ⟨i, hb⟩)
  have hde : d.1.val < F.occurrences.length := by
    change 2 * d.1.val + d.2.toNat = i at hd
    omega
  have hindex (a : Dart (incidenceGraph (probeBody F ports)))
      (ha : a.1.val < F.occurrences.length) : a.index < 2 * F.occurrences.length := by
    rcases a with ⟨j, side⟩
    change j.val < F.occurrences.length at ha
    cases side <;> simp only [Dart.index, Bool.toNat_false, Bool.toNat_true] <;> omega
  have hstep : c.successor.getD i 0 = (r.rotate d).index := by
    rw [← hd, RotationCertificate.index_decode_rotate]
  rcases rotate_probeBody_short_returns F ports hn r d hde with ha | ha
  · exact Or.inl (hstep ▸ hindex (r.rotate d) ha)
  · apply Or.inr
    rw [hstep, ← RotationCertificate.index_decode_rotate h (r.rotate d)]
    exact hindex (r.rotate (r.rotate d)) ha

/-- An accepted raw rotation funds restriction to its full table and stays literally equal.
The empty table is included; no source label or table entry supplies an iteration clock. -/
theorem restrictPrefix_eq_self_of_verifyRotation {G : Graph} {c : RotationCertificate}
    (h : RotationCertificate.verifyRotation G c = true) :
    restrictPrefix c.successor.length c = c := by
  apply restrictPrefix_eq_self
  intro i hi
  have hb : i < 2 * G.2.length := by rwa [RotationCertificate.length_of_verifyRotation h] at hi
  let d := (Dart.indexEquiv G).symm ⟨i, hb⟩
  have hd : d.index = i := congrArg Fin.val ((Dart.indexEquiv G).apply_symm_apply ⟨i, hb⟩)
  rw [← hd, ← RotationCertificate.index_decode_rotate h d]
  rw [RotationCertificate.length_of_verifyRotation h]
  exact (Dart.indexEquiv G ((RotationCertificate.decode G c h).rotate d)).isLt

/-- A zero-port probe is only an isolated constraint point. Its raw ordered numerical
certificate is accepted for the literal original-language body without changing the table. -/
theorem verifyRotationCertificate_probeBody_nil (F : CSP Rel V) (c : RotationCertificate) :
    verifyRotationCertificate (probeBody F []) c = verifyRotationCertificate F c := by
  have hm : F.map (fun c => (some c.1, c.2)) =
      F.map (fun (r, scope) => (some r, scope)) := by
    congr 1
  simp only [probeBody, List.reverse_nil, hm, verifyRotationCertificate_append_nullary,
    verifyRotationCertificate_mapRelation]

/-- At zero ports the canonical executable body restriction returns the very same accepted
raw table, including an empty body and arbitrary original nullary constraints. -/
theorem bodyCertificate_eq_of_probe_nil {F : CSP Rel V} {c : RotationCertificate}
    (h : verifyRotationCertificate (probeBody F []) c = true) : bodyCertificate F c = c := by
  rw [verifyRotationCertificate_probeBody_nil] at h
  obtain ⟨hrot, -, -⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp h
  have hn : c.successor.length = 2 * F.occurrences.length := by
    rw [RotationCertificate.length_of_verifyRotation hrot, incidenceGraph_edges, List.length_map]
  rw [bodyCertificate, ← hn]
  exact restrictPrefix_eq_self_of_verifyRotation hrot

/-- Acceptance of the actual augmented probe table internally supplies acceptance of its
canonical body restriction when the boundary names are distinct. Nullary and disconnected
body constraints are retained, and the empty body needs no nonempty-alphabet premise. -/
theorem bodyCertificate_accepted_of_probe (F : CSP Rel V) (ports : List V)
    (hn : ports.Nodup) (c : RotationCertificate)
    (h : verifyRotationCertificate (probeBody F ports) c = true) :
    verifyRotationCertificate F (bodyCertificate F c) = true := by
  induction ports generalizing c with
  | nil =>
    rw [bodyCertificate_eq_of_probe_nil h]
    rwa [verifyRotationCertificate_probeBody_nil] at h
  | cons p ports ih =>
    have ht := verifyRotationCertificate_restrictPrefix_lastArgument
      (F.map (fun c => (some c.1, c.2))) none ports.reverse p c (by
        simpa only [probeBody, List.reverse_cons] using h)
    have ht' : verifyRotationCertificate (probeBody F ports)
        (restrictPrefix (2 * (probeBody F ports).occurrences.length) c) = true := ht
    have hbody := ih hn.of_cons _ ht'
    obtain ⟨hrot, -, -⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp h
    have hc : 2 ≤ c.successor.length := by
      rw [RotationCertificate.length_of_verifyRotation hrot, incidenceGraph_edges, List.length_map,
        length_occurrences_probeBody, List.length_cons]
      omega
    have hmn : 2 * F.occurrences.length ≤ 2 * (probeBody F ports).occurrences.length := by
      rw [length_occurrences_probeBody]
      omega
    have hs := probeBody_certificate_short_returns F (p :: ports) hn c hrot
    rw [bodyCertificate, restrictPrefix_restrictPrefix_of_short_returns c _ _ hmn hc hs] at hbody
    exact hbody

/-- Construct the full actual-body boundary witness directly from its supplied probe table.
Body acceptance is proved internally; this is not a template-planarity provider premise. -/
@[expose] def Witness.ofProbe {F : CSP Rel V} {ports : List V} (hn : ports.Nodup)
    (c : RotationCertificate) (h : verifyRotationCertificate (probeBody F ports) c = true) :
    Witness F ports where
  certificate := c
  accepted := (verify_eq_true_iff _ _ _).mpr
    ⟨bodyCertificate_accepted_of_probe F ports hn c h, h⟩

/-- Deleting the first marker computes an accepted probe for the inherited remaining word.
The body, all original relation scopes and their clockwise argument rotations are retained. -/
theorem verifyRotationCertificate_restrictPrefix_probe_cons (F : CSP Rel V) (p : V)
    (ports : List V) (c : RotationCertificate)
    (h : verifyRotationCertificate (probeBody F (p :: ports)) c = true) :
    verifyRotationCertificate (probeBody F ports)
      (restrictPrefix (2 * (probeBody F ports).occurrences.length) c) = true := by
  have ht := verifyRotationCertificate_restrictPrefix_lastArgument
    (F.map (fun c => (some c.1, c.2))) none ports.reverse p c (by
      simpa only [probeBody, List.reverse_cons] using h)
  exact ht

/-- Forget the first boundary marker by deleting its actual final probe argument. The
original body is unchanged, including repeated body variables and closed components. -/
@[expose] def Witness.forgetHead {F : CSP Rel V} {p : V} {ports : List V}
    (w : Witness F (p :: ports)) (hn : ports.Nodup) : Witness F ports :=
  Witness.ofProbe hn
    (restrictPrefix (2 * (probeBody F ports).occurrences.length) w.certificate)
    (verifyRotationCertificate_restrictPrefix_probe_cons F p ports w.certificate w.probe_accepted)

end Cslib.Complexity.CSP.OrderedBoundary
