/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem
public import Complexity.Computability.PolyTime.Graph.RotationSystem
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.GetD

/-!
# Finite ordered incidence rotation certificates

The graph and argument occurrences are exactly those of the existing CSP incidence model.
The constraint-side successor follows the original scope order, including repeated variables
and identical constraint records. Nullary constraints have no argument ports; their order test
is vacuous and no zero-length face is invented. A false nullary relation requires a separate
satisfiability guard, which is not an order condition.

This verifies a supplied rotation with componentwise numerical Euler. It does not recognize
geometric planarity, construct an embedding from a bare CSP, normalize nullary constraints,
identify disconnected outer faces, or prove an ordinary planar-CSP complexity classification.
The source mapping is the ordered incidence multigraph of Fulla–Živný, arXiv:1602.06323v3,
Section 2.1, paragraph preceding Definition 1. The geometric face model of
[KazdaKolmogorovRolinek2018], Definition 12, p. 6 is a later correspondence obligation.
Fulla–Živný use weighted valued constraints of positive arity; this decision-CSP interface omits
weights and retains nullary scopes as an explicit extension, without asserting their geometric
face correspondence.

## Main results

* `Cslib.Complexity.CSP.verifyArgumentOrder_eq_true_iff`: exact original cyclic argument order.
* `Cslib.Complexity.CSP.exists_bounded_rotationCertificate_iff`: bounded certificate completeness.
* `Cslib.Complexity.CSP.computableInPolyTime_verifyRotationCertificate`: native supplied-certificate
  verification, with arbitrary encoded source variable labels.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

/-- Constraint and scope positions of each existing argument occurrence, in edge-list order. -/
@[expose] def argumentPositions (F : CSP Rel V) : List (ℕ × ℕ) :=
  F.occurrences.map fun (constraint, (argument, _variable)) => (constraint, argument)

/-- A constraint's actual scope length, read from the input list. Missing constraints return zero;
relation arities are never used as clocks. -/
@[expose] def scopeLength (F : CSP Rel V) (i : ℕ) : ℕ :=
  (F.map fun c => c.2.length).getD i 0

/-- Edge position of the next argument, with last-to-first wraparound in its original scope. -/
@[expose] def argumentNextIndex (F : CSP Rel V) (i j : ℕ) : ℕ :=
  (argumentPositions F).idxOf (i, if j + 1 < scopeLength F i then j + 1 else 0)

omit [DecidableEq V] in
/-- Distinct occurrences have distinct position pairs, even with repeated variable labels. -/
theorem argumentPositions_nodup (F : CSP Rel V) : (argumentPositions F).Nodup := by
  apply F.occurrences_nodup.map_on
  intro a ha b hb hab
  obtain ⟨⟨i, j⟩, rfl⟩ := CSP.mem_occurrences.mp ha
  obtain ⟨⟨k, l⟩, rfl⟩ := CSP.mem_occurrences.mp hb
  have hi : i = k := Fin.ext (congrArg Prod.fst hab)
  subst k
  have hj : j = l := Fin.ext (congrArg Prod.snd hab)
  subst l
  rfl

private theorem getElem_argumentPositions (o : F.Occurrence) :
    (argumentPositions F)[incidenceEdgeIndex o]'(by
      simpa only [argumentPositions, List.length_map, incidenceGraph_edges]
        using incidenceEdgeIndex_lt o) = (o.1.val, o.2.val) := by
  simp only [argumentPositions, List.getElem_map, incidenceEdgeIndex]
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  rfl

omit [DecidableEq V] in
/-- The executable length reader uses the occurrence's actual scope. -/
theorem scopeLength_occurrence (o : F.Occurrence) :
    scopeLength F o.1 = F[o.1.val].2.length := by
  unfold scopeLength
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using o.1.isLt)]
  simp only [List.getElem_map]

private theorem nextPosition_finRotate {n : ℕ} (j : Fin n) :
    (if j.val + 1 < n then j.val + 1 else 0) = (finRotate n j).val := by
  cases n with
  | zero => exact j.elim0
  | succ n =>
    rw [coe_finRotate]
    simp only [Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega

/-- The native next-index calculation is precisely the existing cyclic argument successor. -/
theorem argumentNextIndex_occurrence (o : F.Occurrence) :
    argumentNextIndex F o.1 o.2 = incidenceEdgeIndex (argumentSuccessor o) := by
  unfold argumentNextIndex
  rw [scopeLength_occurrence o, nextPosition_finRotate]
  change (argumentPositions F).idxOf
    ((argumentSuccessor o).1.val, (argumentSuccessor o).2.val) = _
  rw [← getElem_argumentPositions (argumentSuccessor o)]
  exact (argumentPositions_nodup F).idxOf_getElem _ _

/-- Verify the constraint-side successor at every actual argument occurrence. -/
@[expose] def verifyArgumentOrder (F : CSP Rel V) (c : Graph.RotationCertificate) : Bool :=
  F.occurrences.zipIdx.all fun entry =>
    let ((constraint, (argument, _variable)), k) := entry
    decide (c.successor.getD (2 * k + 1) 0 =
      2 * argumentNextIndex F constraint argument + 1)

/-- Framed CSP followed by its finite graph-rotation certificate. The source variable encoding
is explicit; graph labels and certificate successor indices remain binary. -/
abbrev encCSPRotationCertificate (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :=
  encPair (encCSP encRel encV) Graph.encRotationCertificate

/-- Verify supplied numerical genus zero and the original cyclic argument order together. -/
@[expose] def verifyRotationCertificate (F : CSP Rel V) (c : Graph.RotationCertificate) : Bool :=
  Graph.RotationCertificate.verifyGenusZero (incidenceGraph F) c && verifyArgumentOrder F c

/-- The executed argument-order check is exactly the existing `RespectsArgumentOrder` predicate
on the decoded rotation. -/
theorem verifyArgumentOrder_eq_true_iff {c : Graph.RotationCertificate}
    (h : Graph.RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    verifyArgumentOrder F c = true ↔
      RespectsArgumentOrder (Graph.RotationCertificate.decode (incidenceGraph F) c h) := by
  simp only [verifyArgumentOrder, List.all_eq_true, decide_eq_true_eq, RespectsArgumentOrder]
  constructor
  · intro hc o
    have hm : (o.record, incidenceEdgeIndex o) ∈ F.occurrences.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp only [incidenceEdgeIndex]
      exact List.getElem?_idxOf (CSP.mem_occurrences.mpr ⟨o, rfl⟩)
    have he := hc _ hm
    dsimp only [CSP.Occurrence.record] at he
    rw [argumentNextIndex_occurrence] at he
    apply (Graph.Dart.indexEquiv _).injective
    apply Fin.ext
    change Graph.Dart.index ((Graph.RotationCertificate.decode _ _ h).rotate
      (incidenceDart o true)) = Graph.Dart.index (incidenceDart (argumentSuccessor o) true)
    rw [Graph.RotationCertificate.index_decode_rotate]
    exact he
  · intro hc entry he
    obtain ⟨hi, hrecord⟩ := List.getElem?_eq_some_iff.mp
      (List.mem_zipIdx_iff_getElem?.mp he)
    obtain ⟨o, ho⟩ := CSP.mem_occurrences.mp (List.getElem_mem hi)
    have hk : incidenceEdgeIndex o = entry.2 := by
      unfold incidenceEdgeIndex
      rw [ho]
      exact F.occurrences_nodup.idxOf_getElem _ _
    have hr : o.record = entry.1 := ho.trans hrecord
    have hh := congrArg Graph.Dart.index (hc o)
    rw [Graph.RotationCertificate.index_decode_rotate] at hh
    dsimp only [Graph.Dart.index, incidenceDart, Bool.toNat_true] at hh
    change c.successor.getD (2 * entry.2 + 1) 0 =
      2 * argumentNextIndex F entry.1.1 entry.1.2.1 + 1
    rw [← hr, ← hk]
    dsimp only [CSP.Occurrence.record]
    rw [argumentNextIndex_occurrence]
    exact hh

/-- Exact finite verification on the existing ordered incidence rotation, with no geometric
planarity or satisfiability assumption hidden in the statement. -/
theorem verifyRotationCertificate_eq_true_iff (F : CSP Rel V) (c : Graph.RotationCertificate) :
    verifyRotationCertificate F c = true ↔
      ∃ h : Graph.RotationCertificate.verifyRotation (incidenceGraph F) c = true,
        (Graph.RotationCertificate.decode (incidenceGraph F) c h).NumericalGenusZero ∧
          RespectsArgumentOrder (Graph.RotationCertificate.decode (incidenceGraph F) c h) := by
  simp only [verifyRotationCertificate, Bool.and_eq_true]
  constructor
  · rintro ⟨hg, ho⟩
    obtain ⟨h, he⟩ := (Graph.RotationCertificate.verifyGenusZero_eq_true_iff _ _).mp hg
    exact ⟨h, he, (verifyArgumentOrder_eq_true_iff h).mp ho⟩
  · rintro ⟨h, he, ho⟩
    exact ⟨(Graph.RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr ⟨h, he⟩,
      (verifyArgumentOrder_eq_true_iff h).mpr ho⟩

private theorem incidenceVertices_declared (F : CSP Rel V) :
    ∀ v ∈ (incidenceGraph F).incidenceVertices, v ∈ (incidenceGraph F).1 := by
  intro v hv
  obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact (incidenceGraph_endpoints he).1
  · have hv' := List.mem_singleton.mp hv
    subst v
    exact (incidenceGraph_endpoints he).2

/-- Every existing ordered numerical genus-zero incidence rotation has an accepted finite
certificate. Original scope positions are retained; no embedding construction is assumed. -/
theorem verifyRotationCertificate_ofRotation
    (r : Graph.RotationSystem (incidenceGraph F)) (hg : r.NumericalGenusZero)
    (ho : RespectsArgumentOrder r) :
    verifyRotationCertificate F (Graph.RotationCertificate.ofRotation r) = true := by
  apply (verifyRotationCertificate_eq_true_iff _ _).mpr
  refine ⟨Graph.RotationCertificate.verifyRotation_ofRotation r (incidenceVertices_declared F), ?_⟩
  rw [Graph.RotationCertificate.decode_ofRotation r (incidenceVertices_declared F)]
  exact ⟨hg, ho⟩

/-- Supplied-certificate completeness with a concrete quadratic bound in the native incidence
graph's encoded length. The graph itself is constructed natively from the CSP. -/
theorem exists_bounded_rotationCertificate_iff (F : CSP Rel V) :
    (∃ r : Graph.RotationSystem (incidenceGraph F),
      r.NumericalGenusZero ∧ RespectsArgumentOrder r) ↔
      ∃ c : Graph.RotationCertificate,
        (Graph.encRotationCertificate c).length ≤
          10 * ((encGraph (incidenceGraph F)).length + 1) ^ 2 ∧
          verifyRotationCertificate F c = true := by
  constructor
  · rintro ⟨r, hg, ho⟩
    exact ⟨Graph.RotationCertificate.ofRotation r,
      Graph.RotationCertificate.length_enc_ofRotation_le r,
      verifyRotationCertificate_ofRotation r hg ho⟩
  · rintro ⟨c, -, hc⟩
    obtain ⟨h, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp hc
    exact ⟨Graph.RotationCertificate.decode _ _ h, hg, ho⟩

/-- The concrete incidence-certificate bound is polynomial in the source CSP bit length for
any fixed relation and variable encodings, including binary natural variable names. -/
theorem polyBounded_rotationCertificateBound (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    PolyBounded (fun F : CSP Rel V => (encCSP encRel encV F).length)
      (fun F => 10 * ((encGraph (incidenceGraph F)).length + 1) ^ 2) :=
  (PolyBounded.const 10).mul
    (((computableInPolyTime_incidenceGraph encRel encV).polyBounded_length.add
      (PolyBounded.const 1)).pow 2)

omit [DecidableEq V] in
private theorem argumentPositions_polyTime (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (argumentPositions (Rel := Rel) (V := V)) (encCSP encRel encV)
      (encList (encPair encUnary encUnary)) := by
  unfold argumentPositions
  have ho := computableInPolyTime_occurrences encRel encV
  unfold encOccurrenceRecord at ho
  fun_prop

omit [DecidableEq V] in
private theorem scopeLength_polyTime (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel V × ℕ => scopeLength p.1 p.2)
      (encPair (encCSP encRel encV) encUnary) encUnary := by
  unfold scopeLength encCSP
  fun_prop

omit [DecidableEq V] in
private theorem argumentNextIndex_polyTime (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun p : (CSP Rel V × ℕ) × ℕ => argumentNextIndex p.1.1 p.1.2 p.2)
      (encPair (encPair (encCSP encRel encV) encUnary) encUnary) encUnary := by
  have hpos := argumentPositions_polyTime encRel encV
  have hlen := scopeLength_polyTime encRel encV
  unfold argumentNextIndex
  fun_prop

omit [DecidableEq V] in
/-- The original cyclic argument-order test is native polynomial-time. All counters come from
actual constraint, scope and occurrence lists, independently of relation arities and labels. -/
@[fun_prop] theorem computableInPolyTime_verifyArgumentOrder (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel V × Graph.RotationCertificate =>
      verifyArgumentOrder p.1 p.2) (encCSPRotationCertificate encRel encV) encBool := by
  have ho := computableInPolyTime_occurrences encRel encV
  have hn := argumentNextIndex_polyTime encRel encV
  have hs := Graph.RotationCertificate.computableInPolyTime_successor
  unfold verifyArgumentOrder
  have hz : ComputableInPolyTime (fun p : CSP Rel V × Graph.RotationCertificate =>
      p.1.occurrences.zipIdx) (encCSPRotationCertificate encRel encV)
      (encList (encPair (encOccurrenceRecord encV) encUnary)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zipIdx (encOccurrenceRecord encV)).comp
      (ho.tidy.comp (by fun_prop)))
  apply ComputableInPolyTime.allWithInput hz
  have hk : ComputableInPolyTime
      (fun p : (CSP Rel V × Graph.RotationCertificate) × ((ℕ × ℕ × V) × ℕ) => 2 * p.2.2 + 1)
      (encPair (encCSPRotationCertificate encRel encV)
        (encPair (encOccurrenceRecord encV) encUnary)) encUnary := by
    unfold encCSPRotationCertificate encOccurrenceRecord
    fun_prop
  have hnext : ComputableInPolyTime
      (fun p : (CSP Rel V × Graph.RotationCertificate) × ((ℕ × ℕ × V) × ℕ) =>
        argumentNextIndex p.1.1 p.2.1.1 p.2.1.2.1)
      (encPair (encCSPRotationCertificate encRel encV)
        (encPair (encOccurrenceRecord encV) encUnary)) encUnary :=
    hn.comp (g := fun p : (CSP Rel V × Graph.RotationCertificate) × ((ℕ × ℕ × V) × ℕ) =>
      ((p.1.1, p.2.1.1), p.2.1.2.1)) (by unfold encOccurrenceRecord; fun_prop)
  apply ComputableInPolyTime.decide_eq'
  · exact ComputableInPolyTime.listGetDWithInput (hs.comp (by fun_prop)) hk 0
  · exact .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hnext)
        (ComputableInPolyTime.const 1)).tidy)

/-- Native polynomial-time verification of the supplied incidence rotation, componentwise
numerical genus zero and the CSP's actual cyclic argument order. This supplies no solver or
recognizer on a bare instance. -/
@[fun_prop] theorem computableInPolyTime_verifyRotationCertificate (encRel : Rel ↪ List Bool)
    (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun p : CSP Rel V × Graph.RotationCertificate =>
      verifyRotationCertificate p.1 p.2) (encCSPRotationCertificate encRel encV) encBool := by
  unfold verifyRotationCertificate
  apply ComputableInPolyTime.bool_and'
  · exact Graph.RotationCertificate.computableInPolyTime_verifyGenusZero.comp
      (((computableInPolyTime_incidenceGraph encRel encV).comp (by fun_prop)).prod (by fun_prop))
  · exact computableInPolyTime_verifyArgumentOrder encRel encV

end Cslib.Complexity.CSP
