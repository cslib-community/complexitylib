/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Atom
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.DoubleStar
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Restriction
import CslibFrontier.Foundations.Data.List.IdxOfInjective
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-!
# The full ordered free-port boundary of an arbitrary-arity atom

The structural probe has the literal reversed free scope. Its actual incidence graph is
the two-center ordered star, including two isolated centers in the nullary case. The
supplied table and its executable body restriction use no rotation search.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph.RotationSystem

variable {Rel : Type}

private abbrev finBoundary (r : Rel) (n : ℕ) : CSP (Option Rel) (Fin n) :=
  probeBody [(r, List.finRange n)] (List.finRange n)

private theorem vars_finBoundary (r : Rel) (n : ℕ) :
    (finBoundary r n).vars = List.finRange n ++ (List.finRange n).reverse := by
  simp [finBoundary, probeBody, CSP.vars]

private theorem distinctVars_finBoundary (r : Rel) (n : ℕ) :
    (finBoundary r n).distinctVars = List.finRange n := by
  let l := List.finRange n
  have hi (i : Fin n) : (l ++ l.reverse).idxOf i = i.val := by
    rw [List.idxOf_append_of_mem (List.mem_finRange i), List.idxOf_finRange]
  change selectDistinct (finBoundary r n).vars
    (List.replicate (finBoundary r n).vars.length true) = _
  rw [vars_finBoundary]
  change selectDistinct (l ++ l.reverse) (List.replicate (l ++ l.reverse).length true) = l
  unfold selectDistinct
  rw [List.zipIdx_append, Nat.zero_add, List.filter_append, List.map_append]
  have hfirst : (l.zipIdx.filter fun e =>
      (List.replicate (l ++ l.reverse).length true).getD e.2 false &&
        decide ((l ++ l.reverse).idxOf e.1 = e.2)) = l.zipIdx := by
    apply List.filter_eq_self.mpr
    rintro ⟨i, k⟩ hik
    obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hik)
    have hki : k = i.val := by simpa [l] using congrArg Fin.val he
    have hlt : k < (l ++ l.reverse).length := by simp [l] at hk ⊢; omega
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using hlt)]
    simp [hi, hki]
  have hlast : (l.reverse.zipIdx l.length |>.filter fun e =>
      (List.replicate (l ++ l.reverse).length true).getD e.2 false &&
        decide ((l ++ l.reverse).idxOf e.1 = e.2)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    rintro ⟨i, k⟩ hik
    have hk := List.le_snd_of_mem_zipIdx hik
    have hn : (l ++ l.reverse).idxOf i ≠ k := by rw [hi]; simp [l] at hk; omega
    simp [hn]
  rw [hfirst, hlast, List.map_nil, List.append_nil, List.zipIdx_map_fst]

private theorem numVars_finBoundary (r : Rel) (n : ℕ) : (finBoundary r n).numVars = n := by
  rw [← length_distinctVars, distinctVars_finBoundary, List.length_finRange]

private theorem occurrences_finBoundary (r : Rel) (n : ℕ) :
    (finBoundary r n).occurrences =
      (List.finRange n).map (fun i => (0, i.val, i)) ++
        (List.finRange n).map (fun i => (1, i.val, i.rev)) := by
  have ha : (List.finRange n).zipIdx.map (fun x => (0, x.2, x.1)) =
      (List.finRange n).map (fun i => (0, i.val, i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  have hb : (List.finRange n).reverse.zipIdx.map (fun x => (1, x.2, x.1)) =
      (List.finRange n).map (fun i => (1, i.val, i.rev)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp [Fin.rev, Nat.sub_sub, Nat.add_comm]
  simpa [finBoundary, probeBody, CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences,
    ← List.map_reverse, List.zipIdx_map, List.map_map, Function.comp_def] using
    congrArg₂ (· ++ ·) ha hb

private theorem incidenceGraph_finBoundary (r : Rel) (n : ℕ) :
    incidenceGraph (finBoundary r n) = doubleStarGraph n := by
  apply Prod.ext
  · rw [incidenceGraph_vertices, numVars_finBoundary]
    rfl
  · rw [incidenceGraph_edges, occurrences_finBoundary, distinctVars_finBoundary,
      numVars_finBoundary, List.map_append, List.map_map, List.map_map]
    simp [doubleStarGraph, Function.comp_def]

/-- Supplied atom/probe table for every arity. The proof below checks its actual body and
reversed-probe incidence interpretations, rather than searching for an embedding. -/
@[expose] def atomBoundaryCertificate (n : ℕ) : Graph.RotationCertificate :=
  Graph.RotationCertificate.ofRotation (doubleStarRotation n)

/-- Both stars contribute one edge per free-port position. -/
theorem length_atomBoundaryCertificate (n : ℕ) :
    (atomBoundaryCertificate n).successor.length = 4 * n := by
  rw [atomBoundaryCertificate, Graph.RotationCertificate.length_ofRotation]
  simp [doubleStarGraph]
  omega

private theorem getD_atomBoundary_body_even {n : ℕ} (i : Fin n) :
    (atomBoundaryCertificate n).successor.getD (2 * i.val) 0 = 2 * (n + i.rev.val) := by
  have h := Graph.RotationCertificate.getD_ofRotation (doubleStarRotation n)
    (doubleStarDartEquiv n ((i, false), false))
  simpa [atomBoundaryCertificate, Graph.Dart.index, doubleStarRotation, doubleStarRotor,
    doubleStarDartEquiv, val_doubleStarEdgeEquiv] using h

private theorem getD_atomBoundary_probe_even {n : ℕ} (i : Fin n) :
    (atomBoundaryCertificate n).successor.getD (2 * (n + i.rev.val)) 0 = 2 * i.val := by
  have h := Graph.RotationCertificate.getD_ofRotation (doubleStarRotation n)
    (doubleStarDartEquiv n ((i, true), false))
  simpa [atomBoundaryCertificate, Graph.Dart.index, doubleStarRotation, doubleStarRotor,
    doubleStarDartEquiv, val_doubleStarEdgeEquiv] using h

private theorem getD_atomBoundary_odd {n : ℕ} (b : Bool) (i : Fin n) :
    (atomBoundaryCertificate n).successor.getD (2 * ((if b then n else 0) + i.val) + 1) 0 =
      2 * ((if b then n else 0) + (finRotate n i).val) + 1 := by
  have hi : ((finRotate n).symm i.rev).rev = finRotate n i := by
    apply Fin.ext
    simp only [Fin.val_rev, val_finRotate_symm, val_finRotate]
    have hlt := i.isLt
    split_ifs <;> omega
  cases b
  · have h := Graph.RotationCertificate.getD_ofRotation (doubleStarRotation n)
      (doubleStarDartEquiv n ((i, false), true))
    simpa [atomBoundaryCertificate, Graph.Dart.index, doubleStarRotation, doubleStarRotor,
      doubleStarDartEquiv, val_doubleStarEdgeEquiv] using h
  · have h := Graph.RotationCertificate.getD_ofRotation (doubleStarRotation n)
      (doubleStarDartEquiv n ((i.rev, true), true))
    have hr : (doubleStarRotation n).rotate (doubleStarDartEquiv n ((i.rev, true), true)) =
        doubleStarDartEquiv n ((((finRotate n).symm i.rev), true), true) := by
      simp only [doubleStarRotation, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      rfl
    rw [hr] at h
    change (atomBoundaryCertificate n).successor.getD
      (2 * (doubleStarEdgeEquiv n (i.rev, true)).val + 1) 0 =
        2 * (doubleStarEdgeEquiv n (((finRotate n).symm i.rev), true)).val + 1 at h
    rw [val_doubleStarEdgeEquiv, val_doubleStarEdgeEquiv, Fin.rev_rev, hi] at h
    simpa only [ite_true] using h

private def finBoundaryOccurrence (r : Rel) (n : ℕ) (b : Bool) (i : Fin n) :
    (finBoundary r n).Occurrence :=
  ⟨⟨if b then 1 else 0, by cases b <;> simp [finBoundary, probeBody]⟩,
    ⟨i.val, by cases b <;> simp [finBoundary, probeBody]⟩⟩

private theorem record_finBoundaryOccurrence (r : Rel) (n : ℕ) (b : Bool) (i : Fin n) :
    (finBoundaryOccurrence r n b i).record =
      (if b then 1 else 0, i.val, if b then i.rev else i) := by
  cases b <;> simp [finBoundaryOccurrence, CSP.Occurrence.record, CSP.Occurrence.var,
    finBoundary, probeBody, Fin.rev, Nat.sub_sub, Nat.add_comm]

private theorem incidenceEdgeIndex_finBoundaryOccurrence (r : Rel) (n : ℕ)
    (b : Bool) (i : Fin n) :
    incidenceEdgeIndex (finBoundaryOccurrence r n b i) = (if b then n else 0) + i.val := by
  rw [incidenceEdgeIndex, record_finBoundaryOccurrence, occurrences_finBoundary]
  have ha : ((List.finRange n).map (fun i => (0, i.val, i))).idxOf (0, i.val, i) = i.val := by
    rw [List.idxOf_map_injOn (List.finRange n) (fun i => (0, i.val, i))
      (fun _ _ _ _ h => Fin.ext (congrArg (fun o => o.2.1) h)) (List.mem_finRange i),
      List.idxOf_finRange]
  have hb : ((List.finRange n).map (fun i => (1, i.val, i.rev))).idxOf (1, i.val, i.rev) =
      i.val := by
    rw [List.idxOf_map_injOn (List.finRange n) (fun i => (1, i.val, i.rev))
      (fun _ _ _ _ h => Fin.ext (congrArg (fun o => o.2.1) h)) (List.mem_finRange i),
      List.idxOf_finRange]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hm : (0, i.val, i) ∈ (List.finRange n).map
        (fun j : Fin n => ((0 : ℕ), j.val, j)) :=
      List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    rw [List.idxOf_append_of_mem hm, ha, Nat.zero_add]
  · simp only [↓reduceIte]
    rw [List.idxOf_append_of_notMem (by
      simp only [List.mem_map, not_exists, not_and]
      intro j _ he
      exact Nat.zero_ne_one (congrArg Prod.fst he)), hb]
    simp

private theorem argumentSuccessor_finBoundaryOccurrence (r : Rel) (n : ℕ)
    (b : Bool) (i : Fin n) :
    argumentSuccessor (finBoundaryOccurrence r n b i) =
      finBoundaryOccurrence r n b (finRotate n i) := by
  have hlen : (finBoundary r n)[(finBoundaryOccurrence r n b i).1.val].2.length = n := by
    cases b <;> simp [finBoundaryOccurrence, finBoundary, probeBody]
  refine Sigma.ext (x := argumentSuccessor (finBoundaryOccurrence r n b i))
    (y := finBoundaryOccurrence r n b (finRotate n i)) rfl ?_
  apply heq_of_eq
  apply Fin.ext
  change (finRotate _ (finBoundaryOccurrence r n b i).2).val = (finRotate n i).val
  rw [val_finRotate, val_finRotate]
  change (if i.val + 1 = (finBoundary r n)[(finBoundaryOccurrence r n b i).1.val].2.length
    then 0 else i.val + 1) = _
  rw [hlen]

private theorem argumentNextIndex_finBoundary (r : Rel) (n : ℕ) (b : Bool) (i : Fin n) :
    argumentNextIndex (finBoundary r n) (if b then 1 else 0) i.val =
      (if b then n else 0) + (finRotate n i).val := by
  have h := argumentNextIndex_occurrence (finBoundaryOccurrence r n b i)
  rw [argumentSuccessor_finBoundaryOccurrence, incidenceEdgeIndex_finBoundaryOccurrence] at h
  exact h

private theorem verifyArgumentOrder_finBoundary (r : Rel) (n : ℕ) :
    verifyArgumentOrder (finBoundary r n) (atomBoundaryCertificate n) = true := by
  simp only [verifyArgumentOrder, occurrences_finBoundary, List.zipIdx_append,
    List.zipIdx_map, List.length_map, List.length_finRange, Nat.zero_add,
    List.all_append, List.all_map, Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    rw [List.forall_mem_zipIdx]
    intro j hj
    let i : Fin n := ⟨j, by simpa only [List.length_finRange] using hj⟩
    rw [List.getElem_finRange, Nat.zero_add]
    change decide ((atomBoundaryCertificate n).successor.getD (2 * j + 1) 0 =
      2 * argumentNextIndex (finBoundary r n) 0 j + 1) = true
    rw [decide_eq_true_eq]
    have ha := argumentNextIndex_finBoundary r n false i
    have ht := getD_atomBoundary_odd false i
    simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at ha ht
    rw [ha]
    exact ht
  · apply List.all_eq_true.mpr
    rw [List.forall_mem_zipIdx]
    intro j hj
    let i : Fin n := ⟨j, by simpa only [List.length_finRange] using hj⟩
    rw [List.getElem_finRange]
    change decide ((atomBoundaryCertificate n).successor.getD (2 * (n + j) + 1) 0 =
      2 * argumentNextIndex (finBoundary r n) 1 j + 1) = true
    rw [decide_eq_true_eq]
    have ha := argumentNextIndex_finBoundary r n true i
    have ht := getD_atomBoundary_odd true i
    simp only [ite_true] at ha ht
    rw [ha]
    exact ht

private theorem verifyRotationCertificate_finBoundary (r : Rel) (n : ℕ) :
    verifyRotationCertificate (finBoundary r n) (atomBoundaryCertificate n) = true := by
  rw [verifyRotationCertificate, incidenceGraph_finBoundary, Bool.and_eq_true]
  refine ⟨?_, verifyArgumentOrder_finBoundary r n⟩
  unfold atomBoundaryCertificate
  apply (Graph.RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨Graph.RotationCertificate.verifyRotation_ofRotation (doubleStarRotation n)
    (doubleStarGraph_endpoints_declared n), ?_⟩
  rw [Graph.RotationCertificate.decode_ofRotation (doubleStarRotation n)
    (doubleStarGraph_endpoints_declared n)]
  exact numericalGenusZero_doubleStarRotation _

/-- The list-funded deletion of the actual probe darts gives exactly the ordered-star body
table. Variable corners take two steps; constraint corners take one. -/
theorem restrictPrefix_atomBoundaryCertificate (n : ℕ) :
    restrictPrefix (2 * n) (atomBoundaryCertificate n) = atomBodyCertificate n := by
  suffices hs : (restrictPrefix (2 * n) (atomBoundaryCertificate n)).successor =
      (atomBodyCertificate n).successor by
    exact congrArg Graph.RotationCertificate.mk hs
  apply List.ext_getElem
  · rw [length_restrictPrefix, atomBodyCertificate, Graph.RotationCertificate.length_ofRotation]
    simp [starGraph]
  · intro k hk hl
    have hlt : k < 2 * (starGraph n).2.length := by
      simpa only [length_restrictPrefix, starGraph, List.length_map, List.length_finRange] using hk
    let d := (Graph.Dart.indexEquiv (starGraph n)).symm ⟨k, hlt⟩
    obtain ⟨⟨i, b⟩, hd⟩ := (starDartEquiv n).surjective d
    have hindex : d.index = k := by
      change ((Graph.Dart.indexEquiv (starGraph n))
        ((Graph.Dart.indexEquiv (starGraph n)).symm ⟨k, hlt⟩)).val = k
      rw [Equiv.apply_symm_apply]
    have hi : 2 * i.val + b.toNat = k := by
      have hh := congrArg (fun d : Graph.Dart (starGraph n) => d.index) hd
      change 2 * i.val + b.toNat = d.index at hh
      exact hh.trans hindex
    rw [← List.getD_eq_getElem _ 0 hk, ← List.getD_eq_getElem _ 0 hl, ← hi]
    have hread := Graph.RotationCertificate.getD_ofRotation (starRotation n)
      (starDartEquiv n (i, b))
    have hii := i.isLt
    cases b
    · simp only [Bool.toNat_false, Nat.add_zero]
      rw [getD_restrictPrefix_two _ _ _ (by omega) (by
        rw [length_atomBoundaryCertificate]
        have h := i.isLt
        omega) (by rw [getD_atomBoundary_body_even]; omega)
        (by rw [getD_atomBoundary_body_even, getD_atomBoundary_probe_even]; omega),
        getD_atomBoundary_body_even, getD_atomBoundary_probe_even]
      simpa [atomBodyCertificate, Graph.Dart.index, starRotation, starRotor, starDartEquiv] using
        hread.symm
    · simp only [Bool.toNat_true]
      have ht := getD_atomBoundary_odd false i
      simp only [Bool.false_eq_true, ite_false, Nat.zero_add] at ht
      rw [getD_restrictPrefix_one _ _ _ (by omega) (by
        rw [length_atomBoundaryCertificate]
        have h := i.isLt
        omega) (by rw [ht]; have h := (finRotate n i).isLt; omega), ht]
      simpa [atomBodyCertificate, Graph.Dart.index, starRotation, starRotor, starDartEquiv] using
        hread.symm

private def finAtomWitness (r : Rel) (n : ℕ) :
    Witness [(r, List.finRange n)] (List.finRange n) where
  certificate := atomBoundaryCertificate n
  accepted := by
    apply (verify_eq_true_iff _ _ _).mpr
    constructor
    · have hlen : (CSP.occurrences ([(r, List.finRange n)] : CSP Rel (Fin n))).length = n := by
        rw [CSP.length_occurrences]
        simp
      rw [bodyCertificate, hlen, restrictPrefix_atomBoundaryCertificate]
      simpa only [List.length_finRange] using
        singleScopeCertificate_accepted r (List.finRange n) (List.nodup_finRange n)
    · exact verifyRotationCertificate_finBoundary r n

private theorem finAtomWitness_certificate (r : Rel) (n : ℕ) :
    (finAtomWitness r n).certificate = atomBoundaryCertificate n := rfl

/-- Every literal original-language atom internally supplies the full ordered free-port
boundary, at arbitrary arity. The actual PP body, original relation symbol and argument order
are retained. At arity zero both nullary centers use the separate point convention. -/
@[expose] def Witness.atom (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (r : Rel) :
    GadgetWitness (PPGadget.atom (arity := arity) (sem := sem) r) where
  certificate := atomBoundaryCertificate (arity r)
  accepted := by
    let w := (finAtomWitness r (arity r)).relabel
      (Sum.inl : Fin (arity r) → Fin (arity r) ⊕ Fin 0) (fun _ _ _ _ h => Sum.inl.inj h)
    have h := w.accepted
    have hc := (finAtomWitness r (arity r)).relabel_certificate
      (Sum.inl : Fin (arity r) → Fin (arity r) ⊕ Fin 0) (fun _ _ _ _ h => Sum.inl.inj h)
    rw [finAtomWitness_certificate] at hc
    change w.certificate = atomBoundaryCertificate (arity r) at hc
    rw [hc] at h
    change verify ([(r, List.ofFn Sum.inl)] : CSP Rel (Fin (arity r) ⊕ Fin 0))
      (List.ofFn Sum.inl) (atomBoundaryCertificate (arity r)) = true
    simpa only [CSP.relabel, Constraint.relabel, List.map_cons, List.map_nil,
      List.ofFn_eq_map] using h

/-- The explicit arbitrary-arity atom/probe table passes both actual checks. There is no
template-planarity, normalization, pp-definability or rotation-provider premise. -/
theorem atomBoundaryCertificate_accepted (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) : verify (PPGadget.atom (arity := arity) (sem := sem) r).body
      (List.ofFn Sum.inl) (atomBoundaryCertificate (arity r)) = true :=
  (Witness.atom arity sem r).accepted

end Cslib.Complexity.CSP.OrderedBoundary
