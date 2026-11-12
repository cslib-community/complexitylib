/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Star
import CslibFrontier.Foundations.Data.List.IdxOfInjective
import Mathlib.Data.List.FinRange

/-!
# Literal original-language atoms of arbitrary arity

The incidence graph of a single constraint on distinct indexed free labels is the ordered
star, with its full argument rotation. The indexing proofs below concern the actual CSP list
and positional occurrence table, including the nullary constraint center.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph.RotationSystem

variable {Rel : Type}

private abbrev finBody (r : Rel) (n : ℕ) : CSP Rel (Fin n) := [(r, List.finRange n)]

private theorem vars_finBody (r : Rel) (n : ℕ) : (finBody r n).vars = List.finRange n := by
  simp [finBody, CSP.vars]

private theorem distinctVars_finBody (r : Rel) (n : ℕ) :
    (finBody r n).distinctVars = List.finRange n := by
  change selectDistinct (finBody r n).vars
    (List.replicate (finBody r n).vars.length true) = _
  rw [vars_finBody]
  apply List.Sublist.eq_of_length
  · unfold selectDistinct
    conv_rhs => rw [← List.zipIdx_map_fst 0 (List.finRange n)]
    exact List.filter_sublist.map _
  · rw [length_selectDistinct_replicate, List.toFinset_card_of_nodup (List.nodup_finRange n)]

private theorem numVars_finBody (r : Rel) (n : ℕ) : (finBody r n).numVars = n := by
  rw [← length_distinctVars, distinctVars_finBody, List.length_finRange]

private theorem occurrences_finBody (r : Rel) (n : ℕ) :
    (finBody r n).occurrences = (List.finRange n).map (fun i => (0, i.val, i)) := by
  have h : (List.finRange n).zipIdx.map (fun x => (0, x.2, x.1)) =
      (List.finRange n).map (fun i => (0, i.val, i)) := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp
  simpa [finBody, CSP.occurrences, CSP.varCNF, Cslib.Logic.PL.occurrences,
    List.zipIdx_map, List.map_map, Function.comp_def] using h

private theorem incidenceGraph_finBody (r : Rel) (n : ℕ) :
    incidenceGraph (finBody r n) = starGraph n := by
  apply Graph.ext
  · rw [incidenceGraph_vertices, numVars_finBody]
    rfl
  · rw [incidenceGraph_edges, occurrences_finBody, distinctVars_finBody, numVars_finBody,
      List.map_map]
    simp [starGraph]

private def finOccurrence (r : Rel) (n : ℕ) (i : Fin n) : (finBody r n).Occurrence :=
  ⟨⟨0, by simp [finBody]⟩, ⟨i.val, by simp [finBody]⟩⟩

private theorem incidenceEdgeIndex_finBody (r : Rel) (n : ℕ) (o : (finBody r n).Occurrence) :
    incidenceEdgeIndex o = o.2.val := by
  have hi : o.1.val = 0 := by
    have h := o.1.isLt
    simp only [finBody, List.length_singleton] at h
    omega
  let j : Fin n := ⟨o.2.val, by simpa [finBody, hi] using o.2.isLt⟩
  have hr : o.record = (0, j.val, j) := by
    simp [CSP.Occurrence.record, CSP.Occurrence.var, finBody, j]
  rw [incidenceEdgeIndex, occurrences_finBody, hr]
  have he := List.idxOf_map_injOn (List.finRange n) (fun i => (0, i.val, i))
    (fun _ _ _ _ h => congrArg (fun o => o.2.2) h) (List.mem_finRange j)
  rw [he, List.idxOf_finRange]

private theorem argumentNextIndex_finBody (r : Rel) (n : ℕ) (i : Fin n) :
    argumentNextIndex (finBody r n) 0 i.val = (finRotate n i).val := by
  have h := argumentNextIndex_occurrence (finOccurrence r n i)
  rw [incidenceEdgeIndex_finBody] at h
  simpa [finOccurrence, argumentSuccessor, finBody, Fin.add_def] using h

/-- Finite table for the actual atom's body, supplied by the unbounded ordered-star rotation. -/
@[expose] def atomBodyCertificate (n : ℕ) : Graph.RotationCertificate :=
  Graph.RotationCertificate.ofRotation (starRotation n)

private theorem getD_atomBodyCertificate (n : ℕ) (i : Fin n) :
    (atomBodyCertificate n).successor.getD (2 * i.val + 1) 0 =
      2 * (finRotate n i).val + 1 := by
  have h := Graph.RotationCertificate.getD_ofRotation (starRotation n) (starDartEquiv n (i, true))
  have hr : (starRotation n).rotate (starDartEquiv n (i, true)) =
      starDartEquiv n (finRotate n i, true) := by simp [starRotation, starRotor]
  rw [hr] at h
  simpa [atomBodyCertificate, Graph.Dart.index, starDartEquiv] using h

private theorem verifyArgumentOrder_finBody (r : Rel) (n : ℕ) :
    verifyArgumentOrder (finBody r n) (atomBodyCertificate n) = true := by
  simp only [verifyArgumentOrder, occurrences_finBody, List.zipIdx_map, List.all_map]
  apply List.all_eq_true.mpr
  rintro ⟨i, k⟩ hik
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hik)
  have hki : k = i.val := by simpa using congrArg Fin.val he
  change decide ((atomBodyCertificate n).successor.getD (2 * k + 1) 0 =
    2 * argumentNextIndex (finBody r n) 0 i.val + 1) = true
  rw [hki, argumentNextIndex_finBody, getD_atomBodyCertificate]
  simp

/-- The actual original-language PP atom has precisely the unbounded ordered-star graph. -/
theorem incidenceGraph_atom (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (r : Rel) :
    incidenceGraph (PPGadget.atom (arity := arity) (sem := sem) r).body = starGraph (arity r) := by
  change incidenceGraph ([(r, List.ofFn Sum.inl)] : CSP Rel (Fin (arity r) ⊕ Fin 0)) = _
  have he : ([(r, List.ofFn Sum.inl)] : CSP Rel (Fin (arity r) ⊕ Fin 0)) =
      (finBody r (arity r)).relabel (Sum.inl : Fin (arity r) → Fin (arity r) ⊕ Fin 0) := by
    simp [finBody, CSP.relabel, Constraint.relabel, List.ofFn_eq_map]
  rw [he]
  exact (incidenceGraph_relabel_of_injOn (finBody r (arity r))
    (Sum.inl : Fin (arity r) → Fin (arity r) ⊕ Fin 0)
    (fun _ _ _ _ h => Sum.inl.inj h)).trans (incidenceGraph_finBody r (arity r))

private theorem verifyRotationCertificate_finBody (r : Rel) (n : ℕ) :
    verifyRotationCertificate (finBody r n) (atomBodyCertificate n) = true := by
  rw [verifyRotationCertificate, incidenceGraph_finBody, Bool.and_eq_true]
  refine ⟨?_, verifyArgumentOrder_finBody r n⟩
  unfold atomBodyCertificate
  apply (Graph.RotationCertificate.verifyGenusZero_eq_true_iff _ _).mpr
  refine ⟨Graph.RotationCertificate.verifyRotation_ofRotation (starRotation n)
    (starGraph_endpoints_declared n), ?_⟩
  rw [Graph.RotationCertificate.decode_ofRotation (starRotation n)
    (starGraph_endpoints_declared n)]
  exact numericalGenusZero_starRotation _

/-- A single original constraint on distinct scope names has this supplied ordered numerical
table. The relation label and truth value play no role in the graph check. -/
theorem singleScopeCertificate_accepted {V : Type} [DecidableEq V]
    (r : Rel) (scope : List V) (hn : scope.Nodup) :
    verifyRotationCertificate [(r, scope)] (atomBodyCertificate scope.length) = true := by
  have he : (finBody r scope.length).relabel scope.get = [(r, scope)] := by
    simp [finBody, CSP.relabel, Constraint.relabel, List.map_get_finRange]
  rw [← he]
  have hf : Set.InjOn scope.get {i | i ∈ (finBody r scope.length).vars} :=
    fun _ _ _ _ h => Fin.ext (hn.getElem_inj.mp h)
  exact (verifyRotationCertificate_relabel_of_injOn (finBody r scope.length) scope.get hf
    (atomBodyCertificate scope.length)).trans (verifyRotationCertificate_finBody r scope.length)

/-- The supplied table passes the actual atom's ordered numerical checker at every arity,
including zero and one. No planarity or rotation provider is a premise. -/
theorem atomBodyCertificate_accepted (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (r : Rel) : verifyRotationCertificate (PPGadget.atom (arity := arity) (sem := sem) r).body
      (atomBodyCertificate (arity r)) = true := by
  change verifyRotationCertificate ([(r, List.ofFn Sum.inl)] : CSP Rel (Fin (arity r) ⊕ Fin 0))
    (atomBodyCertificate (arity r)) = true
  rw [List.ofFn_eq_map]
  change verifyRotationCertificate ((finBody r (arity r)).relabel
    (Sum.inl : Fin (arity r) → Fin (arity r) ⊕ Fin 0)) (atomBodyCertificate (arity r)) = true
  rw [verifyRotationCertificate_relabel_of_injOn _ _ (fun _ _ _ _ h => Sum.inl.inj h)]
  exact verifyRotationCertificate_finBody r (arity r)

/-- Every literal original-language atom internally supplies an ordered numerical realization
of its actual body. An outer free-port boundary additionally needs its probe rotation. -/
theorem atomBody_realization (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) (r : Rel) :
    ∃ rot : Graph.RotationSystem
      (incidenceGraph (PPGadget.atom (arity := arity) (sem := sem) r).body),
      rot.NumericalGenusZero ∧ RespectsArgumentOrder rot := by
  obtain ⟨h, hg, ho⟩ := (verifyRotationCertificate_eq_true_iff _ _).mp
    (atomBodyCertificate_accepted arity sem r)
  exact ⟨Graph.RotationCertificate.decode _ _ h, hg, ho⟩

/-- An empty body with distinct boundary labels has a fully supplied ordered boundary of
any arity. All its ports are unused; the structural probe supplies their actual corners. -/
def Witness.empty {V : Type} [DecidableEq V] (ports : List V) (hn : ports.Nodup) :
    Witness ([] : CSP Rel V) ports where
  certificate := atomBodyCertificate ports.length
  accepted := by
    apply (verify_eq_true_iff _ _ _).mpr
    constructor
    · change verifyRotationCertificate ([] : CSP Rel V) ⟨[]⟩ = true
      rfl
    · change verifyRotationCertificate ([(none, ports.reverse)] : CSP (Option Rel) V)
        (atomBodyCertificate ports.length) = true
      simpa only [List.length_reverse] using
        singleScopeCertificate_accepted (none : Option Rel) ports.reverse
          (List.nodup_reverse.mpr hn)

end Cslib.Complexity.CSP.OrderedBoundary
