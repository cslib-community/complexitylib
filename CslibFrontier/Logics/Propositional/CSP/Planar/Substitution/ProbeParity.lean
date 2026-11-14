/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.SourceParity
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeParity
import CslibFrontier.Foundations.Data.List.Lookup
import Mathlib.Data.List.OfFn

/-!
# Internally determined edge labels on each copied gadget probe

Body labels read the literal replacement-copy positions. Marker labels are the actual copied
free-block sums. Each marker variable is even by its exact first-return tail, including an
unused free port. These labels are proof-side data and do not change the executed table.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- The actual local probe extension with internally computed marker bits. -/
@[expose] def copiedProbeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) :
    Fin (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))).edges.length →
      Bool :=
  probeEdgeLabels _ _
    (fun a => copiedFreeLabels gadgets witnesses B F i x
      ⟨a.val, by simpa only [List.length_ofFn] using a.isLt⟩)
    (copiedEdgeLabels gadgets B F i x)

/-- The copied body restriction and the original shifted block give exactly the same free
marker bit. Every read is justified by an actual local occurrence in that block. -/
theorem sum_freeBoundaryBlock_copiedEdgeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (a : Fin (srcArity F[i.val].rel)) :
    (((freeBoundaryBlocks (gadgets F[i.val].rel) (witnesses F[i.val].rel)).getD a.val []).map
      fun j => (List.ofFn (copiedEdgeLabels gadgets B F i x)).getD j false).sum =
        copiedFreeLabels gadgets witnesses B F i x a := by
  unfold copiedFreeLabels
  congr 1
  apply List.map_congr_left
  intro j hj
  obtain ⟨p, hp, _⟩ := (mem_freeBoundaryBlock_iff _ _ a j).mp hj
  rw [← hp]
  exact List.getD_ofFn (copiedEdgeLabels gadgets B F i x) (incidenceDart p false).1 false

/-- The extended labels at an actual marker are its internally computed free-block bit. -/
theorem copiedProbeLabels_marker
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (a : Fin (srcArity F[i.val].rel)) (side : Bool) :
    copiedProbeLabels gadgets witnesses B F i x
      (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) side).1 =
        copiedFreeLabels gadgets witnesses B F i x a := by
  unfold copiedProbeLabels gadgetProbeOccurrence
  rw [probeEdgeLabels_probeOccurrence]

/-- Copied probe body edges retain exactly the target label at their actual copied occurrence. -/
theorem copiedProbeLabels_bodyOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (o : (gadgets F[i.val].rel).body.Occurrence) (side : Bool) :
    copiedProbeLabels gadgets witnesses B F i x
      (incidenceDart (bodyOccurrence (gadgets F[i.val].rel).body (List.ofFn Sum.inl) o) side).1 =
        x (incidenceDart (replacementOccurrence gadgets B F i o) side).1 := by
  unfold copiedProbeLabels
  rw [probeEdgeLabels_bodyOccurrence, copiedEdgeLabels_incidenceDart]

/-- Every canonical marker variable has zero parity in the actual extension. The proof
does not assume target vertex evenness: the marker bit is defined as its exact body-block sum. -/
theorem vertexParity_copiedProbeLabels_marker_variable
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (a : Fin (srcArity F[i.val].rel)) :
    (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))).vertexParity
      (copiedProbeLabels gadgets witnesses B F i x)
      (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) false).vertex = false := by
  unfold copiedProbeLabels gadgetProbeOccurrence
  rw [vertexParity_probeEdgeLabels_marker_variable _ _ (List.nodup_ofFn.mpr Sum.inl_injective)
    (witnesses F[i.val].rel)]
  have he := getD_freeBoundaryBlocks (gadgets F[i.val].rel) (witnesses F[i.val].rel) a
  unfold gadgetProbeOccurrence at he
  rw [← he]
  rw [sum_freeBoundaryBlock_copiedEdgeLabels]
  simpa only [Bool.zero_eq_false] using BooleanRing.add_self
    (copiedFreeLabels gadgets witnesses B F i x a)

/-- The actual probe center has even parity by the internally proved complete marker tuple. -/
theorem vertexParity_copiedProbeLabels_marker_constraint
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (a : Fin (srcArity F[i.val].rel)) :
    (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))).vertexParity
      (copiedProbeLabels gadgets witnesses B F i x)
      (incidenceDart (gadgetProbeOccurrence (gadgets F[i.val].rel) a) true).vertex = false := by
  unfold copiedProbeLabels gadgetProbeOccurrence
  rw [vertexParity_probeEdgeLabels_probe_constraint]
  apply Eq.trans ?_ (sum_copiedFreeLabels_eq_false gadgets witnesses B hB F i x hx)
  apply congrArg List.sum
  have hlen : (List.ofFn (Sum.inl : Fin (srcArity F[i.val].rel) →
      Fin (srcArity F[i.val].rel) ⊕ Fin (gadgets F[i.val].rel).numAux)).length =
      srcArity F[i.val].rel := List.length_ofFn
  rw [List.ofFn_congr hlen]
  congr 1

/-- Every target vertex-even labeling internally extends to a vertex-even labeling on each
actual gadget probe. Free/auxiliary/constraint fibers and the complete marker tuple are proved
above; no local parity, source validity, rotation or genus provider is supplied. -/
theorem vertexEven_copiedProbeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x) :
    (incidenceGraph (probeBody (gadgets F[i.val].rel).body (List.ofFn Sum.inl))).VertexEven
      (copiedProbeLabels gadgets witnesses B F i x) := by
  let g := gadgets F[i.val].rel
  let ports := List.ofFn (Sum.inl : Fin (srcArity F[i.val].rel) →
    Fin (srcArity F[i.val].rel) ⊕ Fin g.numAux)
  let t : Fin ports.length → Bool := fun a => copiedFreeLabels gadgets witnesses B F i x
    ⟨a.val, by simpa only [ports, List.length_ofFn] using a.isLt⟩
  have hlabels : copiedProbeLabels gadgets witnesses B F i x =
      probeEdgeLabels g.body ports t (copiedEdgeLabels gadgets B F i x) := rfl
  rw [Graph.vertexEven_iff_dart]
  intro d
  obtain ⟨p, hp⟩ := exists_incidenceDart d
  have h (side : Bool) :
      (incidenceGraph (probeBody g.body ports)).vertexParity
        (copiedProbeLabels gadgets witnesses B F i x)
        (incidenceDart p side).vertex = false := by
    rcases exists_bodyOccurrence_or_probeOccurrence g.body ports p with ⟨o, rfl⟩ | ⟨j, rfl⟩
    · cases side
      · cases ho : o.var with
        | inl a =>
          have hv : (incidenceDart (bodyOccurrence g.body ports o) false).vertex =
              (incidenceDart (gadgetProbeOccurrence g a) false).vertex :=
            (vertex_incidenceDart_eq_iff _ _ false false).mpr
              ⟨rfl, (var_bodyOccurrence g.body ports o).trans
                (ho.trans (var_gadgetProbeOccurrence g a).symm)⟩
          rw [hv]
          exact vertexParity_copiedProbeLabels_marker_variable gadgets witnesses B F i x a
        | inr a =>
          rw [hlabels, vertexParity_probeEdgeLabels_variable_of_not_mem g.body ports t _ o
            (by simp [ports, ho])]
          exact vertexParity_copiedEdgeLabels_auxiliary gadgets witnesses B hB F i a x hx o ho
      · rw [hlabels, vertexParity_probeEdgeLabels_body_constraint]
        exact vertexParity_copiedEdgeLabels_constraint gadgets B F i x hx o
    · let a : Fin (srcArity F[i.val].rel) := ⟨j.val, by
        simpa only [ports, List.length_ofFn] using j.isLt⟩
      have he : probeOccurrence g.body ports j = gadgetProbeOccurrence g a := by
        unfold gadgetProbeOccurrence
        congr 1
      rw [he]
      cases side
      · exact vertexParity_copiedProbeLabels_marker_variable gadgets witnesses B F i x a
      · exact vertexParity_copiedProbeLabels_marker_constraint gadgets witnesses B hB F i x hx a
  simpa only [hp] using h d.2

end Cslib.Complexity.CSP.GadgetRotation
