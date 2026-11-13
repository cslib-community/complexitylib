/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyParity
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Parity
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Restrict target edge bits to their actual gadget copies

Local labels read the exact target occurrence-prefix offset. Constraint parity and private
auxiliary parity follow internally from target vertex evenness and the proved occurrence fibers.
The labels are mathematical proof data; the executed replacement body and table do not change.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Restrict target edge bits to one actual local gadget copy at its literal prefix offset. -/
@[expose] def copiedEdgeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) : Fin (incidenceGraph (gadgets F[i.val].rel).body).edges.length → Bool :=
  fun j => (List.ofFn x).getD
    (occurrencePrefix (fun r => (gadgets r).template) F i.val + j.val) false

/-- At an original local occurrence, restriction reads exactly its copied target edge bit. -/
theorem copiedEdgeLabels_incidenceDart
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (o : (gadgets F[i.val].rel).body.Occurrence) (side : Bool) :
    copiedEdgeLabels gadgets B F i x (incidenceDart o side).1 =
      x (incidenceDart (replacementOccurrence gadgets B F i o) side).1 := by
  unfold copiedEdgeLabels
  change (List.ofFn x).getD
    (occurrencePrefix (fun r => (gadgets r).template) F i.val + incidenceEdgeIndex o) false = _
  rw [← incidenceEdgeIndex_replacementOccurrence]
  exact List.getD_ofFn x (incidenceDart (replacementOccurrence gadgets B F i o) side).1 false

/-- Every actual local constraint has zero parity in the restricted edge labeling. -/
theorem vertexParity_copiedEdgeLabels_constraint
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (incidenceGraph (gadgets F[i.val].rel).body).vertexParity
      (copiedEdgeLabels gadgets B F i x) (incidenceDart o true).vertex = false := by
  rw [vertexParity_incidenceDart]
  have h := sum_copied_constraint_eq_false gadgets B F i o x hx
  simpa only [ite_true, copiedEdgeLabels_incidenceDart] using h

end Cslib.Complexity.CSP.GadgetRotation
