/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyEdgeLabels
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Internal auxiliary parity in a copied gadget

The local edge-label restriction inherits even parity at every auxiliary body vertex from
its complete private target occurrence fiber. Unused auxiliary labels contribute empty sums.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Actual local auxiliary vertices have zero parity. The uniform bound is used only to
separate private target names, with no assumption on free-port occurrence or connectivity. -/
theorem vertexParity_copiedEdgeLabels_auxiliary
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (i : Fin F.length)
    (a : Fin (gadgets F[i.val].1).numAux)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (o : (gadgets F[i.val].1).body.Occurrence) (ho : o.var = Sum.inr a) :
    (incidenceGraph (gadgets F[i.val].1).body).vertexParity
      (copiedEdgeLabels gadgets B F i x) (incidenceDart o false).vertex = false := by
  let word := (auxiliaryBoundaryBlocks (gadgets F[i.val].1) (witnesses F[i.val].1)).getD a.val []
  have hn : word.Nodup := nodup_auxiliaryBoundaryBlock _ _ a
  have hw (j : ℕ) : j ∈ word ↔ ∃ p : (gadgets F[i.val].1).body.Occurrence,
      incidenceEdgeIndex p = j ∧ p.var = o.var := by
    rw [ho]
    exact mem_auxiliaryBoundaryBlock_iff _ _ a j
  rw [vertexParity_eq_sum_incidenceWord _ o word hn hw]
  have hmap : (word.map fun j => (List.ofFn (copiedEdgeLabels gadgets B F i x)).getD j false) =
      word.map (fun j => (List.ofFn x).getD
        (occurrencePrefix (fun r => (gadgets r).template) F i.val + j) false) := by
    apply List.map_congr_left
    intro j hj
    obtain ⟨p, hp, _⟩ := (hw j).mp hj
    rw [← hp]
    exact List.getD_ofFn (copiedEdgeLabels gadgets B F i x) (incidenceDart p false).1 false
  rw [hmap]
  simpa only [shiftBlock, List.map_map, Function.comp_def] using
    sum_auxiliaryBlock_eq_false gadgets witnesses B hB F i a x hx

end Cslib.Complexity.CSP.GadgetRotation
