/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.LocalParity
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.ConstraintParity
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.GetD

/-!
# Internally determined even marker tuples

Each marker bit is the sum of the actual copied free block. Constraint parity makes the
whole copied body edge sum zero; its complete free/auxiliary partition and private auxiliary
parity then force the complete marker tuple to have even sum. Arity zero is included.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- The actual free-block edge sum determining one structural marker bit. -/
@[expose] def copiedFreeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) : Fin (srcArity F[i.val].rel) → Bool :=
  fun a => (((freeBoundaryBlocks (gadgets F[i.val].rel) (witnesses F[i.val].rel)).getD a.val []).map
    fun j => (List.ofFn x).getD
      (occurrencePrefix (fun r => (gadgets r).template) F i.val + j) false).sum

/-- The complete marker tuple is even, internally derived from actual target vertex
evenness. Closed and nullary body components contribute through the original full partition. -/
theorem sum_copiedFreeLabels_eq_false
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (i : Fin F.length)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x) :
    (List.ofFn (copiedFreeLabels gadgets witnesses B F i x)).sum = false := by
  let g := gadgets F[i.val].rel
  let w := witnesses F[i.val].rel
  let bit := fun j => (List.ofFn x).getD
    (occurrencePrefix (fun r => (gadgets r).template) F i.val + j) false
  have htotal : ((List.range g.body.occurrences.length).map bit).sum = false := by
    have hs := sum_edgeLabels_eq_false_of_constraintParity (copiedEdgeLabels gadgets B F i x)
      (vertexParity_copiedEdgeLabels_constraint gadgets B F i x hx)
    have he : (List.range g.body.occurrences.length).map bit =
        List.ofFn (copiedEdgeLabels gadgets B F i x) := by
      rw [List.map_range_eq_ofFn]
      simp only [copiedEdgeLabels, incidenceGraph_edges, List.length_map, Fin.val_cast, g, bit]
    rw [he]
    exact hs
  have haux : ((auxiliaryBoundaryBlocks g w).flatten.map bit).sum = false := by
    have hz (block : List ℕ) (hb : block ∈ auxiliaryBoundaryBlocks g w) :
        (block.map bit).sum = false := by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hb
      let a : Fin g.numAux := ⟨j, by simpa only [length_auxiliaryBoundaryBlocks] using hj⟩
      have hs := sum_auxiliaryBlock_eq_false gadgets witnesses B hB F i a x hx
      simpa only [shiftBlock, List.map_map, Function.comp_def,
        List.getD_eq_getElem _ _ hj, a, g, w, bit] using hs
    rw [List.map_flatten, List.sum_flatten, List.map_map]
    have he := congrArg List.sum (List.map_congr_left hz)
    exact he.trans (by simp [← Bool.zero_eq_false])
  have hp := ((flatten_boundaryBlocks_perm_range g w).map bit).sum_eq
  rw [List.flatten_append, List.map_append, List.sum_append, haux, htotal] at hp
  have hfree : ((freeBoundaryBlocks g w).flatten.map bit).sum = false := by
    simpa only [← Bool.zero_eq_false, add_zero] using hp
  change (List.ofFn fun a : Fin (srcArity F[i.val].rel) =>
    (((freeBoundaryBlocks g w).getD a.val []).map bit).sum).sum = false
  rw [List.ofFn_getD_eq_map_of_length (fun block : List ℕ => (block.map bit).sum) []
    (length_freeBoundaryBlocks g w)]
  simpa only [List.map_flatten, List.sum_flatten, List.map_map, Function.comp_def] using hfree

end Cslib.Complexity.CSP.GadgetRotation
