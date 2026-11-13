/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.MarkerParity
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateColors
import Mathlib.Data.List.OfFn

/-!
# The internally induced vertex-even source labeling

Every actual source edge receives the sum of its copied free block. Source-variable parity
comes from the literal supplied white-cycle splice; constraint parity comes from the internally
proved even marker tuple. Repeated source names and vanished or empty blocks are retained.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- A source incidence gets the sum of exactly its actual shifted free block. -/
@[expose] def sourceEdgeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) : Fin (incidenceGraph F).edges.length → Bool :=
  fun j => ((incidenceBlock (fun r => (gadgets r).template)
    (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F (2 * j.val)).map
      fun k => (List.ofFn x).getD k false).sum

/-- The induced source edge bit agrees with the internally determined marker at that
original scope position. The finite coordinate equality retains the indexed position. -/
theorem sourceEdgeLabels_incidenceDart
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool) (o : F.Occurrence) (side : Bool) (a : Fin (srcArity o.relation))
    (ha : o.2.val = a.val) :
    sourceEdgeLabels gadgets witnesses B F x (incidenceDart o side).1 =
      copiedFreeLabels gadgets witnesses B F o.1 x a := by
  unfold sourceEdgeLabels
  change ((incidenceBlock _ _ F (2 * incidenceEdgeIndex o)).map _).sum = _
  rw [incidenceBlock_occurrence]
  simp only [copiedFreeLabels, shiftBlock, List.map_map, Function.comp_def, ha,
    CSP.Occurrence.relation]

/-- The literal source white cycle has zero induced parity, including arbitrarily long
stretches of empty replacement blocks. Its anchoring uses the original first-occurrence API. -/
theorem vertexParity_sourceEdgeLabels_variable
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (o : F.Occurrence) :
    (incidenceGraph F).vertexParity (sourceEdgeLabels gadgets witnesses B F x)
      (incidenceDart o false).vertex = false := by
  obtain ⟨q, hq, hvar⟩ := exists_occurrence_at_first_index o.var o.var_mem
  have hv : (incidenceDart o false).vertex = (incidenceDart q false).vertex :=
    (vertex_incidenceDart_eq_iff o q false false).mpr ⟨rfl, hvar.symm⟩
  have hstart : (incidenceDart q false).index = 2 * F.vars.idxOf o.var := by
    change 2 * incidenceEdgeIndex q + 0 = _
    rw [hq, Nat.add_zero]
  rw [hv, RotationCertificate.vertexParity_eq_sum_cycleWord hc]
  have hs : ((RotationCertificate.cycleWord c (incidenceDart q false).index).map
      (Dart.colorAtIndex fun d => sourceEdgeLabels gadgets witnesses B F x d.1)).sum =
      ((variableBlock (fun r => (gadgets r).template)
        (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F c o.var).map
          fun j => (List.ofFn x).getD j false).sum := by
    unfold variableBlock
    rw [CSP.map_occurrences, ← hstart, List.map_flatMap, List.flatMap,
      List.sum_flatten, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j hj
    obtain ⟨p, hp, _⟩ := (mem_variable_cycleWord_iff hc q j).mp hj
    rw [hp]
    change Dart.colorAtIndex _ (incidenceDart p false).index = _
    rw [Dart.colorAtIndex_index]
    rfl
  rw [hs]
  exact sum_variableBlock_eq_false gadgets witnesses B F hF c hc x hx o.var o.var_mem

/-- Original source constraints have even induced parity by the complete marker-tuple
calculation. The proof uses every indexed scope position, with no injectivity premise. -/
theorem vertexParity_sourceEdgeLabels_constraint
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (hF : WellFormed srcArity F)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (o : F.Occurrence) :
    (incidenceGraph F).vertexParity (sourceEdgeLabels gadgets witnesses B F x)
      (incidenceDart o true).vertex = false := by
  rw [vertexParity_eq_sum_scope]
  have hn := hF F[o.1.val] (List.getElem_mem o.1.isLt)
  rw [List.ofFn_congr hn]
  have he := congrArg List.ofFn (funext fun a : Fin (srcArity F[o.1.val].1) =>
    sourceEdgeLabels_incidenceDart gadgets witnesses B F x
      (⟨o.1, Fin.cast hn.symm a⟩ : F.Occurrence) true a rfl)
  rw [he]
  exact sum_copiedFreeLabels_eq_false gadgets witnesses B hB F o.1 x hx

/-- Every target vertex-even labeling internally induces a vertex-even labeling on the
accepted source. No source genus or supplied source-color provider is needed for this step. -/
theorem vertexEven_sourceEdgeLabels
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (hF : WellFormed srcArity F)
    (c : RotationCertificate) (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x) :
    (incidenceGraph F).VertexEven (sourceEdgeLabels gadgets witnesses B F x) := by
  rw [Graph.vertexEven_iff_dart]
  intro d
  obtain ⟨o, ho⟩ := exists_incidenceDart d
  have h (side : Bool) : (incidenceGraph F).vertexParity (sourceEdgeLabels gadgets witnesses B F x)
      (incidenceDart o side).vertex = false := by
    cases side
    · exact vertexParity_sourceEdgeLabels_variable gadgets witnesses B F hF c hc x hx o
    · exact vertexParity_sourceEdgeLabels_constraint gadgets witnesses B hB F hF x hx o
  simpa only [ho] using h d.2

end Cslib.Complexity.CSP.GadgetRotation
