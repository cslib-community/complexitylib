/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Partition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.VariableFibers
public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.VertexParity

/-!
# Parity inherited by the actual substitution words

Every target vertex-even edge labeling has zero sum on each executed source-variable word.
An empty word has zero sum directly; a nonempty word is identified with its complete actual
target endpoint fiber. No nonempty-port or target-genus premise is used.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Target vertex evenness gives zero sum on the exact spliced word for every occurring
source name. A source name can disappear completely when all of its local blocks are empty. -/
theorem sum_variableBlock_eq_false
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x)
    (v : ℕ) (hv : v ∈ F.vars) :
    ((variableBlock (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F c v).map
        fun i => (List.ofFn x).getD i false).sum = false := by
  let T := replaceGadgets B (fun r => (gadgets r).template) F
  let word := variableBlock (fun r => (gadgets r).template)
    (fun r => freeBoundaryBlocks (gadgets r) (witnesses r)) F c v
  have hf (i : ℕ) : i ∈ word ↔ i < T.vars.length ∧ T.vars.getD i 0 = 2 * v :=
    mem_variableBlock_iff_targetName gadgets witnesses B F hF c hc v hv i
  have hword : word ∈ replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c :=
    List.mem_append_left _ (List.mem_map.mpr ⟨v, CSP.mem_distinctVars.mpr hv, rfl⟩)
  have hn : word.Nodup :=
    (List.nodup_flatten.mp (nodup_flatten_replacementCycles gadgets witnesses F hF c hc)).1 _ hword
  exact sum_eq_false_of_vertexEven_word x hx word hn (2 * v) 0 hf

/-- Each copied auxiliary word inherits zero sum from its complete private target fiber.
Unused auxiliary ports and a zero uniform auxiliary bound need no exceptional convention. -/
theorem sum_auxiliaryBlock_eq_false
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ)
    (hB : ∀ r, (gadgets r).numAux ≤ B) (F : CSP Src ℕ) (i : Fin F.length)
    (a : Fin (gadgets F[i.val].rel).numAux)
    (x : Fin (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).edges.length →
      Bool)
    (hx : (incidenceGraph (replaceGadgets B (fun r => (gadgets r).template) F)).VertexEven x) :
    ((shiftBlock (occurrencePrefix (fun r => (gadgets r).template) F i.val)
      ((auxiliaryBoundaryBlocks (gadgets F[i.val].rel) (witnesses F[i.val].rel)).getD a.val [])).map
        fun j => (List.ofFn x).getD j false).sum = false := by
  have hn := (nodup_auxiliaryBoundaryBlock (gadgets F[i.val].rel) (witnesses F[i.val].rel) a).map
    (f := (occurrencePrefix (fun r => (gadgets r).template) F i.val + ·))
    (fun _ _ h => Nat.add_left_cancel h)
  exact sum_eq_false_of_vertexEven_word x hx _ hn (2 * (B * i.val + a.val) + 1) 0
    (mem_shifted_auxiliaryBlock_iff_targetName gadgets witnesses B hB F i.isLt a)

end Cslib.Complexity.CSP.GadgetRotation
