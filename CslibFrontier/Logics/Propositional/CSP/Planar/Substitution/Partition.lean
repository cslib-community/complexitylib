/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyPartition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.VariableBlocks
import Mathlib.Data.List.Perm.Basic

/-!
# The full occurrence partition of the executed substitution cycles

The actual `replacementCycles` regroup every local free block along the supplied source white
rotation and retain each auxiliary block in its own copy. Their flattening enumerates exactly
all occurrences of the exact existing replacement body, without repetition. Source variables
may repeat within scopes and across duplicate constraints. No target-rotation, genus or
planarity premise is supplied.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- The exact executed cycle list partitions the target's actual occurrence indices.
This proves positional coverage and distinctness, independently of the target's binary names. -/
theorem flatten_replacementCycles_perm
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    (replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c).flatten.Perm
      (List.range (replaceGadgets B (fun r => (gadgets r).template) F).vars.length) := by
  let templates := fun r => (gadgets r).template
  let free := fun r => freeBoundaryBlocks (gadgets r) (witnesses r)
  let aux := fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)
  have hfree : ∀ row ∈ F, (free row.1).length = row.2.length := by
    intro row hr
    exact (length_freeBoundaryBlocks _ _).trans (hF row hr).symm
  have hp := flatten_variableBlocks_perm templates free F c hc
  rw [flatten_incidenceBlocks_eq templates free F hfree] at hp
  have hj := List.flatMap_append_perm F.zipIdx
    (fun entry => (free entry.1.1).flatMap
      (shiftBlock (occurrencePrefix templates F entry.2)))
    (fun entry => (aux entry.1.1).flatMap
      (shiftBlock (occurrencePrefix templates F entry.2)))
  have hr := shifted_boundaryBlocks_perm_target_range gadgets witnesses B F
  change (replacementCycles templates free aux F c).flatten.Perm _
  simp only [replacementCycles, List.flatten_eq_flatMap, List.flatMap_append,
    List.flatMap_map, List.flatMap_assoc, id_eq]
  apply (hp.append (List.Perm.refl _)).trans
  apply hj.trans
  unfold shiftBlock
  simpa only [List.flatten_eq_flatMap, List.map_flatMap, List.flatMap_append, List.map_append,
    id_eq, templates, free, aux] using hr

/-- Every produced occurrence word is disjoint from every other one, and has no repetitions
itself. Empty words at unused ports remain harmless members of the executed list. -/
theorem nodup_flatten_replacementCycles
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) :
    (replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c).flatten.Nodup :=
  (flatten_replacementCycles_perm gadgets witnesses 0 F hF c hc).nodup_iff.mpr List.nodup_range

/-- Every actual target position appears in one executed word, and no out-of-range position
can appear. The bound concerns occurrence positions, not the magnitude of a variable name. -/
theorem mem_flatten_replacementCycles_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ)
    (hF : WellFormed srcArity F) (c : RotationCertificate)
    (hc : RotationCertificate.verifyRotation (incidenceGraph F) c = true) (index : ℕ) :
    index ∈ (replacementCycles (fun r => (gadgets r).template)
      (fun r => freeBoundaryBlocks (gadgets r) (witnesses r))
      (fun r => auxiliaryBoundaryBlocks (gadgets r) (witnesses r)) F c).flatten ↔
      index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length := by
  rw [(flatten_replacementCycles_perm gadgets witnesses B F hF c hc).mem_iff, List.mem_range]

end Cslib.Complexity.CSP.GadgetRotation
