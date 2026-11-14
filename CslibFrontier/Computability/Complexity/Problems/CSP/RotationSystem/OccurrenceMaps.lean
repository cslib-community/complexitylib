/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.FlatMap
public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Relabel
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Directed argument succession through literal occurrence maps

Variable renaming and body concatenation preserve the original positive cyclic scope order.
The equations use actual constraint and argument positions, without injectivity requirements
on variable names or any degree or nonempty-scope assumption.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

/-- Renaming variables preserves the original directed cyclic argument successor. -/
theorem argumentSuccessor_relabelOccurrence {Rel V W : Type} (F : CSP Rel V) (f : V → W)
    (o : F.Occurrence) :
    argumentSuccessor (CSP.relabelOccurrence F f o) =
      CSP.relabelOccurrence F f (argumentSuccessor o) := by
  apply CSP.Occurrence.eq_of_positions
  · rfl
  · simp only [argumentSuccessor, CSP.relabelOccurrence, val_finRotate, CSP.relabel,
      List.getElem_map, Constraint.relabel, List.length_map]

/-- Concatenating bodies preserves the selected local constraint's directed scope cycle. -/
theorem argumentSuccessor_flatMapOccurrence {α Rel V : Type} (l : List α)
    (f : α → CSP Rel V) (i : Fin l.length) (o : (f l[i.val]).Occurrence) :
    argumentSuccessor (CSP.flatMapOccurrence l f i o) =
      CSP.flatMapOccurrence l f i (argumentSuccessor o) := by
  apply CSP.Occurrence.eq_of_positions
  · rfl
  · simp only [argumentSuccessor, CSP.flatMapOccurrence, val_finRotate,
      List.getElem_flatMap_prefix_add l f i.isLt o.1.isLt]

end Cslib.Complexity.CSP
