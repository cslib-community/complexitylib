/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem
public import Complexity.Logics.Propositional.CSP.Occurrence.AppendScope
import Complexity.Logics.Propositional.CSP.Occurrence.Positions
import Complexity.Foundations.GroupTheory.Perm.Fin

/-!
# Clockwise successors in appended-scope coordinates

The actual old-body occurrences retain their original cyclic successor. The appended scope's
successor is exactly `finRotate` on its positional argument indices, including repeated labels
and arities zero and one. These original identities do not reflect or reorder original bodies.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V : Type}

/-- Old occurrences retain exactly the original directed argument successor after a scope
is appended, including duplicate constraints and repeated variables. -/
theorem argumentSuccessor_appendOfFnOccurrenceEquiv_inl (F : CSP Rel V) (r : Rel)
    {n : ℕ} (scope : Fin n → V) (o : F.Occurrence) :
    argumentSuccessor (appendOfFnOccurrenceEquiv F r scope (Sum.inl o)) =
      appendOfFnOccurrenceEquiv F r scope (Sum.inl (argumentSuccessor o)) := by
  let a := appendOfFnOccurrenceEquiv F r scope (Sum.inl o)
  let b := appendOfFnOccurrenceEquiv F r scope (Sum.inl (argumentSuccessor o))
  have ha := record_appendOfFnOccurrenceEquiv_inl F r scope o
  have hb := record_appendOfFnOccurrenceEquiv_inl F r scope (argumentSuccessor o)
  have hac : a.1.val = o.1.val := congrArg Prod.fst ha
  have hbc : b.1.val = o.1.val := congrArg Prod.fst hb
  have haj : a.2.val = o.2.val := congrArg (fun record => record.2.1) ha
  have hbj : b.2.val = (finRotate _ o.2).val := congrArg (fun record => record.2.1) hb
  have hw : (F ++ [(r, List.ofFn scope)])[a.1.val].2.length = F[o.1.val].2.length := by
    simp only [hac, List.getElem_append_left o.1.isLt]
  apply Occurrence.eq_of_positions
  · change a.1.val = b.1.val
    exact hac.trans hbc.symm
  · change (finRotate _ a.2).val = b.2.val
    rw [val_finRotate, hbj, val_finRotate, haj, hw]

/-- The appended scope's actual cyclic successor is the positive `finRotate` permutation
on its original argument positions. No condition on repeated variable labels is used. -/
theorem argumentSuccessor_appendOfFnOccurrenceEquiv_inr (F : CSP Rel V) (r : Rel)
    {n : ℕ} (scope : Fin n → V) (j : Fin n) :
    argumentSuccessor (appendOfFnOccurrenceEquiv F r scope (Sum.inr j)) =
      appendOfFnOccurrenceEquiv F r scope (Sum.inr (finRotate n j)) := by
  let a := appendOfFnOccurrenceEquiv F r scope (Sum.inr j)
  let b := appendOfFnOccurrenceEquiv F r scope (Sum.inr (finRotate n j))
  have ha := record_appendOfFnOccurrenceEquiv_inr F r scope j
  have hb := record_appendOfFnOccurrenceEquiv_inr F r scope (finRotate n j)
  have hac : a.1.val = F.length := congrArg Prod.fst ha
  have hbc : b.1.val = F.length := congrArg Prod.fst hb
  have haj : a.2.val = j.val := congrArg (fun record => record.2.1) ha
  have hbj : b.2.val = (finRotate n j).val := congrArg (fun record => record.2.1) hb
  have hw : (F ++ [(r, List.ofFn scope)])[a.1.val].2.length = n := by
    simp only [hac, List.getElem_append_right (le_refl F.length), Nat.sub_self,
      List.getElem_cons_zero, List.length_ofFn]
  apply Occurrence.eq_of_positions
  · change a.1.val = b.1.val
    exact hac.trans hbc.symm
  · change (finRotate _ a.2).val = b.2.val
    rw [val_finRotate, hbj, val_finRotate, haj, hw]

end Cslib.Complexity.CSP
