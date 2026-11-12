/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.AppendScope
import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Positional occurrences under body concatenation

Every original constraint and argument position has its own image. The right constraint
block is shifted by the left body length. No occurrence, repeated record or nullary
constraint is discarded. Directed cyclic argument successors retain their source order.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type}

/-- Place each original occurrence at its exact position in the concatenated bodies. -/
@[expose] def appendOccurrence (F H : CSP Rel V) :
    F.Occurrence ⊕ H.Occurrence → (F ++ H).Occurrence
  | Sum.inl o => ⟨⟨o.1.val, by simp only [List.length_append]; omega⟩,
      ⟨o.2.val, by simpa only [List.getElem_append_left o.1.isLt] using o.2.isLt⟩⟩
  | Sum.inr o => ⟨⟨F.length + o.1.val, by simp only [List.length_append]; omega⟩,
      ⟨o.2.val, by simpa only [List.getElem_append_right (by omega : F.length ≤
        F.length + o.1.val), Nat.add_sub_cancel_left] using o.2.isLt⟩⟩

private theorem appendOccurrence_bijective (F H : CSP Rel V) :
    Function.Bijective (appendOccurrence F H) := by
  constructor
  · intro a b he
    have hc := congrArg (fun o : (F ++ H).Occurrence => o.1.val) he
    have hj := congrArg (fun o : (F ++ H).Occurrence => o.2.val) he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Occurrence.eq_of_positions hc hj)
      | inr b => have ha := a.1.isLt; change a.1.val = F.length + b.1.val at hc; omega
    | inr a =>
      cases b with
      | inl b => have hb := b.1.isLt; change F.length + a.1.val = b.1.val at hc; omega
      | inr b =>
        apply congrArg Sum.inr
        have hc' : a.1.val = b.1.val := by
          change F.length + a.1.val = F.length + b.1.val at hc
          omega
        exact Occurrence.eq_of_positions hc' hj
  · intro o
    by_cases hi : o.1.val < F.length
    · let i : Fin F.length := ⟨o.1.val, hi⟩
      let j : Fin F[i.val].2.length := ⟨o.2.val, by
        simpa only [List.getElem_append_left hi] using o.2.isLt⟩
      exact ⟨Sum.inl ⟨i, j⟩, Occurrence.eq_of_positions rfl rfl⟩
    · have hbound : o.1.val - F.length < H.length := by
        have := o.1.isLt
        simp only [List.length_append] at this
        omega
      let i : Fin H.length := ⟨o.1.val - F.length, hbound⟩
      let j : Fin H[i.val].2.length := ⟨o.2.val, by
        simpa only [List.getElem_append_right (Nat.le_of_not_gt hi)] using o.2.isLt⟩
      exact ⟨Sum.inr ⟨i, j⟩, Occurrence.eq_of_positions (by
        change F.length + (o.1.val - F.length) = o.1.val; omega) rfl⟩

/-- The exact complete left-then-right occurrence correspondence, without deduplication. -/
@[expose] noncomputable def appendOccurrenceEquiv (F H : CSP Rel V) :
    F.Occurrence ⊕ H.Occurrence ≃ (F ++ H).Occurrence :=
  Equiv.ofBijective (appendOccurrence F H) (by exact appendOccurrence_bijective F H)

/-- Original left constraint positions and labels are unchanged. -/
theorem record_appendOccurrenceEquiv_inl (F H : CSP Rel V) (o : F.Occurrence) :
    (appendOccurrenceEquiv F H (Sum.inl o)).record = o.record := by
  change (o.1.val, o.2.val, (F ++ H)[o.1.val].2[o.2.val]) = o.record
  simp only [List.getElem_append_left o.1.isLt, Occurrence.record, Occurrence.var]

/-- Original right argument positions and labels are unchanged; constraint positions shift. -/
theorem record_appendOccurrenceEquiv_inr (F H : CSP Rel V) (o : H.Occurrence) :
    (appendOccurrenceEquiv F H (Sum.inr o)).record = (F.length + o.1.val, o.2.val, o.var) := by
  change (F.length + o.1.val, o.2.val, (F ++ H)[F.length + o.1.val].2[o.2.val]) = _
  simp only [List.getElem_append_right (Nat.le_add_right F.length o.1.val),
    Nat.add_sub_cancel_left, Occurrence.var]

end Cslib.Logic.PL.CSP

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Rel V : Type}

/-- The complete concatenation correspondence preserves each directed source argument cycle. -/
theorem argumentSuccessor_appendOccurrenceEquiv (F H : CSP Rel V)
    (o : F.Occurrence ⊕ H.Occurrence) :
    argumentSuccessor (appendOccurrenceEquiv F H o) = appendOccurrenceEquiv F H
      (Sum.map argumentSuccessor argumentSuccessor o) := by
  cases o with
  | inl o =>
    apply Occurrence.eq_of_positions
    · rfl
    · simp only [argumentSuccessor, appendOccurrenceEquiv, Equiv.ofBijective_apply,
        appendOccurrence, Sum.map_inl, val_finRotate, List.getElem_append_left o.1.isLt]
      change (if o.2.val + 1 = F[o.1.val].2.length then 0 else o.2.val + 1) =
        (finRotate _ o.2).val
      rw [val_finRotate]
  | inr o =>
    apply Occurrence.eq_of_positions
    · rfl
    · simp only [argumentSuccessor, appendOccurrenceEquiv, Equiv.ofBijective_apply,
        appendOccurrence, Sum.map_inr, val_finRotate,
        List.getElem_append_right (Nat.le_add_right F.length o.1.val), Nat.add_sub_cancel_left]
      change (if o.2.val + 1 = H[o.1.val].2.length then 0 else o.2.val + 1) =
        (finRotate _ o.2).val
      rw [val_finRotate]

end Cslib.Complexity.CSP
