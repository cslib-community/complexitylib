/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import CslibFrontier.Foundations.Data.List.Fold

/-!
# Linear-space finite case analysis

A computed tag selects a branch retaining the original input. The finite tag type and branch
machines are fixed independently of runtime input. Encodings are arbitrary, and neither the tag
nor result type requires an inhabitant.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.finite_cases`: dispatch within linear encoded-input space.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- A fixed finite tag selects a linear-space branch with the original input captured.
This also handles an empty tag type (and hence an empty input type). -/
theorem finite_cases {α β Tag : Type} [Finite Tag]
    {input : α ↪ List Bool} {output : β ↪ List Bool} {tagEncoding : Tag ↪ List Bool}
    {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInSpace tag input tagEncoding (fun a => (input a).length))
    (hbranch : ∀ choice, ComputableInSpace (branch choice) input output
      (fun a => (input a).length)) :
    ComputableInSpace (fun a => branch (tag a) a) input output
      (fun a => (input a).length) := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInSpace (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output (fun a => (input a).length) := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        have htest := budget_finite (encC := encBool) (fun t : Tag => decide (t = choice)) htag
        simpa only [List.foldr_cons, Bool.decide_iff] using
          (budget_ite htest (hbranch choice) ih)
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableInSpace
