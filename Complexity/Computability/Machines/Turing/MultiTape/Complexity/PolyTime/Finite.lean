/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Foundations.Data.List.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Polynomial-time finite case analysis

An efficiently computed finite tag selects a branch retaining the original input. Both the tag
encoding and output encoding are arbitrary. The finite type and all branch machines are fixed
independently of runtime input; this does not enumerate a family whose size grows with the input.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`,
  `Turing.MultiTapeTM.ComputableTidilyInPolyTime.finite_cases`: finite dispatch with captured input.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableInPolyTime (branch choice) input output) :
    ComputableInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        simpa only [List.foldr_cons, decide_eq_true_eq] using
          (htag.decide_eq' (const choice)).ite (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- A fixed finite tag selects a certified branch, charging the tag and captured input.
Neither the tag nor the result type requires a default inhabitant. -/
theorem finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → β}
    (htag : ComputableTidilyInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, ComputableTidilyInPolyTime (branch choice) input output) :
    ComputableTidilyInPolyTime (fun a => branch (tag a) a) input output := by
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    exact of_finite _
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : ComputableTidilyInPolyTime (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) input output := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih => exact (htag.decide_eq' (const choice)).ite_decide (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
