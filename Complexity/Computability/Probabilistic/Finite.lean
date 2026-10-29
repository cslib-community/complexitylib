/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Foundations.Data.List.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Efficient finite case analysis for probabilistic programs

A computed finite tag selects among certified programs retaining the original input. The finite
control type and its branch machines are fixed independently of runtime input. Each branch may
return values of unbounded encoded length, which its certificate charges.

## Main results

* `Cslib.Probability.IsPPTOn.finite_cases`: finite probabilistic dispatch with captured input.

## References

Adapts Computability/Probabilistic/Finite.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the existing tidy calculus and closed PPT rules.
-/

@[expose] public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- A fixed finite tag selects a certified probabilistic branch with captured input.
The result has the chosen branch's exact distribution, including state returned with its output. -/
theorem IsPPTOn.finite_cases
    {α β Tag : Type} [Finite Tag] {input : α ↪ List Bool} {output : β ↪ List Bool}
    {tagEncoding : Tag ↪ List Bool} {tag : α → Tag} {branch : Tag → α → ProbComp β}
    (htag : ComputableInPolyTime tag input tagEncoding)
    (hbranch : ∀ choice, IsPPTOn input output (branch choice)) :
    IsPPTOn input output (fun a => branch (tag a) a) := by
  have htag := htag.tidy
  classical
  let _ := Fintype.ofFinite Tag
  cases isEmpty_or_nonempty Tag with
  | inl hempty =>
    let : IsEmpty α := ⟨fun a => isEmptyElim (tag a)⟩
    apply (ComputableTidilyInPolyTime.of_finite (encA := input) (encB := output)
      (fun a : α => isEmptyElim a)).isPPTOn.congr
    intro a
    exact isEmptyElim a
  | inr hnonempty =>
    let fallback := Classical.choice hnonempty
    have hselect (tags : List Tag) : IsPPTOn input output (fun a =>
        tags.foldr (fun choice rest => if tag a = choice then branch choice a else rest)
          (branch fallback a)) := by
      induction tags with
      | nil => exact hbranch fallback
      | cons choice tags ih =>
        exact IsPPTOn.ite (htag.decide_eq' (.const choice)) (hbranch choice) ih
    simpa only [List.foldr_ite_eq_of_mem, Finset.mem_toList, Finset.mem_univ] using
      hselect (Finset.univ.toList : List Tag)

end Cslib.Probability
