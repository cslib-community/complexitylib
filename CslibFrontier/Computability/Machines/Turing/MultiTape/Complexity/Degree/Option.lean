/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives

/-!
# Options and list heads for `fun_prop` at degree one

`fun_prop` assembles `ComputableInDegree … 1 1` certificates from rules for each operation. This
module adds the rules for options and list heads that it lacked, so that a definition using them
needs no restatement in terms of tests and defaults:

* `Option.elim`, which is also the form `option_match_to_elim` gives a `match` on an option;
* `List.head?`;
* `Option.some`, `Option.getD`, `List.headD`, `List.tail` and `List.isEmpty`, registered as
  `fun_prop` rules.

`Option.elim` and `List.head?` are stated for linear time and space and linear output growth,
which is what composition at degree one needs.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.optionElim_one`: eliminating an option.
* `Turing.MultiTapeTM.ComputableInDegree.head?_one`: the head of a framed list.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

attribute [fun_prop] optionSome getD headD tail isEmpty

/-- **Eliminating an option** in linear time and space: the handler of `some` receives the input
and the value. -/
@[fun_prop]
theorem optionElim_one {α β γ : Type} [Inhabited β] {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    (hv : ComputableInDegree value encA (encOption encB) 1 1)
    (hn : ComputableInDegree fallback encA encC 1 1)
    (hb : ComputableInDegree (fun p : α × β => body p.1 p.2) (encPair encA encB) encC 1 1) :
    ComputableInDegree (fun a => (value a).elim (fallback a) (body a)) encA encC 1 1 := by
  have h : (fun a => (value a).elim (fallback a) (body a)) =
      fun a => if (value a).isSome then body a ((value a).getD default) else fallback a := by
    funext a
    cases value a <;> rfl
  rw [h]
  have hg : ComputableInDegree (fun a => (value a).getD default) encA encB 1 1 :=
    ((getD (enc₁ := encB) default).comp hv).mono
  exact ite_le ((isSome encB).comp hv) ((hb.comp (id'.prod hg)).mono (d' := 1) (e' := 1)) hn
    (by simp) (by simp)

/-- **The head of a framed list**, as an option, in linear time and space. -/
@[fun_prop]
theorem head?_one {β : Type} [Inhabited β] {enc : β ↪ List Bool} :
    ComputableInDegree (fun l : List β => l.head?) (encList enc) (encOption enc) 1 1 := by
  have h : (fun l : List β => l.head?) =
      fun l => if l.isEmpty then none else some (l.headD default) := by
    funext l
    cases l <;> rfl
  rw [h]
  fun_prop (disch := first | apply le_refl | lia)

end Turing.MultiTapeTM.ComputableInDegree
