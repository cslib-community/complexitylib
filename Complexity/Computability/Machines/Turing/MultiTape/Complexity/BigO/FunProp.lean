/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# `fun_prop` rules for bounds up to constants

`fun_prop` proves `Turing.MultiTapeTM.ComputableInO f encIn encOut T S` from rules in
compositional form. The bounds of each rule's conclusion are a function of the bounds of its
premises, so in a goal whose bounds `T` and `S` are metavariables, `fun_prop` assembles them from
the parts of `f`. The usual pattern compares the assembled bounds with the intended ones in a
single step:

```
refine .mono (by fun_prop) k (fun a => ?_) fun a => ?_
```

The rules cover constants, the identity, composition, pairs and their projections, case
distinction on a computed Boolean, and `Option.isSome` and `Option.getD`. Other certificates
become rules in the same compositional form, for example `fun x => F (g x)` from
`Turing.MultiTapeTM.ComputableInO.comp'`.

## Main results

* `Turing.MultiTapeTM.ComputableInO.id'`, `.comp'`: the identity and composition, in the form
  required by `fun_prop`.
* `Turing.MultiTapeTM.ComputableInO.optionIsSome`, `.optionGetD`: option tests and defaults, with
  the bounds of the option.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {T S : α → ℕ}

attribute [fun_prop] ComputableInO
attribute [fun_prop] const prod fst' snd' ite

/-- Copy an encoded value, within linear time and space. -/
@[fun_prop]
theorem id' : ComputableInO (fun b : β => b) encMid encMid (fun b => (encMid b).length)
    fun b => (encMid b).length :=
  of_eq fun _ => rfl

/-- `Turing.MultiTapeTM.ComputableInO.comp` in the form required by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encMid encOut T₂ S₂) (hg : ComputableInO g encIn encMid T₁ S₁) :
    ComputableInO (fun a => f (g a)) encIn encOut (fun a => T₁ a + T₂ (g a))
      fun a => S₁ a + S₂ (g a) :=
  hf.comp hg

/-- Whether a computed option holds a value, within the bounds of the option. -/
@[fun_prop]
theorem optionIsSome {enc : β ↪ List Bool} {o : α → Option β}
    (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun a => (o a).isSome) encIn encBool T S :=
  (ComputableInDegree.isSome enc).inO_one.comp_linear h

/-- The value of a computed option, or a fixed default, within the bounds of the option. -/
@[fun_prop]
theorem optionGetD {enc : β ↪ List Bool} {o : α → Option β} (d : β)
    (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun a => (o a).getD d) encIn enc T S :=
  (ComputableInDegree.optionGetD enc d).inO_one.comp_linear h

end Turing.MultiTapeTM.ComputableInO
