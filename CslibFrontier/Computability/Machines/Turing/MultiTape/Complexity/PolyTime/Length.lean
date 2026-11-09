/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Tactic.PolyTime.Init

/-!
# Binary list length in polynomial time

`Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_list` computes the length of a framed list in
unary (`encUnary`), the representation required by bounded loops and `List.range`. Verifiers and
reductions that compare a list length against a binary parameter or add it to binary wire and
vertex indices instead need the length in the binary natural encoding `encNat`. Composing
`length_list` with `unary_to_binary` provides plain rules for `fun_prop` and `polytime`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary`: the length of a framed list in
  the binary encoding `encNat`.
* `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary'`: the binary length of a computed
  framed list, fixing the intermediate list encoding for proof search.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Length of a framed list in binary (`encNat`); the element encoding is inferred from the list
encoding. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem length_list_binary {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun l : List α => l.length) (encList enc) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (.length_list enc))

/-- Length of a computed framed list in binary (`encNat`), fixing the intermediate list encoding for
proof search. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem length_list_binary' {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {list : α → List β} (hlist : ComputableInPolyTime list input (encList enc)) :
    ComputableInPolyTime (fun a => (list a).length) input encNat :=
  (length_list_binary enc).comp hlist

end Turing.MultiTapeTM.ComputableInPolyTime
