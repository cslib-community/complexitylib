/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives

/-!
# `fun_prop` rules for linear list, option and number operations

The linear primitives of `Turing.MultiTapeTM.ComputableInDegree`, as `fun_prop` rules for
`Turing.MultiTapeTM.ComputableInO`, so that a program over these operations is assembled by
`fun_prop` and its bounds are checked once with `Turing.MultiTapeTM.ComputableInO.mono`. Each
rule is linear in its encoded argument, and `Turing.MultiTapeTM.ComputableInO.comp'` composes
them.

## Main results

* `Turing.MultiTapeTM.ComputableInO.take'`, `.drop'`: prefixes and suffixes, with a unary count.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool} {T₁ S₁ T₂ S₂ : γ → ℕ}

/-- The linear primitive `h` as a `fun_prop` rule. -/
local macro "linear_rule " n:ident " : " f:term " from " e₁:term " to " e₂:term " := " h:term :
    command =>
  `(@[fun_prop] theorem $n : ComputableInO $f $e₁ $e₂
      (fun a => ($e₁ a).length) fun a => ($e₁ a).length := ComputableInDegree.inO_one $h)

linear_rule cons' : (fun p : α × List α => p.1 :: p.2) from (encPair enc (encList enc))
  to (encList enc) := ComputableInDegree.cons enc
linear_rule snoc' : (fun p : List α × α => p.1 ++ [p.2]) from (encPair (encList enc) enc)
  to (encList enc) := ComputableInDegree.snoc enc
linear_rule append' : (fun p : List α × List α => p.1 ++ p.2)
  from (encPair (encList enc) (encList enc)) to (encList enc) := ComputableInDegree.listAppend enc
linear_rule tail' : (fun l : List α => l.tail) from (encList enc) to (encList enc) :=
  ComputableInDegree.listTail enc

/-- Whether a computed list is empty. The list is a premise since a Boolean does not determine its
encoding. -/
@[fun_prop]
theorem isEmpty' {l : γ → List α} (hl : ComputableInO l encIn (encList enc) T₁ S₁) :
    ComputableInO (fun x => (l x).isEmpty) encIn encBool
      (fun x => T₁ x + (encList enc (l x)).length) fun x => S₁ x + (encList enc (l x)).length :=
  ComputableInO.comp' (ComputableInDegree.listIsEmpty enc).inO_one hl

@[fun_prop]
theorem headD' (d : α) : ComputableInO (fun l : List α => l.headD d) (encList enc) enc
    (fun l => (encList enc l).length) fun l => (encList enc l).length :=
  (ComputableInDegree.listHeadD enc d).inO_one

@[fun_prop]
theorem unarySucc' : ComputableInO (fun n : ℕ => n + 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_succ.inO_one

@[fun_prop]
theorem unaryPred' : ComputableInO (fun n : ℕ => n - 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_pred.inO_one

/-- The first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem take' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).take (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.take p.2)
    (ComputableInDegree.takeUnary enc).inO_one (hl.prod hn)

/-- All but the first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem drop' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).drop (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.drop p.2)
    (ComputableInDegree.dropUnary enc).inO_one (hl.prod hn)

end Turing.MultiTapeTM.ComputableInO
