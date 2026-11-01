/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives

/-!
# `fun_prop` rules for linear list, option, number and test operations

The linear primitives of `Turing.MultiTapeTM.ComputableInDegree`, as `fun_prop` rules for
`Turing.MultiTapeTM.ComputableInO`, so that a program over these operations is assembled by
`fun_prop` and its bounds are checked once with `Turing.MultiTapeTM.ComputableInO.mono`. Each
rule is linear in its encoded argument, and `Turing.MultiTapeTM.ComputableInO.comp'` composes
them. A test takes the tested value as a premise, since a Boolean does not determine the encoding
of what it tests, and passes on its bounds unchanged.

## Main results

* `Turing.MultiTapeTM.ComputableInO.take'`, `.drop'`: prefixes and suffixes, with a unary count.
* `Turing.MultiTapeTM.ComputableInO.not'`, `.and'`, `.or'`: Boolean connectives.
* `Turing.MultiTapeTM.ComputableInO.decideEq'`, `.natIsZero'`: tests against a constant.
* `Turing.MultiTapeTM.ComputableInO.eq'`: equality of computed values, enabled locally by a client.
* `Turing.MultiTapeTM.ComputableInO.iteDecide`: case distinction on a decidable proposition.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
  {T S T₁ S₁ T₂ S₂ T₃ S₃ : γ → ℕ}

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
theorem some' : ComputableInO (fun a : α => some a) enc (encOption enc)
    (fun a => (enc a).length) fun a => (enc a).length :=
  (ComputableInDegree.optionSome (enc₁ := enc) (enc := encOption enc)).inO_one

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

attribute [fun_prop] natSucc natPred

/-- The negation of a computed Boolean. -/
@[fun_prop]
theorem not' {b : γ → Bool} (hb : ComputableInO b encIn encBool T S) :
    ComputableInO (fun x => !b x) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) not).inO_one.comp_linear hb

/-- The conjunction of two computed Booleans. -/
@[fun_prop]
theorem and' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x && b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 && q.2).inO_one.comp_linear (ha.prod hb)

/-- The disjunction of two computed Booleans. -/
@[fun_prop]
theorem or' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x || b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 || q.2).inO_one.comp_linear (ha.prod hb)

/-- Whether two computed values agree. This is not a global `fun_prop` rule, since it would also
apply to tests against a constant, which have cheaper rules; a client enables it locally. -/
theorem eq' [DecidableEq α] {a b : γ → α} (ha : ComputableInO a encIn enc T₁ S₁)
    (hb : ComputableInO b encIn enc T₂ S₂) :
    ComputableInO (fun x => decide (a x = b x)) encIn encBool
      (fun x => T₁ x + T₂ x +
        ((enc (a x)).length + 1) * ((enc (a x)).length + (enc (b x)).length + 1))
      fun x => S₁ x + S₂ x + (encPair enc enc (a x, b x)).length :=
  (eq enc).comp' (ha.prod hb)

/-- Whether a computed option is empty, within the bounds of the option. -/
@[fun_prop]
theorem optionIsNone {o : γ → Option α} (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun x => (o x).isNone) encIn encBool T S :=
  (not' h.optionIsSome).of_enc_eq fun x => by cases o x <;> rfl

/-- Whether a computed value of a finite type equals a fixed value. -/
@[fun_prop]
theorem decideEq' [Finite α] [DecidableEq α] (c : α) {v : γ → α}
    (hv : ComputableInO v encIn enc T S) :
    ComputableInO (fun x => decide (v x = c)) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := enc) (encMid := encBool)
    fun a => decide (a = c)).inO_one.comp_linear hv

/-- Whether a computed binary number is zero. -/
@[fun_prop]
theorem natIsZero' {n : γ → ℕ} (hn : ComputableInO n encIn encNat T S) :
    ComputableInO (fun x => decide (n x = 0)) encIn encBool T S :=
  natIsZero.comp_linear hn

/-- Case distinction on a decidable proposition, through its computed `decide`. -/
@[fun_prop]
theorem iteDecide {β : Type} {encOut : β ↪ List Bool} {c : γ → Prop} [DecidablePred c]
    {f g : γ → β} (hc : ComputableInO (fun x => decide (c x)) encIn encBool T₁ S₁)
    (hf : ComputableInO f encIn encOut T₂ S₂) (hg : ComputableInO g encIn encOut T₃ S₃) :
    ComputableInO (fun x => if c x then f x else g x) encIn encOut
      (fun x => T₁ x + if decide (c x) then T₂ x else T₃ x)
      fun x => S₁ x + if decide (c x) then S₂ x else S₃ x :=
  (hc.ite hf hg).of_enc_eq fun x => by simp only [decide_eq_true_eq]

-- Registered again so that a Boolean condition is tried here before `iteDecide`.
attribute [fun_prop] ite

end Turing.MultiTapeTM.ComputableInO
