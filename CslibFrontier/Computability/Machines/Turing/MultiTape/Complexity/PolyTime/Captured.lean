/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Tactic.PolyTime.Init
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision

/-!
# Captured plain polynomial-time rules

Plain `Turing.MultiTapeTM.ComputableInPolyTime` composition rules for operations that combine
multiple arguments computed from a shared input. Rules whose head and encoding disambiguate
search are registered with `fun_prop`, and rules whose result hides an element or index encoding
additionally carry `program_certificate`; `binary_mod'` stays explicit alongside
`Turing.MultiTapeTM.ComputableInPolyTime.binary_div'` so `HMod.hMod` automation on
`Turing.MultiTapeTM.encUnary` remains unambiguous.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.cond'`: Boolean `_root_.cond` case distinction.
* `Turing.MultiTapeTM.ComputableInPolyTime.listHead?WithInput`: optional head of a computed
  framed list, fixing the element encoding without typeclass synthesis.
* `Turing.MultiTapeTM.ComputableInPolyTime.listHeadDWithInput`: head of a computed framed list
  with a computed fallback.
* `Turing.MultiTapeTM.ComputableInPolyTime.listTakeWithInput`: prefix of a computed framed list
  of computed unary length.
* `Turing.MultiTapeTM.ComputableInPolyTime.listDropWithInput`: suffix of a computed framed list
  after dropping a computed unary prefix.
* `Turing.MultiTapeTM.ComputableInPolyTime.countWithInput`: unary occurrence count of a computed
  value in a computed framed list.
* `Turing.MultiTapeTM.ComputableInPolyTime.anyConst`: existential Boolean scan over a fixed list
  with input-dependent predicates.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_mod'`: explicit remainder of computed binary
  naturals on `Turing.MultiTapeTM.encNat`.
-/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Case distinction on a computed Boolean guard in any encoding of `Bool`, for `_root_.cond`. -/
@[fun_prop]
public theorem cond' {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {encC : Bool ↪ List Bool} {c : α → Bool} {t e : α → β}
    (hc : ComputableInPolyTime c encIn encC) (ht : ComputableInPolyTime t encIn encOut)
    (he : ComputableInPolyTime e encIn encOut) :
    ComputableInPolyTime (fun a => _root_.cond (c a) (t a) (e a)) encIn encOut :=
  (hc.ite ht he).of_enc_eq fun a => by cases c a <;> rfl

/-- Read the optional head of a computed framed list, inferring the element encoding directly
from the list certificate without waiting on `ListEncoding` synthesis. -/
@[fun_prop, program_certificate hlist]
public theorem listHead?WithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun a => (list a).head?) encIn (encOption encA) :=
  (head? encA).comp hlist

/-- Read the head of a computed framed list with a computed fallback, inferring the element
encoding from the list before checking the fallback or composing with an outer projection. -/
@[fun_prop, program_certificate hlist]
public theorem listHeadDWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {fallback : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hfallback : ComputableInPolyTime fallback encIn encA) :
    ComputableInPolyTime (fun a => (list a).headD (fallback a)) encIn encA :=
  (optionGetDWithInput (listHead?WithInput hlist) hfallback).of_enc_eq fun a => by
    cases list a <;> rfl

/-- Drop a computed unary number of elements from a computed framed list. -/
@[fun_prop]
public theorem listDropWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun a => (list a).drop (count a)) encIn (encList encA) :=
  (dropUnary (encA := encA)).comp (hlist.prod hcount)

/-- Take a computed unary number of elements from a computed framed list. -/
@[fun_prop]
public theorem listTakeWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun a => (list a).take (count a)) encIn (encList encA) :=
  (listReverseWithInput (listDropWithInput (listReverseWithInput hlist)
    (unary_sub' ((length_list encA).comp hlist) hcount))).of_enc_eq fun a => by
    simp only [Function.comp_def, ← List.reverse_take, List.reverse_reverse]

/-- Count occurrences of a computed value in a computed framed list using lawful Boolean equality,
returning the count in unary. -/
@[fun_prop, program_certificate hlist]
public theorem countWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    [BEq α] [LawfulBEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun a => (list a).count (value a)) encIn encUnary := by
  simp only [List.count_eq_countP]
  exact countPWithInput hlist ((snd encIn encA).beq (hvalue.comp (fst encIn encA)))

/-- Test whether any element of a fixed list satisfies an input-dependent predicate. Only the
list's members need certificates; the index type may live in any universe and requires no
encoding. -/
@[fun_prop, program_certificate]
public theorem anyConst {γ : Type} {encIn : γ ↪ List Bool} {ι : Type*} (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableInPolyTime (fun a => test a i) encIn encBool) :
    ComputableInPolyTime (fun a => l.any (test a)) encIn encBool := by
  induction l with
  | nil => exact const false
  | cons i l ih =>
    exact bool_or.comp ((htest i (List.mem_cons_self ..)).prod
      (ih fun j hj => htest j (List.mem_cons_of_mem _ hj)))

/-- Remainder of computed binary naturals on `encNat`. Like
`Turing.MultiTapeTM.ComputableInPolyTime.binary_div'`, this rule is kept out of `fun_prop` and
`program_certificate` so `HMod.hMod` dispatch on `encUnary` stays unambiguous. -/
public theorem binary_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a % right a) input encNat :=
  binary_mod.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime
