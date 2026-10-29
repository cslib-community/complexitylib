/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-! # Direct word and List clients -/

open Turing.MultiTapeTM

run_elab do
  let env ← Lean.getEnv
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree,
      `Turing.MultiTapeTM.ComputableTidilyInO] do
    if env.contains name then throwError "unexpected high-level tidy predicate: {name}"

example {γ : Type} {input : γ ↪ List Bool} {word : γ → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun x => (word x).reverse) input encBits := by
  fun_prop

-- This is the all-word reverse/trim/reverse shape used by the natural-number decoder.
example (htrim : ComputableInPolyTime (fun word : List Bool => word.dropWhile (!·))
    encBits encBits) :
    ComputableInPolyTime (fun word : List Bool => (word.reverse.dropWhile (!·)).reverse)
      encBits encBits := by
  fun_prop

example (_unknown : List Bool → List Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun word => (_unknown word).reverse) encBits encBits := by
      fun_prop
  trivial

example : ComputableInPolyTime List.range encUnary (encList encUnary) :=
  ComputableInPolyTime.range

example {α γ : Type} {element : α ↪ List Bool} {input : γ ↪ List Bool}
    {list : γ → List α} {test : γ → α → Bool}
    (hlist : ComputableInPolyTime list input (encList element))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair input element) encBool) :
    ComputableInPolyTime (fun x => (list x).all (test x)) input encBool := by
  fun_prop

example (test : ℕ → ℕ → Bool)
    (htest : ComputableInPolyTime (fun p : ℕ × ℕ => test p.1 p.2)
      (encPair encUnary encUnary) encBool) :
    ComputableInPolyTime (fun n => (List.range n).all (test n)) encUnary encBool := by
  fun_prop

example {γ : Type} {input : γ ↪ List Bool} {ι : Type*} (l : List ι)
    {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableInPolyTime (fun x => test x i) input encBool) :
    ComputableInPolyTime (fun x => l.all (test x)) input encBool := by
  exact ComputableInPolyTime.allConst l htest

-- No callback or encoding is needed for a type with no selected members.
example {ι : Type*} (test : List Bool → ι → Bool) :
    ComputableInPolyTime (fun word => ([] : List ι).all (test word)) encBits encBool := by
  apply ComputableInPolyTime.allConst
  simp

example (_test : List Bool → ℕ → Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun word => [0].all (_test word)) encBits encBool := by
      fun_prop
  trivial

example {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → β}
    (hf : ComputableInPolyTime f encA encB) :
    ComputableInPolyTime (List.map f) (encList encA) (encList encB) := by
  fun_prop

-- The complete frames/map/decode shape, with the actual total-provider contracts.
example {α : Type} {enc : α ↪ List Bool} {decode : List Bool → α}
    {frames : List Bool → List (List Bool)}
    (hdecode : ComputableInPolyTime decode encBits enc)
    (hframes : ComputableInPolyTime frames encBits (encList encBits)) :
    ComputableInPolyTime (fun word => (frames word).map decode) encBits (encList enc) := by
  fun_prop

-- Both the list and its natural-number elements vary at runtime; empty element types also work.
example :
    let enc : Empty ↪ List Bool := ⟨Empty.elim, fun x => x.elim⟩
    ComputableInPolyTime (List.map (fun n : ℕ => n + 1)) (encList encUnary) (encList encUnary) ∧
    ComputableInPolyTime (List.map (id : Empty → Empty)) (encList enc) (encList enc) ∧
    ComputableInPolyTime (List.reverse : List Empty → List Empty) (encList enc) (encList enc) :=
  ⟨ComputableInPolyTime.map ComputableInPolyTime.unary_succ,
    ComputableInPolyTime.map ComputableInPolyTime.id',
    ComputableInPolyTime.listReverseWithInput ComputableInPolyTime.id'⟩

example (_f : ℕ → ℕ) : True := by
  fail_if_success
    have : ComputableInPolyTime (List.map _f) (encList encUnary) (encList encUnary) := by
      fun_prop
  trivial

-- The condition's Boolean encoding and the tail/reverse branch are inferred from real rules.
example :
    ComputableInPolyTime List.tail encBits encBits ∧
    ComputableInPolyTime List.isEmpty encBits encBool ∧
    ComputableInPolyTime
      (fun word : List Bool => if word.isEmpty then [] else word.tail.reverse)
      encBits encBits ∧
    ComputableInPolyTime (fun p : ℕ × List ℕ => (p.1 :: p.2).reverse ++ p.2)
      (encPair encUnary (encList encUnary)) (encList encUnary) :=
  ⟨by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩

example :
    ([] : List Bool).tail = [] ∧
    ([] : List Bool).isEmpty = true ∧
    ([false] : List Bool).isEmpty = false ∧
    List.range 0 = [] ∧
    (encList encUnary (List.range 4)).length = 16 ∧
    (([false, true] : List Bool).reverse ++ [true]) = [true, false, true] := by decide

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.bitsReverse' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.bitsReverse

-- The full generic input and element encodings are retained; no finite/nonempty element premise.
example {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {head : γ → α} {tail : γ → List α}
    (hhead : ComputableInPolyTime head encIn encA)
    (htail : ComputableInPolyTime tail encIn (encList encA)) :
    ComputableInPolyTime (fun x => head x :: tail x) encIn (encList encA) := by
  fail_if_success (clear hhead; fun_prop)
  fail_if_success (clear htail; fun_prop)
  fun_prop

example {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {left right : γ → List α}
    (hleft : ComputableInPolyTime left encIn (encList encA))
    (hright : ComputableInPolyTime right encIn (encList encA)) :
    ComputableInPolyTime (fun x => (left x).reverse ++ right x) encIn (encList encA) := by
  fail_if_success (clear hleft; fun_prop)
  fail_if_success (clear hright; fun_prop)
  fun_prop

-- A captured computed word may change representation before the direct reverse recipe.
example {γ : Type} {input : γ ↪ List Bool} {word : γ → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun x => (word x).reverse) input encBits := by
  fail_if_success (clear hword; fun_prop)
  exact ComputableInPolyTime.bitsReverseWithInput hword

/--
info: 'Turing.MultiTapeTM.ComputableInPolyTime.listReverseWithInput' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.listReverseWithInput

-- A callback family need not choose an encoding convention; the outer certificate may fix it.
example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} (f : β → γ) (g : α → β)
    (hf : ComputableInPolyTime f middle output)
    (hg : ∀ encoding : β ↪ List Bool, ComputableInPolyTime g input encoding) :
    ComputableInPolyTime (fun a => f (g a)) input output := by
  fail_if_success (clear hf; fun_prop)
  fun_prop
