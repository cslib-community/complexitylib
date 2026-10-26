/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Lean.Elab.Command

/-! Option construction and fixed defaults, with arbitrary encodings and growing runtime words. -/
open Turing.MultiTapeTM

example {α : Type*} (a : α ↪ List Bool) (o : Option α ↪ List Bool) [OptionEncoding a o] :
    ComputableInDegree some a o 1 1 := .optionSome

example {α : Type*} (a : α ↪ List Bool) (o : Option α ↪ List Bool) [OptionEncoding a o]
    (d : α) : ComputableInDegree (fun x => x.getD d) o a 1 1 := .getD d

example : ComputableInDegree some (Function.Embedding.refl (List Bool))
    (encOption (Function.Embedding.refl _)) 1 1 := .optionSome

example (d : List Bool) : ComputableInDegree (fun x => x.getD d)
    (encOption (Function.Embedding.refl _)) (Function.Embedding.refl _) 1 1 := .getD d

example (n : ℕ) : (encOption (Function.Embedding.refl _) (some (List.replicate n true))).length
    = n + 1 := by simp

example {α : Type*} (a : α ↪ List Bool) :
    ComputableInDegree (fun _ : Option α => none) (encOption a) (encOption a) 1 0 := .const none

example {α : Type*} (a : α ↪ List Bool) :
    ComputableInDegree (fun o : Option α => o.isSome) (encOption a) encBool 1 0 := .isSome a

example (a : Empty ↪ List Bool) :
    ComputableInDegree (fun o : Option Empty => o.isSome) (encOption a) encBool 1 0 := .isSome a

example : (none : Option (List Bool)).isSome = false := rfl
example : (some ([] : List Bool)).isSome = true := rfl
example (d : List Bool) : (none : Option (List Bool)).getD d = d := rfl
example (d : List Bool) : (some ([] : List Bool)).getD d = [] := rfl

example {α : Type*} (_a : α ↪ List Bool) (_o : Option α ↪ List Bool) : True := by
  fail_if_success
    have : ComputableInDegree some _a _o 1 1 := ComputableInDegree.optionSome
  trivial

-- Raw-linear encoding fields remain a documented temporary capability only.
open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO, `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
