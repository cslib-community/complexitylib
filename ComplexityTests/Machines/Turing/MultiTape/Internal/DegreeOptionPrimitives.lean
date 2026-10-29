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

example {α : Type*} (a : α ↪ List Bool) (o _o : Option α ↪ List Bool) [OptionEncoding a o]
    (d : α) (dBits : List Bool) (n : ℕ) (aEmpty : Empty ↪ List Bool) :
    ComputableInDegree some a o 1 1 ∧
    ComputableInDegree (fun x => x.getD d) o a 1 1 ∧
    ComputableInDegree some (Function.Embedding.refl (List Bool))
      (encOption (Function.Embedding.refl _)) 1 1 ∧
    ComputableInDegree (fun x => x.getD dBits)
      (encOption (Function.Embedding.refl _)) (Function.Embedding.refl _) 1 1 ∧
    (encOption (Function.Embedding.refl _) (some (List.replicate n true))).length = n + 1 ∧
    ComputableInDegree (fun _ : Option α => none) (encOption a) (encOption a) 1 0 ∧
    ComputableInDegree (fun opt : Option α => opt.isSome) (encOption a) encBool 1 0 ∧
    ComputableInDegree (fun opt : Option Empty => opt.isSome) (encOption aEmpty) encBool 1 0 ∧
    (none : Option (List Bool)).isSome = false ∧
    (some ([] : List Bool)).isSome = true ∧
    (none : Option (List Bool)).getD dBits = dBits ∧
    (some ([] : List Bool)).getD dBits = [] := by
  fail_if_success
    have : ComputableInDegree some a _o 1 1 := ComputableInDegree.optionSome
  exact ⟨.optionSome, .getD d, .optionSome, .getD dBits, by simp,
    .const none, .isSome a, .isSome aEmpty, rfl, rfl, rfl, rfl⟩

-- Raw-linear encoding fields remain a documented temporary capability only.
open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
