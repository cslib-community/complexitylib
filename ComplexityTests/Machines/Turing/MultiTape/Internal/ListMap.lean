/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap

/-! # Captured list mapping with full uniform callback contexts -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← Lean.getEnv).contains name then throwError "unexpected higher tidy calculus: {name}"

example {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encIn : γ ↪ List Bool} {f : γ → α → β} {list : γ → List α} (n : ℕ)
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun p : γ × α => f p.1 p.2) (encPair encIn encA) encB) :
    ComputableInPolyTime (fun x => (list x).map (f x)) encIn (encList encB) ∧
    ComputableInPolyTime (fun x => (list x).map fun a => (x, a))
      encIn (encList (encPair encIn encA)) ∧
    ComputableInPolyTime (fun x : γ => ([] : List Bool).map fun _ => x)
      encIn (encList encIn) ∧
    ((List.range n).map fun i => (n, i)).length = n ∧
    (([] : List Bool).map fun b => (b, true)) = [] := by
  refine ⟨?_, by fun_prop,
    ComputableInPolyTime.mapWithInput (encA := encBool)
      (ComputableInPolyTime.const []) (ComputableInPolyTime.fst encIn encBool),
    by simp, rfl⟩
  fail_if_success (clear hlist; fun_prop)
  fail_if_success (clear hf; fun_prop)
  exact @ComputableInPolyTime.mapWithInput α β γ encA encB encIn f list hlist hf
