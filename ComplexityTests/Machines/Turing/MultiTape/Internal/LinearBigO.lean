/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-! # Linear normalization and an uncharged, zero-workspace streaming transducer -/

@[expose] public section

open Turing.MultiTapeTM

def word : List Bool ↪ List Bool := Function.Embedding.refl _

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

-- Copying arbitrary words writes unbounded output with zero workspace.
theorem streamingIdentity :
    ComputableInBigO (fun w : List Bool => w) word word List.length (fun _ => 0) := by
  refine ⟨1, ?_⟩
  obtain ⟨k, State, hfinite, tm, htm⟩ := computableInTimeAndSpace_id (enc := word)
  refine ⟨k, State, hfinite, tm, fun w => ?_⟩
  simpa only [one_mul, word, Function.Embedding.refl_apply, zero_add] using
    show tm.ComputesInTimeAndSpace w w (w.length + 1) 1 from
      ⟨(htm w).1, (htm w).2.1, (htm w).2.2.mono (Nat.zero_le 1)⟩

-- The charged predicate cannot be silently substituted for that contract.
example : ¬ ComputableInO (fun w : List Bool => w) word word List.length (fun _ => 0) := by
  rintro ⟨c, _, hl⟩
  have h := hl (List.replicate (c + 1) true)
  simp only [word, Function.Embedding.refl_apply, List.length_replicate, zero_add, mul_one] at h
  omega

example : ComputableInLinearTimeAndSpace (fun w : List Bool => w) word word :=
  .of_eq fun _ => rfl

example : ComputableInLinearTimeAndSpace (fun _ : List Bool => []) word word :=
  .const []

example : ComputableInLinearTimeAndSpace (fun _ : List Bool => []) word word :=
  (ComputableInLinearTimeAndSpace.const []).comp (.of_eq fun _ => rfl)

-- Independent functions and unrelated input/output universes are preserved by normalization.
example {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {T S : α → ℕ} (h : ComputableInBigO f encIn encOut T S) :
    ∃ c, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a))
        (c * (T a + 1)) (c * (S a + 1)) := Internal.NormalForm.bigO h

/-- info: 'Turing.MultiTapeTM.ComputableInLinearTimeAndSpace.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInLinearTimeAndSpace.comp
