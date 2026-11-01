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
      `Turing.MultiTapeTM.ComputableTidilyInO] do
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

-- The charged predicate cannot be silently substituted for that contract, while linear-time
-- combinators and BigO normal forms preserve independent functions and universes.
example {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} {T S : α → ℕ} (h : ComputableInBigO f encIn encOut T S) :
    (¬ ComputableInO (fun w : List Bool => w) word word List.length (fun _ => 0)) ∧
    ComputableInDegree (fun w : List Bool => w) word word 1 1 ∧
    ComputableInDegree (fun _ : List Bool => []) word word 1 1 ∧
    (∃ c, ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : Turing.MultiTapeTM k Bool State),
      ∀ a, tm.ComputesTidilyInTimeAndSpace (encIn a) (encOut (f a))
        (c * (T a + 1)) (c * (S a + 1))) := by
  refine ⟨?_, .of_eq fun _ => rfl,
    ((ComputableInDegree.const []).comp (.of_eq fun _ => rfl)).mono,
    Internal.NormalForm.bigO h⟩
  rintro ⟨c, _, hl⟩
  have hc := hl (List.replicate (c + 1) true)
  simp only [word, Function.Embedding.refl_apply, List.length_replicate, zero_add, mul_one] at hc
  omega

-- The copy machine retains exactly zero workspace and needs a genuinely linear output bound.
example : ComputableInTimeAndSpace id word word (fun w => w.length + 1) (fun _ => 0) ∧
    ComputableInDegree id word word 1 1 ∧
    ¬ DegreeBounded (List.length (α := Bool)) List.length 0 := by
  have h : ComputableInTimeAndSpace id word word (fun w => w.length + 1) (fun _ => 0) :=
    computableInTimeAndSpace_id
  have hd := ComputableInDegree.of_bounds
    (show DegreeBounded (fun w => (word w).length) (fun w => w.length + 1) 1 from
      ⟨1, fun _ => by simp [word]⟩) (DegreeBounded.const 0) h
  -- Converting independent constants to a common bound and back preserves the function class.
  refine ⟨h, ComputableInDegree.one_one_iff.mpr (ComputableInDegree.one_one_iff.mp hd), ?_⟩
  rintro ⟨c, hc⟩
  have := hc (List.replicate (c + 1) true)
  simp only [pow_zero, mul_one, List.length_replicate] at this
  omega
