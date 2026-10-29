/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Lean.Elab.Command

/-! Direct machine certificates, empty inputs, growing words and independent zero degrees. -/

@[expose] public section

open Turing.MultiTapeTM

namespace ComplexityTests.Internal.DegreePrimitives

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

/-- Identity encoding of a runtime word. -/
def word : List Bool ↪ List Bool := Function.Embedding.refl _

private def bit : Bool ↪ List Bool :=
  ⟨fun b => [b], by intro a b h; simpa using h⟩

private def emptyWord : Empty ↪ List Bool := ⟨Empty.elim, fun a => Empty.elim a⟩

private def unitWord : Unit ↪ List Bool := ⟨fun _ => [], by intro a b _; cases a; cases b; rfl⟩

private def liftedWord : ULift.{1} (List Bool) ↪ List Bool :=
  ⟨ULift.down, by intro a b h; cases a; cases b; cases h; rfl⟩

/-- A real machine on arbitrary-length words can have zero cost/output degrees when it ignores
the input. This supplies an inhabited degree-zero witness for both encoding transports. -/
theorem zeroDegree : ComputableInDegree (fun _ : List Bool => []) word word 0 0 := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := word) (encOut := word) []
  exact ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩,
    DegreeBounded.const 0⟩

-- Empty domains, growing words, Type 1 input domains, and encoding transports.
example (n : ℕ) {α β γ : Type*} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} {f : α → β} {g : α → γ} {d e : ℕ}
    (hf : ComputableInDegree f input middle d e)
    (h : ∀ a, output (g a) = middle (f a)) :
    ComputableInDegree (fun _ : List Bool => []) word word 1 0 ∧
    ComputableInDegree (fun w : List Bool => w) word word 1 1 ∧
    (word (List.replicate n true)).length = n ∧
    ComputableInDegree Bool.not bit bit 1 0 ∧
    ComputableInDegree (Empty.elim : Empty → Empty) emptyWord emptyWord 1 0 ∧
    ComputableInDegree (fun _ : List Bool => ()) word unitWord 0 0 ∧
    ComputableInDegree (fun _ : ULift.{1} (List Bool) => []) liftedWord word 0 0 ∧
    ComputableInDegree g input output d e :=
  ⟨.const [], .of_eq fun _ => rfl, by simp [word], .of_finite Bool.not, .of_finite Empty.elim,
    zeroDegree.of_enc_eq fun _ => rfl, zeroDegree.of_encIn_eq ULift.down fun _ => rfl,
    hf.of_enc_eq h⟩

end ComplexityTests.Internal.DegreePrimitives
