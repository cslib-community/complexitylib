/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition

/-! # Direct plain core contracts without the higher tidy calculus -/

open Turing.MultiTapeTM

run_elab do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← Lean.getEnv).contains name then
      throwError "unexpected higher tidy calculus: {name}"

section Projections
universe u
variable {α β : Type u} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
variable (enc : α × β ↪ List Bool) [PairEncoding encA encB enc]

-- Explicit generic certificates retain arbitrary encoding instances, including their other
-- component encoding, which is not inferable from an opaque input encoding alone.
example :
    ComputableInPolyTime (fun p : α × β => p.1) enc encA ∧
    ComputableInPolyTime (fun p : α × β => p.2) enc encB ∧
    ComputableInPolyTime (fun p : α × β => p.1) enc encA ∧
    ComputableInPolyTime (fun p : α × β => p.1) (encPair encA encB) encA ∧
    ComputableInPolyTime (fun p : α × β => p.2) (encPair encA encB) encB := by
  have hf : ComputableInPolyTime (fun p : α × β => p.1) enc encA :=
    PairEncoding.computableInPolyTime_fst (enc₂ := encB)
  exact ⟨PairEncoding.computableInPolyTime_fst (enc₂ := encB),
    PairEncoding.computableInPolyTime_snd (enc₁ := encA),
    by fun_prop, ComputableInPolyTime.fst encA encB, by fun_prop⟩
end Projections

-- The constructor and projections compose on an actual finite encoding, without a raw bridge.
example :
    ComputableInPolyTime (fun b : Bool => (b, !b)) encBool (encPair encBool encBool) ∧
    ComputableInPolyTime (fun b : Bool => if b then !b else b) encBool encBool :=
  ⟨by fun_prop, by fun_prop⟩

section Resources
variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {f : β → γ} {g : α → β}

-- The degree witness comes from the same polynomial-time machine, at unrelated universes, and the
-- output exponent is independent of the cost/workspace exponent.
example (h : ComputableInPolyTime g encA encB)
    {d₁ e₁ d₂ e₂ : ℕ} (hf : ComputableInDegree f encB encC d₂ e₂)
    (hg : ComputableInDegree g encA encB d₁ e₁)
    (hf₀ : ComputableInDegree f encB encC 0 0)
    (hg₀ : ComputableInDegree g encA encB 0 0)
    {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hfO : ComputableInO f encB encC T₂ S₂) (hgO : ComputableInO g encA encB T₁ S₁) :
    (∃ d e, ComputableInDegree g encA encB d e) ∧
    ComputableInDegree (fun a => f (g a)) encA encC (max d₁ (e₁ * d₂)) (e₁ * e₂) ∧
    ComputableInDegree (fun a => f (g a)) encA encC 0 0 ∧
    ComputableInO (fun a => f (g a)) encA encC (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) :=
  ⟨h.exists_degree, hf.comp hg, hf₀.comp hg₀, hfO.comp hgO⟩
end Resources

-- The ordinary word interfaces work on every input, including malformed frames, and XOR,
-- conjunction, and branching require all their callback certificates.
example {α β : Type} {input : α ↪ List Bool} {word _unknown : α → List Bool}
    (hword : ComputableInPolyTime word input encBits)
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {left right _right : α → Bool}
    (hl : ComputableInPolyTime left encA encBool)
    (hr : ComputableInPolyTime right encA encBool)
    {pLeft pRight : α → Prop} [∀ a, Decidable (pLeft a)] [∀ a, Decidable (pRight a)]
    (hpl : ComputableInPolyTime (fun a => decide (pLeft a)) encA encBool)
    (hpr : ComputableInPolyTime (fun a => decide (pRight a)) encA encBool)
    {condition _ucond : α → Prop} [∀ a, Decidable (condition a)] [∀ a, Decidable (_ucond a)]
    {yes no : α → β}
    (hc : ComputableInPolyTime (fun a => decide (condition a)) encA encBool)
    (hy : ComputableInPolyTime yes encA encB) (hn : ComputableInPolyTime no encA encB) :
    unframe ([] : List Bool) = [] ∧
    unframe [true] = [] ∧
    dropFrame [true] = [] ∧
    dropFrame [false, true] = [true] ∧
    ComputableInPolyTime (fun a => (frame (word a), unframe (word a), dropFrame (word a)))
      input (encPair encBits (encPair encBits encBits)) ∧
    ComputableInPolyTime (fun a => left a ^^ right a) encA encBool ∧
    ComputableInPolyTime (fun a => decide (pLeft a ∧ pRight a)) encA encBool ∧
    ComputableInPolyTime (fun a => if condition a then yes a else no a) encA encB := by
  fail_if_success
    have : ComputableInPolyTime (fun a => unframe (_unknown a)) input encBits := by fun_prop
  fail_if_success
    have : ComputableInPolyTime (fun a => left a ^^ _right a) encA encBool := by fun_prop
  fail_if_success
    have : ComputableInPolyTime (fun a => if _ucond a then yes a else no a) encA encB := by
      fun_prop
  exact ⟨rfl, rfl, rfl, rfl, by fun_prop, by fun_prop, by fun_prop, by fun_prop⟩
