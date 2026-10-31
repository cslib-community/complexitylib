/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

module
-- upstream: local-only (independent comparator statements)

public import Mathlib.Data.Set.Operations
public import Cslib.Computability.Circuit.Complexity

/-!
# Independently stated reduction and circuit contracts

The reduction claim is expanded into membership-preserving maps. The circuit claim uses the
pinned upstream CSLib minimum gate count over a complete interpreted signature. This module
imports no complexitylib proof, definition or custom syntax.
-/

@[expose] public section

namespace ComplexityComparator.Basic

/-- Membership-preserving admissible maps compose when admissibility is closed under composition. -/
def ManyOneTrans.{u, v, w} : Prop :=
  ∀ {α : Type u} {β : Type v} {γ : Type w},
    ∀ (Good₁ : (α → β) → Prop) (Good₂ : (β → γ) → Prop) (Good₃ : (α → γ) → Prop),
    ∀ (A : Set α) (B : Set β) (C : Set γ),
    (∀ (f : α → β) (g : β → γ), Good₁ f → Good₂ g → Good₃ (fun a => g (f a))) →
    (∃ f : α → β, Good₁ f ∧ ∀ a, a ∈ A ↔ f a ∈ B) →
    (∃ g : β → γ, Good₂ g ∧ ∀ b, b ∈ B ↔ g b ∈ C) →
    ∃ h : α → γ, Good₃ h ∧ ∀ a, a ∈ A ↔ h a ∈ C

/-- A function unequal to every coordinate projection requires at least one circuit gate. -/
def NonprojectionNeedsGate.{u, s} : Prop :=
  ∀ {σ : Cslib.Circuits.Signature.{s}} {U : Type u},
    ∀ (I : Cslib.Circuits.Interpretation σ U),
    ∀ [Cslib.Circuits.Interpretation.IsComplete I],
    ∀ (n : Nat) (f : (Fin n → U) → U),
    (∀ i : Fin n, f ≠ fun x => x i) →
    Nat.le 1 (Cslib.Circuits.complexity I (fun x (_ : Fin 1) => f x))

end ComplexityComparator.Basic
