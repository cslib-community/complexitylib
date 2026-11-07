/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Operator.Polarity

/-!
# Blocks of quantifiers in operator formulas

`Formula.exs` binds a finite tuple of fresh first-order variables. Its semantics, formation
check, and polarity check reduce to those of its body. This supplies the quantifier blocks
needed when pulling fixed-point formulas back along tuple interpretations.
-/

public section

universe u v w z s

open FirstOrder Language

namespace Cslib.Logic.FO.Operator.Formula

variable {L : Language.{u, v}} {O : Type s} {shape : O → Shape}
  {Γ : List ℕ} {α : Type w}

/-- Bind all variables in the right summand, in increasing coordinate order. -/
@[expose] def exs : {α : Type w} → (n : ℕ) →
    Formula L shape Γ (α ⊕ Fin n) → Formula L shape Γ α
  | _, 0, φ => φ.relabel (Sum.elim id Fin.elim0)
  | _, n + 1, φ => .ex (exs n (φ.relabel (Sum.elim
      (fun a => Sum.inl (some a))
      (Fin.cases (Sum.inl none) Sum.inr))))

/-- A block of existential quantifiers chooses one complete tuple. -/
@[simp, fo_realize] theorem realize_exs {M : Type z} [L.Structure M]
    (I : Interpretation shape M) (n : ℕ) (φ : Formula L shape Γ (α ⊕ Fin n))
    (ρ : RelEnv Γ M) (v : α → M) :
    (φ.exs n).Realize I ρ v ↔ ∃ xs, φ.Realize I ρ (Sum.elim v xs) := by
  induction n generalizing α with
  | zero =>
    simp only [exs, realize_relabel]
    constructor
    · intro h
      refine ⟨Fin.elim0, ?_⟩
      convert h using 1
      funext y
      cases y with
      | inl a => rfl
      | inr i => exact i.elim0
    · rintro ⟨xs, h⟩
      convert h using 1
      funext y
      cases y with
      | inl a => rfl
      | inr i => exact i.elim0
  | succ n ih =>
    simp only [exs, realize_ex, ih, realize_relabel]
    constructor
    · rintro ⟨x, xs, h⟩
      refine ⟨Fin.cons x xs, ?_⟩
      convert h using 1
      funext y
      cases y with
      | inl a => rfl
      | inr i => exact Fin.cases rfl (fun _ => rfl) i
    · rintro ⟨xs, h⟩
      refine ⟨xs 0, Fin.tail xs, ?_⟩
      convert h using 1
      funext y
      cases y with
      | inl a => rfl
      | inr i => exact Fin.cases rfl (fun _ => rfl) i

/-- Quantifying a tuple leaves the formation check unchanged. -/
@[simp] theorem wellFormed_exs (policy : Policy shape) (n : ℕ)
    (φ : Formula L shape Γ (α ⊕ Fin n)) :
    (φ.exs n).wellFormed policy = φ.wellFormed policy := by
  induction n generalizing α with
  | zero => simp [exs]
  | succ n ih => simp only [exs, wellFormed, ih, wellFormed_relabel]

/-- Quantifying a tuple leaves dependence on scoped relations unchanged. -/
@[simp] theorem checkPolarity_exs (variance : Variances shape) (n : ℕ)
    (φ : Formula L shape Γ (α ⊕ Fin n)) (sign : Bool) (mark : Marking Γ) :
    (φ.exs n).checkPolarity variance sign mark = φ.checkPolarity variance sign mark := by
  induction n generalizing α with
  | zero => simp [exs]
  | succ n ih => simp only [exs, checkPolarity, ih, checkPolarity_relabel]

end Cslib.Logic.FO.Operator.Formula
