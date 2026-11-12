/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure
public import CslibFrontier.Logics.FirstOrder.Operator.Quantifiers

/-!
# Positive occurrences of transitive closure

`TC.Positive φ s` holds when every closure operator of `φ` occurs at polarity `true` when `φ`
itself occurs at polarity `s`, with negation flipping the polarity. Sentences with
`TC.Positive φ true` form the FO(positive TC) fragment of [Immerman1987], Section 3, written
with negations pushed through by polarity: a closure may occur under an even number of
negations. `TC.width φ` is the largest tuple width of a closure in `φ`.

This is a polarity of closure operators. It is unrelated to the polarity of relation variables
checked by `Operator.Formula.checkPolarity`.

## Main definitions

* `Cslib.Logic.FO.TC.Positive`: closures occur positively.
* `Cslib.Logic.FO.TC.width`: the largest closure tuple width.

## Main results

* `Cslib.Logic.FO.TC.positive_relabel`, `Cslib.Logic.FO.TC.positive_exs`: renaming free
  variables and quantifying a block of them preserve closure polarity.

## References

* [N. Immerman, *Languages That Capture Complexity Classes*, Section 3][Immerman1987]
-/

public section

universe u v w

open FirstOrder Language

namespace Cslib.Logic.FO.TC

open Operator

variable {L : Language.{u, v}}

/-- `Positive φ s`: every closure operator of `φ` occurs at the polarity `true` when `φ` itself
occurs at polarity `s`; negation flips the polarity. -/
@[expose] def Positive : {Γ : List ℕ} → {α : Type w} → Formula L shape Γ α → Bool → Prop
  | _, _, .ofFO _, _ => True
  | _, _, .rel _ _, _ => True
  | _, _, .neg φ, s => Positive φ (!s)
  | _, _, .conj φ ψ, s => Positive φ s ∧ Positive ψ s
  | _, _, .ex φ, s => Positive φ s
  | _, _, .op _ body _, s => s = true ∧ Positive (body ⟨0, Nat.one_pos⟩) true

/-- The largest width of a closure operator in a formula. -/
@[expose] def width : {Γ : List ℕ} → {α : Type w} → Formula L shape Γ α → ℕ
  | _, _, .ofFO _ => 0
  | _, _, .rel _ _ => 0
  | _, _, .neg φ => width φ
  | _, _, .conj φ ψ => max (width φ) (width ψ)
  | _, _, .ex φ => width φ
  | _, _, .op k body _ => max k (width (body ⟨0, Nat.one_pos⟩))

/-- Renaming free variables does not change the polarity of closure operators. -/
@[simp] theorem positive_relabel {Γ : List ℕ} {α β : Type w} (g : α → β)
    (φ : Formula L shape Γ α) (s : Bool) : Positive (φ.relabel g) s ↔ Positive φ s := by
  induction φ generalizing β s with
  | ofFO _ => exact Iff.rfl
  | rel _ _ => exact Iff.rfl
  | neg φ ih => exact ih g (!s)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ g s) (ihψ g s)
  | ex φ ih => exact ih (Option.map g) s
  | op k body args ih => exact and_congr Iff.rfl (ih ⟨0, Nat.one_pos⟩ (Sum.map g id) true)

/-- Quantifying a block of variables does not change the polarity of closure operators. -/
@[simp] theorem positive_exs {Γ : List ℕ} {α : Type w} (n : ℕ)
    (φ : Formula L shape Γ (α ⊕ Fin n)) (s : Bool) : Positive (φ.exs n) s ↔ Positive φ s := by
  induction n generalizing α with
  | zero => exact positive_relabel _ φ s
  | succ n ih => exact (ih _).trans (positive_relabel _ φ s)

end Cslib.Logic.FO.TC
