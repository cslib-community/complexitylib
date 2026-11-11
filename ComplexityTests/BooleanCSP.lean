/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CSP.Basic

/-! Concrete syntax, satisfiability, and empty/nullary edge cases for fixed Boolean CSPs. -/

namespace ComplexityTests.BooleanCSP

open Cslib.Complexity Cslib.Logic.PL

private def unary : Bool → ℕ := fun _ => 1
private def pin (b : Bool) (vs : List Bool) : Bool := vs == [b]

-- Variable labels need not be dense or bounded by the number of constraints.
example : [(true, [2 ^ 80])] ∈ CSPSAT unary pin := by
  refine ⟨by decide, fun _ => true, ?_⟩
  decide

-- Opposite unary pins on the same variable are inconsistent.
example : [(true, [37]), (false, [37])] ∉ CSPSAT unary pin := by
  rintro ⟨_, σ, hσ⟩
  cases h : σ 37 <;> simp [CSP.eval, Constraint.eval, pin, h] at hσ

-- The arity guard rejects syntax even when an unconstrained list semantics would accept it.
example : [(true, [0, 1])] ∉ CSPSAT unary (fun _ _ => true) := by
  rintro ⟨h, _⟩
  have hw := h (true, [0, 1]) (by simp)
  norm_num [unary] at hw

-- Repeated variables occupy multiple positions; no distinctness restriction is imposed.
example : [((), [7, 7])] ∈ CSPSAT (fun _ : Unit => 2)
    (fun _ vs => vs == [true, true]) := by
  refine ⟨by decide, fun _ => true, ?_⟩
  decide

-- A nullary true relation is satisfied; a nullary false relation makes an instance false.
example : [((), [])] ∈ CSPSAT (fun _ : Unit => 0) (fun _ _ => true) := by
  exact ⟨by decide, fun _ => false, rfl⟩

example : [((), [])] ∉ CSPSAT (fun _ : Unit => 0) (fun _ _ => false) := by
  rintro ⟨_, σ, hσ⟩
  exact Bool.false_ne_true hσ

-- An empty relation of positive arity is handled by its actual false semantics.
example : [((), [0])] ∉ CSPSAT (fun _ : Unit => 1) (fun _ _ => false) := by
  rintro ⟨_, σ, hσ⟩
  exact Bool.false_ne_true hσ

-- The empty conjunction is valid and satisfiable for every language.
example {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    ([] : CSP Rel ℕ) ∈ CSPSAT arity sem := by
  exact ⟨by simp [CSP.WellFormed], fun _ => false, rfl⟩

-- Unary false does not preserve the true-pin relation.
example : ¬ CSP.HasPolymorphism unary pin (fun _ : Fin 1 → Bool => false) := by
  intro h
  have hp := h true (fun _ => fun _ => true) (by
    intro _
    change pin true (List.ofFn (fun _ : Fin 1 => true)) = true
    decide)
  change pin true (List.ofFn (fun _ : Fin 1 => false)) = true at hp
  norm_num [pin, List.ofFn_succ] at hp

-- Empty relations impose no condition on a unary constant polymorphism.
example : CSP.HasPolymorphism (fun _ : Unit => 1) (fun _ _ => false)
    (fun _ : Fin 1 → Bool => false) := by
  intro _ a ha
  exact (Bool.false_ne_true (ha 0)).elim

end ComplexityTests.BooleanCSP
