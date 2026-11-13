/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Polymorphism
import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Composition

/-! Ordinary semantic import, actual repeated scopes, false nullaries and nullary operations. -/

assert_not_exists Cslib.Complexity.Graph.RotationSystem

namespace CslibFrontierTests.CSPGadgetPolymorphism

open Cslib.Logic.PL Cslib.Logic.PL.CSP

private def arity (_ : Unit) := 2
private def sem (_ : Unit) (scope : List Bool) : Bool := decide (scope.getD 0 false =
  scope.getD 1 false)
private theorem common_and : HasPolymorphism arity sem (fun a : Fin 2 → Bool => a 0 && a 1) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
  decide +kernel

example : Cslib.Logic.IsPolymorphism (fun a : Fin 2 → Bool => a 0 && a 1)
    (booleanRelation arity sem ()) :=
  (PPGadget.atom (arity := arity) (sem := sem) ()).isPolymorphism common_and

example (a : Fin 2 → ℕ → Bool)
    (ha : ∀ j, CSP.eval sem (a j) ([⟨(), [7, 7]⟩, ⟨(), [7, 9]⟩] : CSP Unit ℕ) = true) :
    CSP.eval sem (fun i => a 0 i && a 1 i)
      ([⟨(), [7, 7]⟩, ⟨(), [7, 9]⟩] : CSP Unit ℕ) = true :=
  common_and.eval _ (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> rfl) a ha

-- A nullary operation is permitted when it really preserves the original unary-one symbol.
private def pinArity (_ : Unit) := 1
private def pinSem (_ : Unit) (scope : List Bool) := scope.getD 0 false
private theorem nullary_true : HasPolymorphism pinArity pinSem
    (fun _ : Fin 0 → Bool => true) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
  decide +kernel
example : Cslib.Logic.IsPolymorphism (fun _ : Fin 0 → Bool => true)
    (booleanRelation pinArity pinSem ()) :=
  (PPGadget.atom (arity := pinArity) (sem := pinSem) ()).isPolymorphism nullary_true
example : ¬HasPolymorphism pinArity pinSem (fun _ : Fin 0 → Bool => false) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
  decide +kernel

-- Positive-arity operations preserve an unsatisfiable false-nullary conjunction vacuously.
example (a : Fin 1 → ℕ → Bool)
    (ha : ∀ j, CSP.eval (fun _ _ => false) (a j) ([⟨(), []⟩] : CSP Unit ℕ) = true) :
    CSP.eval (fun _ _ => false) (fun i => !(a 0 i)) ([⟨(), []⟩] : CSP Unit ℕ) = true := by
  have h : HasPolymorphism (fun _ : Unit => 0) (fun _ _ => false)
      (fun a : Fin 1 → Bool => !(a 0)) := by
    unfold HasPolymorphism Cslib.Logic.IsPolymorphism booleanRelation
    decide +kernel
  exact h.eval _ (by
    intro c hc
    have he := List.mem_singleton.mp hc
    subst c
    rfl) a ha

end CslibFrontierTests.CSPGadgetPolymorphism
