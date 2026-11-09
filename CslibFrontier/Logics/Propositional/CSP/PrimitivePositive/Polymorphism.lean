/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive
import Mathlib.Data.List.OfFn

/-!
# Polymorphism preservation by actual primitive-positive bodies

The existing common-polymorphism interface acts on satisfying assignments of each literal
wellformed CSP body, then on its existential auxiliary assignments. This original adapter
includes repeated variable positions, empty conjunctions, nullary constraints and nullary
operations. It is solely semantic: arbitrary primitive-positive definability supplies no
ordered boundary or planarity conclusion.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V J : Type*} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {f : (J → Bool) → Bool}

/-- A common polymorphism preserves satisfying assignments of an actual wellformed body.
Every scope is read at its declared arity; duplicate occurrences and nullaries remain literal. -/
theorem HasPolymorphism.eval (h : HasPolymorphism arity sem f) (F : CSP Rel V)
    (hw : WellFormed arity F) (a : J → V → Bool) (ha : ∀ j, F.eval sem (a j) = true) :
    F.eval sem (fun v => f (fun j => a j v)) = true := by
  simp only [CSP.eval, List.all_eq_true] at ha ⊢
  intro c hc
  let scope : Fin (arity c.1) → V := fun i => c.2[i.val]'(by have := hw c hc; omega)
  have hs : List.ofFn scope = c.2 := by
    apply List.ext_getElem
    · rw [List.length_ofFn]
      exact (hw c hc).symm
    · intro i hi hj
      simp only [List.getElem_ofFn, scope]
  have hin (j : J) : (fun i => a j (scope i)) ∈ booleanRelation arity sem c.1 := by
    change sem c.1 (List.ofFn (a j ∘ scope)) = true
    rw [← List.map_ofFn, hs]
    exact ha j c hc
  have hout := h c.1 (fun j i => a j (scope i)) hin
  change sem c.1 (c.2.map (fun v => f (fun j => a j v))) = true
  rw [← hs, List.map_ofFn]
  exact hout

/-- Every actual primitive-positive gadget preserves the language's common polymorphisms.
This forward semantic fact includes nullary operations and makes no boundary assertion. -/
theorem PPGadget.isPolymorphism {Rel : Type} {arity : Rel → ℕ}
    {sem : Rel → List Bool → Bool} {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (h : HasPolymorphism arity sem f) : IsPolymorphism f R := by
  classical
  intro a ha
  choose b hb using fun j => (g.correct (a j)).mp (ha j)
  apply (g.correct _).mpr
  refine ⟨fun i => f (fun j => b j i), ?_⟩
  have he : Sum.elim (fun i => f (fun j => a j i)) (fun i => f (fun j => b j i)) =
      fun v => f (fun j => Sum.elim (a j) (b j) v) := by
    funext v
    cases v <;> rfl
  rw [he]
  exact h.eval g.body g.wellFormed (fun j => Sum.elim (a j) (b j)) hb

end Cslib.Logic.PL.CSP
