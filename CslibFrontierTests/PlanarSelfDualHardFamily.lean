/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

-- upstream: candidate

import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Crossover
import CslibFrontier.Logics.Propositional.CSP.Planar.Normalization

/-! The selfdual bad-difference hypotheses are inhabited by Γ={NAE3,CROSS}. -/

namespace CslibFrontierTests.PlanarSelfDualHardFamily

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.BitString

private def arity (r : Bool) : ℕ := if r then 4 else 3
private def sem (r : Bool) (scope : List Bool) : Bool :=
  if r then decide (scope.getD 0 false = scope.getD 2 false ∧
      scope.getD 1 false = scope.getD 3 false)
  else decide (scope.count true ≠ 0 ∧ scope.count true ≠ 3)

private instance (r : Bool) : DecidablePred (· ∈ booleanRelation arity sem r) := fun x =>
  inferInstanceAs (Decidable (sem r (List.ofFn x) = true))

example : HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0)) := by
  unfold HasPolymorphism Cslib.Logic.IsPolymorphism
  decide +kernel

example : ¬ HasSchaeferPolymorphism arity sem := by
  intro h
  rcases h with h | h | h | h | h | h
  · have hh := h false (fun _ => ![true, false, false]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h false (fun _ => ![true, false, false]) (by intro j; rfl)
    exact Bool.false_ne_true hh
  · have hh := h false ![![true, false, false], ![false, true, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h false ![![true, false, false], ![false, true, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h false
      ![![true, false, false], ![false, true, false], ![false, false, true]] (by decide)
    exact Bool.false_ne_true hh
  · have hh := h false
      ![![true, false, false], ![false, true, false], ![true, true, false]] (by decide)
    exact Bool.false_ne_true hh

example : booleanRelation arity sem true = cross := by
  ext a
  simp [booleanRelation, arity, sem, cross, List.ofFn_succ]

private theorem cyclicCross (x : Fin 4 → Bool) :
    x ∈ cyclicDifferenceRelation cross ↔ x = (fun _ => false) ∨ x = (fun _ => true) := by
  unfold cyclicDifferenceRelation
  change (∃ y : Fin 4 → Bool, (y 0 = y 2 ∧ y 1 = y 3) ∧ cyclicDifference y = x) ↔ _
  revert x
  decide +kernel

example : cross.Nonempty := ⟨fun _ => false, by decide⟩

example : ¬ IsEvenDeltaMatroid (cyclicDifferenceRelation cross) := by
  intro h
  have hzero := (cyclicCross (fun _ => false)).mpr (Or.inl rfl)
  have hone := (cyclicCross (fun _ => true)).mpr (Or.inr rfl)
  obtain ⟨j, _, hj⟩ := h.isDeltaMatroid.exchange hzero hone (i := 0) (by decide)
  have hn : ∀ j : Fin 4, flipOn {0, j} (fun _ => false) ∉ cyclicDifferenceRelation cross := by
    intro j
    rw [cyclicCross]
    revert j
    decide +kernel
  exact hn j hj

end CslibFrontierTests.PlanarSelfDualHardFamily
