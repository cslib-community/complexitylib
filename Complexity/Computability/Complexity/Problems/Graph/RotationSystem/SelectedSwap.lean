/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.ComponentSplice
import Complexity.Foundations.GroupTheory.Perm.InvariantPredicate

/-!
# Local face counts for incoming successor swaps

A cofacial vertex identification swaps two distinct incoming face successors. On an invariant
selection, this adds one face exactly when the selected component contains the two corners.
All orbit classes, including fixed points, remain counted. No Euler count is assumed here.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem.CornerFaces

open Equiv CycleSplice

variable {α : Type} [Finite α] [DecidableEq α]

open Classical in
/-- An incoming swap at distinct cofacial points adds one selected orbit in their invariant
component, and retains every selected orbit outside that component. -/
theorem card_orbitOn_swap_mul (f : Perm α) (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a)
    (h k : α) (hne : h ≠ k) (hc : f.SameCycle h k) :
    Nat.card (OrbitOn (swap h k * f) p) = Nat.card (OrbitOn f p) + if p h then 1 else 0 := by
  have hm : p h ↔ p k := Iff.of_eq (Perm.sameCycle_one.mp (hc.map_of_semiconj
    (show Function.Semiconj p f (1 : Perm Prop) from fun a => propext (hp a))))
  let hp' : ∀ a, p ((swap h k * f) a) ↔ p a := fun a =>
    (Equiv.predicate_swap p h k hm (f a)).trans (hp a)
  rw [← Nat.card_congr (subtypeOrbitEquiv (swap h k * f) p hp')]
  by_cases hh : p h
  · have hk := hm.mp hh
    let h' : {a // p a} := ⟨h, hh⟩
    let k' : {a // p a} := ⟨k, hk⟩
    have he : (swap h k * f).subtypePerm hp' = swap h' k' * f.subtypePerm hp := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change swap h k (f a.val) = (swap h' k' (f.subtypePerm hp a)).val
      exact (Subtype.val_injective.map_swap h' k' (f.subtypePerm hp a)).symm
    rw [he]
    have h₁ := (card_orbits_swap_mul (f.subtypePerm hp) h' k'
      (fun he => hne (congrArg Subtype.val he))).1 (Perm.sameCycle_subtypePerm.mpr hc)
    rw [h₁, Nat.card_congr (subtypeOrbitEquiv f p hp)]
    simp only [hh, ite_true]
  · have hk : ¬ p k := fun hk => hh (hm.mpr hk)
    have he : (swap h k * f).subtypePerm hp' = f.subtypePerm hp := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change swap h k (f a.val) = f a.val
      exact swap_apply_of_ne_of_ne
        (fun he => hh (he ▸ (hp a.val).mpr a.property))
        (fun he => hk (he ▸ (hp a.val).mpr a.property))
    rw [he, Nat.card_congr (subtypeOrbitEquiv f p hp)]
    simp only [hh, ite_false, Nat.add_zero]

end Cslib.Complexity.Graph.RotationSystem.CornerFaces
