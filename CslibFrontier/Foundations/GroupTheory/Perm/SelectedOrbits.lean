/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Cycle)

public import CslibFrontier.Foundations.GroupTheory.Perm.CycleSurgery
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate

/-!
# Complete permutation orbits on invariant subsets

`Equiv.Perm.SelectedOrbits.OrbitOn` selects complete orbit classes meeting an invariant
subset. Subtype and coordinate equivalences localize the counts, including singleton
cycles. Exact splice and incoming-swap counts require no graph or genus assumptions.
-/

public section

namespace Equiv.Perm.SelectedOrbits

open Equiv CycleSurgery

variable {α : Type}

/-- Actual orbit classes with a representative in the selected invariant dart set. -/
abbrev OrbitOn (f : Perm α) (p : α → Prop) :=
  {q : Quotient (Perm.SameCycle.setoid f) // ∃ a, p a ∧ Quotient.mk _ a = q}

/-- Restriction to invariant darts identifies exactly the selected original orbit classes. -/
noncomputable def subtypeOrbitEquiv (f : Perm α) (p : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) :
    Quotient (Perm.SameCycle.setoid (f.subtypePerm hp)) ≃ OrbitOn f p :=
  Equiv.ofBijective (fun q => ⟨Quotient.map Subtype.val (fun _ _ h =>
    Perm.sameCycle_subtypePerm.mp h) q,
    Quotient.inductionOn q (fun a => ⟨a.val, a.property, rfl⟩)⟩) (by
      constructor
      · intro q r he
        induction q using Quotient.inductionOn with
        | h a =>
          induction r using Quotient.inductionOn with
          | h b =>
            exact Quotient.sound (Perm.sameCycle_subtypePerm.mpr
              (Quotient.exact (congrArg Subtype.val he)))
      · rintro ⟨q, a, ha, he⟩
        exact ⟨Quotient.mk _ ⟨a, ha⟩, Subtype.ext he⟩)

/-- Include both new indexed ends in a selected component exactly when `newPoints` holds. -/
@[expose] def extendedPredicate (p : α → Prop) (newPoints : Prop) :
    Option (Option α) → Prop
  | none => newPoints
  | some none => newPoints
  | some (some a) => p a

/-- A splice retains an invariant dart selection when its two corners agree on membership. -/
theorem splice_preserves [DecidableEq α] (f : Perm α) (p : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (h k : α) (q : Prop)
    (hh : p h ↔ q) (hk : p k ↔ q) :
    ∀ z, extendedPredicate p q (splice f h k z) ↔ extendedPredicate p q z := by
  intro z
  have hf : ∀ z, extendedPredicate p q (f.optionCongr.optionCongr z) ↔
      extendedPredicate p q z := by
    rintro (_ | (_ | a))
    · rfl
    · rfl
    · exact hp a
  change extendedPredicate p q
    (swap (some (some k)) none (swap (some (some h)) (some none)
      (f.optionCongr.optionCongr (swap (some none) none z)))) ↔ _
  rw [Equiv.predicate_swap (extendedPredicate p q) (some (some k)) none hk,
    Equiv.predicate_swap (extendedPredicate p q) (some (some h)) (some none) hh, hf,
    Equiv.predicate_swap (extendedPredicate p q) (some none) none Iff.rfl]

/-- When both new points are selected, the selected dart type is literally the old selected
set with two indexed ends adjoined. -/
@[expose] def selectedPointEquiv (p : α → Prop) :
    Option (Option {a // p a}) ≃ {z // extendedPredicate p True z} where
  toFun z := match z with
    | none => ⟨none, True.intro⟩
    | some none => ⟨some none, True.intro⟩
    | some (some a) => ⟨some (some a.val), a.property⟩
  invFun z := match z with
    | ⟨none, _⟩ => none
    | ⟨some none, _⟩ => some none
    | ⟨some (some a), ha⟩ => some (some ⟨a, ha⟩)
  left_inv := by rintro (_ | (_ | a)) <;> rfl
  right_inv := by rintro ⟨_ | (_ | a), ha⟩ <;> rfl

private theorem coe_selectedPointEquiv (p : α → Prop) (z : Option (Option {a // p a})) :
    ((selectedPointEquiv p) z).val = Option.map (Option.map Subtype.val) z := by
  rcases z with _ | (_ | a) <;> rfl

private theorem map_splice {β : Type} [DecidableEq α] [DecidableEq β]
    (u : α → β) (hu : Function.Injective u) (f : Perm α) (g : Perm β)
    (hm : ∀ a, u (f a) = g (u a)) (h k : α) (z : Option (Option α)) :
    Option.map (Option.map u) (splice f h k z) =
      splice g (u h) (u k) (Option.map (Option.map u) z) := by
  let v := Option.map (Option.map u)
  have hv : Function.Injective v := Option.map_injective (Option.map_injective hu)
  have hf : ∀ z, v (f.optionCongr.optionCongr z) = g.optionCongr.optionCongr (v z) := by
    rintro (_ | (_ | a))
    · rfl
    · rfl
    · exact congrArg (some ∘ some) (hm a)
  change v (splice f h k z) = splice g (u h) (u k) (v z)
  simp only [splice, Perm.coe_mul, Function.comp_apply]
  rw [hv.map_swap, hv.map_swap, hf, hv.map_swap]
  rfl

/-- Splice restriction when both corners belong to the selected invariant component. -/
theorem selected_splice_permCongr [DecidableEq α] (f : Perm α) (p : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (h k : α) (hh : p h) (hk : p k) :
    (selectedPointEquiv p).permCongr (splice (f.subtypePerm hp) ⟨h, hh⟩ ⟨k, hk⟩) =
      (splice f h k).subtypePerm
        (splice_preserves f p hp h k True (iff_true_intro hh) (iff_true_intro hk)) := by
  apply Equiv.ext
  intro z
  obtain ⟨z, rfl⟩ := (selectedPointEquiv p).surjective z
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  change ((selectedPointEquiv p) (splice (f.subtypePerm hp) ⟨h, hh⟩ ⟨k, hk⟩ z)).val =
    splice f h k ((selectedPointEquiv p) z).val
  rw [coe_selectedPointEquiv, coe_selectedPointEquiv]
  exact map_splice Subtype.val Subtype.val_injective (f.subtypePerm hp) f
    (fun _ => rfl) ⟨h, hh⟩ ⟨k, hk⟩ z

/-- Within the selected component, cofacial insertion adds one actual face class. -/
theorem card_orbitOn_splice_selected [Finite α] [DecidableEq α] (f : Perm α) (p : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (h k : α) (hh : p h) (hk : p k)
    (hc : f.SameCycle h k) :
    Nat.card (OrbitOn (splice f h k) (extendedPredicate p True)) =
      Nat.card (OrbitOn f p) + 1 := by
  let hp' := splice_preserves f p hp h k True (iff_true_intro hh) (iff_true_intro hk)
  rw [← Nat.card_congr (subtypeOrbitEquiv (splice f h k) _ hp'),
    ← selected_splice_permCongr f p hp h k hh hk, CycleSurgery.card_orbits_permCongr,
    card_orbits_splice_sameCycle _ _ _ (Perm.sameCycle_subtypePerm.mpr hc),
    Nat.card_congr (subtypeOrbitEquiv f p hp)]

/-- Excluding both new ends leaves exactly the old selected darts. -/
@[expose] def unselectedPointEquiv (p : α → Prop) :
    {a // p a} ≃ {z // extendedPredicate p False z} where
  toFun a := ⟨some (some a.val), a.property⟩
  invFun z := match z with
    | ⟨none, h⟩ => False.elim h
    | ⟨some none, h⟩ => False.elim h
    | ⟨some (some a), ha⟩ => ⟨a, ha⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨_ | (_ | a), ha⟩
    · exact False.elim ha
    · exact False.elim ha
    · rfl

/-- A component disjoint from the splice corners retains its literal restricted rotation. -/
theorem unselected_splice_permCongr [DecidableEq α] (f : Perm α) (p : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (h k : α) (hh : ¬ p h) (hk : ¬ p k) :
    (unselectedPointEquiv p).permCongr (f.subtypePerm hp) =
      (splice f h k).subtypePerm
        (splice_preserves f p hp h k False (iff_false_intro hh) (iff_false_intro hk)) := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (unselectedPointEquiv p).surjective z
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  have hfh : f a.val ≠ h := fun he => hh (he ▸ (hp a.val).mpr a.property)
  have hfk : f a.val ≠ k := fun he => hk (he ▸ (hp a.val).mpr a.property)
  change some (some (f a.val)) = splice f h k (some (some a.val))
  simp [splice, swap_apply_def, hfh, hfk]

/-- Faces in every component disjoint from the corners are unchanged, including singleton
faces and the empty set of dart faces at a declared point component. -/
theorem card_orbitOn_splice_unselected [Finite α] [DecidableEq α] (f : Perm α)
    (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a) (h k : α) (hh : ¬ p h) (hk : ¬ p k) :
    Nat.card (OrbitOn (splice f h k) (extendedPredicate p False)) =
      Nat.card (OrbitOn f p) := by
  let hp' := splice_preserves f p hp h k False (iff_false_intro hh) (iff_false_intro hk)
  rw [← Nat.card_congr (subtypeOrbitEquiv (splice f h k) _ hp'),
    ← unselected_splice_permCongr f p hp h k hh hk, CycleSurgery.card_orbits_permCongr,
    Nat.card_congr (subtypeOrbitEquiv f p hp)]

open Classical in
/-- Exact local face count for a cofacial splice in any invariant selection. -/
theorem card_orbitOn_splice [Finite α] [DecidableEq α] (f : Perm α)
    (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a) (h k : α)
    (hm : p h ↔ p k) (hc : f.SameCycle h k) :
    Nat.card (OrbitOn (splice f h k) (extendedPredicate p (p h))) =
      Nat.card (OrbitOn f p) + if p h then 1 else 0 := by
  classical
  by_cases hh : p h
  · simpa only [hh, ite_true] using
      card_orbitOn_splice_selected f p hp h k hh (hm.mp hh) hc
  · simpa only [hh, ite_false, Nat.add_zero] using
      card_orbitOn_splice_unselected f p hp h k hh (fun hk => hh (hm.mpr hk))

/-- Coordinate transport preserves the selected original orbit classes. -/
noncomputable def orbitOnEquiv {β : Type} [Finite α] [Finite β]
    (e : α ≃ β) (f : Perm α) (g : Perm β) (hm : ∀ a, e (f a) = g (e a))
    (p : α → Prop) (q : β → Prop) (hp : ∀ a, p a ↔ q (e a)) :
    OrbitOn f p ≃ OrbitOn g q :=
  let eq := Quotient.congr e (fun a b => (Perm.sameCycle_equiv_iff e f g hm a b).symm)
  Equiv.subtypeEquiv eq (by
    intro z
    constructor
    · rintro ⟨a, ha, he⟩
      exact ⟨e a, (hp a).mp ha, congrArg eq he⟩
    · rintro ⟨b, hb, he⟩
      refine ⟨e.symm b, (hp _).mpr (by simpa only [e.apply_symm_apply] using hb), ?_⟩
      apply eq.injective
      change Quotient.mk _ (e (e.symm b)) = eq z
      simpa only [e.apply_symm_apply] using he)

variable [Finite α] [DecidableEq α]

open Classical in
/-- An incoming swap at distinct same-cycle points adds one selected orbit in their invariant
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

end Equiv.Perm.SelectedOrbits
