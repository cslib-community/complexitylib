/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.CornerFaces

/-!
# Localizing face surgery to invariant dart sets

Component faces are a subset of the full orbit quotient, rather than separate geometric
outer faces. This module transports such subsets to the permutation restricted to their
invariant darts. In particular singleton cycles remain present in every count.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem.CornerFaces

open Equiv

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

private theorem predicate_swap [DecidableEq α] (p : α → Prop) (a b : α)
    (hab : p a ↔ p b) (x : α) : p (swap a b x) ↔ p x := by
  by_cases hxa : x = a
  · subst x; simpa only [swap_apply_left] using hab.symm
  · by_cases hxb : x = b
    · subst x; simpa only [swap_apply_right] using hab
    · rw [swap_apply_of_ne_of_ne hxa hxb]

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
  rw [predicate_swap (extendedPredicate p q) (some (some k)) none hk,
    predicate_swap (extendedPredicate p q) (some (some h)) (some none) hh, hf,
    predicate_swap (extendedPredicate p q) (some none) none Iff.rfl]

/-- When both new points are selected, the selected dart type is literally the old selected
set with two indexed ends adjoined. -/
@[expose] def selectedDartEquiv (p : α → Prop) :
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

private theorem coe_selectedDartEquiv (p : α → Prop) (z : Option (Option {a // p a})) :
    ((selectedDartEquiv p) z).val = Option.map (Option.map Subtype.val) z := by
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
    (selectedDartEquiv p).permCongr (splice (f.subtypePerm hp) ⟨h, hh⟩ ⟨k, hk⟩) =
      (splice f h k).subtypePerm
        (splice_preserves f p hp h k True (iff_true_intro hh) (iff_true_intro hk)) := by
  apply Equiv.ext
  intro z
  obtain ⟨z, rfl⟩ := (selectedDartEquiv p).surjective z
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  change ((selectedDartEquiv p) (splice (f.subtypePerm hp) ⟨h, hh⟩ ⟨k, hk⟩ z)).val =
    splice f h k ((selectedDartEquiv p) z).val
  rw [coe_selectedDartEquiv, coe_selectedDartEquiv]
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
    ← selected_splice_permCongr f p hp h k hh hk, CycleSplice.card_orbits_permCongr,
    card_orbits_splice_cofacial _ _ _ (Perm.sameCycle_subtypePerm.mpr hc),
    Nat.card_congr (subtypeOrbitEquiv f p hp)]

/-- Excluding both new ends leaves exactly the old selected darts. -/
@[expose] def unselectedDartEquiv (p : α → Prop) :
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
    (unselectedDartEquiv p).permCongr (f.subtypePerm hp) =
      (splice f h k).subtypePerm
        (splice_preserves f p hp h k False (iff_false_intro hh) (iff_false_intro hk)) := by
  apply Equiv.ext
  intro z
  obtain ⟨a, rfl⟩ := (unselectedDartEquiv p).surjective z
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
    ← unselected_splice_permCongr f p hp h k hh hk, CycleSplice.card_orbits_permCongr,
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

end Cslib.Complexity.Graph.RotationSystem.CornerFaces
