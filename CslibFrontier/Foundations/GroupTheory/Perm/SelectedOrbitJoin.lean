/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate (Mathlib GroupTheory/Perm/Cycle)

public import CslibFrontier.Foundations.GroupTheory.Perm.SelectedOrbits
import CslibFrontier.Foundations.GroupTheory.Perm.InvariantPredicate
import Mathlib.Logic.Embedding.Set

/-!
# Joining selected complete permutation orbits

Disjoint predicates, one invariant, select disjoint sets of complete orbits. Their union
has the sum of their cardinalities. A transposition joining two different cycles removes
one selected orbit exactly when its corners are selected. Fixed points and empty selections
are included. Incoming and outgoing successor conventions are both explicit.
-/

public section

namespace Equiv.Perm.SelectedOrbits

open Equiv CycleSurgery

/-- The complete orbits selected by disjoint predicates, the first invariant, are exactly
the disjoint sum of the two selected orbit sets, including singleton cycles. -/
noncomputable def orbitOnUnionEquiv {α : Type} [Finite α] (f : Perm α) (p q : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (hd : _root_.Disjoint p q) :
    OrbitOn f (fun a => p a ∨ q a) ≃ OrbitOn f p ⊕ OrbitOn f q := by
  classical
  let u (z : Quotient (Perm.SameCycle.setoid f)) := ∃ a, p a ∧ Quotient.mk _ a = z
  let v (z : Quotient (Perm.SameCycle.setoid f)) := ∃ a, q a ∧ Quotient.mk _ a = z
  have huv : _root_.Disjoint u v := by
    intro t ht hs z hz
    obtain ⟨a, ha, he⟩ := ht z hz
    obtain ⟨b, hb, he'⟩ := hs z hz
    have hcycle := (Quotient.exact (he.trans he'.symm) : f.SameCycle a b)
    have hm : Function.Semiconj p f (1 : Perm Prop) := fun a => propext (hp a)
    have hab := Perm.sameCycle_one.mp (hcycle.map_of_semiconj hm)
    exact hd.le_bot b ⟨hab ▸ ha, hb⟩
  let e : OrbitOn f (fun a => p a ∨ q a) ≃ {z // u z ∨ v z} :=
    Equiv.subtypeEquivRight (fun z => by
      constructor
      · rintro ⟨a, ha | ha, he⟩
        · exact Or.inl ⟨a, ha, he⟩
        · exact Or.inr ⟨a, ha, he⟩
      · rintro (⟨a, ha, he⟩ | ⟨a, ha, he⟩)
        · exact ⟨a, Or.inl ha, he⟩
        · exact ⟨a, Or.inr ha, he⟩)
  exact e.trans (subtypeOrEquiv u v huv)

/-- The disjoint union of invariant selections adds their complete orbit counts. Only the
first predicate needs invariance to exclude a shared orbit. The other may select partial
representatives, because `OrbitOn` itself selects their complete equivalence classes. -/
theorem card_orbitOn_union {α : Type} [Finite α] (f : Perm α) (p q : α → Prop)
    (hp : ∀ a, p (f a) ↔ p a) (hd : _root_.Disjoint p q) :
    Nat.card (OrbitOn f (fun a => p a ∨ q a)) =
      Nat.card (OrbitOn f p) + Nat.card (OrbitOn f q) :=
  (Nat.card_congr (orbitOnUnionEquiv f p q hp hd)).trans Nat.card_sum

open Classical in
private theorem card_orbitOn_swap_join {α : Type} [Finite α] [DecidableEq α]
    (f : Perm α) (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a)
    (h k : α) (hm : p h ↔ p k) (hc : ¬ f.SameCycle h k) (incoming : Bool) :
    Nat.card (OrbitOn (if incoming then swap h k * f else f * swap h k) p) +
      (if p h then 1 else 0) = Nat.card (OrbitOn f p) := by
  classical
  have hne : h ≠ k := fun he => hc (he ▸ Perm.SameCycle.rfl)
  have hs (a : α) : p (swap h k a) ↔ p a := Equiv.predicate_swap p h k hm a
  have hp' : ∀ a, p ((if incoming then swap h k * f else f * swap h k) a) ↔ p a := by
    intro a
    cases incoming
    · exact (hp _).trans (hs a)
    · exact (hs _).trans (hp a)
  rw [← Nat.card_congr (subtypeOrbitEquiv _ p hp')]
  by_cases hh : p h
  · let h' : {a // p a} := ⟨h, hh⟩
    let k' : {a // p a} := ⟨k, hm.mp hh⟩
    have he : (if incoming then swap h k * f else f * swap h k).subtypePerm hp' =
        if incoming then swap h' k' * f.subtypePerm hp else
          f.subtypePerm hp * swap h' k' := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      cases incoming
      · change f (swap h k a.val) = f ((swap h' k' a).val)
        rw [Subtype.val_injective.map_swap]
      · change swap h k (f a.val) = (swap h' k' (f.subtypePerm hp a)).val
        exact (Subtype.val_injective.map_swap h' k' (f.subtypePerm hp a)).symm
    rw [he]
    have hn : h' ≠ k' := fun he => hne (congrArg Subtype.val he)
    have hncycle : ¬ (f.subtypePerm hp).SameCycle h' k' :=
      fun he => hc (Perm.sameCycle_subtypePerm.mp he)
    cases incoming
    · simpa only [Bool.false_eq_true, ite_false, hh, ite_true,
        Nat.card_congr (subtypeOrbitEquiv f p hp)] using
        (card_orbits_mul_swap (f.subtypePerm hp) h' k' hn).2 hncycle
    · simpa only [ite_true, hh, Nat.card_congr (subtypeOrbitEquiv f p hp)] using
        (card_orbits_swap_mul (f.subtypePerm hp) h' k' hn).2 hncycle
  · have hk : ¬ p k := fun hk => hh (hm.mpr hk)
    have he : (if incoming then swap h k * f else f * swap h k).subtypePerm hp' =
        f.subtypePerm hp := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      cases incoming
      · change f (swap h k a.val) = f a.val
        rw [swap_apply_of_ne_of_ne (show a.val ≠ h from fun he => hh (he ▸ a.property))
          (show a.val ≠ k from fun he => hk (he ▸ a.property))]
      · change swap h k (f a.val) = f a.val
        exact swap_apply_of_ne_of_ne (fun he => hh (he ▸ (hp a.val).mpr a.property))
          (fun he => hk (he ▸ (hp a.val).mpr a.property))
    rw [he, Nat.card_congr (subtypeOrbitEquiv f p hp)]
    simp only [hh, ite_false, Nat.add_zero]

open Classical in
/-- An incoming successor swap joining different cycles removes one selected complete
orbit when both corners are selected; an unselected pair changes no selected orbit. -/
theorem card_orbitOn_swap_mul_of_not_sameCycle {α : Type} [Finite α] [DecidableEq α]
    (f : Perm α) (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a)
    (h k : α) (hm : p h ↔ p k) (hc : ¬ f.SameCycle h k) :
    Nat.card (OrbitOn (swap h k * f) p) + (if p h then 1 else 0) =
      Nat.card (OrbitOn f p) :=
  card_orbitOn_swap_join f p hp h k hm hc true

open Classical in
/-- The corresponding exact count for an outgoing successor swap. The old cycle relation
and old corner membership determine the decrease, including singleton and empty cases. -/
theorem card_orbitOn_mul_swap_of_not_sameCycle {α : Type} [Finite α] [DecidableEq α]
    (f : Perm α) (p : α → Prop) (hp : ∀ a, p (f a) ↔ p a)
    (h k : α) (hm : p h ↔ p k) (hc : ¬ f.SameCycle h k) :
    Nat.card (OrbitOn (f * swap h k) p) + (if p h then 1 else 0) =
      Nat.card (OrbitOn f p) :=
  card_orbitOn_swap_join f p hp h k hm hc false

/-- Disjoint-sum coordinates split all selected complete orbits into their source blocks.
No invariance is needed: selections mean the full orbits meeting the given predicates. -/
noncomputable def orbitOnSumEquiv {α β : Type} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) (p : α → Prop) (q : β → Prop) :
    OrbitOn (Equiv.sumCongr f g) (Sum.elim p q) ≃ OrbitOn f p ⊕ OrbitOn g q := by
  let selected : Quotient (Perm.SameCycle.setoid f) ⊕
      Quotient (Perm.SameCycle.setoid g) → Prop :=
    Sum.elim (fun z => ∃ a, p a ∧ Quotient.mk _ a = z)
      (fun z => ∃ b, q b ∧ Quotient.mk _ b = z)
  let e := Equiv.subtypeEquiv (Perm.sumOrbitEquiv f g) (p := fun z =>
    ∃ d, Sum.elim p q d ∧ Quotient.mk _ d = z) (q := selected) (by
      intro z
      induction z using Quotient.inductionOn with
      | h d =>
        cases d with
        | inl a =>
          change (∃ d, Sum.elim p q d ∧ Quotient.mk _ d = Quotient.mk _ (Sum.inl a)) ↔
            ∃ b, p b ∧ Quotient.mk _ b = Quotient.mk _ a
          constructor
          · rintro ⟨d, hd, he⟩
            have hh := congrArg (Perm.sumOrbitEquiv f g) he
            cases d with
            | inl b => exact ⟨b, hd, Sum.inl.inj hh⟩
            | inr b => cases hh
          · rintro ⟨b, hb, he⟩
            exact ⟨Sum.inl b, hb, (Perm.sumOrbitEquiv f g).injective
              (congrArg Sum.inl he)⟩
        | inr a =>
          change (∃ d, Sum.elim p q d ∧ Quotient.mk _ d = Quotient.mk _ (Sum.inr a)) ↔
            ∃ b, q b ∧ Quotient.mk _ b = Quotient.mk _ a
          constructor
          · rintro ⟨d, hd, he⟩
            have hh := congrArg (Perm.sumOrbitEquiv f g) he
            cases d with
            | inl b => cases hh
            | inr b => exact ⟨b, hd, Sum.inr.inj hh⟩
          · rintro ⟨b, hb, he⟩
            exact ⟨Sum.inr b, hb, (Perm.sumOrbitEquiv f g).injective
              (congrArg Sum.inr he)⟩)
  exact e.trans Equiv.subtypeSum

/-- The selected complete orbit count of a sum is the sum of its selected block counts. -/
theorem card_orbitOn_sum {α β : Type} [Finite α] [Finite β]
    (f : Perm α) (g : Perm β) (p : α → Prop) (q : β → Prop) :
    Nat.card (OrbitOn (Equiv.sumCongr f g) (Sum.elim p q)) =
      Nat.card (OrbitOn f p) + Nat.card (OrbitOn g q) :=
  (Nat.card_congr (orbitOnSumEquiv f g p q)).trans Nat.card_sum

end Equiv.Perm.SelectedOrbits
