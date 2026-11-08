/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.DartInsertion
public import Complexity.Foundations.GroupTheory.Perm.Doubled
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Complete orbit counts for permutation surgery

The orbit quotients count singleton cycles. Removing an isolated permutation point drops
one orbit; removing a point from a longer cycle preserves its orbit. The identities retain
the directed successor convention and serve face-cycle accounting for rotation surgery.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem.CycleSplice

open Equiv
open DartInsertion

variable {α : Type} [DecidableEq α] [Finite α]

omit [DecidableEq α] in
private theorem sameCycle_optionCongr (f : Perm α) (a b : α) :
    Perm.SameCycle f.optionCongr (some a) (some b) ↔ f.SameCycle a b := by
  have hm : Function.Semiconj some f f.optionCongr := fun _ => rfl
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    apply Option.some.inj
    rw [zpow_natCast, ← Perm.iterate_eq_pow, hm.iterate_right n,
      Perm.iterate_eq_pow, hn]
  · exact fun h => h.map_of_semiconj hm

/-- Adding a fixed permutation point adds one actual orbit, including when all old points
are absent. The old nontrivial and singleton cycles are both retained. -/
noncomputable def optionOrbitEquiv (f : Perm α) :
    Quotient (Perm.SameCycle.setoid f.optionCongr) ≃
      Option (Quotient (Perm.SameCycle.setoid f)) where
  toFun := Quotient.lift (Option.map (Quotient.mk _)) (by
    intro x y h
    cases x with
    | none =>
      have he := h.eq_of_left rfl
      cases he
      rfl
    | some a =>
      cases y with
      | none =>
        have he : some a = none := h.eq_of_right rfl
        cases he
      | some b =>
        exact congrArg some (Quotient.sound ((sameCycle_optionCongr f a b).mp h)))
  invFun q := match q with
    | none => Quotient.mk _ none
    | some q => Quotient.map some (fun a b h => (sameCycle_optionCongr f a b).mpr h) q
  left_inv := by
    intro q
    refine Quotient.inductionOn q fun x => ?_
    cases x <;> rfl
  right_inv := by
    intro q
    cases q with
    | none => rfl
    | some q => exact Quotient.inductionOn q fun _ => rfl

omit [DecidableEq α] in
/-- The additional singleton orbit is counted exactly once. -/
theorem card_orbits_optionCongr (f : Perm α) :
    Nat.card (Quotient (Perm.SameCycle.setoid f.optionCongr)) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) + 1 := by
  classical
  rw [Nat.card_congr (optionOrbitEquiv f), Finite.card_option]

omit [DecidableEq α] in
/-- Removing a fixed point removes its one singleton orbit; it does not discard any other
fixed points or faces. -/
theorem card_orbits_removeNone_fixed (f : Perm (Option α)) (hn : f none = none) :
    Nat.card (Quotient (Perm.SameCycle.setoid f)) =
      Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f))) + 1 := by
  classical
  have he : (removeNone f).optionCongr = f := by
    calc
      _ = swap none (f none) * f := map_equiv_removeNone f
      _ = f := by rw [hn, swap_self]; rfl
  conv_lhs => rw [← he]
  exact card_orbits_optionCongr (removeNone f)

omit [DecidableEq α] in
/-- Deleting a permutation point preserves the orbit relation on every retained pair,
whether the deleted point was a singleton or belonged to a longer cycle. -/
theorem sameCycle_removeNone (f : Perm (Option α)) (a b : α) :
    Perm.SameCycle (removeNone f) a b ↔ f.SameCycle (some a) (some b) := by
  classical
  by_cases hn : f none = none
  · have he : (removeNone f).optionCongr = f := by
      calc
        _ = swap none (f none) * f := map_equiv_removeNone f
        _ = f := by rw [hn, swap_self]; rfl
    conv_rhs => rw [← he]
    exact (sameCycle_optionCongr _ _ _).symm
  · exact sameCycle_removeNone_iff f hn a b

omit [Finite α] in
/-- Deletion commutes with swapping the outgoing successors of two retained points.
The removed point is fixed by the swap, but may lie anywhere in the original permutation. -/
theorem removeNone_mul_swap (f : Perm (Option α)) (a b : α) :
    removeNone (f * swap (some a) (some b)) = removeNone f * swap a b := by
  apply Equiv.optionCongr_injective
  calc
    _ = swap none ((f * swap (some a) (some b)) none) *
        (f * swap (some a) (some b)) := map_equiv_removeNone _
    _ = (swap none (f none) * f) * (swap a b).optionCongr := by
      simp [mul_assoc, swap_apply_of_ne_of_ne]
    _ = (removeNone f).optionCongr * (swap a b).optionCongr := by
      rw [map_equiv_removeNone]
    _ = _ := by
      apply Equiv.ext
      intro x
      cases x <;> rfl

omit [DecidableEq α] [Finite α] in
/-- Deleting the extra point commutes with postcomposition by a permutation of the
retained points. The extra point need not be fixed by the first permutation. -/
theorem removeNone_mul_optionCongr (f : Perm (Option α)) (g : Perm α) :
    removeNone (f * g.optionCongr) = removeNone f * g := by
  classical
  apply Equiv.optionCongr_injective
  have hm : (removeNone f * g).optionCongr =
      (removeNone f).optionCongr * g.optionCongr := by
    ext x
    cases x <;> rfl
  rw [hm, map_equiv_removeNone, map_equiv_removeNone]
  have hn : (f * g.optionCongr) none = f none := rfl
  rw [hn, mul_assoc]

omit [DecidableEq α] in
/-- Transporting a permutation retains its complete orbit count. -/
theorem card_orbits_permCongr {β : Type} [Finite β] (e : α ≃ β) (f : Perm α) :
    Nat.card (Quotient (Perm.SameCycle.setoid (e.permCongr f))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) := by
  apply (Nat.card_congr (Quotient.congr e ?_)).symm
  intro x y
  exact (Perm.sameCycle_equiv_iff e f (e.permCongr f)
    (fun z => by simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]) x y).symm

omit [DecidableEq α] in
/-- Deleting a point drops exactly its singleton orbit when it is fixed. -/
theorem card_orbits_removeNone_add (f : Perm (Option α)) :
    Nat.card (Quotient (Perm.SameCycle.setoid f)) =
      Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f))) +
        if f none = none then 1 else 0 := by
  classical
  by_cases hn : f none = none
  · simpa only [hn, ite_true] using card_orbits_removeNone_fixed f hn
  · simpa only [hn, ite_false, Nat.add_zero] using (card_orbits_removeNone f hn).symm

omit [DecidableEq α] in
/-- A permutation of retained points does not affect the number of singleton orbits lost
by deleting the extra point. All counts use the full orbit quotient. -/
theorem card_orbits_removeNone_balance (f : Perm (Option α)) (g : Perm α) :
    Nat.card (Quotient (Perm.SameCycle.setoid (f * g.optionCongr))) +
        Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f))) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) +
        Nat.card (Quotient (Perm.SameCycle.setoid (removeNone (f * g.optionCongr)))) := by
  classical
  have h₁ := card_orbits_removeNone_add (f * g.optionCongr)
  have h₂ := card_orbits_removeNone_add f
  have hn : (f * g.optionCongr) none = f none := rfl
  rw [hn] at h₁
  omega

private theorem card_orbits_twoPoints (f : Perm α) (a b : α) (hab : a ≠ b)
    (cover : ∀ x, x = a ∨ x = b) :
    Nat.card (Quotient (Perm.SameCycle.setoid f)) = if f a = a then 2 else 1 := by
  classical
  let e := Equiv.optionSubtypeNe a
  let f' := e.symm.permCongr f
  have hs : Subsingleton {x : α // x ≠ a} := ⟨by
    intro x y
    apply Subtype.ext
    exact ((cover x).resolve_left x.property).trans
      ((cover y).resolve_left y.property).symm⟩
  let := hs
  have hi : Nonempty (Quotient (Perm.SameCycle.setoid (removeNone f'))) :=
    ⟨Quotient.mk _ ⟨b, hab.symm⟩⟩
  let := hi
  have hcsmall : Nat.card (Quotient (Perm.SameCycle.setoid (removeNone f'))) = 1 :=
    Nat.card_unique
  have hc := card_orbits_removeNone_add f'
  rw [hcsmall] at hc
  have hfix : f' none = none ↔ f a = a := by
    change e.symm (f (e none)) = none ↔ f a = a
    rw [← e.symm_apply_apply none, e.symm.injective.eq_iff]
    simp only [e, Equiv.apply_symm_apply, Equiv.optionSubtypeNe_none]
  rw [card_orbits_permCongr] at hc
  simp only [hfix] at hc
  split_ifs at hc ⊢ <;> omega

/-- Swapping two distinct outgoing successors splits their common orbit into two,
or merges their two different orbits. Singleton cycles are included. -/
theorem card_orbits_mul_swap (f : Perm α) (a b : α) (hab : a ≠ b) :
    (f.SameCycle a b →
      Nat.card (Quotient (Perm.SameCycle.setoid (f * swap a b))) =
        Nat.card (Quotient (Perm.SameCycle.setoid f)) + 1) ∧
    (¬ f.SameCycle a b →
      Nat.card (Quotient (Perm.SameCycle.setoid (f * swap a b))) + 1 =
        Nat.card (Quotient (Perm.SameCycle.setoid f))) := by
  classical
  generalize hn : Nat.card α = n
  induction n using Nat.strong_induction_on generalizing α with
  | ind n ih =>
    by_cases hex : ∃ c : α, c ≠ a ∧ c ≠ b
    · obtain ⟨c, hca, hcb⟩ := hex
      let e := Equiv.optionSubtypeNe c
      let f' := e.symm.permCongr f
      let a' : {x : α // x ≠ c} := ⟨a, hca.symm⟩
      let b' : {x : α // x ≠ c} := ⟨b, hcb.symm⟩
      have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
      have hlt : Nat.card {x : α // x ≠ c} < n := by
        rw [← hn]
        exact Finite.card_subtype_lt (not_not.mpr rfl)
      have hi := ih _ hlt (removeNone f') a' b' hab' rfl
      have hsame : Perm.SameCycle (removeNone f') a' b' ↔ f.SameCycle a b := by
        rw [sameCycle_removeNone]
        exact (Perm.sameCycle_equiv_iff e f' f
          (fun z => by simp only [f', Equiv.permCongr_apply, Equiv.apply_symm_apply,
            Equiv.symm_symm]) (some a') (some b')).symm
      have hconj : e.symm.permCongr (f * swap a b) =
          f' * swap (some a') (some b') := by
        ext z
        simp only [Equiv.permCongr_apply, Perm.coe_mul, Function.comp_apply, f']
        cases z with
        | none => simp [e, swap_apply_of_ne_of_ne, hca, hcb]
        | some z =>
          by_cases hza : z = a'
          · subst z; simp [e, a', b']
          · by_cases hzb : z = b'
            · subst z; simp [e, a', b']
            · have hza' : (z : α) ≠ a := fun h => hza (Subtype.ext h)
              have hzb' : (z : α) ≠ b := fun h => hzb (Subtype.ext h)
              simp [e, swap_apply_of_ne_of_ne, hza, hzb, hza', hzb']
      have hcf := card_orbits_removeNone_add f'
      have hcg := card_orbits_removeNone_add (f' * swap (some a') (some b'))
      rw [removeNone_mul_swap] at hcg
      have hfixed : (f' * swap (some a') (some b')) none = f' none := by
        simp [swap_apply_def]
      rw [hfixed] at hcg
      rw [← hconj, card_orbits_permCongr] at hcg
      rw [card_orbits_permCongr] at hcf
      constructor
      · intro h
        have hi' := hi.1 (hsame.mpr h)
        omega
      · intro h
        have hi' := hi.2 (fun h' => h (hsame.mp h'))
        omega
    · have cover : ∀ x, x = a ∨ x = b := by
        intro x
        by_contra hx
        push Not at hx
        exact hex ⟨x, hx⟩
      have hcf := card_orbits_twoPoints f a b hab cover
      have hcg := card_orbits_twoPoints (f * swap a b) a b hab cover
      by_cases hfa : f a = a
      · have hfb : f b = b := by
          rcases cover (f b) with h | h
          · exact False.elim (hab (f.injective (hfa.trans h.symm)))
          · exact h
        have hga : (f * swap a b) a = b := by simp [hfb]
        have hnot : ¬ f.SameCycle a b := fun h => hab (h.eq_of_left hfa)
        simp only [hfa, ite_true, hga, hab.symm, ite_false] at hcf hcg
        constructor
        · exact fun h => False.elim (hnot h)
        · intro _; omega
      · have hfb : f b = a := by
          have hfa' := (cover (f a)).resolve_left hfa
          rcases cover (f b) with h | h
          · exact h
          · exact False.elim (hab (f.injective (hfa'.trans h.symm)))
        have hga : (f * swap a b) a = a := by simp [hfb]
        have hsame : f.SameCycle a b := by
          rw [← hfb]
          exact Perm.sameCycle_apply_left.mpr .rfl
        simp only [hfa, ite_false, hga, ite_true] at hcf hcg
        constructor
        · intro _; omega
        · exact fun h => False.elim (h hsame)

omit [DecidableEq α] [Finite α] in
/-- Reversing the directed traversal of every orbit retains the full orbit quotient. -/
theorem card_orbits_inv (f : Perm α) :
    Nat.card (Quotient (Perm.SameCycle.setoid f⁻¹)) =
      Nat.card (Quotient (Perm.SameCycle.setoid f)) :=
  Nat.card_congr (Quotient.congr (Equiv.refl α) (fun _ _ => Perm.sameCycle_inv))

/-- Swapping incoming successors has the same exact split/merge count as swapping outgoing
successors. The orbit condition is evaluated in the original permutation. -/
theorem card_orbits_swap_mul (f : Perm α) (a b : α) (hab : a ≠ b) :
    (f.SameCycle a b →
      Nat.card (Quotient (Perm.SameCycle.setoid (swap a b * f))) =
        Nat.card (Quotient (Perm.SameCycle.setoid f)) + 1) ∧
    (¬ f.SameCycle a b →
      Nat.card (Quotient (Perm.SameCycle.setoid (swap a b * f))) + 1 =
        Nat.card (Quotient (Perm.SameCycle.setoid f))) := by
  have h := card_orbits_mul_swap f⁻¹ a b hab
  have he : f⁻¹ * swap a b = (swap a b * f)⁻¹ := by simp
  rw [he, card_orbits_inv, card_orbits_inv] at h
  simpa only [Perm.sameCycle_inv] using h

end Cslib.Complexity.Graph.RotationSystem.CycleSplice
