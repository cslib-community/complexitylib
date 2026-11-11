/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sunflower lemma

A family of sets is a *sunflower* with core `K` when any two distinct members intersect exactly in
`K`. The Erdős–Rado sunflower lemma says that a family of more than `(p - 1) ^ w * w!` sets, each
of at most `w` elements, contains a sunflower with `p` petals [Erdős and Rado][ErdosRado1960].

The proof takes a maximal subfamily of pairwise disjoint sets. If it has `p` members, it is a
sunflower with empty core. Otherwise its union is small and meets every nonempty set of the family,
so some point lies in many sets; removing that point from them and applying the lemma for size
`w - 1` gives a sunflower, and putting the point back gives one for the family.

## Main definitions

* `Cslib.IsSunflower`, `Cslib.ContainsSunflower`.
* `Cslib.sunflowerBound`: `(p - 1) ^ w * w!`.

## Main results

* `Cslib.containsSunflower_of_forall_card_le`: the sunflower lemma.

## References

* [P. Erdős, R. Rado, *Intersection theorems for systems of sets*][ErdosRado1960]
-/

@[expose] public section

namespace Cslib

open Finset

variable {α : Type*} [DecidableEq α]

/-- `S` is a sunflower with core `K`: any two distinct members of `S` intersect exactly in `K`. -/
def IsSunflower (S : Finset (Finset α)) (K : Finset α) : Prop :=
  (S : Set (Finset α)).Pairwise fun s t => s ∩ t = K

/-- `F` contains a sunflower with `p` petals. -/
def ContainsSunflower (p : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ S ⊆ F, S.card = p ∧ ∃ K, IsSunflower S K

/-- The bound of the sunflower lemma for sets of size at most `w`: `(p - 1) ^ w * w!`. -/
def sunflowerBound (p w : ℕ) : ℕ := (p - 1) ^ w * w.factorial

/-- The sunflower bound is positive when `2 ≤ p`. -/
theorem sunflowerBound_pos {p : ℕ} (hp : 2 ≤ p) (w : ℕ) : 0 < sunflowerBound p w :=
  Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.factorial_pos w)

/-- A subfamily of a sunflower with core `K` is a sunflower with core `K`. -/
theorem IsSunflower.mono {S T : Finset (Finset α)} {K : Finset α} (h : IsSunflower T K)
    (hST : S ⊆ T) : IsSunflower S K :=
  Set.Pairwise.mono (coe_subset.2 hST) h

/-- The core of a sunflower with at least two petals is contained in every petal. -/
theorem IsSunflower.subset_of_mem {S : Finset (Finset α)} {K s : Finset α} (h : IsSunflower S K)
    (hS : 2 ≤ S.card) (hs : s ∈ S) : K ⊆ s := by
  obtain ⟨t, ht, hts⟩ := exists_mem_ne (by omega : 1 < S.card) s
  rw [← h hs ht (Ne.symm hts)]
  exact inter_subset_left

/-- Pairwise disjoint sets form a sunflower with empty core. -/
theorem isSunflower_empty_of_pairwise_disjoint {S : Finset (Finset α)}
    (h : (S : Set (Finset α)).Pairwise Disjoint) : IsSunflower S ∅ :=
  h.mono' fun _ _ hd => disjoint_iff_inter_eq_empty.1 hd

/-- Adding a point outside all members to every member of a sunflower gives a sunflower. -/
theorem IsSunflower.image_insert {S : Finset (Finset α)} {K : Finset α} (h : IsSunflower S K)
    (x : α) : IsSunflower (S.image (insert x)) (insert x K) := by
  rintro _ hs' _ ht' hne
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
  obtain ⟨t, ht, rfl⟩ := mem_image.1 ht'
  rw [← insert_inter_distrib, h hs ht fun e => hne (by rw [e])]

private theorem containsSunflower_aux {p : ℕ} (hp : 2 ≤ p) :
    ∀ (w : ℕ) (F : Finset (Finset α)), (∀ s ∈ F, s.card ≤ w) →
      sunflowerBound p w < F.card → ContainsSunflower p F
  | 0, F, hF, hlarge => by
    have : F ⊆ {∅} := fun s hs => mem_singleton.2 (card_eq_zero.1 (Nat.le_zero.1 (hF s hs)))
    have := card_le_card this
    simp only [sunflowerBound, pow_zero, Nat.factorial_zero, mul_one, card_singleton]
      at hlarge this
    omega
  | w + 1, F, hF, hlarge => by
    classical
    -- A maximal subfamily of pairwise disjoint sets.
    obtain ⟨D, hDmax⟩ := (F.powerset.filter fun D : Finset (Finset α) =>
      (D : Set (Finset α)).Pairwise Disjoint).exists_maximal ⟨∅, by simp⟩
    have hDF : D ⊆ F := mem_powerset.1 (mem_filter.1 hDmax.1).1
    have hD : (D : Set (Finset α)).Pairwise Disjoint := (mem_filter.1 hDmax.1).2
    have hmax : ∀ E ⊆ F, (E : Set (Finset α)).Pairwise Disjoint → D ⊆ E → E ⊆ D :=
      fun E hE hEd hDE => hDmax.2 (mem_filter.2 ⟨mem_powerset.2 hE, hEd⟩) hDE
    by_cases hpD : p ≤ D.card
    · obtain ⟨S, hSD, hS⟩ := exists_subset_card_eq hpD
      exact ⟨S, hSD.trans hDF, hS, ∅, isSunflower_empty_of_pairwise_disjoint (hD.mono hSD)⟩
    -- A set disjoint from the nonempty sets of `D` is in `D`.
    set U := (D.erase ∅).biUnion id
    have hmemD : ∀ s ∈ F, Disjoint s U → s ∈ D := by
      intro s hs hdisj
      by_contra hsD
      refine hsD (hmax (insert s D) (insert_subset hs hDF) ?_ (subset_insert s D)
        (mem_insert_self s D))
      rw [coe_insert]
      refine hD.insert fun t ht _ => ?_
      by_cases ht0 : t = ∅
      · subst ht0
        exact ⟨disjoint_empty_right s, disjoint_empty_left s⟩
      · have := hdisj.mono_right (subset_biUnion_of_mem id (mem_erase.2 ⟨ht0, ht⟩))
        exact ⟨this, this.symm⟩
    -- So every nonempty set of `F` meets `U`, which is small.
    have hmeet : ∀ s ∈ F, s ≠ ∅ → ∃ x ∈ U, x ∈ s := by
      intro s hs hne
      by_contra! h
      have hdisj : Disjoint s U := disjoint_left.2 fun x hxs hxU => h x hxU hxs
      exact hne (disjoint_self.1 (hdisj.mono_right
        (subset_biUnion_of_mem id (mem_erase.2 ⟨hne, hmemD s hs hdisj⟩))))
    have hU : U.card ≤ (D.erase ∅).card * (w + 1) :=
      card_biUnion_le_card_mul _ _ _ fun s hs => hF s (hDF (mem_of_mem_erase hs))
    -- Some point of `U` lies in more than `sunflowerBound p w` sets of `F`.
    set B := sunflowerBound p w
    have hB : 1 ≤ B := sunflowerBound_pos hp w
    obtain ⟨x, -, hx⟩ : ∃ x ∈ U, B < (F.filter (x ∈ ·)).card := by
      by_contra! h
      have hcover : F ⊆ F.filter (· = ∅) ∪ U.biUnion fun x => F.filter (x ∈ ·) := fun s hs => by
        by_cases hs0 : s = ∅
        · exact mem_union_left _ (mem_filter.2 ⟨hs, hs0⟩)
        · obtain ⟨x, hxU, hxs⟩ := hmeet s hs hs0
          exact mem_union_right _ (mem_biUnion.2 ⟨x, hxU, mem_filter.2 ⟨hs, hxs⟩⟩)
      have hF' : F.card ≤ (F.filter (· = ∅)).card + U.card * B :=
        (card_le_card hcover).trans ((card_union_le _ _).trans (Nat.add_le_add_left
          ((card_biUnion_le.trans (sum_le_card_nsmul _ _ _ h)).trans_eq (smul_eq_mul _ _)) _))
      have hUB : U.card * B ≤ (D.erase ∅).card * ((w + 1) * B) :=
        (Nat.mul_le_mul_right B hU).trans_eq (Nat.mul_assoc _ _ _)
      have hsucc : sunflowerBound p (w + 1) = (p - 2) * ((w + 1) * B) + (w + 1) * B := by
        rw [← Nat.succ_mul, show (p - 2).succ = p - 1 by omega]
        simp only [B, sunflowerBound, pow_succ, Nat.factorial_succ]
        ring
      have hX : 1 ≤ (w + 1) * B := Nat.one_le_iff_ne_zero.2 (by positivity)
      by_cases hE : ∅ ∈ F
      · have h1 : (F.filter (· = ∅)).card = 1 := by
          simp [filter_eq' F ∅, hE]
        have h2 : (D.erase ∅).card ≤ p - 2 := by
          have := hmemD ∅ hE (disjoint_empty_left _)
          rw [card_erase_of_mem this]
          omega
        have := Nat.mul_le_mul_right ((w + 1) * B) h2
        omega
      · have h1 : (F.filter (· = ∅)).card = 0 := by
          simp [filter_eq' F ∅, hE]
        have h2 : (D.erase ∅).card ≤ p - 1 :=
          (card_le_card (erase_subset _ _)).trans (by omega)
        have := Nat.mul_le_mul_right ((w + 1) * B) h2
        have : (p - 1) * ((w + 1) * B) = (p - 2) * ((w + 1) * B) + (w + 1) * B := by
          rw [← Nat.succ_mul, show (p - 2).succ = p - 1 by omega]
        omega
    -- Remove `x`, apply the lemma for size `w`, and put `x` back.
    set G := F.filter (x ∈ ·)
    have hinj : Set.InjOn (fun s : Finset α => s.erase x) G := fun s hs t ht hst => by
      rw [← insert_erase (mem_filter.1 hs).2, ← insert_erase (mem_filter.1 ht).2]
      exact congrArg (insert x) hst
    obtain ⟨S, hSG, hS, K, hSK⟩ := containsSunflower_aux hp w (G.image (·.erase x))
      (fun s hs => by
        obtain ⟨t, ht, rfl⟩ := mem_image.1 hs
        rw [card_erase_of_mem (mem_filter.1 ht).2]
        have := hF t (mem_filter.1 ht).1
        omega)
      (by rwa [card_image_of_injOn hinj])
    have hxS : ∀ s ∈ S, x ∉ s := fun s hs => by
      obtain ⟨t, -, rfl⟩ := mem_image.1 (hSG hs)
      exact notMem_erase x t
    refine ⟨S.image (insert x), fun _ hs' => ?_, ?_, insert x K, hSK.image_insert x⟩
    · obtain ⟨s, hs, rfl⟩ := mem_image.1 hs'
      obtain ⟨t, ht, rfl⟩ := mem_image.1 (hSG hs)
      rw [insert_erase (mem_filter.1 ht).2]
      exact (mem_filter.1 ht).1
    · rw [card_image_of_injOn fun s hs t ht hst => by
        rw [← erase_insert (hxS s hs), ← erase_insert (hxS t ht)]
        exact congrArg (·.erase x) hst, hS]

/-- **The sunflower lemma** [Erdős and Rado][ErdosRado1960]. A family of more than
`(p - 1) ^ w * w!` sets of at most `w` elements contains a sunflower with `p` petals. -/
theorem containsSunflower_of_forall_card_le (p w : ℕ) (F : Finset (Finset α))
    (hF : ∀ s ∈ F, s.card ≤ w) (hlarge : sunflowerBound p w < F.card) :
    ContainsSunflower p F := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · -- At most one petal: any `p` sets will do.
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (show p ≤ F.card by omega)
    exact ⟨S, hS, hcard, ∅, fun s hs t ht hne =>
      absurd (card_le_one.1 (show S.card ≤ 1 by omega) s hs t ht) hne⟩
  exact containsSunflower_aux hp w F hF hlarge

end Cslib
