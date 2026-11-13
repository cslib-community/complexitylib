/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Communication.Nondeterministic.CoverNumber
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Nondeterministic communication complexity of unique disjointness

This module formalizes the Kaibel–Weltge exponential lower bound `(3 / 2) ^ n` on the rectangle
covering number and nondeterministic communication complexity of unique disjointness
[KaibelWeltge2015, Sections 2–3].

A subset `R ⊆ D(U)` of pairs of disjoint subsets of `U` is *valid* (`IsValidDisjointSet`) if no
`(a, b), (a', b') ∈ R` satisfy `|a ∩ b'| = 1`, equivalently if `R` lies inside a
`1`-monochromatic rectangle of the unique-disjointness relation (`uniqueDisjointnessRel`). By
inductively splitting `R` along an element `x ∈ U`, Kaibel and Weltge show `R.card ≤ 2 ^ U.card`
(`card_le_two_pow_of_isValidDisjointSet`). Since `D(U)` has size `3 ^ U.card`
(`card_disjointPairs`), any `1`-cover has size at least `(3 / 2) ^ |α|`
(`three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel`).

## Main definitions

* `Cslib.Communication.Nondeterministic.uniqueDisjointnessRel`: the unique-disjointness relation
  on subsets of `α`.
* `Cslib.Communication.Nondeterministic.nonUniqueInter`: the Boolean predicate `|a ∩ b| ≠ 1`.
* `Cslib.Communication.Nondeterministic.nonUniqueInterVec`: the `α → Bool` predicate `|a ∩ b| ≠ 1`.
* `Cslib.Communication.Nondeterministic.disjointPairs`: the family `D(U)` of pairs of disjoint
  subsets of `U`.
* `Cslib.Communication.Nondeterministic.IsValidDisjointSet`: Kaibel–Weltge validity on `D(U)`.

## Main results

* `Cslib.Communication.Nondeterministic.card_disjointPairs`: `(disjointPairs U).card = 3 ^ U.card`.
* `Cslib.Communication.Nondeterministic.card_le_two_pow_of_isValidDisjointSet`: any valid
  `R ⊆ D(U)` has `R.card ≤ 2 ^ U.card`.
* `Cslib.Communication.Nondeterministic.three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel`:
  `(3 : ℕ) ^ |α| ≤ 2 ^ |α| * coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ`.
* `Cslib.Communication.Nondeterministic.three_pow_le_two_pow_mul_coverNumberFun_nonUniqueInter`:
  the same `(3 / 2) ^ |α|` bound on `coverNumberFun true (nonUniqueInter α) Set.univ Set.univ`.
* `Cslib.Communication.Nondeterministic.clog_ceil_div_le_ecomplexity_uniqueDisjointnessRel`: the
  `⌈log₂ ⌈(3 / 2) ^ |α|⌉⌉` lower bound on `N¹(UDISJ)`.

## References

* [KaibelWeltge2015], Sections 2–3 (Theorem 1).
-/

public section

namespace Cslib.Communication

namespace Nondeterministic

open Finset

section Finset

variable {α : Type*}

/-- The **unique disjointness** relation on subsets of `α`: `true` is acceptable when
`|a ∩ b| ≠ 1`, and `false` is acceptable when `a` and `b` are not disjoint. Every `1`-cover
covers all disjoint pairs `(a, b)` with rectangles whose cross-intersections never have size `1`
[KaibelWeltge2015, Sections 2–3]. -/
@[expose] def uniqueDisjointnessRel (α : Type*) [DecidableEq α] (a b : Finset α)
    (z : Bool) : Prop :=
  if z then (a ∩ b).card ≠ 1 else ¬ Disjoint a b

/-- The Boolean predicate `|a ∩ b| ≠ 1` on subsets of `α` (the support of the correlation slack
matrix `(1 - |a ∩ b|)²`). -/
@[expose] def nonUniqueInter (α : Type*) [DecidableEq α] (a b : Finset α) : Bool :=
  decide ((a ∩ b).card ≠ 1)

/-- The Boolean predicate `|{i | u i ∧ v i}| ≠ 1` on Boolean vectors `u, v : α → Bool`. -/
@[expose] def nonUniqueInterVec (α : Type*) [Fintype α] (u v : α → Bool) : Bool :=
  decide ((Finset.univ.filter fun i => u i && v i).card ≠ 1)

variable [DecidableEq α]

/-- The set `D(U)` of ordered pairs `(a, b)` of disjoint subsets of `U`
[KaibelWeltge2015, Section 2]. -/
def disjointPairs (U : Finset α) : Finset (Finset α × Finset α) :=
  (U.powerset ×ˢ U.powerset).filter fun p => Disjoint p.1 p.2

/-- A subset `R ⊆ D(U)` is *valid* if no two pairs `(a, b), (a', b') ∈ R` satisfy `|a ∩ b'| = 1`
[KaibelWeltge2015, Section 2]. -/
@[expose] def IsValidDisjointSet (U : Finset α) (R : Finset (Finset α × Finset α)) : Prop :=
  R ⊆ disjointPairs U ∧ ∀ p ∈ R, ∀ q ∈ R, (p.1 ∩ q.2).card ≠ 1

theorem mem_disjointPairs {U a b : Finset α} :
    (a, b) ∈ disjointPairs U ↔ a ⊆ U ∧ b ⊆ U ∧ Disjoint a b := by
  simp only [disjointPairs, mem_filter, mem_product, mem_powerset, and_assoc]

@[simp] theorem disjointPairs_empty : disjointPairs (∅ : Finset α) = {(∅, ∅)} := by
  ext ⟨a, b⟩
  simp only [mem_disjointPairs, subset_empty, mem_singleton, Prod.mk.injEq]
  refine ⟨fun ⟨ha, hb, _⟩ => ⟨ha, hb⟩, fun ⟨ha, hb⟩ => ?_⟩
  subst ha hb
  exact ⟨rfl, rfl, disjoint_empty_left ∅⟩

private def insertPair (x : α) : Fin 3 × (Finset α × Finset α) → Finset α × Finset α
  | (0, p) => p
  | (1, p) => (insert x p.1, p.2)
  | (2, p) => (p.1, insert x p.2)

private theorem insertPair_mem {x : α} {U : Finset α} (hx : x ∉ U)
    {tp : Fin 3 × (Finset α × Finset α)}
    (htp : tp ∈ (univ : Finset (Fin 3)) ×ˢ disjointPairs U) :
    insertPair x tp ∈ disjointPairs (insert x U) := by
  rcases tp with ⟨t, a, b⟩
  rw [mem_product, mem_disjointPairs] at htp
  obtain ⟨-, ha, hb, hab⟩ := htp
  have hxa : x ∉ a := fun h => hx (ha h)
  have hxb : x ∉ b := fun h => hx (hb h)
  rw [mem_disjointPairs]
  fin_cases t
  · exact ⟨ha.trans (subset_insert x U), hb.trans (subset_insert x U), hab⟩
  · exact ⟨insert_subset_insert x ha, hb.trans (subset_insert x U),
      disjoint_insert_left.2 ⟨hxb, hab⟩⟩
  · exact ⟨ha.trans (subset_insert x U), insert_subset_insert x hb,
      disjoint_insert_right.2 ⟨hxa, hab⟩⟩

private theorem insertPair_injOn {x : α} {U : Finset α} (hx : x ∉ U) :
    ∀ tp₁ ∈ (univ : Finset (Fin 3)) ×ˢ disjointPairs U,
      ∀ tp₂ ∈ (univ : Finset (Fin 3)) ×ˢ disjointPairs U,
        insertPair x tp₁ = insertPair x tp₂ → tp₁ = tp₂ := by
  rintro ⟨t₁, a₁, b₁⟩ h₁ ⟨t₂, a₂, b₂⟩ h₂ heq
  rw [mem_product, mem_disjointPairs] at h₁ h₂
  have hxa₁ : x ∉ a₁ := fun h => hx (h₁.2.1 h)
  have hxb₁ : x ∉ b₁ := fun h => hx (h₁.2.2.1 h)
  have hxa₂ : x ∉ a₂ := fun h => hx (h₂.2.1 h)
  have hxb₂ : x ∉ b₂ := fun h => hx (h₂.2.2.1 h)
  have he : ∀ t (a b : Finset α), x ∉ a → x ∉ b →
      ((insertPair x (t, a, b)).1.erase x = a ∧ (insertPair x (t, a, b)).2.erase x = b) := by
    intro t a b ha hb
    fin_cases t
    · exact ⟨erase_eq_of_notMem ha, erase_eq_of_notMem hb⟩
    · exact ⟨erase_insert ha, erase_eq_of_notMem hb⟩
    · exact ⟨erase_eq_of_notMem ha, erase_insert hb⟩
  have ha : a₁ = a₂ := by
    have := congrArg (fun p => p.1.erase x) heq
    rwa [(he t₁ a₁ b₁ hxa₁ hxb₁).1, (he t₂ a₂ b₂ hxa₂ hxb₂).1] at this
  have hb : b₁ = b₂ := by
    have := congrArg (fun p => p.2.erase x) heq
    rwa [(he t₁ a₁ b₁ hxa₁ hxb₁).2, (he t₂ a₂ b₂ hxa₂ hxb₂).2] at this
  subst ha hb
  fin_cases t₁ <;> fin_cases t₂ <;> simp only [insertPair, Prod.mk.injEq] at heq ⊢
  · exact absurd (heq.1.symm ▸ mem_insert_self x a₁) hxa₁
  · exact absurd (heq.2.symm ▸ mem_insert_self x b₁) hxb₁
  · exact absurd (heq.1 ▸ mem_insert_self x a₁) hxa₁
  · exact absurd (heq.1 ▸ mem_insert_self x a₁) hxa₁
  · exact absurd (heq.2 ▸ mem_insert_self x b₁) hxb₁
  · exact absurd (heq.1.symm ▸ mem_insert_self x a₁) hxa₁

/-- There are `3 ^ U.card` pairs of disjoint subsets of `U` [KaibelWeltge2015, Section 2]. -/
theorem card_disjointPairs (U : Finset α) : (disjointPairs U).card = 3 ^ U.card := by
  induction U using Finset.induction_on with
  | empty => simp only [disjointPairs_empty, card_singleton, card_empty, pow_zero]
  | @insert x U hx ih =>
      rw [card_insert_of_notMem hx, pow_succ', ← ih]
      symm
      calc
        3 * (disjointPairs U).card = ((univ : Finset (Fin 3)) ×ˢ disjointPairs U).card := by
          rw [card_product, card_fin]
        _ = (disjointPairs (insert x U)).card := by
          refine Finset.card_bij (fun tp _ => insertPair x tp)
            (fun _ h => insertPair_mem hx h) (insertPair_injOn hx) fun ⟨a, b⟩ hab => ?_
          rw [mem_disjointPairs] at hab
          obtain ⟨ha, hb, habd⟩ := hab
          have hsub : ∀ s : Finset α, s ⊆ insert x U → s.erase x ⊆ U :=
            fun s hs y hy => by
              have hmem := hs (mem_of_mem_erase hy)
              exact (mem_insert.1 hmem).resolve_left (ne_of_mem_erase hy)
          by_cases hxa : x ∈ a
          · have hxb : x ∉ b := Finset.disjoint_left.1 habd hxa
            refine ⟨(1, a.erase x, b), mem_product.2 ⟨mem_univ _, mem_disjointPairs.2
              ⟨hsub a ha, fun y hy => (mem_insert.1 (hb hy)).resolve_left
                (fun hyx => hxb (hyx ▸ hy)), habd.mono_left (erase_subset x a)⟩⟩, ?_⟩
            simp only [insertPair, insert_erase hxa]
          · by_cases hxb : x ∈ b
            · refine ⟨(2, a, b.erase x), mem_product.2 ⟨mem_univ _, mem_disjointPairs.2
                ⟨fun y hy => (mem_insert.1 (ha hy)).resolve_left (fun hyx => hxa (hyx ▸ hy)),
                  hsub b hb, habd.mono_right (erase_subset x b)⟩⟩, ?_⟩
              simp only [insertPair, insert_erase hxb]
            · refine ⟨(0, a, b), mem_product.2 ⟨mem_univ _, mem_disjointPairs.2
                ⟨fun y hy => (mem_insert.1 (ha hy)).resolve_left (fun hyx => hxa (hyx ▸ hy)),
                  fun y hy => (mem_insert.1 (hb hy)).resolve_left (fun hyx => hxb (hyx ▸ hy)),
                  habd⟩⟩, rfl⟩

private def flipPair (p : Finset α × Finset α) : Finset α × Finset α :=
  (p.2, p.1)

private theorem isValidDisjointSet_image_flipPair {U : Finset α}
    {R : Finset (Finset α × Finset α)} (hR : IsValidDisjointSet U R) :
    IsValidDisjointSet U (R.image flipPair) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqd := mem_disjointPairs.1 (hR.1 hq)
    exact mem_disjointPairs.2 ⟨hqd.2.1, hqd.1, hqd.2.2.symm⟩
  · intro p hp q hq
    rw [mem_image] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    simpa only [flipPair, inter_comm] using hR.2 q' hq' p' hp'

private def leftSplit (x : α) (R : Finset (Finset α × Finset α)) :
    Finset (Finset α × Finset α) :=
  R.filter fun p => x ∉ p.2 ∧ (x ∈ p.1 ∨ (insert x p.1, p.2) ∉ R)

private theorem leftSplit_image_erase_isValid {x : α} {U : Finset α}
    {R : Finset (Finset α × Finset α)} (hR : IsValidDisjointSet (insert x U) R) :
    IsValidDisjointSet U ((leftSplit x R).image fun p => (p.1.erase x, p.2.erase x)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    have hqR := (mem_filter.1 hq).1
    obtain ⟨ha, hb, hab⟩ := mem_disjointPairs.1 (hR.1 hqR)
    have hsub : ∀ s : Finset α, s ⊆ insert x U → s.erase x ⊆ U := fun s hs y hy =>
      (mem_insert.1 (hs (mem_of_mem_erase hy))).resolve_left (ne_of_mem_erase hy)
    exact mem_disjointPairs.2
      ⟨hsub q.1 ha, hsub q.2 hb, hab.mono (erase_subset x q.1) (erase_subset x q.2)⟩
  · intro p hp q hq
    rw [mem_image] at hp hq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    have hp'R := (mem_filter.1 hp').1
    have hq'R := (mem_filter.1 hq').1
    have hxq' : x ∉ q'.2 := (mem_filter.1 hq').2.1
    rw [erase_eq_of_notMem hxq', erase_inter,
      erase_eq_of_notMem fun h => hxq' (mem_inter.1 h).2]
    exact hR.2 p' hp'R q' hq'R

private theorem injOn_erase_leftSplit {x : α} {R : Finset (Finset α × Finset α)} :
    Set.InjOn (fun p : Finset α × Finset α => (p.1.erase x, p.2.erase x)) (leftSplit x R) := by
  intro p hp q hq heq
  rw [mem_coe, leftSplit, mem_filter] at hp hq
  rw [Prod.mk.injEq] at heq
  have hp2 : x ∉ p.2 := hp.2.1
  have hq2 : x ∉ q.2 := hq.2.1
  have hb : p.2 = q.2 := by
    simpa only [erase_eq_of_notMem hp2, erase_eq_of_notMem hq2] using heq.2
  have hmem : x ∈ p.1 ↔ x ∈ q.1 := by
    by_contra hne
    have hcases : (x ∈ p.1 ∧ x ∉ q.1) ∨ (x ∈ q.1 ∧ x ∉ p.1) := by tauto
    rcases hcases with ⟨hxp, hxq⟩ | ⟨hxq, hxp⟩
    · have ha : p.1 = insert x q.1 := by
        rw [← insert_erase hxp, heq.1, erase_eq_of_notMem hxq]
      have hbad := hq.2.2.resolve_left hxq
      rw [← ha, ← hb] at hbad
      exact hbad hp.1
    · have ha : q.1 = insert x p.1 := by
        rw [← insert_erase hxq, ← heq.1, erase_eq_of_notMem hxp]
      have hbad := hp.2.2.resolve_left hxp
      rw [← ha, hb] at hbad
      exact hbad hq.1
  have ha : p.1 = q.1 := by
    ext y
    by_cases hyx : y = x
    · subst hyx; exact hmem
    · have := congrArg (y ∈ ·) heq.1
      simpa only [mem_erase, ne_eq, hyx, not_false_eq_true, true_and, eq_iff_iff] using this
  exact Prod.ext ha hb

private theorem subset_leftSplit_union {x : α} {U : Finset α} {R : Finset (Finset α × Finset α)}
    (hR : IsValidDisjointSet (insert x U) R) :
    R ⊆ leftSplit x R ∪ (leftSplit x (R.image flipPair)).image flipPair := by
  intro ⟨a, b⟩ hab
  rw [mem_union, mem_image]
  have habd : Disjoint a b := (mem_disjointPairs.1 (hR.1 hab)).2.2
  by_cases hxa : x ∈ a
  · left
    exact mem_filter.2 ⟨hab, Finset.disjoint_left.1 habd hxa, Or.inl hxa⟩
  · by_cases hxb : x ∈ b
    · right
      refine ⟨(b, a), mem_filter.2 ⟨mem_image.2 ⟨(a, b), hab, rfl⟩,
        Finset.disjoint_right.1 habd hxb, Or.inl hxb⟩, rfl⟩
    · by_cases hia : (insert x a, b) ∈ R
      · by_cases hib : (a, insert x b) ∈ R
        · exfalso
          have hne := hR.2 (insert x a, b) hia (a, insert x b) hib
          have hinter : insert x a ∩ insert x b = {x} := by
            ext y
            simp only [mem_inter, mem_insert, mem_singleton]
            refine ⟨fun ⟨hy₁, hy₂⟩ => ?_, fun hy => ⟨Or.inl hy, Or.inl hy⟩⟩
            rcases hy₁ with rfl | hya
            · rfl
            · rcases hy₂ with rfl | hyb
              · rfl
              · exact absurd (Finset.disjoint_left.1 habd hya) (fun h => h hyb)
          rw [hinter, card_singleton] at hne
          exact hne rfl
        · right
          refine ⟨(b, a), mem_filter.2 ⟨mem_image.2 ⟨(a, b), hab, rfl⟩, hxa,
            Or.inr fun h => hib ?_⟩, rfl⟩
          rw [mem_image] at h
          obtain ⟨q, hq, hqeq⟩ := h
          have : q = (a, insert x b) := by
            rw [flipPair, Prod.mk.injEq] at hqeq
            exact Prod.ext hqeq.2 hqeq.1
          rwa [← this]
      · left
        exact mem_filter.2 ⟨hab, hxb, Or.inr hia⟩

/-- Any valid subset `R ⊆ D(U)` has size at most `2 ^ U.card`
[KaibelWeltge2015, proof of Theorem 1]. -/
theorem card_le_two_pow_of_isValidDisjointSet {U : Finset α}
    {R : Finset (Finset α × Finset α)} (hR : IsValidDisjointSet U R) : R.card ≤ 2 ^ U.card := by
  induction U using Finset.induction_on generalizing R with
  | empty =>
      calc
        R.card ≤ (disjointPairs (∅ : Finset α)).card := card_le_card hR.1
        _ = 1 := by simp only [disjointPairs_empty, card_singleton]
        _ = 2 ^ (∅ : Finset α).card := by simp only [card_empty, pow_zero]
  | @insert x U hx ih =>
      have h1 : (leftSplit x R).card ≤ 2 ^ U.card := by
        rw [← card_image_of_injOn injOn_erase_leftSplit]
        exact ih (leftSplit_image_erase_isValid hR)
      have h2 : (leftSplit x (R.image flipPair)).card ≤ 2 ^ U.card := by
        rw [← card_image_of_injOn injOn_erase_leftSplit]
        exact ih (leftSplit_image_erase_isValid (isValidDisjointSet_image_flipPair hR))
      calc
        R.card ≤ (leftSplit x R ∪ (leftSplit x (R.image flipPair)).image flipPair).card :=
          card_le_card (subset_leftSplit_union hR)
        _ ≤ (leftSplit x R).card + ((leftSplit x (R.image flipPair)).image flipPair).card :=
          card_union_le _ _
        _ ≤ (leftSplit x R).card + (leftSplit x (R.image flipPair)).card :=
          Nat.add_le_add_left card_image_le _
        _ ≤ 2 ^ U.card + 2 ^ U.card := Nat.add_le_add h1 h2
        _ = 2 ^ (insert x U).card := by rw [card_insert_of_notMem hx, pow_succ, mul_two]

section Cover

variable [Fintype α]

/-- Any `1`-cover of `uniqueDisjointnessRel α` by `r` rectangles satisfies
`3 ^ |α| ≤ r * 2 ^ |α|` [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_of_isCover_uniqueDisjointnessRel {κ : Type*} [Fintype κ]
    {C : κ → Set (Finset α) × Set (Finset α)}
    (hcov : IsCover true (uniqueDisjointnessRel α) Set.univ Set.univ C) :
    3 ^ Fintype.card α ≤ Fintype.card κ * 2 ^ Fintype.card α := by
  classical
  let R : κ → Finset (Finset α × Finset α) := fun w =>
    (disjointPairs Finset.univ).filter fun p => p.1 ∈ (C w).1 ∧ p.2 ∈ (C w).2
  have hvalid : ∀ w, IsValidDisjointSet Finset.univ (R w) := fun w =>
    ⟨filter_subset _ _, fun p hp q hq => by
      have hp1 : p.1 ∈ (C w).1 := (mem_filter.1 hp).2.1
      have hq2 : q.2 ∈ (C w).2 := (mem_filter.1 hq).2.2
      exact hcov.1 w p.1 (Set.mem_univ _) hp1 q.2 (Set.mem_univ _) hq2⟩
  have hsub : disjointPairs Finset.univ ⊆ Finset.univ.biUnion R := by
    intro p hp
    have hdisj : Disjoint p.1 p.2 := (mem_disjointPairs.1 hp).2.2
    obtain ⟨w, hw1, hw2⟩ := hcov.2 p.1 (Set.mem_univ _) p.2 (Set.mem_univ _) (by
      simpa only [Bool.not_true, uniqueDisjointnessRel, Bool.false_eq_true, ↓reduceIte,
        not_not] using hdisj)
    exact mem_biUnion.2 ⟨w, mem_univ w, mem_filter.2 ⟨hp, hw1, hw2⟩⟩
  calc
    3 ^ Fintype.card α = (disjointPairs (Finset.univ : Finset α)).card :=
      (card_disjointPairs Finset.univ).symm
    _ ≤ (Finset.univ.biUnion R).card := card_le_card hsub
    _ ≤ ∑ w : κ, (R w).card := card_biUnion_le
    _ ≤ ∑ _w : κ, 2 ^ Fintype.card α :=
      Finset.sum_le_sum fun w _ =>
        (card_le_two_pow_of_isValidDisjointSet (hvalid w)).trans_eq
          (congrArg (2 ^ ·) (Finset.card_univ : (Finset.univ : Finset α).card = Fintype.card α))
    _ = Fintype.card κ * 2 ^ Fintype.card α := by
      simp only [Finset.sum_const, smul_eq_mul, card_univ]

private theorem ceilDiv_le_of_three_pow_le {n r : ℕ} (h : 3 ^ n ≤ r * 2 ^ n) :
    (3 ^ n + 2 ^ n - 1) / 2 ^ n ≤ r := by
  have hpos : 0 < 2 ^ n := by positivity
  exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hpos).2 (by
    rw [Nat.add_one_mul]
    omega))

private theorem three_pow_le_two_pow_mul_ceilDiv (n : ℕ) :
    3 ^ n ≤ 2 ^ n * ((3 ^ n + 2 ^ n - 1) / 2 ^ n) := by
  have hpos : 0 < 2 ^ n := by positivity
  have hmod : (3 ^ n + 2 ^ n - 1) % 2 ^ n ≤ 2 ^ n - 1 := Nat.le_pred_of_lt (Nat.mod_lt _ hpos)
  have hdiv := Nat.div_add_mod (3 ^ n + 2 ^ n - 1) (2 ^ n)
  omega

/-- The rectangle covering number of `uniqueDisjointnessRel α` is at least `⌈(3 / 2) ^ |α|⌉`
[KaibelWeltge2015, Sections 2–3]. -/
theorem ceil_three_div_two_pow_le_coverNumber_uniqueDisjointnessRel :
    (((3 ^ Fintype.card α + 2 ^ Fintype.card α - 1) / 2 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ :=
  le_coverNumber_iff.2 fun r C hcov => by
    exact_mod_cast ceilDiv_le_of_three_pow_le
      (by simpa only [Fintype.card_fin] using
        three_pow_le_two_pow_mul_of_isCover_uniqueDisjointnessRel hcov)

/-- In `ℕ∞`, `(3 : ℕ) ^ |α| ≤ 2 ^ |α| * coverNumber true (uniqueDisjointnessRel α) ...`
[KaibelWeltge2015, Sections 2–3]. -/
theorem three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel :
    ((3 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      (2 ^ Fintype.card α : ℕ∞) * coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ := by
  calc
    ((3 ^ Fintype.card α : ℕ) : ℕ∞) ≤
        ((2 ^ Fintype.card α * ((3 ^ Fintype.card α + 2 ^ Fintype.card α - 1) /
          2 ^ Fintype.card α) : ℕ) : ℕ∞) := by
      exact_mod_cast three_pow_le_two_pow_mul_ceilDiv (Fintype.card α)
    _ = (2 ^ Fintype.card α : ℕ∞) *
          (((3 ^ Fintype.card α + 2 ^ Fintype.card α - 1) / 2 ^ Fintype.card α : ℕ) : ℕ∞) := by
      push_cast; rfl
    _ ≤ (2 ^ Fintype.card α : ℕ∞) *
          coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ :=
      mul_le_mul_right ceil_three_div_two_pow_le_coverNumber_uniqueDisjointnessRel _

/-- Any `1`-cover of `uniqueDisjointnessRel α` has size at least `(3 / 2) ^ |α|` in any linearly
ordered field [KaibelWeltge2015, Theorem 1]. -/
theorem three_div_two_pow_le_of_coverNumber_uniqueDisjointnessRel_le {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r : ℕ}
    (hr : coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤ r) :
    (3 / 2 : K) ^ Fintype.card α ≤ r := by
  obtain ⟨C, hcov⟩ := coverNumber_le_iff.1 hr
  have hnat : 3 ^ Fintype.card α ≤ r * 2 ^ Fintype.card α := by
    simpa only [Fintype.card_fin] using
      three_pow_le_two_pow_mul_of_isCover_uniqueDisjointnessRel hcov
  have hcast : ((3 : K) ^ Fintype.card α) ≤ (r : K) * (2 : K) ^ Fintype.card α := by
    exact_mod_cast hnat
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact hcast

omit [Fintype α] in
/-- Covering the total predicate `nonUniqueInter α` (`|a ∩ b| ≠ 1`) is at least as hard as
covering `uniqueDisjointnessRel α`. -/
theorem coverNumber_uniqueDisjointnessRel_le_coverNumberFun_nonUniqueInter :
    coverNumber true (uniqueDisjointnessRel α) Set.univ Set.univ ≤
      coverNumberFun true (nonUniqueInter α) Set.univ Set.univ := by
  refine le_coverNumber_iff.2 fun r C hcov => ?_
  rw [isCover_fun_iff] at hcov
  refine coverNumber_le_iff.2 ⟨C, fun w a _ ha b _ hb => ?_, fun a _ b _ hnd => ?_⟩
  · simpa only [uniqueDisjointnessRel, ↓reduceIte, nonUniqueInter, decide_eq_true_eq] using
      hcov.1 w a (Set.mem_univ _) ha b (Set.mem_univ _) hb
  · rw [uniqueDisjointnessRel] at hnd
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, not_not] at hnd
    refine hcov.2 a (Set.mem_univ _) b (Set.mem_univ _) ?_
    simp only [nonUniqueInter, decide_eq_true_eq]
    rw [Finset.disjoint_iff_inter_eq_empty.1 hnd, card_empty]
    norm_num

/-- In `ℕ∞`, `(3 : ℕ) ^ |α| ≤ 2 ^ |α| * coverNumberFun true (nonUniqueInter α) ...`. -/
theorem three_pow_le_two_pow_mul_coverNumberFun_nonUniqueInter :
    ((3 ^ Fintype.card α : ℕ) : ℕ∞) ≤
      (2 ^ Fintype.card α : ℕ∞) * coverNumberFun true (nonUniqueInter α) Set.univ Set.univ :=
  three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel.trans
    (mul_le_mul_right coverNumber_uniqueDisjointnessRel_le_coverNumberFun_nonUniqueInter _)

/-- Covering `nonUniqueInterVec α` on Boolean vectors `α → Bool` is at least as hard as covering
`nonUniqueInter α` on subsets of `α`. -/
theorem coverNumberFun_nonUniqueInter_le_vec :
    coverNumberFun true (nonUniqueInter α) Set.univ Set.univ ≤
      coverNumberFun true (nonUniqueInterVec α) Set.univ Set.univ := by
  let f : Finset α → (α → Bool) := fun s i => decide (i ∈ s)
  have heq : ∀ a b : Finset α, nonUniqueInterVec α (f a) (f b) = nonUniqueInter α a b := by
    intro a b
    have hfilter : (Finset.univ.filter fun i => f a i && f b i) = a ∩ b := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_inter, Bool.and_eq_true, f, decide_eq_true_eq]
    simp only [nonUniqueInterVec, nonUniqueInter, hfilter]
  refine le_coverNumber_iff.2 fun r C hcov => ?_
  rw [isCover_fun_iff] at hcov
  have hcov' : IsCover true (fun a b r => nonUniqueInter α a b = r) Set.univ Set.univ
      (fun w => (f ⁻¹' (C w).1, f ⁻¹' (C w).2)) := by
    rw [isCover_fun_iff]
    refine ⟨fun w a _ ha b _ hb => ?_, fun a _ b _ hab => ?_⟩
    · rw [← heq a b]
      exact hcov.1 w (f a) (Set.mem_univ _) ha (f b) (Set.mem_univ _) hb
    · rw [← heq a b] at hab
      exact hcov.2 (f a) (Set.mem_univ _) (f b) (Set.mem_univ _) hab
  exact coverNumber_le_iff.2 ⟨_, hcov'⟩

/-- Nondeterministic `1`-communication complexity of `uniqueDisjointnessRel α` is at least
`⌈log₂ ⌈(3 / 2) ^ |α|⌉⌉` [KaibelWeltge2015, Section 3]. -/
theorem clog_ceil_div_le_ecomplexity_uniqueDisjointnessRel :
    (Nat.clog 2 ((3 ^ Fintype.card α + 2 ^ Fintype.card α - 1) / 2 ^ Fintype.card α) : ℕ∞) ≤
      ecomplexity true (uniqueDisjointnessRel α) Set.univ Set.univ := by
  refine le_ecomplexity_iff.2 fun k ⟨C, hcov⟩ => ?_
  have hcard := three_pow_le_two_pow_mul_of_isCover_uniqueDisjointnessRel hcov
  have hbit : Fintype.card (BitString k) = 2 ^ k := by
    simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [hbit] at hcard
  exact_mod_cast (Nat.clog_le_iff_le_pow (by norm_num)).2 (ceilDiv_le_of_three_pow_le hcard)

end Cover

end Finset

end Nondeterministic

end Cslib.Communication
