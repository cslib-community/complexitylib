/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.Sort.LEQuery.QueriedPairs
public import Mathlib.Order.Defs.Unbundled

/-!
# Fooling arguments for comparison programs

Tools for adversary and fooling arguments against comparison programs `FreeM (LEQuery α) γ`.
An element `x` is *found above* (`Cslib.Query.FoundAbove`) by a list of comparisons `a ≤ b` if one
of them with `a ≠ b` puts `x` on its strictly larger side, and *found below*
(`Cslib.Query.FoundBelow`) if one puts it on its strictly smaller side. Moving an element that is
never found above to the bottom of a linear order (`Cslib.Query.moveToBot`), or one that is never
found below to the top (`Cslib.Query.moveToTop`), gives a linear order that answers the
comparisons alike, so a comparison program cannot tell the two orders apart.

## Main definitions

* `Cslib.Query.moveToBot`, `Cslib.Query.moveToTop`: a linear order with one element moved to the
  bottom or the top.
* `Cslib.Query.FoundAbove`, `Cslib.Query.FoundBelow`: an element is strictly larger, or strictly
  smaller, than the other side of some comparison.
* `Cslib.Query.AgreeOn`: two orders answer the given comparisons alike.

## Main results

* `Cslib.Query.isLinearOrder_moveToBot`, `Cslib.Query.isLinearOrder_moveToTop`: moving an element
  keeps a linear order linear.
* `Cslib.Query.agreeOn_moveToBot`, `Cslib.Query.agreeOn_moveToTop`: moving an element that is not
  found above (below) to the bottom (top) keeps every answer.
* `Cslib.Query.eval_moveToBot_eq`, `Cslib.Query.eval_moveToTop_eq`: hence a comparison program
  returns the same result against the modified order.
-/

public section

namespace Cslib.Query

variable {α γ : Type}

/-! ## Moving one element to the bottom or the top of a linear order -/

/-- The order `r` with `x` moved to the bottom. -/
def moveToBot (r : α → α → Prop) (x : α) (a b : α) : Prop :=
  a = x ∨ (b ≠ x ∧ r a b)

/-- The order `r` with `x` moved to the top. -/
def moveToTop (r : α → α → Prop) (x : α) (a b : α) : Prop :=
  b = x ∨ (a ≠ x ∧ r a b)

theorem moveToBot_iff {r : α → α → Prop} {x a b : α} :
    moveToBot r x a b ↔ a = x ∨ (b ≠ x ∧ r a b) :=
  Iff.rfl

theorem moveToTop_iff {r : α → α → Prop} {x a b : α} :
    moveToTop r x a b ↔ b = x ∨ (a ≠ x ∧ r a b) :=
  Iff.rfl

theorem moveToBot_bot (r : α → α → Prop) (x b : α) : moveToBot r x x b := Or.inl rfl

theorem moveToTop_top (r : α → α → Prop) (x a : α) : moveToTop r x a x := Or.inl rfl

theorem isLinearOrder_moveToBot (r : α → α → Prop) [IsLinearOrder α r] (x : α) :
    IsLinearOrder α (moveToBot r x) where
  refl a := by
    by_cases h : a = x
    · exact Or.inl h
    · exact Or.inr ⟨h, refl_of r a⟩
  trans a b c hab hbc := by
    rcases hab with hab | ⟨hbx, hab⟩
    · exact Or.inl hab
    rcases hbc with hbc | ⟨hcx, hbc⟩
    · exact absurd hbc hbx
    · exact Or.inr ⟨hcx, _root_.trans hab hbc⟩
  antisymm a b hab hba := by
    rcases hab with hab | ⟨hbx, hab⟩ <;> rcases hba with hba | ⟨hax, hba⟩
    · exact hab.trans hba.symm
    · exact absurd hab hax
    · exact absurd hba hbx
    · exact antisymm hab hba
  total a b := by
    by_cases ha : a = x
    · exact Or.inl (Or.inl ha)
    by_cases hb : b = x
    · exact Or.inr (Or.inl hb)
    rcases total_of r a b with h | h
    · exact Or.inl (Or.inr ⟨hb, h⟩)
    · exact Or.inr (Or.inr ⟨ha, h⟩)

/-- Moving `x` to the top is moving it to the bottom of the reversed order, reversed. -/
theorem isLinearOrder_moveToTop (r : α → α → Prop) [IsLinearOrder α r] (x : α) :
    IsLinearOrder α (moveToTop r x) :=
  haveI := isLinearOrder_moveToBot (Function.swap r) x
  inferInstanceAs (IsLinearOrder α (Function.swap (moveToBot (Function.swap r) x)))

/-! ## Elements found above or below along a run -/

/-- `x` is *found above* by the comparisons `T` against `r`: some comparison `a ≤ b` in `T`
with `a ≠ b` has `x` on its strictly larger side under `r`. -/
def FoundAbove (r : α → α → Prop) (T : List (α × α)) (x : α) : Prop :=
  ∃ a b, (a, b) ∈ T ∧ a ≠ b ∧ ((x = b ∧ r a b) ∨ (x = a ∧ ¬ r a b))

/-- `x` is *found below* by the comparisons `T` against `r`: some comparison `a ≤ b` in `T`
with `a ≠ b` has `x` on its strictly smaller side under `r`. -/
def FoundBelow (r : α → α → Prop) (T : List (α × α)) (x : α) : Prop :=
  ∃ a b, (a, b) ∈ T ∧ a ≠ b ∧ ((x = a ∧ r a b) ∨ (x = b ∧ ¬ r a b))

/-- Two orders give the same answers to the comparisons `T`. -/
def AgreeOn (r r' : α → α → Prop) (T : List (α × α)) : Prop :=
  ∀ a b, (a, b) ∈ T → (r a b ↔ r' a b)

theorem foundAbove_iff {r : α → α → Prop} {T : List (α × α)} {x : α} :
    FoundAbove r T x ↔ ∃ a b, (a, b) ∈ T ∧ a ≠ b ∧ ((x = b ∧ r a b) ∨ (x = a ∧ ¬ r a b)) :=
  Iff.rfl

theorem foundBelow_iff {r : α → α → Prop} {T : List (α × α)} {x : α} :
    FoundBelow r T x ↔ ∃ a b, (a, b) ∈ T ∧ a ≠ b ∧ ((x = a ∧ r a b) ∨ (x = b ∧ ¬ r a b)) :=
  Iff.rfl

@[simp] theorem not_foundAbove_nil (r : α → α → Prop) (x : α) : ¬ FoundAbove r [] x := by
  rintro ⟨a, b, hab, -⟩
  simp at hab

@[simp] theorem not_foundBelow_nil (r : α → α → Prop) (x : α) : ¬ FoundBelow r [] x := by
  rintro ⟨a, b, hab, -⟩
  simp at hab

/-- Appending one comparison `(a, b)` to `T` adds exactly that comparison to an existential
over the comparisons of `T`; the six `append_singleton` lemmas below specialize it. -/
private theorem exists_mem_append_singleton_iff {T : List (α × α)} {a b : α}
    {P : α → α → Prop} :
    (∃ c d, (c, d) ∈ T ++ [(a, b)] ∧ P c d) ↔ (∃ c d, (c, d) ∈ T ∧ P c d) ∨ P a b := by
  simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq, or_and_right, exists_or,
    exists_and_left, exists_eq_left, and_assoc]

/-- A comparison `a ≤ b` with `a ≠ b` answered true finds `b` above. -/
theorem foundAbove_append_singleton_of_rel {r : α → α → Prop} {T : List (α × α)} {a b : α}
    (hab : a ≠ b) (h : r a b) (x : α) :
    FoundAbove r (T ++ [(a, b)]) x ↔ FoundAbove r T x ∨ x = b := by
  unfold FoundAbove
  rw [exists_mem_append_singleton_iff]
  simp [hab, h]

/-- A comparison `a ≤ b` with `a ≠ b` answered false finds `a` above. -/
theorem foundAbove_append_singleton_of_not_rel {r : α → α → Prop} {T : List (α × α)} {a b : α}
    (hab : a ≠ b) (h : ¬ r a b) (x : α) :
    FoundAbove r (T ++ [(a, b)]) x ↔ FoundAbove r T x ∨ x = a := by
  unfold FoundAbove
  rw [exists_mem_append_singleton_iff]
  simp [hab, h]

/-- A comparison `a ≤ b` with `a ≠ b` answered true finds `a` below. -/
theorem foundBelow_append_singleton_of_rel {r : α → α → Prop} {T : List (α × α)} {a b : α}
    (hab : a ≠ b) (h : r a b) (x : α) :
    FoundBelow r (T ++ [(a, b)]) x ↔ FoundBelow r T x ∨ x = a := by
  unfold FoundBelow
  rw [exists_mem_append_singleton_iff]
  simp [hab, h]

/-- A comparison `a ≤ b` with `a ≠ b` answered false finds `b` below. -/
theorem foundBelow_append_singleton_of_not_rel {r : α → α → Prop} {T : List (α × α)} {a b : α}
    (hab : a ≠ b) (h : ¬ r a b) (x : α) :
    FoundBelow r (T ++ [(a, b)]) x ↔ FoundBelow r T x ∨ x = b := by
  unfold FoundBelow
  rw [exists_mem_append_singleton_iff]
  simp [hab, h]

/-- A comparison of an element with itself finds nothing above. -/
theorem foundAbove_append_singleton_self {r : α → α → Prop} {T : List (α × α)} (a x : α) :
    FoundAbove r (T ++ [(a, a)]) x ↔ FoundAbove r T x := by
  unfold FoundAbove
  rw [exists_mem_append_singleton_iff]
  simp

/-- A comparison of an element with itself finds nothing below. -/
theorem foundBelow_append_singleton_self {r : α → α → Prop} {T : List (α × α)} (a x : α) :
    FoundBelow r (T ++ [(a, a)]) x ↔ FoundBelow r T x := by
  unfold FoundBelow
  rw [exists_mem_append_singleton_iff]
  simp

theorem AgreeOn.refl (r : α → α → Prop) (T : List (α × α)) : AgreeOn r r T :=
  fun _ _ _ => Iff.rfl

theorem AgreeOn.iff {r r' : α → α → Prop} {T : List (α × α)} (h : AgreeOn r r' T) {a b : α}
    (hab : (a, b) ∈ T) : r a b ↔ r' a b :=
  h a b hab

theorem AgreeOn.trans {r r' r'' : α → α → Prop} {T : List (α × α)} (h : AgreeOn r r' T)
    (h' : AgreeOn r' r'' T) : AgreeOn r r'' T :=
  fun a b hab => (h a b hab).trans (h' a b hab)

theorem AgreeOn.mono {r r' : α → α → Prop} {T T' : List (α × α)} (h : AgreeOn r r' T')
    (hT : ∀ p ∈ T, p ∈ T') : AgreeOn r r' T :=
  fun a b hab => h a b (hT _ hab)

theorem foundAbove_congr {r r' : α → α → Prop} {T : List (α × α)} (h : AgreeOn r r' T)
    (x : α) :
    FoundAbove r T x ↔ FoundAbove r' T x := by
  unfold FoundAbove
  refine exists₂_congr fun a b => ⟨fun ⟨hab, hne, hx⟩ => ⟨hab, hne, ?_⟩,
    fun ⟨hab, hne, hx⟩ => ⟨hab, hne, ?_⟩⟩ <;> simpa [h a b hab] using hx

theorem foundBelow_congr {r r' : α → α → Prop} {T : List (α × α)} (h : AgreeOn r r' T)
    (x : α) :
    FoundBelow r T x ↔ FoundBelow r' T x := by
  unfold FoundBelow
  refine exists₂_congr fun a b => ⟨fun ⟨hab, hne, hx⟩ => ⟨hab, hne, ?_⟩,
    fun ⟨hab, hne, hx⟩ => ⟨hab, hne, ?_⟩⟩ <;> simpa [h a b hab] using hx

/-- Moving an element that is never found above to the bottom keeps every answer. -/
theorem agreeOn_moveToBot {r : α → α → Prop} [Std.Refl r] {T : List (α × α)} {x : α}
    (hx : ¬ FoundAbove r T x) : AgreeOn r (moveToBot r x) T := by
  intro a b hab
  unfold moveToBot
  by_cases heq : a = b
  · subst heq
    exact ⟨fun h => (eq_or_ne a x).elim Or.inl fun hax => Or.inr ⟨hax, h⟩, fun _ => refl_of r a⟩
  by_cases hbx : b = x
  · subst hbx
    have h : ¬ r a b := fun h => hx ⟨a, b, hab, heq, Or.inl ⟨rfl, h⟩⟩
    simp only [h, heq, ne_eq, not_true_eq_false, false_and, or_self]
  by_cases hax : a = x
  · subst hax
    have h : r a b := by_contra fun h => hx ⟨a, b, hab, heq, Or.inr ⟨rfl, h⟩⟩
    simp only [h, true_or]
  · simp only [hax, hbx, ne_eq, not_false_eq_true, true_and, false_or]

/-- Being found below is being found above in the reversed order, for the reversed comparisons. -/
private theorem foundAbove_swap_iff {r : α → α → Prop} {T : List (α × α)} {x : α} :
    FoundAbove (Function.swap r) (T.map Prod.swap) x ↔ FoundBelow r T x := by
  simp only [FoundAbove, FoundBelow, List.mem_map, Prod.exists, Prod.swap_prod_mk,
    Prod.mk.injEq, Function.swap]
  constructor
  · rintro ⟨a, b, ⟨c, d, hcd, rfl, rfl⟩, hab, h⟩
    exact ⟨c, d, hcd, Ne.symm hab, h⟩
  · rintro ⟨c, d, hcd, hcd', h⟩
    exact ⟨d, c, ⟨c, d, hcd, rfl, rfl⟩, Ne.symm hcd', h⟩

/-- Moving an element that is never found below to the top keeps every answer. -/
theorem agreeOn_moveToTop {r : α → α → Prop} [Std.Refl r] {T : List (α × α)} {x : α}
    (hx : ¬ FoundBelow r T x) : AgreeOn r (moveToTop r x) T := fun a b hab =>
  agreeOn_moveToBot (r := Function.swap r) (mt foundAbove_swap_iff.mp hx) b a
    (List.mem_map_of_mem (f := Prod.swap) hab)

/-! ## The fooling argument -/

open Classical in
/-- If `x` is never found above along the run of `p` against `oracle`, which implements `r`, then
`p` gives the same result when `x` is moved to the bottom of `r`. -/
theorem eval_moveToBot_eq {r : α → α → Prop} [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (p : FreeM (LEQuery α) γ) {x : α}
    (hx : ¬ FoundAbove r (LEQuery.queriedPairs oracle p) x) :
    p.eval (LEQuery.oracleOf fun a b => decide (moveToBot r x a b)) = p.eval oracle :=
  LEQuery.eval_eq_of_agree _ _ p fun a b hab => by
    rw [horacle, LEQuery.oracleOf_le]
    exact decide_eq_decide.mpr (agreeOn_moveToBot hx a b hab)

open Classical in
/-- If `x` is never found below along the run of `p` against `oracle`, which implements `r`, then
`p` gives the same result when `x` is moved to the top of `r`. -/
theorem eval_moveToTop_eq {r : α → α → Prop} [DecidableRel r] [IsLinearOrder α r]
    (oracle : {ι : Type} → LEQuery α ι → ι)
    (horacle : ∀ a b, oracle (.le a b) = decide (r a b)) (p : FreeM (LEQuery α) γ) {x : α}
    (hx : ¬ FoundBelow r (LEQuery.queriedPairs oracle p) x) :
    p.eval (LEQuery.oracleOf fun a b => decide (moveToTop r x a b)) = p.eval oracle :=
  LEQuery.eval_eq_of_agree _ _ p fun a b hab => by
    rw [horacle, LEQuery.oracleOf_le]
    exact decide_eq_decide.mpr (agreeOn_moveToTop hx a b hab)

end Cslib.Query
