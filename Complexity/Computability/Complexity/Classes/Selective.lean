/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Reduction
public import Mathlib.Order.UpperLower.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# P-selective sets

A *selector* for a set `A` picks one of any two instances so that the pick is in `A` whenever
either instance is (`Cslib.Complexity.IsSelector`). A set is *P-selective*
(`Cslib.Complexity.PSel`) when it has a selector computable in polynomial time [Selman1979];
see also [Hemaspaandra and Torenvliet, *Introduction to Semi-Feasible
Computation*][HemaspaandraTorenvliet2003].
P-selective sets are the "semi-feasible" sets: membership need not be decidable, but of any two
instances one that is in `A` if either is can be found in polynomial time.

Selectors here output one of their two arguments, as in Selman's definition. Equivalently, a
P-selective set has a polynomial-time Boolean selector that says which argument to pick
(`Cslib.Complexity.mem_PSel_iff_bool`).

Every set in `P` is P-selective (`Cslib.Complexity.P_subset_PSel`), and the P-selective sets are
closed under complement (`Cslib.Complexity.compl_mem_PSel`) and downward closed under
polynomial-time many-one reductions (`Cslib.Complexity.PolyTimeReducible.mem_PSel`)
[Selman1979]. Lower sets of a total order compared in polynomial time are
P-selective (`Cslib.Complexity.mem_PSel_of_isLowerSet`): the minimum is a selector. Left cuts of
infinite binary sequences, an uncountable family of P-selective sets, are built from this in
`Complexity.Computability.Complexity.Classes.Selective.LeftCut`.

## Main definitions

* `Cslib.Complexity.IsSelector`: `f` selects for `A`.
* `Cslib.Complexity.PSel`: the P-selective sets.

## Main results

* `Cslib.Complexity.mem_PSel_iff_bool`: P-selectivity with a Boolean selector.
* `Cslib.Complexity.P_subset_PSel`: sets in `P` are P-selective.
* `Cslib.Complexity.compl_mem_PSel`: the complement of a P-selective set is P-selective.
* `Cslib.Complexity.PolyTimeReducible.mem_PSel`: a set reducing to a P-selective set is
  P-selective.
* `Cslib.Complexity.mem_PSel_of_isLowerSet`: a lower set of a linear order compared in polynomial
  time is P-selective.

## References

* [A. L. Selman, *P-selective sets, tally languages, and the behavior of polynomial time
  reducibilities on NP*][Selman1979]
* [L. A. Hemaspaandra and L. Torenvliet, *Theory of Semi-Feasible Algorithms*, chapter
  *Introduction to Semi-Feasible Computation*][HemaspaandraTorenvliet2003]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*}

/-- `f` is a *selector* for `A`: it picks one of its two arguments, and the pick is in `A` whenever
either argument is. -/
@[expose] def IsSelector (A : Set α) (f : α → α → α) : Prop :=
  ∀ x y, (f x y = x ∨ f x y = y) ∧ (x ∈ A ∨ y ∈ A → f x y ∈ A)

/-- The *P-selective* sets with respect to the encoding `enc`: `A ∈ PSel enc` when `A` has a
selector computable in polynomial time on pairs of encoded instances [Selman1979]. -/
@[expose] def PSel (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → α → α, ComputableInPolyTime (fun p : α × α => f p.1 p.2) (encPair enc enc) enc ∧
    IsSelector A f}

theorem mem_PSel {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PSel enc ↔ ∃ f : α → α → α,
      ComputableInPolyTime (fun p : α × α => f p.1 p.2) (encPair enc enc) enc ∧ IsSelector A f :=
  Iff.rfl

namespace IsSelector

variable {A : Set α} {f : α → α → α}

/-- A selector picks one of its arguments. -/
theorem eq_or_eq (hf : IsSelector A f) (x y : α) : f x y = x ∨ f x y = y := (hf x y).1

/-- The pick of a selector is in `A` when either argument is. -/
theorem mem (hf : IsSelector A f) {x y : α} (h : x ∈ A ∨ y ∈ A) : f x y ∈ A := (hf x y).2 h

/-- An instance beaten by a member of `A`, in either order, is in `A`. -/
theorem mem_of_mem_of_eq {x y : α} (hf : IsSelector A f) (hy : y ∈ A)
    (h : f x y = x ∨ f y x = x) : x ∈ A := by
  rcases h with h | h
  · exact h ▸ hf.mem (.inr hy)
  · exact h ▸ hf.mem (.inl hy)

end IsSelector

/-- **Boolean selectors.** A set is P-selective exactly when a polynomial-time Boolean function `g`
says which of two instances to pick: the first when `g` answers `true`, the second otherwise. -/
theorem mem_PSel_iff_bool {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ PSel enc ↔ ∃ g : α × α → Bool, ComputableInPolyTime g (encPair enc enc) encBool ∧
      ∀ x y, x ∈ A ∨ y ∈ A → (if g (x, y) then x else y) ∈ A := by
  classical
  constructor
  · rintro ⟨f, hf, hsel⟩
    refine ⟨fun p => decide (f p.1 p.2 = p.1), ComputableInPolyTime.decide_eq' hf (.fst enc enc),
      fun x y hxy => ?_⟩
    change (if decide (f x y = x) = true then x else y) ∈ A
    by_cases hx : f x y = x
    · rw [decide_eq_true hx, ite_eq_left rfl, ← hx]
      exact hsel.mem hxy
    · rw [decide_eq_false hx, ite_eq_right Bool.false_ne_true,
        ← (hsel.eq_or_eq x y).resolve_left hx]
      exact hsel.mem hxy
  · rintro ⟨g, hg, hA⟩
    refine ⟨fun x y => if g (x, y) then x else y, hg.ite' (.fst enc enc) (.snd enc enc),
      fun x y => ⟨?_, hA x y⟩⟩
    by_cases h : g (x, y) = true
    · exact .inl (ite_eq_left h)
    · exact .inr (ite_eq_right h)

/-- **`P ⊆ PSel`**: a polynomial-time decider `d` gives the selector picking the first instance
exactly when `d` accepts it. -/
theorem P_subset_PSel {α : Type} {enc : α ↪ List Bool} : P enc ⊆ PSel enc := by
  rintro A ⟨d, hd, hA⟩
  refine mem_PSel_iff_bool.2 ⟨fun p => d p.1, hd.comp (.fst enc enc), fun x y hxy => ?_⟩
  by_cases h : d x = true
  · rw [ite_eq_left h]
    exact (hA x).2 h
  · rw [ite_eq_right h]
    exact hxy.resolve_left fun hx => h ((hA x).1 hx)

/-- **Complements.** The complement of a P-selective set is P-selective: pick the instance the
selector rejects. -/
theorem compl_mem_PSel {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ PSel enc) :
    Aᶜ ∈ PSel enc := by
  obtain ⟨g, hg, hsel⟩ := mem_PSel_iff_bool.1 hA
  refine mem_PSel_iff_bool.2 ⟨fun p => !g p, ComputableInPolyTime.bool_not.comp hg,
    fun x y hxy => ?_⟩
  change (if (!g (x, y)) = true then x else y) ∈ Aᶜ
  by_cases h : g (x, y) = true
  · rw [h, Bool.not_true, ite_eq_right Bool.false_ne_true]
    intro hy
    have hx := hsel x y (.inr hy)
    rw [ite_eq_left h] at hx
    exact hxy.elim (· hx) (· hy)
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.not_false, ite_eq_left rfl]
    intro hx
    have hy := hsel x y (.inl hx)
    rw [h, ite_eq_right Bool.false_ne_true] at hy
    exact hxy.elim (· hx) (· hy)

/-- **Reductions.** A set that reduces to a P-selective set in polynomial time is P-selective:
select between the images [Selman1979]. -/
theorem PolyTimeReducible.mem_PSel {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (h : PolyTimeReducible encA encB A B) (hB : B ∈ PSel encB) :
    A ∈ PSel encA := by
  obtain ⟨r, hr, hrA⟩ := h
  obtain ⟨g, hg, hsel⟩ := mem_PSel_iff_bool.1 hB
  refine mem_PSel_iff_bool.2 ⟨fun p => g (r p.1, r p.2),
    hg.comp ((hr.comp (.fst encA encA)).prod (hr.comp (.snd encA encA))), fun x y hxy => ?_⟩
  have hsel' := hsel (r x) (r y) (hxy.imp (hrA x).1 (hrA y).1)
  by_cases h : g (r x, r y) = true
  · rw [ite_eq_left h] at hsel' ⊢
    exact (hrA x).2 hsel'
  · rw [ite_eq_right h] at hsel' ⊢
    exact (hrA y).2 hsel'

/-- **Lower sets are P-selective.** If a linear order on the instances is compared in polynomial
time, every lower set of it is P-selective: the minimum of two instances is a selector. -/
theorem mem_PSel_of_isLowerSet {α : Type} [LinearOrder α] {enc : α ↪ List Bool} {A : Set α}
    (hA : IsLowerSet A)
    (hle : ComputableInPolyTime (fun p : α × α => decide (p.1 ≤ p.2)) (encPair enc enc) encBool) :
    A ∈ PSel enc := by
  refine mem_PSel_iff_bool.2 ⟨_, hle, fun x y hxy => ?_⟩
  by_cases h : x ≤ y
  · rw [decide_eq_true h, ite_eq_left rfl]
    exact hxy.elim id (hA h)
  · rw [decide_eq_false h, ite_eq_right Bool.false_ne_true]
    exact hxy.elim (hA ((le_total x y).resolve_left h)) id

end Cslib.Complexity
