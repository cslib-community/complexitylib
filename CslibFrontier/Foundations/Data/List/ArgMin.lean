/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/MinMax.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.List.MinMax

/-!
# The first minimizer of a nonempty list

Mathlib's `List.argmin f l` is `none` exactly on the empty list. Algorithms that select a
cheapest candidate usually need the positive form, and often read the choice off with a
default through `Option.getD`. This file provides those forms.

## Main results

* `List.exists_argmin_eq_some`: a nonempty list has a first minimizer.
* `List.getD_argmin_mem`: on a nonempty list, the minimizer read with any default is a member.
* `List.getD_argmin_le`: the minimizer read with any default is at most every member.
-/

public section

namespace List

variable {α β : Type*} [LinearOrder β] {f : α → β} {l : List α}

/-- A nonempty list has a first minimizer. -/
theorem exists_argmin_eq_some (hl : l ≠ []) : ∃ m, l.argmin f = some m :=
  Option.ne_none_iff_exists'.1 (mt argmin_eq_none.1 hl)

/-- On a nonempty list, the first minimizer read with any default is a member of the list. -/
theorem getD_argmin_mem (hl : l ≠ []) (d : α) : (l.argmin f).getD d ∈ l := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) hl
  rw [hm, Option.getD_some]
  exact argmin_mem hm

/-- The first minimizer read with any default is at most every member of the list. -/
theorem getD_argmin_le {x : α} (hx : x ∈ l) (d : α) : f ((l.argmin f).getD d) ≤ f x := by
  obtain ⟨m, hm⟩ := exists_argmin_eq_some (f := f) (ne_nil_of_mem hx)
  rw [hm, Option.getD_some]
  exact le_of_mem_argmin hx hm

theorem argmin_map_equiv {α γ : Type*} {δ : Type*} [LinearOrder δ]
    (e : α → γ) (l : List α) (f : γ → δ) :
    (l.argmin (f ∘ e)).map e = (l.map e).argmin f := by
  unfold List.argmin
  rw [List.foldl_map]
  have hgen : ∀ (acc : Option α),
      (l.foldl (fun a b => List.argAux (fun x y => (f ∘ e) x < (f ∘ e) y) a b) acc).map e =
        l.foldl (fun a b => List.argAux (fun x y => f x < f y) a (e b)) (acc.map e) := by
    intro acc
    induction l generalizing acc with
    | nil => rfl
    | cons x l ih =>
      simp only [List.foldl_cons]
      have harg : (List.argAux (fun x y => (f ∘ e) x < (f ∘ e) y) acc x).map e =
          List.argAux (fun x y => f x < f y) (acc.map e) (e x) := by
        cases acc with
        | none => rfl
        | some c =>
          unfold List.argAux
          simp only [Option.map_some, Function.comp_apply]
          split_ifs <;> rfl
      rw [← harg]
      exact ih _
  simpa using hgen none

theorem argmin_congr_mem {α δ : Type*} [LinearOrder δ] (all l : List α) {f g : α → δ}
    (hl : ∀ x ∈ l, x ∈ all) (hfg : ∀ x ∈ all, f x = g x) :
    l.argmin f = l.argmin g := by
  have hinv : ∀ (m : List α) (acc : Option α),
      (∀ z, acc = some z → z ∈ all) →
      (∀ x ∈ m, x ∈ all) →
      m.foldl (List.argAux fun a b => f a < f b) acc =
        m.foldl (List.argAux fun a b => g a < g b) acc := by
    intro m
    induction m with
    | nil => intro acc _ _; rfl
    | cons x m ih =>
      intro acc hacc hm
      have hx : x ∈ all := hm x List.mem_cons_self
      have hm' : ∀ y ∈ m, y ∈ all := fun y hy => hm y (List.mem_cons_of_mem _ hy)
      have hstep :
          List.argAux (fun a b => f a < f b) acc x =
            List.argAux (fun a b => g a < g b) acc x := by
        cases acc with
        | none => rfl
        | some z => simp only [List.argAux, hfg x hx, hfg z (hacc z rfl)]
      simp only [List.foldl_cons, hstep]
      refine ih _ (fun z hz => ?_) hm'
      cases acc with
      | none =>
        have : x = z := by simpa [List.argAux] using hz
        exact this ▸ hx
      | some y =>
        dsimp only [List.argAux] at hz
        split_ifs at hz <;> simp only [Option.some.injEq] at hz
        · exact hz ▸ hx
        · exact hz ▸ hacc y rfl
  exact hinv l none (fun _ h => by simp at h) hl

theorem isSome_argmin_filter {α δ : Type*} [LinearOrder δ] (l : List α) (p : α → Bool)
    (f : α → δ) : ((l.filter p).argmin f).isSome = l.any p := by
  by_cases h : ∃ x ∈ l, p x = true
  · obtain ⟨x, hx1, hx2⟩ := h
    have hne : l.filter p ≠ [] := List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx1, hx2⟩)
    obtain ⟨m, hm⟩ := List.exists_argmin_eq_some (f := f) hne
    rw [hm, Option.isSome_some]
    symm
    exact List.any_eq_true.mpr ⟨x, hx1, hx2⟩
  · have hnil : l.filter p = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx hpx
      exact h ⟨x, hx, by simpa using hpx⟩
    rw [hnil, List.argmin_nil, Option.isSome_none]
    symm
    rw [Bool.eq_false_iff]
    intro hbad
    exact h (List.any_eq_true.mp hbad)


end List
