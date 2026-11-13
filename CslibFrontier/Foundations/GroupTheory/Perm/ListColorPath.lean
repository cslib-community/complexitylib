/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.ColorPath
public import Mathlib.GroupTheory.Perm.List

/-!
# Corner colors along listed cycles

Directed cycle equations give literal chains of entry/exit colors. Identity-colored
seams can be removed when concatenating chains, including chains with no interior entries.
These facts use arbitrary colors and have no graph or nonemptiness premise on a block.
-/

public section

namespace List

variable {α β : Type*}

/-- The forward equations of a listed cycle give every consecutive corner equation. -/
theorem isChain_colorPairs_of_formPerm [DecidableEq α] (word : List α) (hn : word.Nodup)
    (P Q : α → β) (h : ∀ a ∈ word, P (word.formPerm a) = Q a) :
    IsChain (fun p q : β × β => p.2 = q.1) (word.map fun a => (P a, Q a)) := by
  rw [isChain_map, isChain_iff_getElem]
  intro i hi
  exact (h word[i] (getElem_mem (by omega))).symm.trans
    (congrArg P (formPerm_apply_lt_getElem word hn i hi))

/-- Cutting a listed cycle after its marked entry gives a path from that entry's exit
color back to its entry color. An empty tail forces the two colors to be equal. -/
theorem isChain_colorPairs_cut_formPerm [DecidableEq α] (a : α) (tail : List α)
    (hn : (a :: tail).Nodup) (P Q : α → β)
    (h : ∀ b ∈ a :: tail, P ((a :: tail).formPerm b) = Q b) :
    IsChain (fun p q : β × β => p.2 = q.1)
      ((Q a, Q a) :: tail.map (fun b => (P b, Q b)) ++ [(P a, P a)]) := by
  have hc := isChain_colorPairs_of_formPerm (a :: tail) hn P Q h
  have hl : Q ((a :: tail).getLast (cons_ne_nil _ _)) = P a := by
    have he := h _ (getLast_mem (cons_ne_nil a tail))
    rw [formPerm_apply_getLast] at he
    exact he.symm
  have hc' := hc.append (IsChain.singleton (P a, P a)) (by
    intro x hx y hy
    simp only [getLast?_map, getLast?_eq_some_getLast (cons_ne_nil a tail), Option.map_some,
      Option.mem_some_iff] at hx
    simp only [head?_cons, Option.mem_some_iff] at hy
    subst x
    subst y
    exact hl)
  simpa only [map_cons, cons_append, isChain_cons] using hc'

/-- A complete directed cycle is a closed entry/exit color path, anchored at its actual
first entry. No nonempty condition on subsequently substituted blocks is needed. -/
theorem isChain_colorPairs_cycle_formPerm [DecidableEq α] (a : α) (tail : List α)
    (hn : (a :: tail).Nodup) (P Q : α → β)
    (h : ∀ b ∈ a :: tail, P ((a :: tail).formPerm b) = Q b) :
    IsChain (fun p q : β × β => p.2 = q.1)
      ((P a, P a) :: (a :: tail).map (fun b => (P b, Q b)) ++ [(P a, P a)]) := by
  have hc := isChain_colorPairs_cut_formPerm a tail hn P Q h
  have hp : IsChain (fun p q : β × β => p.2 = q.1)
      ((P a, P a) :: [(P a, Q a)] ++ [(Q a, Q a)]) := by simp
  have hfull := isChain_colorPairs_append hp hc
  simpa only [map_cons, cons_append, nil_append] using hfull

/-- A closed path of entry/exit colors supplies the exact forward cycle equations of the
original duplicate-free word. Empty words are allowed and have no equations to check. -/
theorem formPerm_colorPairs_of_isChain [DecidableEq α] (word : List α) (hn : word.Nodup)
    (P Q : α → β) (c : β)
    (h : IsChain (fun p q : β × β => p.2 = q.1)
      ((c, c) :: word.map (fun a => (P a, Q a)) ++ [(c, c)])) :
    ∀ a ∈ word, P (word.formPerm a) = Q a := by
  simp only [cons_append] at h
  intro a ha
  obtain ⟨i, hi, rfl⟩ := mem_iff_getElem.mp ha
  have hpos : 0 < word.length := by omega
  have hzero : 0 < (word.map fun a => (P a, Q a)).length := by
    simpa only [length_map] using hpos
  have hfirst := (isChain_iff_getElem.mp h) 0 (by
    simp only [length_append, length_cons, length_map, length_nil]
    omega)
  simp only [getElem_cons_zero, getElem_cons_succ] at hfirst
  rw [getElem_append_left hzero, getElem_map] at hfirst
  have hs := (isChain_iff_getElem.mp h) (i + 1) (by
    simp only [length_append, length_cons, length_map, length_nil]
    omega)
  simp only [getElem_cons_succ] at hs
  have himap : i < (word.map fun a => (P a, Q a)).length := by
    simpa only [length_map] using hi
  rw [getElem_append_left himap, getElem_map] at hs
  rw [formPerm_apply_getElem word hn i hi]
  by_cases hj : i + 1 < word.length
  · simp only [Nat.mod_eq_of_lt hj]
    have hjmap : i + 1 < (word.map fun a => (P a, Q a)).length := by
      simpa only [length_map] using hj
    rw [getElem_append_left hjmap, getElem_map] at hs
    exact hs.symm
  · have hlast : i + 1 = word.length := by omega
    simp only [hlast, Nat.mod_self]
    have hjmap : (word.map fun a => (P a, Q a)).length ≤ i + 1 := by
      simp only [length_map]
      omega
    rw [getElem_append_right hjmap] at hs
    have hz : i + 1 - (word.map fun a => (P a, Q a)).length = 0 := by
      simp only [length_map]
      omega
    simp only [hz, getElem_cons_zero] at hs
    exact hfirst.symm.trans hs.symm

end List
