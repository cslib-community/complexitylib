/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Sections

/-!
# The odometer order of sections

A section of a list of lists `L = [l₀, l₁, …]` picks one entry from each list (`List.sections`).
`List.sections` lists them in odometer order, with the first entry running fastest.
`Cslib.Algorithms.WordRAM.PPSZ.nextSection` is the odometer step: advance the first entry to its
successor in its list, or, at the end of that list, return it to the start and carry into the
rest. `Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections` proves that it steps through
`List.sections L` in order and stops after the last section, when every list is duplicate-free.
A word-RAM program that keeps a section in an array and steps it with `nextSection` therefore
visits every section exactly once.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.succIn`: the entry after a given one in a list.
* `Cslib.Algorithms.WordRAM.PPSZ.nextSection`: the odometer step on sections.
* `Cslib.Algorithms.WordRAM.PPSZ.Enumerates`: a list of sections in odometer order, ending with
  a section that has no successor.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.succIn_getElem`: the successor in a duplicate-free list.
* `Cslib.Algorithms.WordRAM.PPSZ.nextSection_sections`: the odometer enumerates
  `List.sections L`.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

/-- The entry after the first occurrence of `a` in the list `l`, if any. -/
def succIn : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | b :: l, a => if a = b then l.head? else succIn l a

/-- **The odometer step**: the section after `t` among the sections of `L`, if any. The first entry
advances to its successor in its list; at the end of its list, it returns to the start of the list
and the rest of the section advances. -/
def nextSection : List (List ℕ) → List ℕ → Option (List ℕ)
  | l :: L, a :: t =>
    match succIn l a with
    | some a' => some (a' :: t)
    | none => (nextSection L t).map (l.headD 0 :: ·)
  | _, _ => none

/-- In a duplicate-free list, the successor of the `i`-th entry is the `i + 1`-st, if any. -/
theorem succIn_getElem {l : List ℕ} (hl : l.Nodup) {i : ℕ} (hi : i < l.length) :
    succIn l l[i] = l[i + 1]? := by
  induction l generalizing i with
  | nil => simp at hi
  | cons b l ih =>
    rcases i with _ | i
    · simp [succIn, List.head?_eq_getElem?]
    · have hi' : i < l.length := by simp at hi; omega
      have hne : l[i] ≠ b := fun h => (List.nodup_cons.mp hl).1 (h ▸ List.getElem_mem _)
      simp only [List.getElem_cons_succ, succIn, hne, ↓reduceIte]
      exact ih (List.nodup_cons.mp hl).2 hi'

/-- The list `xs` lists sections of `L` in odometer order: the odometer leads from each entry to
the next one, and from the last entry nowhere. -/
def Enumerates (L : List (List ℕ)) (xs : List (List ℕ)) : Prop :=
  ∀ i (h : i < xs.length), nextSection L xs[i] = xs[i + 1]?

/-- The first step of an enumeration. -/
theorem Enumerates.head {L : List (List ℕ)} {t : List ℕ} {xs : List (List ℕ)}
    (h : Enumerates L (t :: xs)) : nextSection L t = xs.head? := by
  have := h 0 (by simp)
  simpa only [List.getElem_cons_zero, Nat.zero_add, List.getElem?_cons_succ,
    List.head?_eq_getElem?] using this

/-- The rest of an enumeration. -/
theorem Enumerates.tail {L : List (List ℕ)} {t : List ℕ} {xs : List (List ℕ)}
    (h : Enumerates L (t :: xs)) : Enumerates L xs :=
  fun i hi => by
    have := h (i + 1) (by simpa using hi)
    simpa only [List.getElem_cons_succ, List.getElem?_cons_succ] using this

/-- One more list in front: each section of the rest is extended by every entry of `l`. -/
private theorem enumerates_flatMap {l : List ℕ} (hl : l.Nodup) (hne : l ≠ [])
    {L : List (List ℕ)} :
    ∀ S : List (List ℕ), Enumerates L S →
      Enumerates (l :: L) (S.flatMap fun t => l.map (· :: t))
  | [], _ => fun i hi => by simp at hi
  | t :: S, h => by
    have ih := enumerates_flatMap hl hne S h.tail
    have hhead := h.head
    have hm : 0 < l.length := List.length_pos_iff.mpr hne
    intro i hi
    simp only [List.flatMap_cons] at hi ⊢
    by_cases hil : i < l.length
    · rw [List.getElem_append_left (by simpa using hil)]
      simp only [List.getElem_map]
      by_cases hi1 : i + 1 < l.length
      · rw [List.getElem?_append_left (by simpa using hi1)]
        simp [nextSection, succIn_getElem hl hil, List.getElem?_eq_getElem hi1]
      · have hi1' : i + 1 = l.length := by omega
        rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_map, hi1', Nat.sub_self]
        have hs : succIn l l[i] = none := by
          rw [succIn_getElem hl hil, List.getElem?_eq_none (by omega)]
        simp only [nextSection, hs, hhead]
        rcases S with _ | ⟨t', S⟩
        · simp
        · obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hne
          simp
    · have hil' : l.length ≤ i := by omega
      rw [List.getElem_append_right (by simpa using hil'),
        List.getElem?_append_right (by simp; omega)]
      have hi' : i - (l.map (· :: t)).length < (S.flatMap fun t => l.map (· :: t)).length := by
        simp only [List.length_append, List.length_map] at hi ⊢; omega
      rw [ih _ hi']
      congr 1
      simp only [List.length_map]
      omega

/-- **The odometer enumerates the sections.** When every list of `L` is duplicate-free, the
odometer step leads from each section of `L` to the next one in `List.sections L`, and from the
last one nowhere. -/
theorem nextSection_sections : ∀ {L : List (List ℕ)}, (∀ l ∈ L, l.Nodup) →
    Enumerates L L.sections
  | [], _ => fun i hi => by
    simp only [List.sections, List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simp [nextSection]
  | l :: L, hL => by
    by_cases hne : l = []
    · subst hne
      intro i hi
      simp only [List.sections, List.map_nil, List.length_nil,
        List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)] at hi
      simp at hi
    · exact enumerates_flatMap (hL l (by simp)) hne _
        (nextSection_sections fun l' h => hL l' (by simp [h]))

end Cslib.Algorithms.WordRAM.PPSZ
