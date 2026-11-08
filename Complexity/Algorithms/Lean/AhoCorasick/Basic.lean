/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
import Mathlib.Data.List.Nodup

/-!
# Aho–Corasick Goto-Graph States, Failure and Output Functions

This module develops the combinatorics of the Aho–Corasick pattern matching machine
(`[AhoCorasick1975]`) for a list `P : List (List α)` of keywords over an alphabet with decidable
equality. As in `[AhoCorasick1975]`, Section 4, a state is represented by its string: the states
are the prefixes of keywords together with the start state `[]` (`IsNode P`); the goto function
sends `u` on `a` to `u ++ [a]` when that is a state, and the start state loops on every other
symbol.

The failure function, the output function and the state reached after reading a text are given
by their specifications (`[AhoCorasick1975]`, Lemmas 1–3): `failure P u` is the longest proper
suffix of `u` that is a state, `output P w` lists the keywords that are nonempty suffixes of `w`,
and the state after reading `w` is `longestNodeSuffix P w`. The recurrences proved here are the
ones used by Algorithms 1 and 3 in `Complexity.Algorithms.Lean.AhoCorasick.Search`.

## Main definitions

* `Cslib.Algorithms.Lean.AhoCorasick.IsNode`: `u = []` or `u` is a prefix of a keyword of `P`.
* `Cslib.Algorithms.Lean.AhoCorasick.longestNodeSuffix`: the longest suffix of `w` that is a
  state.
* `Cslib.Algorithms.Lean.AhoCorasick.failure`: the failure function, `longestNodeSuffix P u.tail`.
* `Cslib.Algorithms.Lean.AhoCorasick.nextMove`: one operating cycle (failure transitions followed
  by one goto transition).
* `Cslib.Algorithms.Lean.AhoCorasick.output`: the keywords of `P` that are nonempty suffixes of
  `w`, longest first, without repetitions.
* `Cslib.Algorithms.Lean.AhoCorasick.IsOccurrence`: keyword `y ∈ P` ends at the `1`-indexed
  position `i` of `t`.
* `Cslib.Algorithms.Lean.AhoCorasick.occurrences`: all occurrences, by increasing end position.

## Main results

* `Cslib.Algorithms.Lean.AhoCorasick.eq_failure_iff`: `[AhoCorasick1975]`, Lemma 1.
* `Cslib.Algorithms.Lean.AhoCorasick.mem_output_iff` and `output_eq_of_ne_nil`:
  `[AhoCorasick1975]`, Lemma 2, and the output recurrence of Algorithm 3.
* `Cslib.Algorithms.Lean.AhoCorasick.longestNodeSuffix_append_singleton_eq_nextMove` and
  `foldl_nextMove`: `[AhoCorasick1975]`, Lemma 3.
* `Cslib.Algorithms.Lean.AhoCorasick.failure_append_singleton`: the failure recurrence of
  Algorithm 3.
* `Cslib.Algorithms.Lean.AhoCorasick.mem_occurrences_iff`, `nodup_occurrences`,
  `pairwise_occurrences` and `occurrences_append_singleton`.

## References

* [A. V. Aho and M. J. Corasick, *Efficient String Matching: An Aid to Bibliographic
  Search*][AhoCorasick1975]
-/

public section

namespace Cslib.Algorithms.Lean.AhoCorasick

variable {α : Type*}

/-! ## Goto-graph nodes -/

/-- `u` is a state of the goto graph of `P`: the start state `[]` or a prefix of a keyword. -/
@[expose] def IsNode (P : List (List α)) (u : List α) : Prop :=
  u = [] ∨ ∃ p ∈ P, u <+: p

instance [DecidableEq α] (P : List (List α)) : DecidablePred (IsNode P) :=
  fun u => inferInstanceAs (Decidable (u = [] ∨ ∃ p ∈ P, u <+: p))

@[simp]
theorem isNode_nil (P : List (List α)) : IsNode P [] := Or.inl rfl

theorem IsNode.of_prefix {P : List (List α)} {u v : List α} (hv : IsNode P v) (h : u <+: v) :
    IsNode P u := by
  rcases hv with rfl | ⟨p, hp, hvp⟩
  · exact Or.inl (List.prefix_nil.mp h)
  · exact Or.inr ⟨p, hp, h.trans hvp⟩

theorem isNode_of_mem {P : List (List α)} {p : List α} (hp : p ∈ P) : IsNode P p :=
  Or.inr ⟨p, hp, List.prefix_rfl⟩

theorem isNode_take {P : List (List α)} {p : List α} (hp : p ∈ P) (n : ℕ) : IsNode P (p.take n) :=
  Or.inr ⟨p, hp, List.take_prefix n p⟩

variable [DecidableEq α]

/-! ## Longest node suffix -/

/-- The longest suffix of `w` that is a state of the goto graph of `P`. -/
def longestNodeSuffix (P : List (List α)) : List α → List α
  | [] => []
  | b :: w => if IsNode P (b :: w) then b :: w else longestNodeSuffix P w

@[simp]
theorem longestNodeSuffix_nil (P : List (List α)) : longestNodeSuffix P [] = [] := by
  rw [longestNodeSuffix]

theorem longestNodeSuffix_cons_of_not_isNode {P : List (List α)} {b : α} {w : List α}
    (h : ¬ IsNode P (b :: w)) : longestNodeSuffix P (b :: w) = longestNodeSuffix P w := by
  rw [longestNodeSuffix]
  simp only [h, ↓reduceIte]

theorem longestNodeSuffix_suffix (P : List (List α)) (w : List α) :
    longestNodeSuffix P w <:+ w := by
  induction w with
  | nil => exact List.suffix_rfl
  | cons b w ih =>
    rw [longestNodeSuffix]
    split_ifs
    · exact List.suffix_rfl
    · exact ih.trans (List.suffix_cons b w)

theorem isNode_longestNodeSuffix (P : List (List α)) (w : List α) :
    IsNode P (longestNodeSuffix P w) := by
  induction w with
  | nil => exact isNode_nil P
  | cons b w ih =>
    rw [longestNodeSuffix]
    split_ifs with h
    · exact h
    · exact ih

theorem length_le_longestNodeSuffix {P : List (List α)} {v w : List α} (hv : IsNode P v)
    (hvw : v <:+ w) : v.length ≤ (longestNodeSuffix P w).length := by
  induction w with
  | nil =>
    rw [List.suffix_nil.mp hvw]
    exact Nat.zero_le _
  | cons b w ih =>
    rw [longestNodeSuffix]
    split_ifs with h
    · exact hvw.length_le
    · rcases List.suffix_cons_iff.mp hvw with rfl | hvw'
      · exact absurd hv h
      · exact ih hvw'

theorem eq_longestNodeSuffix {P : List (List α)} {v w : List α} (hvw : v <:+ w)
    (hv : IsNode P v) (hmax : ∀ x, x <:+ w → IsNode P x → x.length ≤ v.length) :
    v = longestNodeSuffix P w := by
  have h1 := length_le_longestNodeSuffix hv hvw
  have h2 := hmax _ (longestNodeSuffix_suffix P w) (isNode_longestNodeSuffix P w)
  exact (List.suffix_of_suffix_length_le hvw (longestNodeSuffix_suffix P w) h1).eq_of_length
    (by omega)

theorem longestNodeSuffix_of_isNode {P : List (List α)} {u : List α} (hu : IsNode P u) :
    longestNodeSuffix P u = u := by
  cases u with
  | nil => rfl
  | cons b u =>
    rw [longestNodeSuffix]
    simp only [hu, ↓reduceIte]

theorem longestNodeSuffix_append_singleton (P : List (List α)) (w : List α) (a : α) :
    longestNodeSuffix P (longestNodeSuffix P w ++ [a]) = longestNodeSuffix P (w ++ [a]) := by
  set s := longestNodeSuffix P w
  set r := longestNodeSuffix P (s ++ [a])
  have hs : s <:+ w := longestNodeSuffix_suffix P w
  have hrs : r <:+ s ++ [a] := longestNodeSuffix_suffix P _
  refine eq_longestNodeSuffix (hrs.trans (List.suffix_append_self_iff.mpr hs))
    (isNode_longestNodeSuffix P _) fun x hx hxn => ?_
  rcases List.suffix_concat_iff.mp hx with rfl | ⟨t, rfl, htw⟩
  · exact Nat.zero_le _
  · have htn : IsNode P t := hxn.of_prefix (List.prefix_append t [a])
    have hts : t <:+ s :=
      List.suffix_of_suffix_length_le htw hs (length_le_longestNodeSuffix htn htw)
    exact length_le_longestNodeSuffix hxn (List.suffix_append_self_iff.mpr hts)

/-! ## Failure function -/

/-- The failure function: the longest proper suffix of `u` that is a goto-graph state
(`[AhoCorasick1975]`, Lemma 1). -/
def failure (P : List (List α)) (u : List α) : List α :=
  longestNodeSuffix P u.tail

@[simp]
theorem failure_nil (P : List (List α)) : failure P [] = [] := by
  rw [failure, List.tail_nil, longestNodeSuffix]

theorem failure_cons (P : List (List α)) (b : α) (u : List α) :
    failure P (b :: u) = longestNodeSuffix P u := by
  rw [failure, List.tail_cons]

theorem isNode_failure (P : List (List α)) (u : List α) : IsNode P (failure P u) :=
  isNode_longestNodeSuffix P u.tail

theorem failure_suffix (P : List (List α)) (u : List α) : failure P u <:+ u :=
  (longestNodeSuffix_suffix P u.tail).trans (List.tail_suffix u)

theorem length_failure_lt (P : List (List α)) {u : List α} (hu : u ≠ []) :
    (failure P u).length < u.length := by
  obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  have h := (longestNodeSuffix_suffix P u).length_le
  rw [failure_cons, List.length_cons]
  omega

theorem failure_eq_nil_of_length_le_one (P : List (List α)) {u : List α} (hu : u.length ≤ 1) :
    failure P u = [] := by
  match u, hu with
  | [], _ => exact failure_nil P
  | [_], _ => rw [failure_cons, longestNodeSuffix]

/-- `[AhoCorasick1975]`, Lemma 1: for a nonempty `u`, `failure P u` is the longest proper suffix of
`u` that is a goto-graph state. -/
theorem eq_failure_iff {P : List (List α)} {u v : List α} (hu : u ≠ []) :
    v = failure P u ↔ v <:+ u ∧ v.length < u.length ∧ IsNode P v ∧
      ∀ x, x <:+ u → x.length < u.length → IsNode P x → x.length ≤ v.length := by
  obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  have proper : ∀ x, x <:+ b :: u → x.length < (b :: u).length → x <:+ u := fun x hx hlt =>
    (List.suffix_cons_iff.mp hx).resolve_left fun h => by rw [h] at hlt; omega
  rw [failure_cons]
  constructor
  · rintro rfl
    have hsuf := longestNodeSuffix_suffix P u
    refine ⟨hsuf.trans (List.suffix_cons b u), ?_, isNode_longestNodeSuffix P u,
      fun x hx hlt hxn => length_le_longestNodeSuffix hxn (proper x hx hlt)⟩
    have := hsuf.length_le
    rw [List.length_cons]
    omega
  · rintro ⟨hvu, hlt, hvn, hmax⟩
    exact eq_longestNodeSuffix (proper v hvu hlt) hvn fun x hx hxn =>
      hmax x (hx.trans (List.suffix_cons b u))
        (by have := hx.length_le; rw [List.length_cons]; omega) hxn

/-! ## The next-move function -/

/-- The composite transition of one operating cycle: follow failure links from `u` until the goto
function is defined on `a`, then take that goto transition (the next-move function `δ` of
`[AhoCorasick1975]`, Section 6). -/
def nextMove (P : List (List α)) (u : List α) (a : α) : List α :=
  if IsNode P (u ++ [a]) then u ++ [a]
  else if _hu : u = [] then []
  else nextMove P (failure P u) a
termination_by u.length
decreasing_by exact length_failure_lt P _hu

theorem nextMove_of_isNode {P : List (List α)} {u : List α} {a : α} (h : IsNode P (u ++ [a])) :
    nextMove P u a = u ++ [a] := by
  rw [nextMove]
  simp only [h, ↓reduceIte]

theorem nextMove_of_not_isNode_of_eq_nil {P : List (List α)} {u : List α} {a : α}
    (h : ¬ IsNode P (u ++ [a])) (hu : u = []) : nextMove P u a = [] := by
  subst hu
  rw [nextMove]
  simp only [h, ↓reduceIte, ↓reduceDIte]

theorem nextMove_of_not_isNode {P : List (List α)} {u : List α} {a : α}
    (h : ¬ IsNode P (u ++ [a])) (hu : u ≠ []) : nextMove P u a = nextMove P (failure P u) a := by
  rw [nextMove]
  simp only [h, hu, ↓reduceIte, ↓reduceDIte]

theorem nextMove_eq_longestNodeSuffix (P : List (List α)) (u : List α) (a : α) :
    nextMove P u a = longestNodeSuffix P (u ++ [a]) := by
  induction h : u.length using Nat.strongRecOn generalizing u with
  | ind n ih =>
    rw [nextMove]
    split_ifs with hnode hu
    · exact (longestNodeSuffix_of_isNode hnode).symm
    · subst hu
      rw [List.nil_append] at hnode ⊢
      rw [longestNodeSuffix_cons_of_not_isNode hnode]
      rfl
    · obtain ⟨b, u', rfl⟩ := List.exists_cons_of_ne_nil hu
      rw [ih _ (h ▸ length_failure_lt P hu) _ rfl, failure_cons,
        longestNodeSuffix_append_singleton, List.cons_append,
        longestNodeSuffix_cons_of_not_isNode (by rwa [← List.cons_append])]

/-- `[AhoCorasick1975]`, Lemma 3 (one cycle): the longest node suffix of `w ++ [a]` is reached from
the longest node suffix of `w` by one operating cycle. -/
theorem longestNodeSuffix_append_singleton_eq_nextMove (P : List (List α)) (w : List α) (a : α) :
    longestNodeSuffix P (w ++ [a]) = nextMove P (longestNodeSuffix P w) a := by
  rw [nextMove_eq_longestNodeSuffix, longestNodeSuffix_append_singleton]

/-- The recurrence used by Algorithm 3 of `[AhoCorasick1975]`: for nonempty `u`, the failure state
of `u ++ [a]` is reached from the failure state of `u` by one operating cycle on `a`. -/
theorem failure_append_singleton (P : List (List α)) {u : List α} (hu : u ≠ []) (a : α) :
    failure P (u ++ [a]) = nextMove P (failure P u) a := by
  obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  rw [List.cons_append, failure_cons, failure_cons, longestNodeSuffix_append_singleton_eq_nextMove]

/-! ## Output function -/

/-- The keywords of `P` that are nonempty suffixes of `w`, longest first, without repetitions. -/
def output (P : List (List α)) : List α → List (List α)
  | [] => []
  | b :: w => if b :: w ∈ P then (b :: w) :: output P w else output P w

@[simp]
theorem output_nil (P : List (List α)) : output P [] = [] := by
  rw [output]

theorem output_cons (P : List (List α)) (b : α) (w : List α) :
    output P (b :: w) = if b :: w ∈ P then (b :: w) :: output P w else output P w := by
  rw [output]

theorem mem_output_iff {P : List (List α)} {w v : List α} :
    v ∈ output P w ↔ v ≠ [] ∧ v ∈ P ∧ v <:+ w := by
  induction w with
  | nil =>
    rw [output_nil, List.suffix_nil]
    simp only [List.not_mem_nil, false_iff, not_and]
    intro hv _ hv'
    exact hv hv'
  | cons b w ih =>
    rw [output, List.suffix_cons_iff]
    split_ifs with h
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hv, hvP, hvw⟩)
        · exact ⟨List.cons_ne_nil b w, h, Or.inl rfl⟩
        · exact ⟨hv, hvP, Or.inr hvw⟩
      · rintro ⟨hv, hvP, rfl | hvw⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hv, hvP, hvw⟩
    · rw [ih]
      constructor
      · rintro ⟨hv, hvP, hvw⟩
        exact ⟨hv, hvP, Or.inr hvw⟩
      · rintro ⟨hv, hvP, rfl | hvw⟩
        · exact absurd hvP h
        · exact ⟨hv, hvP, hvw⟩

theorem pairwise_length_gt_output (P : List (List α)) (w : List α) :
    (output P w).Pairwise (fun x y => y.length < x.length) := by
  induction w with
  | nil =>
    rw [output_nil]
    exact List.Pairwise.nil
  | cons b w ih =>
    rw [output]
    split_ifs
    · refine List.Pairwise.cons (fun y hy => ?_) ih
      have := (mem_output_iff.mp hy).2.2.length_le
      rw [List.length_cons]
      omega
    · exact ih

theorem nodup_output (P : List (List α)) (w : List α) : (output P w).Nodup :=
  (pairwise_length_gt_output P w).imp fun h heq => by rw [heq] at h; omega

/-- Keywords that are suffixes of `w` are the keywords that are suffixes of its longest node
suffix. -/
theorem output_longestNodeSuffix (P : List (List α)) (w : List α) :
    output P (longestNodeSuffix P w) = output P w := by
  induction w with
  | nil => rw [longestNodeSuffix]
  | cons b w ih =>
    by_cases h : IsNode P (b :: w)
    · rw [longestNodeSuffix_of_isNode h]
    · rw [longestNodeSuffix_cons_of_not_isNode h, ih, output]
      simp only [mt isNode_of_mem h, ↓reduceIte]

/-- `[AhoCorasick1975]`, Lemma 2 and the last statement of Algorithm 3: the output of a nonempty
state `u` is `u` itself (when `u` is a keyword) followed by the output of its failure state. -/
theorem output_eq_of_ne_nil (P : List (List α)) {u : List α} (hu : u ≠ []) :
    output P u = (if u ∈ P then [u] else []) ++ output P (failure P u) := by
  obtain ⟨b, u, rfl⟩ := List.exists_cons_of_ne_nil hu
  rw [failure_cons, output_longestNodeSuffix, output]
  split_ifs <;> rfl

/-! ## Occurrences -/

/-- Keyword `y ∈ P` ends at position `i` of `t` (`1`-indexed end position, as in
`[AhoCorasick1975]`, Algorithm 1): `y` is nonempty and a suffix of `t.take i`, with
`i ≤ t.length`. -/
@[expose] def IsOccurrence (P : List (List α)) (t : List α) (i : ℕ) (y : List α) : Prop :=
  i ≤ t.length ∧ y ≠ [] ∧ y ∈ P ∧ y <:+ t.take i

/-- All occurrences of keywords of `P` in `t`, by increasing end position and, at equal end
positions, by decreasing length. -/
def occurrences (P : List (List α)) (t : List α) : List (ℕ × List α) :=
  (List.range (t.length + 1)).flatMap fun i => (output P (t.take i)).map fun y => (i, y)

theorem mem_occurrences_iff {P : List (List α)} {t : List α} {i : ℕ} {y : List α} :
    (i, y) ∈ occurrences P t ↔ IsOccurrence P t i y := by
  simp only [occurrences, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq,
    mem_output_iff, IsOccurrence]
  constructor
  · rintro ⟨j, hj, z, ⟨hz, hzP, hzt⟩, rfl, rfl⟩
    exact ⟨by omega, hz, hzP, hzt⟩
  · rintro ⟨hi, hy, hyP, hyt⟩
    exact ⟨i, by omega, y, ⟨hy, hyP, hyt⟩, rfl, rfl⟩

theorem nodup_occurrences (P : List (List α)) (t : List α) : (occurrences P t).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ => (nodup_output P _).map fun _ _ h => (Prod.mk.inj h).2,
    (List.nodup_range).pairwise_of_forall_ne fun i _ j _ hij x hxi hxj => ?_⟩
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hxi
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hxj
  exact hij (Prod.mk.inj hz).1.symm

@[simp]
theorem occurrences_nil (P : List (List α)) : occurrences P [] = [] := by
  simp only [occurrences, List.length_nil, Nat.zero_add, List.range_one, List.flatMap_cons,
    List.take_nil, output_nil, List.map_nil, List.flatMap_nil, List.append_nil]

/-- Appending a symbol to the text appends the occurrences ending at the new last position. -/
theorem occurrences_append_singleton (P : List (List α)) (w : List α) (a : α) :
    occurrences P (w ++ [a]) =
      occurrences P w ++ (output P (w ++ [a])).map fun y => (w.length + 1, y) := by
  rw [occurrences, List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
    List.flatMap_singleton, occurrences,
    List.take_of_length_le (by rw [List.length_append, List.length_singleton]; exact Nat.le_refl _)]
  congr 1
  refine List.flatMap_congr fun i hi => ?_
  rw [List.take_append_of_le_length (by have := List.mem_range.mp hi; omega)]

/-- `[AhoCorasick1975]`, Lemma 3, from an arbitrary text prefix: running the operating cycles on
`w` from the state of `u` reaches the state of `u ++ w`. -/
theorem foldl_nextMove_longestNodeSuffix (P : List (List α)) (u w : List α) :
    w.foldl (nextMove P) (longestNodeSuffix P u) = longestNodeSuffix P (u ++ w) := by
  induction w generalizing u with
  | nil => rw [List.foldl_nil, List.append_nil]
  | cons a w ih =>
    rw [List.foldl_cons, ← longestNodeSuffix_append_singleton_eq_nextMove, ih, List.append_assoc,
      List.singleton_append]

/-- `[AhoCorasick1975]`, Lemma 3: after the operating cycles on `w` from the start state, the
state is the longest suffix of `w` that is a goto-graph state. -/
theorem foldl_nextMove (P : List (List α)) (w : List α) :
    w.foldl (nextMove P) [] = longestNodeSuffix P w := by
  have h := foldl_nextMove_longestNodeSuffix P [] w
  rwa [longestNodeSuffix_nil, List.nil_append] at h

/-- Occurrences are listed by increasing end position and, at equal end positions, by decreasing
keyword length. -/
theorem pairwise_occurrences (P : List (List α)) (t : List α) :
    (occurrences P t).Pairwise fun x y =>
      x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2.length < x.2.length) := by
  rw [occurrences, List.pairwise_flatMap]
  refine ⟨fun i _ => ?_, List.pairwise_lt_range.imp fun {i j} hij x hx y hy => ?_⟩
  · rw [List.pairwise_map]
    exact (pairwise_length_gt_output P _).imp fun h => Or.inr ⟨rfl, h⟩
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hy
    exact Or.inl hij

end Cslib.Algorithms.Lean.AhoCorasick
