/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.Walk

/-!
# Reversing and joining indexed incidence trails

These elementary list operations support parent-path assembly in the edge-CSP forest search.
Reversal preserves the underlying trail predicate. Prefix validity requires separate reasoning
about the selected DAG subpaths; no closure of arbitrary f-walks under reversal is asserted.

## Main definitions

* `Cslib.Logic.PL.CSP.Walk.reverse`: reverse the step order and swap each incidence pair.
* `Cslib.Logic.PL.CSP.Walk.append`: concatenate candidate step lists.

## Main results

* `Cslib.Logic.PL.CSP.Walk.IsWalk.reverse`: reversal preserves incidence trails.
* `Cslib.Logic.PL.CSP.Walk.IsWalk.append`: linked disjoint trails concatenate.
* `Cslib.Logic.PL.CSP.Walk.flip_reverse`: reversal leaves the flipped incidence set unchanged.
* `Cslib.Logic.PL.CSP.Walk.IsFPrefix.take`: closure under prefixes.
* `Cslib.Logic.PL.CSP.Walk.IsFPrefix.not_inconsistent_finish_take`:
  consistency at positive proper endpoints.
-/

public section

namespace Cslib.Logic.PL.CSP.Walk

variable {Rel V : Type*} {F : CSP Rel V}

/-- Reverse the step order and swap the two incidences of each candidate step. -/
@[expose] def reverse (w : Walk F) : Walk F :=
  ⟨w.finish, w.steps.reverse.map Prod.swap⟩

/-- Concatenate candidate steps, retaining the first candidate's starting variable. -/
@[expose] def append (w z : Walk F) : Walk F := ⟨w.start, w.steps ++ z.steps⟩

/-- Reversing all incidence pairs reverses the traversed incidence list. -/
theorem edgesOf_reverse_map_swap (s : List (Occurrence F × Occurrence F)) :
    edgesOf (s.reverse.map Prod.swap) = (edgesOf s).reverse := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    rcases a with ⟨o, p⟩
    rw [List.reverse_cons, List.map_append]
    change edgesOf (s.reverse.map Prod.swap ++ [(p, o)]) = (edgesOf ((o, p) :: s)).reverse
    rw [edgesOf_append, ih]
    change (edgesOf s).reverse ++ [p, o] = (o :: p :: edgesOf s).reverse
    rw [List.reverse_cons, List.reverse_cons, List.append_assoc]
    rfl

/-- A reversed candidate traverses precisely the original incidences in reverse order. -/
@[simp] theorem edges_reverse (w : Walk F) : w.reverse.edges = w.edges.reverse :=
  edgesOf_reverse_map_swap w.steps

/-- A linked candidate returns to its original start when read in reverse. -/
theorem Linked.finishFrom_reverse {v : V} {s : List (Occurrence F × Occurrence F)}
    (h : Linked v s) :
    finishFrom (finishFrom v s) (s.reverse.map Prod.swap) = v := by
  cases s with
  | nil => rfl
  | cons a s =>
    rcases a with ⟨o, p⟩
    rw [List.reverse_cons, List.map_append, finishFrom_append]
    exact h.1

/-- Incidence linkage is preserved by reversing a trail's candidate steps. -/
theorem Linked.reverse {v : V} {s : List (Occurrence F × Occurrence F)}
    (h : Linked v s) : Linked (finishFrom v s) (s.reverse.map Prod.swap) := by
  induction s generalizing v with
  | nil => trivial
  | cons a s ih =>
    rcases a with ⟨o, p⟩
    obtain ⟨ho, hc, hs⟩ := h
    rw [List.reverse_cons, List.map_append]
    change Linked (finishFrom p.var s) (s.reverse.map Prod.swap ++ [(p, o)])
    exact (ih hs).snoc hs.finishFrom_reverse.symm hc.symm

/-- The endpoint of a reversed linked candidate is its original starting variable. -/
@[simp] theorem finish_reverse (w : Walk F) (h : Linked w.start w.steps) :
    w.reverse.finish = w.start := h.finishFrom_reverse

/-- Reversing a trail preserves linkage and absence of repeated incidences. -/
theorem IsWalk.reverse {w : Walk F} (h : w.IsWalk) : w.reverse.IsWalk :=
  ⟨h.1.reverse, by rw [edges_reverse]; exact List.nodup_reverse.mpr h.2⟩

/-- Concatenation appends the two traversed incidence lists. -/
@[simp] theorem edges_append (w z : Walk F) : (w.append z).edges = w.edges ++ z.edges :=
  edgesOf_append w.steps z.steps

/-- Linked incidence trails concatenate when their incidence lists are disjoint. -/
theorem IsWalk.append {w z : Walk F} (hw : w.IsWalk) (hz : z.IsWalk)
    (hend : w.finish = z.start) (hd : List.Disjoint w.edges z.edges) :
    (w.append z).IsWalk := by
  constructor
  · change Linked w.start (w.steps ++ z.steps)
    rw [linked_append_iff]
    refine ⟨hw.1, ?_⟩
    change Linked w.finish z.steps
    rw [hend]
    exact hz.1
  · rw [edges_append]
    apply List.nodup_append.mpr
    refine ⟨hw.2, hz.2, ?_⟩
    intro a ha b hb he
    subst b
    exact hd ha hb

/-- The set of flipped incidences is independent of traversal orientation. -/
theorem flip_reverse (w : Walk F) (f : OccurrenceLabeling F Bool) :
    w.reverse.flip f = w.flip f := by
  simp only [flip, edges_reverse, List.toFinset_reverse]

/-- Every shorter candidate prefix inherits validity after each of its prefixes. -/
theorem PrefixValid.take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {s : List (Occurrence F × Occurrence F)}
    (h : PrefixValid sem f s) (n : ℕ) : PrefixValid sem f (s.take n) := by
  induction n generalizing f s with
  | zero =>
    cases s with
    | nil => exact h
    | cons a s => exact h.1
  | succ n ih =>
    cases s with
    | nil => exact h
    | cons a s => exact ⟨h.1, ih h.2⟩

/-- Internal consistency is inherited by a shorter candidate prefix. -/
theorem InternallyConsistent.take {f : OccurrenceLabeling F Bool}
    {s : List (Occurrence F × Occurrence F)} (h : InternallyConsistent f s) (n : ℕ) :
    InternallyConsistent f (s.take n) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    cases s with
    | nil => trivial
    | cons a s =>
      refine ⟨?_, ih h.2⟩
      rcases h.1 with hs | hc
      · exact Or.inl (by simp only [hs, List.take_nil])
      · exact Or.inr hc

/-- Every variable-ended prefix inherits the f-prefix conditions. -/
theorem IsFPrefix.take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (h : w.IsFPrefix sem f) (n : ℕ) :
    (w.take n).IsFPrefix sem f :=
  ⟨h.1.take n, h.2.1.take n, h.2.2.take n⟩

/-- A positive proper prefix ends at an original internal variable. -/
theorem InternallyConsistent.not_inconsistent_finishFrom_take
    {f : OccurrenceLabeling F Bool} {s : List (Occurrence F × Occurrence F)}
    (h : InternallyConsistent f s) (v : V) {n : ℕ} (hn : 0 < n) (hlt : n < s.length) :
    ¬ Inconsistent f (finishFrom v (s.take n)) := by
  induction n generalizing v s with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => simp at hlt
    | cons a s =>
      cases n with
      | zero =>
        change ¬ Inconsistent f a.2.var
        rcases h.1 with hs | hc
        · simp [hs] at hlt
        · exact hc
      | succ n =>
        exact ih h.2 a.2.var (Nat.succ_pos n) (by simpa using hlt)

/-- The endpoint of a positive proper f-prefix is consistent in the original labeling. -/
theorem IsFPrefix.not_inconsistent_finish_take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (h : w.IsFPrefix sem f)
    {n : ℕ} (hn : 0 < n) (hlt : n < w.steps.length) :
    ¬ Inconsistent f (w.take n).finish :=
  h.2.1.not_inconsistent_finishFrom_take w.start hn hlt

end Cslib.Logic.PL.CSP.Walk
