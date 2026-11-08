/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Edge.Defects
import Mathlib.Data.List.TakeDrop
import Complexity.Foundations.Data.Finset.SymmDiff

/-!
# Incidence trails and prefix-valid edge-CSP walks

A step is a pair of actual ordered occurrences in one constraint. Traversed incidences are
never reused, while constraint positions may repeat. Closed and length-zero trails are allowed.
`Walk.IsFWalk` additionally requires distinct variable endpoints, consistent internal variables,
and validity after every variable-ended prefix. This is Definitions 22–23 of
[KazdaKolmogorovRolinek2018], arXiv v6, printed p. 9.

## Main definitions

* `Walk.IsWalk`: a trail of indexed incidence pairs, allowing closed walks.
* `Walk.IsFWalk`: distinct endpoints, consistent internal variables, and prefix validity.
* `Walk.IsAugmenting`: an f-walk with two defective endpoints.

## Main results

* `Walk.IsWalk.partner_transition`: consecutive steps use the partner involution.
* `Walk.IsFPrefix.valid_take`: every variable-ended prefix flip is valid.
* `Walk.IsAugmenting.card_defects_flip_add_two`: augmentation removes exactly two defects.
-/

public section

namespace Cslib.Logic.PL.CSP

open BitString Finset
open scoped symmDiff

variable {Rel V : Type*} {F : CSP Rel V} [DecidableEq V]

/-- A variable-to-variable trail is represented by its starting variable and its sequence of
incidence pairs. `IsWalk` checks incidence adjacency and absence of repeated incidences. -/
structure Walk (F : CSP Rel V) where
  /-- Starting variable, also the endpoint of a length-zero trail. -/
  start : V
  /-- Ordered variable-to-variable steps, each represented by its two incidences. -/
  steps : List (Occurrence F × Occurrence F)

namespace Walk

/-- The terminal variable, also defined for length-zero walks. -/
@[expose] def finishFrom (v : V) : List (Occurrence F × Occurrence F) → V
  | [] => v
  | (_, p) :: s => finishFrom p.var s

/-- Terminal variable of a walk. -/
@[expose] def finish (w : Walk F) : V := finishFrom w.start w.steps

/-- Traversed incidences, in traversal order. -/
@[expose] def edgesOf (s : List (Occurrence F × Occurrence F)) : List (Occurrence F) :=
  s.flatMap fun (o, p) => [o, p]

/-- Traversed incidences of a walk. -/
@[expose] def edges (w : Walk F) : List (Occurrence F) := edgesOf w.steps

/-- Flip each incidence in a list of steps, in order. For a trail this is the set flip. -/
@[expose] def flipSteps (f : OccurrenceLabeling F Bool) :
    List (Occurrence F × Occurrence F) → OccurrenceLabeling F Bool
  | [] => f
  | (o, p) :: s => flipSteps (flipOn {o, p} f) s

/-- Flip the incidences of a walk. -/
@[expose] def flip (w : Walk F) (f : OccurrenceLabeling F Bool) :
    OccurrenceLabeling F Bool := flipOn w.edges.toFinset f

/-- Consecutive steps meet at their variable endpoints; the two incidences of each step
belong to the same positional constraint. -/
@[expose] def Linked (v : V) : List (Occurrence F × Occurrence F) → Prop
  | [] => True
  | (o, p) :: s => o.var = v ∧ o.1 = p.1 ∧ Linked p.var s

/-- An incidence trail, allowing closed trails and repeated constraint positions. -/
@[expose] def IsWalk (w : Walk F) : Prop := Linked w.start w.steps ∧ w.edges.Nodup

/-- Every intermediate labeling (including the initial one) is valid. -/
@[expose] def PrefixValid (sem : Rel → List Bool → Bool) :
    OccurrenceLabeling F Bool → List (Occurrence F × Occurrence F) → Prop
  | f, [] => ValidLabeling sem f
  | f, (o, p) :: s => ValidLabeling sem f ∧ PrefixValid sem (flipOn {o, p} f) s

/-- Internal variable endpoints are consistent in the original labeling. -/
@[expose] def InternallyConsistent (f : OccurrenceLabeling F Bool) :
    List (Occurrence F × Occurrence F) → Prop
  | [] => True
  | (_, p) :: s => (s = [] ∨ ¬ Inconsistent f p.var) ∧ InternallyConsistent f s

/-- The prefix conditions of an f-walk, permitting a length-zero initial prefix. -/
@[expose] def IsFPrefix (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (w : Walk F) : Prop :=
  w.IsWalk ∧ InternallyConsistent f w.steps ∧ PrefixValid sem f w.steps

/-- An f-walk has distinct variable endpoints, consistent internal variables, and a valid
labeling after every variable-ended prefix. Final validity alone does not suffice. -/
@[expose] def IsFWalk (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (w : Walk F) : Prop := w.IsFPrefix sem f ∧ w.start ≠ w.finish

/-- An augmenting f-walk has two f-inconsistent variable endpoints. -/
@[expose] def IsAugmenting (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (w : Walk F) : Prop :=
  w.IsFWalk sem f ∧ Inconsistent f w.start ∧ Inconsistent f w.finish

/-- Append a variable-to-variable step. -/
@[expose] def snoc (w : Walk F) (o p : Occurrence F) : Walk F :=
  ⟨w.start, w.steps ++ [(o, p)]⟩

/-- A prefix ends at a variable, so it contains whole incidence pairs. -/
@[expose] def take (w : Walk F) (n : ℕ) : Walk F := ⟨w.start, w.steps.take n⟩

omit [DecidableEq V] in
@[simp] theorem edgesOf_cons (o p : Occurrence F)
    (s : List (Occurrence F × Occurrence F)) :
    edgesOf ((o, p) :: s) = o :: p :: edgesOf s := rfl

omit [DecidableEq V] in
@[simp]
theorem edgesOf_append (s t : List (Occurrence F × Occurrence F)) :
    edgesOf (s ++ t) = edgesOf s ++ edgesOf t := by
  simp [edgesOf]

omit [DecidableEq V] in
@[simp]
theorem finishFrom_append (v : V) (s t : List (Occurrence F × Occurrence F)) :
    finishFrom v (s ++ t) = finishFrom (finishFrom v s) t := by
  induction s generalizing v with
  | nil => rfl
  | cons a s ih => exact ih a.2.var

omit [DecidableEq V] in
@[simp]
theorem finish_snoc (w : Walk F) (o p : Occurrence F) :
    (w.snoc o p).finish = p.var := by
  simp [finish, snoc, finishFrom]

omit [DecidableEq V] in
/-- Stepwise and setwise flips agree for incidence trails. -/
theorem flipSteps_eq_flipOn (f : OccurrenceLabeling F Bool)
    (s : List (Occurrence F × Occurrence F)) (hs : (edgesOf s).Nodup) :
    flipSteps f s = flipOn (edgesOf s).toFinset f := by
  induction s generalizing f with
  | nil => simp [flipSteps, edgesOf]
  | cons a s ih =>
    rcases a with ⟨o, p⟩
    change (o :: p :: edgesOf s).Nodup at hs
    simp only [List.nodup_cons, List.mem_cons, not_or] at hs
    rw [flipSteps, ih _ hs.2.2]
    simp only [edgesOf_cons, List.toFinset_cons]
    change flipOn (edgesOf s).toFinset (flipOn {o, p} f) =
      flipOn (insert o (insert p (edgesOf s).toFinset)) f
    funext q
    simp only [flipOn_apply, mem_insert, mem_singleton]
    by_cases hqo : q = o <;> by_cases hqp : q = p <;>
      by_cases hqs : q ∈ (edgesOf s).toFinset <;> simp_all

omit [DecidableEq V] in
/-- Prefix validity includes validity after the final step. -/
theorem PrefixValid.final {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {s : List (Occurrence F × Occurrence F)}
    (h : PrefixValid sem f s) : ValidLabeling sem (flipSteps f s) := by
  induction s generalizing f with
  | nil => exact h
  | cons a s ih => exact ih h.2

omit [DecidableEq V] in
/-- In particular, the set flip of an f-walk is valid. -/
theorem IsFPrefix.valid_flip {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (h : w.IsFPrefix sem f) :
    ValidLabeling sem (w.flip f) := by
  rw [flip, edges, ← flipSteps_eq_flipOn f w.steps h.1.2]
  exact h.2.2.final

omit [DecidableEq V] in
/-- Flipping concatenated step lists is sequential composition. -/
theorem flipSteps_append (f : OccurrenceLabeling F Bool)
    (s t : List (Occurrence F × Occurrence F)) :
    flipSteps f (s ++ t) = flipSteps (flipSteps f s) t := by
  induction s generalizing f with
  | nil => rfl
  | cons a s ih => exact ih _

omit [DecidableEq V] in
private theorem nodup_edges_snoc (w : Walk F) (o p : Occurrence F)
    (hw : w.edges.Nodup) (ho : o ∉ w.edges) (hp : p ∉ w.edges) (hop : o ≠ p) :
    (w.snoc o p).edges.Nodup := by
  change (edgesOf (w.steps ++ [(o, p)])).Nodup
  rw [edgesOf_append]
  change (w.edges ++ [o, p]).Nodup
  rw [List.nodup_append]
  refine ⟨hw, by simp [hop], ?_⟩
  intro a ha b hb he
  subst b
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact ho ha
  · exact hp ha

omit [DecidableEq V] in
/-- Appending one fresh step flips precisely its two incidences. -/
theorem flip_snoc (w : Walk F) (f : OccurrenceLabeling F Bool) (o p : Occurrence F)
    (hw : w.IsWalk) (ho : o ∉ w.edges) (hp : p ∉ w.edges) (hop : o ≠ p) :
    (w.snoc o p).flip f = flipOn {o, p} (w.flip f) := by
  have hn := nodup_edges_snoc w o p hw.2 ho hp hop
  rw [flip, edges, ← flipSteps_eq_flipOn f _ hn, snoc, flipSteps_append,
    flipSteps, flipSteps, flip, edges, ← flipSteps_eq_flipOn f _ hw.2]

omit [DecidableEq V] in
/-- Incidence adjacency is preserved by a step from the previous endpoint. -/
theorem Linked.snoc {v : V} {s : List (Occurrence F × Occurrence F)}
    (hl : Linked v s) {o p : Occurrence F} (ho : o.var = finishFrom v s)
    (hc : o.1 = p.1) : Linked v (s ++ [(o, p)]) := by
  induction s generalizing v with
  | nil => exact ⟨ho, hc, trivial⟩
  | cons a s ih => exact ⟨hl.1, hl.2.1, ih hl.2.2 ho⟩

omit [DecidableEq V] in
/-- All prefixes remain valid after a valid final step is appended. -/
theorem PrefixValid.snoc {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {s : List (Occurrence F × Occurrence F)}
    (hv : PrefixValid sem f s) (o p : Occurrence F)
    (hn : ValidLabeling sem (flipOn {o, p} (flipSteps f s))) :
    PrefixValid sem f (s ++ [(o, p)]) := by
  induction s generalizing f with
  | nil => exact ⟨hv, hn⟩
  | cons a s ih => exact ⟨hv.1, ih hv.2 hn⟩

omit [DecidableEq V] in
/-- The old endpoint becomes an internal variable when appending a step. -/
theorem InternallyConsistent.snoc {f : OccurrenceLabeling F Bool}
    {s : List (Occurrence F × Occurrence F)} (hi : InternallyConsistent f s)
    (v : V) (o p : Occurrence F)
    (hend : s = [] ∨ ¬ Inconsistent f (finishFrom v s)) :
    InternallyConsistent f (s ++ [(o, p)]) := by
  induction s generalizing v with
  | nil => exact ⟨Or.inl rfl, trivial⟩
  | cons a s ih =>
    have hend' : ¬ Inconsistent f (finishFrom a.2.var s) := hend.resolve_left (by simp)
    refine ⟨Or.inr ?_, ih hi.2 a.2.var (Or.inr hend')⟩
    rcases hi.1 with he | he
    · subst s
      exact hend'
    · exact he

omit [DecidableEq V] in
/-- Append a fresh locally valid step to a prefix-valid trail. -/
theorem IsFPrefix.snoc {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (hw : w.IsFPrefix sem f)
    {o p : Occurrence F} (ho : o.var = w.finish) (hc : o.1 = p.1)
    (hne : o ≠ p) (hno : o ∉ w.edges) (hnp : p ∉ w.edges)
    (hi : w.steps = [] ∨ ¬ Inconsistent f w.finish)
    (hv : ValidLabeling sem (flipOn {o, p} (w.flip f))) :
    (w.snoc o p).IsFPrefix sem f := by
  refine ⟨⟨hw.1.1.snoc ho hc, ?_⟩, hw.2.1.snoc w.start o p hi, ?_⟩
  · exact nodup_edges_snoc w o p hw.1.2 hno hnp hne
  · apply hw.2.2.snoc o p
    rwa [flipSteps_eq_flipOn f w.steps hw.1.2]

/-- The set of defects after a trail flip differs only at its variable endpoints.
This includes closed trails, whose endpoint toggles cancel. -/
theorem IsWalk.defects_flip (h : EdgeInstance F) {w : Walk F} (hw : w.IsWalk)
    (f : OccurrenceLabeling F Bool) :
    defects (w.flip f) = defects f ∆ {w.start} ∆ {w.finish} := by
  obtain ⟨v, s⟩ := w
  rw [flip, edges, ← flipSteps_eq_flipOn f s hw.2]
  change defects (flipSteps f s) = defects f ∆ {v} ∆ {finishFrom v s}
  induction s generalizing v f with
  | nil => simp [flipSteps, finishFrom]
  | cons a s ih =>
    rcases a with ⟨o, p⟩
    obtain ⟨hl, hn⟩ := hw
    change (o :: p :: edgesOf s).Nodup at hn
    simp only [List.nodup_cons, List.mem_cons, not_or] at hn
    have hs : (edgesOf s).Nodup := hn.2.2
    have hop : o ≠ p := hn.1.1
    have hv := h.var_ne_of_constraint_eq hl.2.1 hop
    rw [flipSteps, ih _ p.var ⟨hl.2.2, hs⟩, h.defects_flipOn_pair f hl.2.1 hop]
    rw [← (show o.var = v from hl.1)]
    simp only [finishFrom]
    ext z
    simp only [mem_symmDiff, mem_insert, mem_singleton]
    by_cases hz : z = o.var <;> by_cases hz' : z = p.var <;> simp_all

/-- Augmentation removes exactly two distinct variable defects. -/
theorem IsAugmenting.card_defects_flip_add_two (h : EdgeInstance F)
    {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool} {w : Walk F}
    (hw : w.IsAugmenting sem f) : (defects (w.flip f)).card + 2 = (defects f).card := by
  rw [hw.1.1.1.defects_flip h, symmDiff_singleton_eq (defects f) w.start,
    ite_eq_left (mem_defects.mpr hw.2.1)]
  have hend : w.finish ∈ (defects f).erase w.start :=
    mem_erase.mpr ⟨hw.1.2.symm, mem_defects.mpr hw.2.2⟩
  rw [symmDiff_singleton_eq, ite_eq_left hend]
  have ha := card_erase_add_one (mem_defects.mpr hw.2.1)
  have hb := card_erase_add_one hend
  omega

omit [DecidableEq V] in
/-- The recursive prefix condition is exactly validity after every variable-ended prefix,
including the initial labeling. -/
theorem prefixValid_iff_forall_take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {s : List (Occurrence F × Occurrence F)} :
    PrefixValid sem f s ↔
      ∀ n ≤ s.length, ValidLabeling sem (flipSteps f (s.take n)) := by
  induction s generalizing f with
  | nil => simp [PrefixValid, flipSteps]
  | cons a s ih =>
    constructor
    · intro hv n hn
      cases n with
      | zero => exact hv.1
      | succ n => exact ih.mp hv.2 n (by simpa only [List.length_cons,
          Nat.succ_le_succ_iff] using hn)
    · intro hv
      exact ⟨hv 0 (Nat.zero_le _), ih.mpr fun n hn => hv (n + 1)
        (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hn)⟩

omit [DecidableEq V] in
/-- Splitting a trail at a variable preserves the positional adjacency conditions. -/
theorem linked_append_iff (v : V) (s t : List (Occurrence F × Occurrence F)) :
    Linked v (s ++ t) ↔ Linked v s ∧ Linked (finishFrom v s) t := by
  induction s generalizing v with
  | nil => simp [Linked, finishFrom]
  | cons a s ih =>
    simp only [List.cons_append, Linked, finishFrom, ih]
    tauto

omit [DecidableEq V] in
/-- Consecutive constraint steps cross a variable by its actual partner incidence.
No incidence may be traversed in both directions or reused at a later visit. -/
theorem IsWalk.partner_transition (h : EdgeInstance F) {w : Walk F} (hw : w.IsWalk)
    {s t : List (Occurrence F × Occurrence F)} {a b o p : Occurrence F}
    (he : w.steps = s ++ (a, b) :: (o, p) :: t) : o = h.partner b := by
  obtain ⟨hl, hn⟩ := hw
  rw [he, linked_append_iff] at hl
  have hov : o.var = b.var := hl.2.2.2.1
  change (edgesOf w.steps).Nodup at hn
  rw [he, edgesOf_append, List.nodup_append] at hn
  have ht := hn.2.1
  change (a :: b :: o :: p :: edgesOf t).Nodup at ht
  simp only [List.nodup_cons, List.mem_cons, not_or] at ht
  rcases h.eq_or_eq_partner hov with hob | hob
  · exact (ht.2.1.1 hob.symm).elim
  · exact hob

omit [DecidableEq V] in
/-- Every variable-ended prefix of an incidence trail is itself an incidence trail. -/
theorem IsWalk.take {w : Walk F} (hw : w.IsWalk) (n : ℕ) : (w.take n).IsWalk := by
  refine ⟨?_, ?_⟩
  · have ht := (linked_append_iff w.start (w.steps.take n) (w.steps.drop n)).mp
      (by simpa only [List.take_append_drop] using hw.1)
    exact ht.1
  · exact ((List.take_sublist n w.steps).flatMap fun (o, p) => [o, p]).nodup hw.2

omit [DecidableEq V] in
/-- Every variable-ended prefix flip of an f-prefix is valid, in the set-flip formulation
of Definition 23. This includes prefixes shorter than a returned augmenting walk. -/
theorem IsFPrefix.valid_take {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F} (hw : w.IsFPrefix sem f)
    (n : ℕ) (hn : n ≤ w.steps.length) : ValidLabeling sem ((w.take n).flip f) := by
  rw [flip, edges, ← flipSteps_eq_flipOn f _ (hw.1.take n).2]
  exact prefixValid_iff_forall_take.mp hw.2.2 n hn

end Walk

end Cslib.Logic.PL.CSP
