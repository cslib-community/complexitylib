/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Logic.Function.DependsOn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Witness structures for the Moser–Tardos algorithm

Moser and Tardos [MoserTardos2010] analyse the resampling algorithm for the variable version of the
Lovász Local Lemma. There are finitely many events `A i`, and each `A i` is determined by the
variables in a finite set `vbl i`. The randomness is a *table* `T`: the sample `T (v, n)` is the
value variable `v` takes after its `n`-th resampling. A run of the algorithm is recorded by a
*log* `w` (latest step first), and `current vbl T w` is the assignment after the steps of `w`.
`IsLog vbl A T w` says that each step of `w` resamples an event that occurs at that point; it does
not constrain which occurring event is chosen.

To the step `i :: w` of a log the paper attaches a witness tree, built by scanning the history
backwards and attaching each earlier step below the deepest vertex whose label shares a variable
with it [MoserTardos2010, Section 2]. The check of a tree only reads the label and depth of each
vertex. So we record a tree as its finite set of `(label, depth)` pairs, the *witness structure*
`witness vbl i w`, and the tree check becomes `Check vbl A S T`: for every vertex `p` of `S`, the
assignment that reads the next sample of each variable of `vbl p.1` after the samples consumed by
the deeper vertices lies in `A p.1`.

## Main definitions

* `Cslib.Probability.MoserTardos.current`, `Cslib.Probability.MoserTardos.IsLog`: the
  assignment after a log and the validity of a log on a table.
* `Cslib.Probability.MoserTardos.Adj`: labels that are equal or share a variable (the paper's
  inclusive neighbourhood `Γ⁺`).
* `Cslib.Probability.MoserTardos.witness`: the witness structure of a step.
* `Cslib.Probability.MoserTardos.Check`, `Cslib.Probability.MoserTardos.Proper`: the check of a
  structure on a table, and properness (no two vertices on one level share a variable).
* `Cslib.Probability.MoserTardos.shapes`: the finite set of structures rooted at `i` of depth at
  most `H` in which each vertex is adjacent to a vertex one level up.

## Main results

* `Cslib.Probability.MoserTardos.check_witness`: if `i :: w` is a valid log on `T`, the witness
  structure of the step passes its check on `T` (the coupling of [MoserTardos2010, Lemma 2.1]).
* `Cslib.Probability.MoserTardos.proper_witness`: witness structures are proper, in the
  level-independence sense proved in [MoserTardos2010, Lemma 2.1(i)].
* `Cslib.Probability.MoserTardos.exists_witnesses`: the steps labelled `i` of a valid log give
  that many distinct proper structures in `shapes`, all passing their checks.
* `Cslib.Probability.MoserTardos.depthUses_ne`: on a proper structure, distinct vertices whose
  labels share a variable read different samples of it.
* `Cslib.Probability.MoserTardos.sum_prod_shapes_le`: under the local-lemma hypothesis, the
  products `∏ p ∈ S, y p.1` sum over `shapes vbl i H` to at most `x i / (1 - x i)`
  [MoserTardos2010, Section 3].

The paper bounds this sum by comparing a Galton–Watson process with the witness trees. We prove it
by induction on the depth: the factor `∏ B ∈ Γ⁺ C, (1 - x B)⁻¹` charged to each label `C` on the
deepest level pays for every choice of children of that level.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

open Finset

namespace Cslib.Probability.MoserTardos

variable {V ι : Type*} {α : V → Type*}

section Log

variable [DecidableEq V] (vbl : ι → Finset V)

/-- The number of entries of `w` whose variable set contains `v`: how often `v` has been
resampled by the steps of `w`. -/
def uses (w : List ι) (v : V) : ℕ := (w.filter fun i => decide (v ∈ vbl i)).length

/-- The assignment after the resamplings recorded in the log `w` (latest first): variable `v`
holds its sample number `uses vbl w v` of the table `T`. -/
def current (T : ∀ p : V × ℕ, α p.1) (w : List ι) : ∀ v, α v :=
  fun v => T (v, uses vbl w v)

/-- `w` (latest first) is a valid log on the table `T`: every step resamples an event that occurs
in the assignment produced by the earlier steps. -/
def IsLog (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) : List ι → Prop
  | [] => True
  | i :: w => current vbl T w ∈ A i ∧ IsLog A T w

theorem current_apply (T : ∀ p : V × ℕ, α p.1) (w : List ι) (v : V) :
    current vbl T w v = T (v, uses vbl w v) := by
  rw [current]

theorem isLog_nil (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) : IsLog vbl A T [] := by
  rw [IsLog]
  trivial

theorem isLog_cons {A : ι → Set (∀ v, α v)} {T : ∀ p : V × ℕ, α p.1} {i : ι} {w : List ι} :
    IsLog vbl A T (i :: w) ↔ current vbl T w ∈ A i ∧ IsLog vbl A T w := by
  rw [IsLog]

/-- The table after the samples read by one resampling of `j`. -/
private def shift (j : ι) (T : ∀ p : V × ℕ, α p.1) : ∀ p : V × ℕ, α p.1 :=
  fun p => T (p.1, p.2 + if p.1 ∈ vbl j then 1 else 0)

private theorem uses_append (w : List ι) (j : ι) (v : V) :
    uses vbl (w ++ [j]) v = uses vbl w v + if v ∈ vbl j then 1 else 0 := by
  unfold uses
  by_cases h : v ∈ vbl j <;> simp [List.filter_append, h]

private theorem current_append (T : ∀ p : V × ℕ, α p.1) (w : List ι) (j : ι) :
    current vbl T (w ++ [j]) = current vbl (shift vbl j T) w := by
  funext v
  simp only [current, shift]
  rw [uses_append]

private theorem isLog_append (A : ι → Set (∀ v, α v)) (T : ∀ p : V × ℕ, α p.1) (j : ι) :
    ∀ w : List ι, IsLog vbl A T (w ++ [j]) ↔
      current vbl T [] ∈ A j ∧ IsLog vbl A (shift vbl j T) w
  | [] => by simp [IsLog]
  | i :: w => by
    simp only [List.cons_append, IsLog, current_append, isLog_append A T j w]
    tauto

end Log

section Structure

variable [DecidableEq V] [DecidableEq ι] (vbl : ι → Finset V)

/-- Labels `i` and `j` are equal or share a variable. -/
def Adj (i j : ι) : Prop := i = j ∨ ¬Disjoint (vbl i) (vbl j)

instance (i j : ι) : Decidable (Adj vbl i j) :=
  inferInstanceAs (Decidable (i = j ∨ ¬Disjoint (vbl i) (vbl j)))

omit [DecidableEq V] [DecidableEq ι] in
theorem adj_comm {i j : ι} : Adj vbl i j ↔ Adj vbl j i := by
  unfold Adj
  rw [eq_comm, disjoint_comm]

omit [DecidableEq V] [DecidableEq ι] in
theorem adj_of_mem {i j : ι} {v : V} (hi : v ∈ vbl i) (hj : v ∈ vbl j) : Adj vbl i j :=
  Or.inr (Finset.not_disjoint_iff.2 ⟨v, hi, hj⟩)

/-- One more than the deepest depth of a vertex of `S` adjacent to `j`, or `0` if there is
none. -/
private def level (j : ι) (S : Finset (ι × ℕ)) : ℕ :=
  (S.filter fun p => Adj vbl p.1 j).sup fun p => p.2 + 1

/-- Attach `j` one level below the deepest vertex adjacent to it, if there is one. -/
private def push (j : ι) (S : Finset (ι × ℕ)) : Finset (ι × ℕ) :=
  if level vbl j S = 0 then S else insert (j, level vbl j S) S

/-- The witness structure of the step labelled `i` with earlier history `w` (latest first): the
`(label, depth)` pairs of the witness tree of [MoserTardos2010, Section 2]. -/
def witness (i : ι) (w : List ι) : Finset (ι × ℕ) :=
  w.foldl (fun S j => push vbl j S) {(i, 0)}

/-- The number of vertices of `S` strictly deeper than `p` whose label contains `v`: the samples
of `v` consumed before vertex `p` in the check of `S`. -/
def depthUses (S : Finset (ι × ℕ)) (p : ι × ℕ) (v : V) : ℕ :=
  #(S.filter fun q => p.2 < q.2 ∧ v ∈ vbl q.1)

/-- The check of the structure `S` passes on the table `T`: processing the vertices from the
deepest level up, each vertex `p` finds `A p.1` occurring on the next samples of its variables. -/
def Check (A : ι → Set (∀ v, α v)) (S : Finset (ι × ℕ)) (T : ∀ p : V × ℕ, α p.1) : Prop :=
  ∀ p ∈ S, (fun v => T (v, depthUses vbl S p v)) ∈ A p.1

omit [DecidableEq ι] in
theorem check_iff {A : ι → Set (∀ v, α v)} {S : Finset (ι × ℕ)} {T : ∀ p : V × ℕ, α p.1} :
    Check vbl A S T ↔ ∀ p ∈ S, (fun v => T (v, depthUses vbl S p v)) ∈ A p.1 := by
  rw [Check]

/-- A structure is proper if distinct vertices on one level are not adjacent. This is the level
independence established in the proof of [MoserTardos2010, Lemma 2.1(i)]; it implies the paper's
properness (distinct children of a vertex receive distinct labels). -/
def Proper (S : Finset (ι × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p.2 = q.2 → ¬Adj vbl p.1 q.1

end Structure

section Coupling

variable [DecidableEq V] [DecidableEq ι] (vbl : ι → Finset V)

omit [DecidableEq ι] in
private theorem check_of_shift_of_not_adj (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {j : ι} {S : Finset (ι × ℕ)}
    (hS : ∀ q ∈ S, ¬Adj vbl q.1 j) {T : ∀ p : V × ℕ, α p.1}
    (h : Check vbl A S (shift vbl j T)) : Check vbl A S T := by
  intro p hp
  have hdisj : Disjoint (vbl p.1) (vbl j) := by
    have h' := hS p hp
    simp only [Adj, not_or, not_not] at h'
    exact h'.2
  refine (hA p.1 (fun v hv => ?_)).mp (h p hp)
  simp only [shift]
  rw [ite_eq_right (Finset.disjoint_left.1 hdisj (Finset.mem_coe.1 hv)), add_zero]

private theorem lt_level {j : ι} {S : Finset (ι × ℕ)} {q : ι × ℕ} (hq : q ∈ S)
    (h : Adj vbl q.1 j) : q.2 < level vbl j S :=
  Nat.lt_of_succ_le (le_sup (f := fun p : ι × ℕ => p.2 + 1) (mem_filter.2 ⟨hq, h⟩))

private theorem level_eq_zero {j : ι} {S : Finset (ι × ℕ)} (h : level vbl j S = 0) {q : ι × ℕ}
    (hq : q ∈ S) : ¬Adj vbl q.1 j := fun ha => by
  have := lt_level vbl hq ha
  omega

private theorem level_notMem (j : ι) (S : Finset (ι × ℕ)) : (j, level vbl j S) ∉ S := fun hm =>
  lt_irrefl _ (lt_level vbl (j := j) (q := (j, level vbl j S)) hm (Or.inl rfl))

private theorem depthUses_push_old {j : ι} {S : Finset (ι × ℕ)} {p : ι × ℕ} (hp : p ∈ S) {v : V}
    (hv : v ∈ vbl p.1) :
    depthUses vbl (insert (j, level vbl j S) S) p v =
      depthUses vbl S p v + if v ∈ vbl j then 1 else 0 := by
  unfold depthUses
  rw [filter_insert]
  by_cases hvj : v ∈ vbl j
  · have hlt : p.2 < level vbl j S := lt_level vbl hp (adj_of_mem vbl hv hvj)
    rw [ite_eq_left ⟨hlt, hvj⟩,
      card_insert_of_notMem (fun hm => level_notMem vbl j S (mem_filter.1 hm).1), ite_eq_left hvj]
  · rw [ite_eq_right (fun h => hvj h.2), ite_eq_right hvj, add_zero]

private theorem depthUses_push_new {j : ι} {S : Finset (ι × ℕ)} {v : V} (hv : v ∈ vbl j) :
    depthUses vbl (insert (j, level vbl j S) S) (j, level vbl j S) v = 0 := by
  unfold depthUses
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q hq ⟨hlt, hqv⟩
  rcases mem_insert.1 hq with rfl | hq
  · exact lt_irrefl _ hlt
  · exact lt_asymm hlt (lt_level vbl hq (adj_of_mem vbl hqv hv))

private theorem check_push (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {j : ι} {S : Finset (ι × ℕ)}
    {T : ∀ p : V × ℕ, α p.1} (hj : current vbl T [] ∈ A j)
    (h : Check vbl A S (shift vbl j T)) : Check vbl A (push vbl j S) T := by
  unfold push
  split_ifs with h0
  · exact check_of_shift_of_not_adj vbl A hA (fun q hq => level_eq_zero vbl h0 hq) h
  intro p hp
  rcases mem_insert.1 hp with rfl | hp
  · refine (hA j (fun v hv => ?_)).mp hj
    simp only [current, uses, List.filter_nil, List.length_nil]
    rw [depthUses_push_new vbl (Finset.mem_coe.1 hv)]
  · refine (hA p.1 (fun v hv => ?_)).mp (h p hp)
    simp only [shift]
    rw [depthUses_push_old vbl hp (Finset.mem_coe.1 hv)]

/-- **Coupling** [MoserTardos2010, Lemma 2.1]: if `i :: w` is a valid log on `T`, the witness
structure of its latest step passes its check on `T`. -/
theorem check_witness (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (i : ι) :
    ∀ (w : List ι) (T : ∀ p : V × ℕ, α p.1), IsLog vbl A T (i :: w) →
      Check vbl A (witness vbl i w) T := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro T h p hp
    rw [witness, List.foldl_nil, mem_singleton] at hp
    subst hp
    refine (hA i (fun v _ => ?_)).mp h.1
    have h0 : depthUses vbl {(i, 0)} (i, 0) v = 0 := by
      unfold depthUses
      rw [card_eq_zero, filter_eq_empty_iff]
      intro q hq hlt
      rw [mem_singleton.1 hq] at hlt
      exact lt_irrefl _ hlt.1
    simp only [current, uses, List.filter_nil, List.length_nil, witness, List.foldl_nil]
    rw [h0]
  | append_singleton w j ih =>
    intro T h
    rw [← List.cons_append, isLog_append] at h
    rw [witness, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact check_push vbl A hA h.1 (ih _ h.2)

end Coupling

section Proper

variable [DecidableEq V] [DecidableEq ι] (vbl : ι → Finset V)

private theorem proper_push {j : ι} {S : Finset (ι × ℕ)} (hS : Proper vbl S) :
    Proper vbl (push vbl j S) := by
  unfold push
  split_ifs with h0
  · exact hS
  have key : ∀ q ∈ S, q.2 = level vbl j S → ¬Adj vbl q.1 j := fun q hq he ha =>
    (lt_level vbl hq ha).ne he
  intro p hp q hq hpq he
  rcases mem_insert.1 hp with rfl | hp <;> rcases mem_insert.1 hq with rfl | hq
  · exact absurd rfl hpq
  · rw [adj_comm]
    exact key q hq he.symm
  · exact key p hp he
  · exact hS p hp q hq hpq he

/-- Witness structures are proper, in the level-independence sense of `Proper`
[MoserTardos2010, Lemma 2.1(i)]. -/
theorem proper_witness (i : ι) (w : List ι) : Proper vbl (witness vbl i w) := by
  unfold witness
  induction w using List.reverseRecOn with
  | nil =>
    intro p hp q hq hpq
    rw [List.foldl_nil, mem_singleton] at hp hq
    exact absurd (hp.trans hq.symm) hpq
  | append_singleton w j ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact proper_push vbl ih

omit [DecidableEq ι] in
/-- On a proper structure, distinct vertices whose labels both contain `v` read different samples
of `v`. -/
theorem depthUses_ne {S : Finset (ι × ℕ)} (hS : Proper vbl S) {p q : ι × ℕ} (hp : p ∈ S)
    (hq : q ∈ S) (hpq : p ≠ q) {v : V} (hvp : v ∈ vbl p.1) (hvq : v ∈ vbl q.1) :
    depthUses vbl S p v ≠ depthUses vbl S q v := by
  have key : ∀ {a b : ι × ℕ}, a ∈ S → b ∈ S → a.2 < b.2 → v ∈ vbl b.1 →
      depthUses vbl S b v < depthUses vbl S a v := by
    intro a b ha hb hlt hvb
    unfold depthUses
    refine card_lt_card ⟨fun r hr => ?_, fun hsub => ?_⟩
    · rw [mem_filter] at hr ⊢
      exact ⟨hr.1, hlt.trans hr.2.1, hr.2.2⟩
    · exact lt_irrefl _ (mem_filter.1 (hsub (mem_filter.2 ⟨hb, hlt, hvb⟩))).2.1
  rcases lt_trichotomy p.2 q.2 with h | h | h
  · exact (key hp hq h hvq).ne'
  · exact absurd (adj_of_mem vbl hvp hvq) (hS p hp q hq hpq h)
  · exact (key hq hp h hvp).ne

/-- The number of vertices of `S` labelled `i`. -/
private def labelCount (i : ι) (S : Finset (ι × ℕ)) : ℕ := #(S.filter fun p => p.1 = i)

private theorem labelCount_push_self {i : ι} {S : Finset (ι × ℕ)} (h : 0 < labelCount i S) :
    labelCount i (push vbl i S) = labelCount i S + 1 := by
  obtain ⟨q, hq⟩ := card_pos.1 h
  rw [mem_filter] at hq
  have hl : q.2 < level vbl i S := lt_level vbl hq.1 (Or.inl hq.2)
  unfold push labelCount
  rw [ite_eq_right (by omega), filter_insert, ite_eq_left rfl,
    card_insert_of_notMem (fun hm => level_notMem vbl i S (mem_filter.1 hm).1)]

private theorem labelCount_push_ne {i j : ι} (hij : j ≠ i) (S : Finset (ι × ℕ)) :
    labelCount i (push vbl j S) = labelCount i S := by
  unfold push labelCount
  split_ifs
  · rfl
  · rw [filter_insert, ite_eq_right hij]

private theorem labelCount_witness (i : ι) (w : List ι) :
    labelCount i (witness vbl i w) = w.count i + 1 := by
  unfold witness
  induction w using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, List.count_nil, zero_add, labelCount]
    rw [filter_singleton, ite_eq_left rfl, card_singleton]
  | append_singleton w j ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.count_append]
    by_cases hj : j = i
    · subst hj
      rw [labelCount_push_self vbl (by omega), ih, List.count_singleton_self]
    · rw [labelCount_push_ne vbl hj, ih, List.count_singleton]
      simp [hj]

end Proper

section Shapes

variable [DecidableEq V] [DecidableEq ι] [Fintype ι] (vbl : ι → Finset V)

/-- The labels on level `l` of `S`. -/
private def lvl (S : Finset (ι × ℕ)) (l : ℕ) : Finset ι :=
  (S.filter fun p => p.2 = l).image Prod.fst

/-- The labels adjacent to some label of `I`, including those of `I`. -/
private def nbr (I : Finset ι) : Finset ι := univ.filter fun j => ∃ i ∈ I, Adj vbl i j

/-- The structures rooted at `i` of depth at most `H` in which every label on level `l + 1` is
adjacent to some label on level `l`. They include all witness structures rooted at `i` of depth
at most `H`. -/
def shapes (i : ι) : ℕ → Finset (Finset (ι × ℕ))
  | 0 => {{(i, 0)}}
  | H + 1 => (shapes i H).biUnion fun S =>
      (nbr vbl (lvl S H)).powerset.image fun J => S ∪ J.image fun j => (j, H + 1)

theorem shapes_mono (i : ι) (H : ℕ) : shapes vbl i H ⊆ shapes vbl i (H + 1) := fun S hS => by
  rw [shapes, mem_biUnion]
  exact ⟨S, hS, mem_image.2 ⟨∅, empty_mem_powerset _, by simp⟩⟩

/-- The members of `shapes vbl i H` have depth at most `H`. -/
theorem le_of_mem_shapes {i : ι} : ∀ {H : ℕ} {S : Finset (ι × ℕ)}, S ∈ shapes vbl i H →
    ∀ p ∈ S, p.2 ≤ H
  | 0, S, hS, p, hp => by
    rw [shapes, mem_singleton] at hS
    subst hS
    rw [mem_singleton.1 hp]
  | H + 1, S, hS, p, hp => by
    rw [shapes, mem_biUnion] at hS
    obtain ⟨S₀, hS₀, hS⟩ := hS
    obtain ⟨J, -, rfl⟩ := mem_image.1 hS
    rcases mem_union.1 hp with hp | hp
    · exact (le_of_mem_shapes hS₀ p hp).trans (Nat.le_succ H)
    · obtain ⟨j, -, rfl⟩ := mem_image.1 hp
      exact le_rfl

omit [Fintype ι] in
/-- A structure rooted at `i` in which every vertex below the root has an adjacent parent one
level up. -/
private structure Rooted (i : ι) (S : Finset (ι × ℕ)) : Prop where
  root : (i, 0) ∈ S
  zero : ∀ p ∈ S, p.2 = 0 → p = (i, 0)
  parent : ∀ p ∈ S, p.2 ≠ 0 → ∃ q ∈ S, q.2 + 1 = p.2 ∧ Adj vbl q.1 p.1

omit [Fintype ι] in
private theorem exists_of_level_ne_zero {j : ι} {S : Finset (ι × ℕ)} (h : level vbl j S ≠ 0) :
    ∃ q ∈ S, q.2 + 1 = level vbl j S ∧ Adj vbl q.1 j := by
  have hne : (S.filter fun p => Adj vbl p.1 j).Nonempty := by
    by_contra hc
    rw [not_nonempty_iff_eq_empty] at hc
    exact h (by rw [level, hc, sup_empty]; rfl)
  obtain ⟨q, hq, he⟩ := exists_mem_eq_sup _ hne fun p : ι × ℕ => p.2 + 1
  rw [mem_filter] at hq
  exact ⟨q, hq.1, he.symm, hq.2⟩

omit [Fintype ι] in
private theorem rooted_witness (i : ι) (w : List ι) : Rooted vbl i (witness vbl i w) := by
  unfold witness
  induction w using List.reverseRecOn with
  | nil =>
    refine ⟨by simp, fun p hp _ => by simpa using hp, fun p hp hp0 => ?_⟩
    rw [List.foldl_nil, mem_singleton] at hp
    exact absurd (by rw [hp]) hp0
  | append_singleton w j ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    unfold push
    split_ifs with h0
    · exact ih
    refine ⟨mem_insert_of_mem ih.root, fun p hp hp0 => ?_, fun p hp hp0 => ?_⟩
    · rcases mem_insert.1 hp with rfl | hp
      · exact absurd hp0 h0
      · exact ih.zero p hp hp0
    · rcases mem_insert.1 hp with rfl | hp
      · obtain ⟨q, hq, he, ha⟩ := exists_of_level_ne_zero vbl h0
        exact ⟨q, mem_insert_of_mem hq, he, ha⟩
      · obtain ⟨q, hq, he, ha⟩ := ih.parent p hp hp0
        exact ⟨q, mem_insert_of_mem hq, he, ha⟩

omit [Fintype ι] in
private theorem witness_le (i : ι) (w : List ι) : ∀ p ∈ witness vbl i w, p.2 ≤ w.length := by
  unfold witness
  induction w using List.reverseRecOn with
  | nil =>
    intro p hp
    rw [List.foldl_nil, mem_singleton] at hp
    rw [hp, List.length_nil]
  | append_singleton w j ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
      List.length_singleton]
    intro p hp
    unfold push at hp
    split_ifs at hp
    · exact (ih p hp).trans (Nat.le_succ _)
    · rcases mem_insert.1 hp with rfl | hp
      · exact Finset.sup_le fun p hp => Nat.succ_le_succ (ih p (mem_filter.1 hp).1)
      · exact (ih p hp).trans (Nat.le_succ _)

private theorem mem_shapes {i : ι} : ∀ (H : ℕ) {S : Finset (ι × ℕ)}, Rooted vbl i S →
    (∀ p ∈ S, p.2 ≤ H) → S ∈ shapes vbl i H
  | 0, S, hS, hH => by
    rw [shapes, mem_singleton]
    refine eq_singleton_iff_unique_mem.2 ⟨hS.root, fun p hp => hS.zero p hp ?_⟩
    have := hH p hp
    omega
  | H + 1, S, hS, hH => by
    set S' := S.filter fun p => p.2 ≤ H with hS'
    have hR : Rooted vbl i S' := by
      refine ⟨mem_filter.2 ⟨hS.root, Nat.zero_le _⟩, fun p hp => hS.zero p (mem_filter.1 hp).1,
        fun p hp hp0 => ?_⟩
      obtain ⟨q, hq, he, ha⟩ := hS.parent p (mem_filter.1 hp).1 hp0
      exact ⟨q, mem_filter.2 ⟨hq, by have := (mem_filter.1 hp).2; omega⟩, he, ha⟩
    have hmem := mem_shapes H hR fun p hp => (mem_filter.1 hp).2
    rw [shapes, mem_biUnion]
    refine ⟨S', hmem, mem_image.2 ⟨lvl S (H + 1), mem_powerset.2 fun j hj => ?_, ?_⟩⟩
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hj
      rw [mem_filter] at hp
      obtain ⟨q, hq, he, ha⟩ := hS.parent p hp.1 (by omega)
      rw [nbr, mem_filter]
      refine ⟨mem_univ _, q.1, mem_image.2 ⟨q, mem_filter.2 ⟨mem_filter.2 ⟨hq, by omega⟩,
        by omega⟩, rfl⟩, ha⟩
    · ext p
      simp only [mem_union, mem_image, lvl, mem_filter, hS']
      constructor
      · rintro (h | ⟨j, ⟨q, ⟨hq, hq2⟩, rfl⟩, rfl⟩)
        · exact h.1
        · rw [← hq2]
          exact hq
      · intro hp
        by_cases h : p.2 ≤ H
        · exact Or.inl ⟨hp, h⟩
        · refine Or.inr ⟨p.1, ⟨p, ⟨hp, by have := hH p hp; omega⟩, rfl⟩, ?_⟩
          have := hH p hp
          exact Prod.ext rfl (show H + 1 = p.2 by omega)

/-- **Witness structures of a log.** If `w` is a valid log on `T` of length at most `H`, there
are `w.count i` distinct structures in `shapes vbl i H`, all proper and passing their checks on
`T`: the witness structures of the steps labelled `i` [MoserTardos2010, Section 2]. -/
theorem exists_witnesses (A : ι → Set (∀ v, α v))
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) (T : ∀ p : V × ℕ, α p.1) (i : ι) (H : ℕ)
    (w : List ι) (hw : IsLog vbl A T w) (hl : w.length ≤ H) :
    ∃ W : Finset (Finset (ι × ℕ)), #W = w.count i ∧
      ∀ S ∈ W, S ∈ shapes vbl i H ∧ Proper vbl S ∧ Check vbl A S T := by
  suffices h : ∀ w : List ι, IsLog vbl A T w → w.length ≤ H →
      ∃ W : Finset (Finset (ι × ℕ)), #W = w.count i ∧
        (∀ S ∈ W, labelCount i S ≤ w.count i) ∧
        ∀ S ∈ W, S ∈ shapes vbl i H ∧ Proper vbl S ∧ Check vbl A S T by
    obtain ⟨W, hcard, -, hW⟩ := h w hw hl
    exact ⟨W, hcard, hW⟩
  intro w
  induction w with
  | nil => exact fun _ _ => ⟨∅, by simp, by simp, by simp⟩
  | cons j w ih =>
    intro h hl
    have hl' : w.length ≤ H := by
      simp only [List.length_cons] at hl
      omega
    obtain ⟨W, hcard, hlab, hsub⟩ := ih ((isLog_cons vbl).1 h).2 hl'
    by_cases hj : j = i
    · subst hj
      have hnew : witness vbl j w ∉ W := fun hm => by
        have := hlab _ hm
        rw [labelCount_witness] at this
        omega
      refine ⟨insert (witness vbl j w) W, ?_, fun S hS => ?_, fun S hS => ?_⟩
      · rw [card_insert_of_notMem hnew, hcard, List.count_cons_self]
      · rw [List.count_cons_self]
        rcases mem_insert.1 hS with rfl | hS
        · rw [labelCount_witness]
        · exact (hlab S hS).trans (Nat.le_succ _)
      · rcases mem_insert.1 hS with rfl | hS
        · exact ⟨mem_shapes vbl H (rooted_witness vbl j w)
            fun p hp => (witness_le vbl j w p hp).trans hl', proper_witness vbl j w,
            check_witness vbl A hA j w T h⟩
        · exact hsub S hS
    · refine ⟨W, ?_, fun S hS => ?_, hsub⟩
      · rw [hcard, List.count_cons_of_ne hj]
      · rw [List.count_cons_of_ne hj]
        exact hlab S hS

end Shapes

section Counting

variable [DecidableEq V] [DecidableEq ι] [Fintype ι] (vbl : ι → Finset V)

private theorem mem_nbr_self (B : ι) : B ∈ nbr vbl {B} :=
  mem_filter.2 ⟨mem_univ _, B, mem_singleton_self B, Or.inl rfl⟩

private theorem nbr_insert (C : ι) (I : Finset ι) :
    nbr vbl (insert C I) = nbr vbl {C} ∪ nbr vbl I := by
  ext B
  simp [nbr]

omit [DecidableEq V] [Fintype ι] in
private theorem prod_union_le_mul {s t : Finset ι} {f : ι → ℝ} (hf : ∀ i, 1 ≤ f i) :
    ∏ i ∈ s ∪ t, f i ≤ (∏ i ∈ s, f i) * ∏ i ∈ t, f i := by
  rw [← prod_union_inter]
  exact le_mul_of_one_le_right (prod_nonneg fun i _ => zero_le_one.trans (hf i))
    (one_le_prod₀ fun i _ => hf i)

private theorem prod_nbr_le {f : ι → ℝ} (hf : ∀ i, 1 ≤ f i) (I : Finset ι) :
    ∏ B ∈ nbr vbl I, f B ≤ ∏ C ∈ I, ∏ B ∈ nbr vbl {C}, f B := by
  induction I using Finset.induction_on with
  | empty => simp [nbr]
  | insert C I hC ih =>
    rw [nbr_insert, prod_insert hC]
    exact (prod_union_le_mul hf).trans (mul_le_mul_of_nonneg_left ih
      (prod_nonneg fun i _ => zero_le_one.trans (hf i)))

private theorem sum_biUnion_le_of_nonneg {κ β : Type*} [DecidableEq β] (s : Finset κ)
    (t : κ → Finset β) {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have h := sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
    have h0 : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := sum_nonneg fun b _ => hf b
    linarith

omit [Fintype ι] in
private theorem lvl_union_image {S : Finset (ι × ℕ)} {H : ℕ} (hS : ∀ p ∈ S, p.2 ≤ H)
    (J : Finset ι) : lvl (S ∪ J.image fun j => (j, H + 1)) (H + 1) = J := by
  ext j
  simp only [lvl, mem_image, mem_filter, mem_union]
  constructor
  · rintro ⟨p, ⟨hp | ⟨j', hj', rfl⟩, hp2⟩, rfl⟩
    · have := hS p hp
      omega
    · exact hj'
  · intro hj
    exact ⟨(j, H + 1), ⟨Or.inr ⟨j, hj, rfl⟩, rfl⟩, rfl⟩

omit [DecidableEq V] [Fintype ι] in
private theorem disjoint_image_level {S : Finset (ι × ℕ)} {H : ℕ} (hS : ∀ p ∈ S, p.2 ≤ H)
    (J : Finset ι) : Disjoint S (J.image fun j => (j, H + 1)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  obtain ⟨j, -, rfl⟩ := mem_image.1 hq
  have := hS _ hp
  omega

/-- `∏ B ∈ Γ⁺ C, (1 - x B)⁻¹`, the weight charged to a label `C` on the deepest level. -/
private noncomputable def zf (x : ι → ℝ) (C : ι) : ℝ := ∏ B ∈ nbr vbl {C}, (1 - x B)⁻¹

omit [DecidableEq V] [DecidableEq ι] [Fintype ι] in
private theorem one_le_inv_one_sub {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) (B : ι) :
    1 ≤ (1 - x B)⁻¹ := by
  have h0 := (hx B).1
  have h1 := (hx B).2
  rw [one_le_inv₀ (by linarith)]
  linarith

private theorem one_le_zf {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) (C : ι) :
    1 ≤ zf vbl x C :=
  one_le_prod₀ fun B _ => one_le_inv_one_sub hx B

private theorem one_add_le_inv {x y : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hyz : ∀ B, y B * zf vbl x B ≤ x B / (1 - x B)) (B : ι) :
    1 + y B * zf vbl x B ≤ (1 - x B)⁻¹ := by
  have h1 := (hx B).2
  have : 1 + x B / (1 - x B) = (1 - x B)⁻¹ := by
    field_simp
    ring
  linarith [hyz B]

/-- The generating-function induction behind [MoserTardos2010, Section 3]: charging the deepest
level with the weights `zf`, the weighted sum over `shapes vbl i H` is at most
`x i / (1 - x i)`. -/
private theorem sum_shapes_le {x y : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) (hy : ∀ i, 0 ≤ y i)
    (hyz : ∀ B, y B * zf vbl x B ≤ x B / (1 - x B)) (i : ι) :
    ∀ H, ∑ S ∈ shapes vbl i H, (∏ p ∈ S, y p.1) * ∏ C ∈ lvl S H, zf vbl x C ≤
      x i / (1 - x i)
  | 0 => by
    have hl : lvl ({(i, 0)} : Finset (ι × ℕ)) 0 = {i} := by
      simp [lvl, filter_singleton]
    rw [shapes, sum_singleton, hl, prod_singleton, prod_singleton]
    exact hyz i
  | H + 1 => by
    have hnn : ∀ S : Finset (ι × ℕ), ∀ l, 0 ≤ (∏ p ∈ S, y p.1) * ∏ C ∈ lvl S l, zf vbl x C :=
      fun S l => mul_nonneg (prod_nonneg fun p _ => hy _)
        (prod_nonneg fun C _ => zero_le_one.trans (one_le_zf vbl hx C))
    refine (sum_biUnion_le_of_nonneg _ _ fun S => hnn S (H + 1)).trans ?_
    refine (sum_le_sum fun S _ => sum_image_le_of_nonneg fun S _ => hnn S (H + 1)).trans ?_
    refine le_trans (sum_le_sum fun S hS => ?_) (sum_shapes_le hx hy hyz i H)
    have hle := le_of_mem_shapes vbl hS
    calc ∑ J ∈ (nbr vbl (lvl S H)).powerset,
          (∏ p ∈ S ∪ J.image (fun j => (j, H + 1)), y p.1) *
            ∏ C ∈ lvl (S ∪ J.image fun j => (j, H + 1)) (H + 1), zf vbl x C
        = ∑ J ∈ (nbr vbl (lvl S H)).powerset,
            (∏ p ∈ S, y p.1) * ∏ j ∈ J, (y j * zf vbl x j) := by
          refine sum_congr rfl fun J _ => ?_
          rw [prod_union (disjoint_image_level hle J),
            prod_image fun a _ b _ h => congrArg Prod.fst h, lvl_union_image hle,
            prod_mul_distrib, mul_assoc]
      _ = (∏ p ∈ S, y p.1) * ∏ B ∈ nbr vbl (lvl S H), (1 + y B * zf vbl x B) := by
          rw [← mul_sum, prod_one_add]
      _ ≤ (∏ p ∈ S, y p.1) * ∏ B ∈ nbr vbl (lvl S H), (1 - x B)⁻¹ := by
          refine mul_le_mul_of_nonneg_left (prod_le_prod₀ (fun B _ => ?_)
            fun B _ => one_add_le_inv vbl hx hyz B) (prod_nonneg fun p _ => hy _)
          exact add_nonneg zero_le_one (mul_nonneg (hy B) (zero_le_one.trans (one_le_zf vbl hx B)))
      _ ≤ (∏ p ∈ S, y p.1) * ∏ C ∈ lvl S H, zf vbl x C :=
          mul_le_mul_of_nonneg_left (prod_nbr_le vbl (one_le_inv_one_sub hx) _)
            (prod_nonneg fun p _ => hy _)

/-- The events other than `B` sharing a variable with `B`. -/
private def nbhd (B : ι) : Finset ι := univ.filter fun C => C ≠ B ∧ ¬Disjoint (vbl B) (vbl C)

private theorem nbr_singleton (B : ι) : nbr vbl {B} = insert B (nbhd vbl B) := by
  ext C
  by_cases h : C = B
  · subst h
    simp [nbr, nbhd, Adj]
  · simp [nbr, nbhd, Adj, h, Ne.symm h]

/-- The local-lemma hypothesis, for any `Γ` containing the variable-sharing neighbours, gives the
bound on the weighted roots used by `sum_shapes_le`. -/
private theorem mul_zf_le {x y : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1) (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    (hy : ∀ B, y B ≤ x B * ∏ C ∈ Γ B, (1 - x C)) (B : ι) :
    y B * zf vbl x B ≤ x B / (1 - x B) := by
  have hpos : ∀ C, 0 < 1 - x C := fun C => by linarith [(hx C).2]
  have hsub : nbhd vbl B ⊆ Γ B := fun C hC => by
    simp only [nbhd, mem_filter, mem_univ, true_and] at hC
    exact hΓ B C hC.1 hC.2
  have hΓle : ∏ C ∈ Γ B, (1 - x C) ≤ ∏ C ∈ nbhd vbl B, (1 - x C) :=
    prod_le_prod_of_subset_of_le_one₀ hsub (fun C _ => (hpos C).le)
      fun C _ _ => by linarith [(hx C).1]
  have hnot : B ∉ nbhd vbl B := by simp [nbhd]
  have hz : zf vbl x B = (1 - x B)⁻¹ * (∏ C ∈ nbhd vbl B, (1 - x C))⁻¹ := by
    rw [zf, nbr_singleton, prod_insert hnot, prod_inv_distrib]
  have hP : 0 < ∏ C ∈ nbhd vbl B, (1 - x C) := prod_pos fun C _ => hpos C
  have hz0 : 0 ≤ zf vbl x B := zero_le_one.trans (one_le_zf vbl hx B)
  calc y B * zf vbl x B
      ≤ (x B * ∏ C ∈ nbhd vbl B, (1 - x C)) * zf vbl x B :=
        mul_le_mul_of_nonneg_right ((hy B).trans
          (mul_le_mul_of_nonneg_left hΓle (hx B).1)) hz0
    _ = x B / (1 - x B) := by
        rw [hz]
        field_simp

/-- **The counting bound** [MoserTardos2010, Section 3]. Under the local-lemma hypothesis
`y i ≤ x i ∏ j ∈ Γ i, (1 - x j)`, where `Γ i` contains every other event sharing a variable with
`A i`, the products `∏ p ∈ S, y p.1` over the structures `S ∈ shapes vbl i H` sum to at most
`x i / (1 - x i)`, for every depth `H`. -/
theorem sum_prod_shapes_le (Γ : ι → Finset ι)
    (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i) {x y : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) (hy0 : ∀ i, 0 ≤ y i)
    (hy : ∀ i, y i ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (i : ι) (H : ℕ) :
    ∑ S ∈ shapes vbl i H, ∏ p ∈ S, y p.1 ≤ x i / (1 - x i) := by
  refine le_trans (sum_le_sum fun S _ => ?_)
    (sum_shapes_le vbl hx hy0 (mul_zf_le vbl hx Γ hΓ hy) i H)
  exact le_mul_of_one_le_right (prod_nonneg fun p _ => hy0 _)
    (one_le_prod₀ fun C _ => one_le_zf vbl hx C)

end Counting

end Cslib.Probability.MoserTardos
