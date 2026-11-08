/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.TSP.Walk
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Sublists
public import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.Permutation
import Mathlib.Data.Nat.Choose.Sum

/-!
# The Bellman–Held–Karp algorithm for the traveling salesman problem

The Bellman–Held–Karp dynamic program [Bellman1962] [HeldKarp1962]
([FominKratsch2010], Section 1.2) computes an optimal traveling salesman tour on `n + 1` cities
in `O(n² · 2ⁿ)` operations, instead of examining the `n!` tours one by one.

## Model

The cities are `Fin (n + 1)`, and `d : Fin (n + 1) → Fin (n + 1) → W` is an arbitrary cost
function with values in a linearly ordered additive commutative monoid `W`: costs need not be
symmetric, nonnegative or metric, and `W` may be `ℕ`, `ℤ`, or `WithTop ℕ` for missing edges.
Every tour starts and ends at city `0`, which loses nothing since a closed tour can be rotated.
A tour is an ordering `L` of the other cities `1, …, n`, given as a list of `Fin n` (city
`i.succ` for `i : Fin n`) that is a permutation of `List.finRange n`, and its cost is
`walkCost d 0 (L.map Fin.succ) 0`, the sum of `d` along `0, L, 0`. For `n = 0` the only tour
is `[]`, of cost `d 0 0`.

## Algorithm

For a set `S` of cities among `1, …, n` and a city `t`, the table holds the least cost of a walk
that leaves `0`, visits the cities of `S` exactly once in some order, and then moves to `t`.
Bellman's principle (`isLeast_walkCosts_of_forall`) computes this entry from the entries for the
sets `S.erase i`: the walk visits some `i ∈ S` last. `heldKarp` fills the table by increasing
`|S|` (`HeldKarp.tableM`) and returns the entry for all cities and `t = 0`.

The entries are indexed by the set `S` of cities visited *before* the target. For a target
`t = i.succ` with `i ∉ S` this is [HeldKarp1962]'s `C(S ∪ {t}, t)`. The table also fills the
entries `(S, 0)` for every `S` (`HeldKarp.targets` always contains city `0`): such an entry is the
least cost of a walk from `0` through `S` back to `0`, which is not a Held–Karp value unless `S` is
every city. Only the final entry `(univ, 0)` is read, and it is the optimal tour; Held and Karp
compute it by a separate closing minimization. The other `(S, 0)` entries cost at most
`n · 2ⁿ⁻¹` extra ticks, within the bound below.

## Cost model

`heldKarp` runs in `TimeM ℕ`. Each candidate `T (S.erase i, i.succ) + d i.succ t` examined for a
table entry costs one tick (one addition and one comparison). Reading and writing table entries
is free, as for an array indexed by the bitmask of `S`; enumerating the subsets is free.
`time_heldKarp_le` bounds the ticks by `n² · 2ⁿ`; on three cities (`n = 2`) the algorithm
takes `6` ticks and on four cities `24`, against `n!` tours of `n + 1` additions each for brute
force. `TimeM` does not measure space: the table has an entry for each of the `2ⁿ` subsets and
`n + 1` targets.

## Main definitions

* `Cslib.Algorithms.Lean.TSP.walkCosts`: the costs of the walks from `0` through `S` to `t`.
* `Cslib.Algorithms.Lean.TSP.heldKarp`: the Bellman–Held–Karp algorithm.
* `Cslib.Algorithms.Lean.TSP.HeldKarp.entryM`, `HeldKarp.fillM`, `HeldKarp.layerM`,
  `HeldKarp.tableM`: a table entry, the entries for one set, one layer, and the table.

## Main results

* `isLeast_walkCosts_of_forall`: Bellman's principle for walks through subsets.
* `isLeast_heldKarp`: `heldKarp d` is the least cost of a tour.
* `isLeast_heldKarp_permutations`: the same against brute force, over all permutations of the
  cities `1, …, n`.
* `time_heldKarp_le`: at most `n² · 2ⁿ` ticks.

## References

* [R. Bellman, *Dynamic programming treatment of the travelling salesman problem*][Bellman1962]
* [M. Held and R. M. Karp, *A dynamic programming approach to sequencing
  problems*][HeldKarp1962]
* [F. V. Fomin and D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010], Section 1.2
-/

public section

namespace Cslib.Algorithms.Lean.TSP

open Cslib.Algorithms.Lean.TimeM

variable {α W : Type*}

namespace HeldKarp

/-! ### Minimum folds -/

section MinFold

variable [LinearOrder W]

/-- Fold `min` over the values of `g` on `l`, starting from `acc`, at one tick per entry. -/
@[expose] def minFoldM (g : α → W) : W → List α → TimeM ℕ W
  | acc, [] => pure acc
  | acc, i :: l => do ✓ minFoldM g (min acc (g i)) l

@[simp] theorem time_minFoldM (g : α → W) (acc : W) (l : List α) :
    (minFoldM g acc l).time = l.length := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
    simp only [minFoldM, time_bind, time_tick, ih, List.length_cons]
    omega

theorem ret_minFoldM_le_acc (g : α → W) (acc : W) (l : List α) :
    (minFoldM g acc l).ret ≤ acc := by
  induction l generalizing acc with
  | nil => exact le_rfl
  | cons i l ih => exact (ih _).trans (min_le_left _ _)

theorem ret_minFoldM_le (g : α → W) (acc : W) {l : List α} {i : α} (hi : i ∈ l) :
    (minFoldM g acc l).ret ≤ g i := by
  induction l generalizing acc with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.1 hi with rfl | hi
    · exact (ret_minFoldM_le_acc g _ l).trans (min_le_right _ _)
    · exact ih _ hi

theorem ret_minFoldM_eq (g : α → W) (acc : W) (l : List α) :
    (minFoldM g acc l).ret = acc ∨ ∃ i ∈ l, (minFoldM g acc l).ret = g i := by
  induction l generalizing acc with
  | nil => exact Or.inl rfl
  | cons j l ih =>
    rcases ih (min acc (g j)) with h | ⟨i, hi, h⟩
    · change (minFoldM g (min acc (g j)) l).ret = acc ∨ _
      rcases min_choice acc (g j) with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr ⟨j, List.mem_cons_self .., h.trans h'⟩
    · exact Or.inr ⟨i, List.mem_cons_of_mem _ hi, h⟩

end MinFold

end HeldKarp

/-! ### Walks through subsets -/

section Walks

variable {n : ℕ}

/-- The costs of the walks that start at city `0`, visit each city of `S` exactly once, in some
order, and then move to `t`. The cities `1, …, n` are the successors `i.succ` of `i : Fin n`. -/
@[expose] def walkCosts [Add W] (d : Fin (n + 1) → Fin (n + 1) → W) (S : Finset (Fin n))
    (t : Fin (n + 1)) : Set W :=
  {c | ∃ L : List (Fin n), L.Nodup ∧ L.toFinset = S ∧ walkCost d 0 (L.map Fin.succ) t = c}

/-- The only walk through no cities is the direct step. -/
theorem isLeast_walkCosts_empty [Add W] [Preorder W] (d : Fin (n + 1) → Fin (n + 1) → W)
    (t : Fin (n + 1)) : IsLeast (walkCosts d ∅ t) (d 0 t) := by
  refine ⟨⟨[], List.nodup_nil, rfl, rfl⟩, ?_⟩
  rintro c ⟨L, -, hL, rfl⟩
  obtain rfl : L = [] := (List.toFinset_eq_empty_iff L).1 hL
  exact le_rfl

variable [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- **Bellman's principle for walks through subsets** [Bellman1962] [HeldKarp1962]. If `f i` is
the least cost of a walk from `0` through `S.erase i` to `i.succ`, for every `i ∈ S`, and `v` is
the least value of `f i + d i.succ t` over `i ∈ S`, then `v` is the least cost of a walk from
`0` through `S` to `t`. -/
theorem isLeast_walkCosts_of_forall {d : Fin (n + 1) → Fin (n + 1) → W} {S : Finset (Fin n)}
    {t : Fin (n + 1)} {f : Fin n → W} {v : W}
    (hf : ∀ i ∈ S, IsLeast (walkCosts d (S.erase i) i.succ) (f i))
    (hle : ∀ i ∈ S, v ≤ f i + d i.succ t) (hmem : ∃ i ∈ S, v = f i + d i.succ t) :
    IsLeast (walkCosts d S t) v := by
  constructor
  · obtain ⟨i, hi, rfl⟩ := hmem
    obtain ⟨⟨L, hnd, hL, hc⟩, -⟩ := hf i hi
    have hiL : i ∉ L := fun h => by simpa [hL] using List.mem_toFinset.2 h
    refine ⟨L ++ [i], ?_, ?_, ?_⟩
    · exact hnd.append (List.nodup_singleton i) (List.disjoint_singleton.2 hiL)
    · ext y
      simp only [List.toFinset_append, hL, Finset.mem_union, Finset.mem_erase, List.mem_toFinset,
        List.mem_singleton]
      constructor
      · rintro (⟨-, hy⟩ | rfl)
        · exact hy
        · exact hi
      · intro hy
        by_cases hyi : y = i
        · exact Or.inr hyi
        · exact Or.inl ⟨hyi, hy⟩
    · rw [List.map_append, List.map_singleton, walkCost_append_singleton, hc]
  · rintro c ⟨L, hnd, hL, rfl⟩
    obtain ⟨i, hi, -⟩ := hmem
    rcases List.eq_nil_or_concat L with rfl | ⟨L', x, rfl⟩
    · simp [← hL] at hi
    rw [List.concat_eq_append] at hnd hL ⊢
    have hx : x ∈ S := hL ▸ List.mem_toFinset.2 (by simp)
    have hxL' : x ∉ L' := fun h => by
      simpa using (List.nodup_append.1 hnd).2.2 x h x (List.mem_singleton_self x)
    have hL' : L'.toFinset = S.erase x := by
      ext y
      simp only [← hL, List.mem_toFinset, Finset.mem_erase, List.mem_append, List.mem_singleton]
      constructor
      · intro hy
        exact ⟨fun h => hxL' (h ▸ hy), Or.inl hy⟩
      · rintro ⟨hy, hy' | rfl⟩
        · exact hy'
        · exact absurd rfl hy
    calc v ≤ f x + d x.succ t := hle x hx
      _ ≤ walkCost d 0 (L'.map Fin.succ) x.succ + d x.succ t :=
          add_le_add ((hf x hx).2 ⟨L', hnd.sublist (List.sublist_append_left _ _), hL', rfl⟩)
            le_rfl
      _ = walkCost d 0 ((L' ++ [x]).map Fin.succ) t := by
          rw [List.map_append, List.map_singleton, walkCost_append_singleton]

end Walks

/-! ### The dynamic program -/

namespace HeldKarp

variable {n : ℕ}

/-- A Held–Karp table: an entry for each set `S` of the cities `1, …, n` and target `t`. -/
abbrev Table (n : ℕ) (W : Type*) := Finset (Fin n) × Fin (n + 1) → W

section Program

variable [Add W] [LinearOrder W]

/-- The table entry for `(S, t)`, where `l` lists the cities of `S`: `d 0 t` when `S` is empty,
and otherwise the least of `T (S.erase i, i.succ) + d i.succ t` over `i ∈ l`, at one tick per
candidate. -/
@[expose] def entryM (d : Fin (n + 1) → Fin (n + 1) → W) (T : Table n W) (S : Finset (Fin n))
    (t : Fin (n + 1)) : List (Fin n) → TimeM ℕ W
  | [] => pure (d 0 t)
  | i :: l => do
      ✓ minFoldM (fun j => T (S.erase j, j.succ) + d j.succ t)
        (T (S.erase i, i.succ) + d i.succ t) l

/-- The targets of the entries for `S`: city `0` and the cities `1, …, n` outside `S`. Only the
entry `(univ, 0)` among those for city `0` is read by `heldKarp`. -/
@[expose] def targets (S : Finset (Fin n)) : List (Fin (n + 1)) :=
  0 :: ((List.finRange n).filter (· ∉ S)).map Fin.succ

/-- Fill the entries `(S, t)` for the targets `t ∈ ts`, where `l` lists the cities of `S`. -/
@[expose] def fillM (d : Fin (n + 1) → Fin (n + 1) → W) (S : Finset (Fin n)) (l : List (Fin n)) :
    Table n W → List (Fin (n + 1)) → TimeM ℕ (Table n W)
  | T, [] => pure T
  | T, t :: ts => do
      let v ← entryM d T S t l
      fillM d S l (Function.update T (S, t) v) ts

/-- Fill the entries of every set listed in `ls`, for all their targets. -/
@[expose] def layerM (d : Fin (n + 1) → Fin (n + 1) → W) :
    Table n W → List (List (Fin n)) → TimeM ℕ (Table n W)
  | T, [] => pure T
  | T, l :: ls => do
      let T' ← fillM d l.toFinset l T (targets l.toFinset)
      layerM d T' ls

/-- The table after the layers of the sets of sizes `1, …, k`, each enumerated by
`List.sublistsLen`. The initial table holds `d 0 t`, the entries for the empty set. -/
@[expose] def tableM (d : Fin (n + 1) → Fin (n + 1) → W) : ℕ → TimeM ℕ (Table n W)
  | 0 => pure fun p => d 0 p.2
  | k + 1 => do
      let T ← tableM d k
      layerM d T ((List.finRange n).sublistsLen (k + 1))

end Program

end HeldKarp

open HeldKarp in
/-- **The Bellman–Held–Karp algorithm** [Bellman1962] [HeldKarp1962] for the traveling salesman
problem on the cities `0, 1, …, n` with costs `d`: fill the table of least walk costs through
each set of the cities `1, …, n`, by increasing size, and read off the entry for all of them
followed by the return to `0`. -/
@[expose] def heldKarp [Add W] [LinearOrder W] {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → W) :
    TimeM ℕ W := do
  let T ← tableM d n
  pure (T (Finset.univ, 0))

/-! ### Correctness -/

namespace HeldKarp

variable {n : ℕ} [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- The table entry `T (S, t)` is the least cost of a walk from `0` through `S` to `t`. -/
private def Correct (d : Fin (n + 1) → Fin (n + 1) → W) (T : Table n W)
    (p : Finset (Fin n) × Fin (n + 1)) : Prop :=
  IsLeast (walkCosts d p.1 p.2) (T p)

private theorem correct_entryM {d : Fin (n + 1) → Fin (n + 1) → W} {T : Table n W}
    {l : List (Fin n)} (t : Fin (n + 1))
    (hT : ∀ i ∈ l, Correct d T (l.toFinset.erase i, i.succ)) :
    IsLeast (walkCosts d l.toFinset t) (entryM d T l.toFinset t l).ret := by
  cases l with
  | nil => exact isLeast_walkCosts_empty d t
  | cons i l =>
    set g : Fin n → W := fun j => T ((i :: l).toFinset.erase j, j.succ) + d j.succ t
    have hret : (entryM d T (i :: l).toFinset t (i :: l)).ret = (minFoldM g (g i) l).ret := rfl
    rw [hret]
    refine isLeast_walkCosts_of_forall (f := fun j => T ((i :: l).toFinset.erase j, j.succ))
      (fun j hj => hT j (List.mem_toFinset.1 hj)) (fun j hj => ?_) ?_
    · rcases List.mem_cons.1 (List.mem_toFinset.1 hj) with rfl | hj
      · exact ret_minFoldM_le_acc g _ l
      · exact ret_minFoldM_le g _ hj
    · rcases ret_minFoldM_eq g (g i) l with h | ⟨j, hj, h⟩
      · exact ⟨i, by simp, h⟩
      · exact ⟨j, by simp [hj], h⟩

omit [IsOrderedAddMonoid W] in
private theorem correct_update {d : Fin (n + 1) → Fin (n + 1) → W} {T : Table n W}
    {p q : Finset (Fin n) × Fin (n + 1)} {v : W} (hp : Correct d T p)
    (hv : IsLeast (walkCosts d q.1 q.2) v) : Correct d (Function.update T q v) p := by
  by_cases h : p = q
  · subst h
    simpa [Correct] using hv
  · simpa [Correct, Function.update_of_ne h] using hp

private theorem correct_fillM {d : Fin (n + 1) → Fin (n + 1) → W} {l : List (Fin n)}
    (ts : List (Fin (n + 1))) (T : Table n W)
    (hT : ∀ i ∈ l, Correct d T (l.toFinset.erase i, i.succ)) :
    (∀ p, Correct d T p → Correct d (fillM d l.toFinset l T ts).ret p) ∧
      ∀ t ∈ ts, Correct d (fillM d l.toFinset l T ts).ret (l.toFinset, t) := by
  induction ts generalizing T with
  | nil => exact ⟨fun _ h => h, by simp⟩
  | cons t ts ih =>
    have hv := correct_entryM t hT
    obtain ⟨h1, h2⟩ := ih (Function.update T (l.toFinset, t) (entryM d T l.toFinset t l).ret)
      fun i hi => correct_update (hT i hi) hv
    refine ⟨fun p hp => h1 p (correct_update hp hv), fun t' ht' => ?_⟩
    rcases List.mem_cons.1 ht' with rfl | ht'
    · exact h1 _ (by simpa [Correct] using hv)
    · exact h2 t' ht'

private theorem correct_layerM {d : Fin (n + 1) → Fin (n + 1) → W} (ls : List (List (Fin n)))
    (T : Table n W) (hT : ∀ l ∈ ls, ∀ i ∈ l, Correct d T (l.toFinset.erase i, i.succ)) :
    (∀ p, Correct d T p → Correct d (layerM d T ls).ret p) ∧
      ∀ l ∈ ls, ∀ t ∈ targets l.toFinset, Correct d (layerM d T ls).ret (l.toFinset, t) := by
  induction ls generalizing T with
  | nil => exact ⟨fun _ h => h, by simp⟩
  | cons l ls ih =>
    obtain ⟨h1, h2⟩ := correct_fillM (targets l.toFinset) T (hT l (List.mem_cons_self ..))
    obtain ⟨g1, g2⟩ := ih (fillM d l.toFinset l T (targets l.toFinset)).ret
      fun l' hl' i hi => h1 _ (hT l' (List.mem_cons_of_mem _ hl') i hi)
    refine ⟨fun p hp => g1 p (h1 p hp), fun l' hl' t ht => ?_⟩
    rcases List.mem_cons.1 hl' with rfl | hl'
    · exact g1 _ (h2 t ht)
    · exact g2 l' hl' t ht

omit [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W] in
private theorem mem_targets_succ {S : Finset (Fin n)} {i : Fin n} (hi : i ∉ S) :
    i.succ ∈ targets S :=
  List.mem_cons_of_mem _
    (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_finRange i, by simpa⟩, rfl⟩)

/-- **The table invariant.** After the layers `1, …, k`, the entry `(S, t)` is the least cost of a
walk from `0` through `S` to `t`, for every set `S` of at most `k` cities and target `t` among
`0` and the cities outside `S`. -/
theorem isLeast_tableM (d : Fin (n + 1) → Fin (n + 1) → W) (k : ℕ) (S : Finset (Fin n))
    (hS : S.card ≤ k) {t : Fin (n + 1)} (ht : t ∈ targets S) :
    IsLeast (walkCosts d S t) ((tableM d k).ret (S, t)) := by
  induction k generalizing S t with
  | zero =>
    obtain rfl : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hS)
    exact isLeast_walkCosts_empty d t
  | succ k ih =>
    have hcard : ∀ l ∈ (List.finRange n).sublistsLen (k + 1), l.toFinset.card = k + 1 :=
      fun l hl => by
        obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.1 hl
        rw [List.toFinset_card_of_nodup ((List.nodup_finRange n).sublist hsub), hlen]
    obtain ⟨h1, h2⟩ := correct_layerM (d := d) ((List.finRange n).sublistsLen (k + 1))
      (tableM d k).ret fun l hl i hi => by
        refine ih _ ?_ (mem_targets_succ (Finset.notMem_erase i _))
        rw [Finset.card_erase_of_mem (List.mem_toFinset.2 hi), hcard l hl]
        omega
    rcases Nat.lt_or_ge S.card (k + 1) with hlt | hge
    · exact h1 (S, t) (ih S (by omega) ht)
    · set l := (List.finRange n).filter (· ∈ S)
      have hlS : l.toFinset = S := by
        ext i
        simp [l]
      have hl : l ∈ (List.finRange n).sublistsLen (k + 1) := by
        refine List.mem_sublistsLen.2 ⟨List.filter_sublist, ?_⟩
        rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), hlS]
        omega
      have := h2 l hl t (hlS ▸ ht)
      rwa [hlS] at this

end HeldKarp

section Correctness

open HeldKarp

variable {n : ℕ} [AddCommMonoid W] [LinearOrder W] [IsOrderedAddMonoid W]

/-- **Correctness of the Bellman–Held–Karp algorithm** [HeldKarp1962]. `heldKarp d` is the least
cost of a closed tour that starts at city `0`, visits each of the cities `1, …, n` exactly once
and returns to `0`. -/
theorem isLeast_heldKarp (d : Fin (n + 1) → Fin (n + 1) → W) :
    IsLeast (walkCosts d Finset.univ 0) (heldKarp d).ret :=
  isLeast_tableM d n Finset.univ (by simp) (List.mem_cons_self ..)

/-- **The Bellman–Held–Karp algorithm agrees with brute force.** `heldKarp d` is the least cost
of the `n!` tours `0, L, 0`, over all permutations `L` of the cities `1, …, n`. -/
theorem isLeast_heldKarp_permutations (d : Fin (n + 1) → Fin (n + 1) → W) :
    IsLeast {c | ∃ L ∈ (List.finRange n).permutations, walkCost d 0 (L.map Fin.succ) 0 = c}
      (heldKarp d).ret := by
  have hiff : ∀ L : List (Fin n), L ∈ (List.finRange n).permutations ↔
      L.Nodup ∧ L.toFinset = Finset.univ := fun L => by
    rw [List.mem_permutations]
    constructor
    · intro h
      exact ⟨h.nodup_iff.2 (List.nodup_finRange n), by ext; simp [h.mem_iff]⟩
    · rintro ⟨hnd, hL⟩
      refine (List.perm_ext_iff_of_nodup hnd (List.nodup_finRange n)).2 fun i => ?_
      exact ⟨fun _ => List.mem_finRange i, fun _ => List.mem_toFinset.1 (hL ▸ Finset.mem_univ i)⟩
  obtain ⟨⟨L, hnd, hL, hc⟩, hle⟩ := isLeast_heldKarp d
  refine ⟨⟨L, (hiff L).2 ⟨hnd, hL⟩, hc⟩, ?_⟩
  rintro c ⟨L', hL', rfl⟩
  obtain ⟨hnd', hL''⟩ := (hiff L').1 hL'
  exact hle ⟨L', hnd', hL'', rfl⟩

end Correctness

/-! ### Running time -/

namespace HeldKarp

variable {n : ℕ} [Add W] [LinearOrder W]

@[simp] theorem time_entryM (d : Fin (n + 1) → Fin (n + 1) → W) (T : Table n W)
    (S : Finset (Fin n)) (t : Fin (n + 1)) (l : List (Fin n)) :
    (entryM d T S t l).time = l.length := by
  cases l with
  | nil => rfl
  | cons i l =>
    simp only [entryM, time_bind, time_tick, time_minFoldM, List.length_cons]
    omega

omit [Add W] [LinearOrder W] in
theorem length_targets (S : Finset (Fin n)) : (targets S).length = 1 + (n - S.card) := by
  have h := List.length_eq_length_filter_add (l := List.finRange n) (fun i => decide (i ∈ S))
  have hS : ((List.finRange n).filter fun i => decide (i ∈ S)).length = S.card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)]
    congr 1
    ext i
    simp
  simp only [List.length_finRange, hS] at h
  have hc : ((List.finRange n).filter fun i => decide (i ∉ S)).length =
      ((List.finRange n).filter fun i => !decide (i ∈ S)).length := by
    simp only [decide_not]
  simp only [targets, List.length_cons, List.length_map, hc]
  omega

@[simp] theorem time_fillM (d : Fin (n + 1) → Fin (n + 1) → W) (S : Finset (Fin n))
    (l : List (Fin n)) (T : Table n W) (ts : List (Fin (n + 1))) :
    (fillM d S l T ts).time = ts.length * l.length := by
  induction ts generalizing T with
  | nil => simp [fillM]
  | cons t ts ih =>
    simp only [fillM, time_bind, time_entryM, ih, List.length_cons]
    ring

theorem time_layerM (d : Fin (n + 1) → Fin (n + 1) → W) (T : Table n W)
    (ls : List (List (Fin n))) :
    (layerM d T ls).time = (ls.map fun l => (1 + (n - l.toFinset.card)) * l.length).sum := by
  induction ls generalizing T with
  | nil => rfl
  | cons l ls ih =>
    simp only [layerM, time_bind, time_fillM, length_targets, ih, List.map_cons, List.sum_cons]

/-- The layers `1, …, k` take at most `n²` ticks for each set of at most `k` cities. -/
theorem time_tableM_le (d : Fin (n + 1) → Fin (n + 1) → W) (k : ℕ) :
    (tableM d k).time ≤ n ^ 2 * ∑ j ∈ Finset.range (k + 1), n.choose j := by
  induction k with
  | zero => simp [tableM]
  | succ k ih =>
    rw [Finset.sum_range_succ _ (k + 1), mul_add]
    simp only [tableM, time_bind, time_layerM]
    refine add_le_add ih ((List.sum_le_length_nsmul _ (n ^ 2) ?_).trans ?_)
    · simp only [List.mem_map]
      rintro _ ⟨l, hl, rfl⟩
      obtain ⟨hsub, hlen⟩ := List.mem_sublistsLen.1 hl
      have hcard : l.toFinset.card = k + 1 := by
        rw [List.toFinset_card_of_nodup ((List.nodup_finRange n).sublist hsub), hlen]
      have hkn : k + 1 ≤ n := by
        have := hsub.length_le
        rwa [hlen, List.length_finRange] at this
      rw [hcard, hlen, sq]
      exact Nat.mul_le_mul (by omega) hkn
    · rw [List.length_map, List.length_sublistsLen, List.length_finRange, nsmul_eq_mul,
        Nat.cast_id, mul_comm]

end HeldKarp

open HeldKarp in
/-- **Running time of the Bellman–Held–Karp algorithm** [HeldKarp1962]. At most `n² · 2ⁿ`
candidate relaxations on `n + 1` cities, against the `n!` tours of brute-force search. -/
theorem time_heldKarp_le [Add W] [LinearOrder W] {n : ℕ} (d : Fin (n + 1) → Fin (n + 1) → W) :
    (heldKarp d).time ≤ n ^ 2 * 2 ^ n := by
  have h := time_tableM_le d n
  rw [Nat.sum_range_choose] at h
  simpa [heldKarp] using h

end Cslib.Algorithms.Lean.TSP
