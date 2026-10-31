/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Paging.Basic
public import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.TakeDrop

/-!
# Least-recently-used (LRU) paging and `k`-competitiveness

This file implements the least-recently-used (LRU) online paging rule and proves its
`k`-competitiveness via a `Cslib.Stateful.Amortized` potential certificate, formalizing Theorem 6
of [Sleator and Tarjan, *Amortized Efficiency of List Update and Paging Rules*, Section 4
("Paging"), p. 207 (proof pp. 207–208)][SleatorTarjan1985] in the equal-capacity
(`n_LRU = n_MIN = k`) demand-paging model of `Complexity.Algorithms.Lean.Paging.Basic`.

## Source statement and mapping

In [SleatorTarjan1985], Section 4 ("Paging"), pp. 207–208, Theorem 6 (p. 207) bounds the page
faults of LRU with fast-memory capacity `n_LRU` against any offline paging algorithm with
fast-memory capacity `n_MIN ≤ n_LRU` by `(n_LRU / (n_LRU - n_MIN + 1)) · F_MIN + n_MIN`.
Specializing to equal online and offline fast-memory capacity (`n_LRU = n_MIN = k`, `0 < k`):

* Concrete LRU memory is a duplicate-free list `q : List α` (`q.Nodup ∧ q.length ≤ k`) ordered from
  most recently used (`head`) to least recently used (`last`).
* `lruNext k q p` moves `p` to the front on a cache hit (`p ∈ q`) and prepends `p` while truncating
  to length `k` on a cache miss (`p ∉ q`), evicting the least recently used page when
  `q.length = k`.
* `lruPotential k s q` is the maximum of:
  1. `maxWeightFrom k s q`: the recency weight `k - i` of the most recent page in `q` absent from
     the offline cache `s` (`0` if `q ⊆ s`), and
  2. `(s \ q.toFinset).card`: the number of offline-cached pages absent from `q` (handling partially
     filled caches `q.length < k`).
* `lruAmortized` packages the single-step inequality
  `stepCost + lruPotential k s' q' ≤ k * stepCost_off + lruPotential k s q`
  as a `Cslib.Stateful.Amortized` certificate over `(problem α k).offlineSpec`.
* Telescoping via `DetStrategy.competitive_of_amortized` and
  `DetStrategy.competitiveAnyInit_of_amortized` yields:
  * `lruStrategy_isCompetitive`: `(lruStrategy k hk).IsCompetitive k 0` when online and offline
    caches start from the same valid initial cache `s₀` (since `lruPotential k s₀ (init s₀) = 0`),
    and
  * `lruStrategy_isCompetitiveAnyInit`: `(lruStrategy k hk).IsCompetitiveAnyInit k k` when online
    and offline caches start from arbitrary valid initial caches of size at most `k` (since
    `lruPotential k s_off q ≤ k`).

Resource augmentation with unequal fast-memory capacities (`n_MIN < n_LRU`) is left as a separate
extension.

## Main definitions

* `Cslib.Algorithms.Lean.Paging.lruNext`, `lruStep`, `lruRun`, `lruFaults`: computable recency-list
  LRU transitions and fault counter.
* `Cslib.Algorithms.Lean.Paging.maxWeightFrom`, `lruPotential`: potential function between an
  offline cache `s : Finset α` and an LRU recency list `q : List α`.
* `Cslib.Algorithms.Lean.Paging.lruStrategy`: `Online.DetStrategy (problem α k)` realization of LRU.

## Main results

* `lruAmortized`: `Cslib.Stateful.Amortized` certificate for LRU against `k` times offline step
  cost.
* `lruFaults_amortized_bound`: computable-list telescoping bound for any valid initial recency list
  and any valid offline schedule.
* `lruStrategy_isCompetitive`: `(lruStrategy k hk).IsCompetitive k 0` from any common initial cache.
* `lruStrategy_isCompetitiveAnyInit`: `(lruStrategy k hk).IsCompetitiveAnyInit k k` across arbitrary
  initial caches.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Paging

open Cslib.Stateful Cslib.Algorithms.Lean.Online

variable {α : Type} [DecidableEq α]

/-! ### Computable recency-list LRU operations -/

/-- Advance the recency-ordered LRU list (most recently used first) of capacity `k` on page `p`. -/
@[expose]
def lruNext (k : Nat) (q : List α) (p : α) : List α :=
  if p ∈ q then p :: q.erase p
  else (p :: q).take k

/-- Single-step LRU update returning the new recency list and whether a page fault occurred. -/
@[expose]
def lruStep (k : Nat) (q : List α) (p : α) : List α × Bool :=
  (lruNext k q p, decide (p ∉ q))

/-- Run `lruNext k` across a request list from initial recency list `q`. -/
@[expose]
def lruRun (k : Nat) (q : List α) : List α → List α
  | [] => q
  | p :: ps => lruRun k (lruNext k q p) ps

/-- Count total page faults incurred by computable recency-list LRU from `q` on `reqs`. -/
@[expose]
def lruFaults (k : Nat) (q : List α) : List α → Nat
  | [] => 0
  | p :: ps => (if p ∈ q then 0 else 1) + lruFaults k (lruNext k q p) ps

@[simp]
theorem lruRun_nil (k : Nat) (q : List α) : lruRun k q [] = q := rfl

@[simp]
theorem lruRun_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    lruRun k q (p :: ps) = lruRun k (lruNext k q p) ps := rfl

@[simp]
theorem lruFaults_nil (k : Nat) (q : List α) : lruFaults k q [] = 0 := rfl

@[simp]
theorem lruFaults_cons (k : Nat) (q : List α) (p : α) (ps : List α) :
    lruFaults k q (p :: ps) = (if p ∈ q then 0 else 1) + lruFaults k (lruNext k q p) ps := rfl

private theorem notMem_erase_of_nodup {q : List α} (hq : q.Nodup) (p : α) : p ∉ q.erase p := by
  induction q with
  | nil => simp
  | cons x xs ih =>
    rcases List.nodup_cons.mp hq with ⟨hx, hxs⟩
    by_cases hxp : x = p
    · subst hxp
      simpa only [List.erase_cons_head] using hx
    · rw [List.erase_cons_tail (by simp [hxp]), List.mem_cons]
      rintro (rfl | hm)
      · exact hxp rfl
      · exact ih hxs hm

/-- `lruNext` preserves `List.Nodup`. -/
theorem nodup_lruNext {k : Nat} {q : List α} (hq : q.Nodup) (p : α) :
    (lruNext k q p).Nodup := by
  unfold lruNext
  split
  · exact List.nodup_cons.mpr ⟨notMem_erase_of_nodup hq p, hq.erase p⟩
  · next hp =>
    exact (List.nodup_cons.mpr ⟨hp, hq⟩).take

/-- `lruNext k` preserves `length ≤ k`. -/
theorem length_lruNext_le {k : Nat} {q : List α} (hq : q.length ≤ k) (p : α) :
    (lruNext k q p).length ≤ k := by
  unfold lruNext
  split
  · next hp =>
    rw [List.length_cons, List.length_erase_of_mem hp]
    have hpos : 1 ≤ q.length := List.length_pos_of_mem hp
    omega
  · exact List.length_take_le k (p :: q)

/-- On a hit `p ∈ q`, `lruNext` preserves the underlying set of cached pages. -/
theorem toFinset_lruNext_of_mem {k : Nat} {q : List α} {p : α} (hp : p ∈ q) :
    (lruNext k q p).toFinset = q.toFinset := by
  simp only [lruNext, hp, ↓reduceIte, List.toFinset_cons]
  ext x
  simp only [Finset.mem_insert, List.mem_toFinset]
  constructor
  · rintro (rfl | hx)
    · exact hp
    · exact List.mem_of_mem_erase hx
  · intro hx
    by_cases hxp : x = p
    · exact Or.inl hxp
    · exact Or.inr ((List.mem_erase_of_ne hxp).mpr hx)

/-- For `0 < k`, `p` always resides in `lruNext k q p`. -/
theorem mem_lruNext {k : Nat} (hk : 0 < k) (q : List α) (p : α) :
    p ∈ lruNext k q p := by
  unfold lruNext
  split
  · exact List.mem_cons_self
  · cases k with
    | zero => omega
    | succ k' =>
      simp only [List.take_succ_cons, List.mem_cons, true_or]

/-- Every page in `lruNext k q p` comes from `insert p q.toFinset`. -/
theorem toFinset_lruNext_subset {k : Nat} (q : List α) (p : α) :
    (lruNext k q p).toFinset ⊆ insert p q.toFinset := by
  intro x hx
  rw [List.mem_toFinset] at hx
  unfold lruNext at hx
  split at hx
  · simp only [List.mem_cons] at hx
    rcases hx with hxp | hx
    · subst x
      exact Finset.mem_insert_self p _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_of_mem_erase hx))
  · have hmem := List.mem_of_mem_take hx
    simp only [List.mem_cons] at hmem
    rcases hmem with hxp | hmem
    · subst x
      exact Finset.mem_insert_self p _
    · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hmem)

/-- For `0 < k`, `lruNext` induces a valid demand-paging transition on `q.toFinset`. -/
theorem validStep_lruNext {k : Nat} (hk : 0 < k) {q : List α}
    (hlen : q.length ≤ k) (p : α) :
    ValidStep k q.toFinset p (lruNext k q p).toFinset := by
  have hcard : q.toFinset.card ≤ k := (List.toFinset_card_le q).trans hlen
  have hcard' : (lruNext k q p).toFinset.card ≤ k :=
    (List.toFinset_card_le _).trans (length_lruNext_le hlen p)
  have hmem : p ∈ (lruNext k q p).toFinset := List.mem_toFinset.mpr (mem_lruNext hk q p)
  refine ⟨hcard, hcard', hmem, ?_⟩
  by_cases hp : p ∈ q
  · have hps : p ∈ q.toFinset := List.mem_toFinset.mpr hp
    simp only [hps, ↓reduceIte, toFinset_lruNext_of_mem hp]
  · have hps : p ∉ q.toFinset := by simpa only [List.mem_toFinset] using hp
    simp only [hps, ↓reduceIte]
    exact toFinset_lruNext_subset q p

/-! ### Packaging LRU as an `Online.DetStrategy` -/

/-- Deterministic online strategy realizing LRU for demand paging with positive capacity `k`.

Marked `noncomputable` solely because `init s₀ := s₀.toList` selects an initial recency ordering on
pre-loaded cache elements from `s₀ : Finset α` (canonically `[]` when `s₀ = ∅`, as witnessed by
`lruStrategy_cost_empty`, with `lruPotential k s₀ s₀.toList = 0` for every `s₀`). For an explicit
initial recency list `q : List α`, `lruRun`, `lruFaults`, and `lruFaults_amortized_bound` are
directly computable. -/
noncomputable abbrev lruStrategy (k : Nat) (hk : 0 < k) : DetStrategy (problem α k) where
  Mem := List α
  ValidMem q := q.Nodup ∧ q.length ≤ k
  project q := q.toFinset
  init s₀ := s₀.toList
  step q p := lruNext k q p
  valid_init hs₀ := by
    refine ⟨⟨Finset.nodup_toList _, ?_⟩, Finset.toList_toFinset _⟩
    rw [Finset.length_toList]
    exact hs₀
  valid_step {q} p hq :=
    ⟨⟨nodup_lruNext hq.1 p, length_lruNext_le hq.2 p⟩, validStep_lruNext hk hq.2 p⟩

/-- `lruStrategy.runMem` agrees with computable `lruRun`. -/
theorem lruStrategy_runMem_eq (k : Nat) (hk : 0 < k) (q : List α) (reqs : List α) :
    (lruStrategy (α := α) k hk).runMem q reqs = lruRun k q reqs := by
  induction reqs generalizing q with
  | nil => rfl
  | cons p ps ih => exact ih (lruNext k q p)

/-- `lruStrategy.costFrom` agrees with computable `lruFaults`. -/
theorem lruStrategy_costFrom_eq (k : Nat) (hk : 0 < k) (q : List α) (reqs : List α) :
    (lruStrategy (α := α) k hk).costFrom q reqs = lruFaults k q reqs := by
  induction reqs generalizing q with
  | nil => rfl
  | cons p ps ih =>
    change stepCost q.toFinset p (lruNext k q p).toFinset +
        (lruStrategy (α := α) k hk).costFrom (lruNext k q p) ps = _
    simp only [stepCost, List.mem_toFinset, ih (lruNext k q p), lruFaults_cons]

/-- From an empty cache `∅`, `lruStrategy.cost` equals computable `lruFaults k [] reqs`. -/
theorem lruStrategy_cost_empty (k : Nat) (hk : 0 < k) (reqs : List α) :
    (lruStrategy (α := α) k hk).cost ∅ reqs = lruFaults k [] reqs := by
  rw [(lruStrategy (α := α) k hk).cost_eq_costFrom (validCache_empty k), lruStrategy_costFrom_eq]
  simp only [Finset.toList_empty]

/-! ### Potential function and structural step inequalities -/

/-- Recency weight of the most recently used element in `q` absent from `s` (`0` if all elements of
`q` belong to `s`), assigning head weight `w` and decrementing by `1` at each step toward the LRU
tail. -/
@[expose]
def maxWeightFrom (w : Nat) (s : Finset α) : List α → Nat
  | [] => 0
  | x :: xs => if x ∈ s then maxWeightFrom (w - 1) s xs else w

/-- Potential function between offline cache `s` and LRU recency list `q` at capacity `k`. -/
@[expose]
def lruPotential (k : Nat) (s : Finset α) (q : List α) : Nat :=
  max (maxWeightFrom k s q) (s \ q.toFinset).card

@[simp]
theorem maxWeightFrom_nil (w : Nat) (s : Finset α) : maxWeightFrom w s ([] : List α) = 0 := rfl

@[simp]
theorem maxWeightFrom_cons (w : Nat) (s : Finset α) (x : α) (xs : List α) :
    maxWeightFrom w s (x :: xs) = if x ∈ s then maxWeightFrom (w - 1) s xs else w := rfl

/-- `maxWeightFrom w s q` never exceeds the head weight `w`. -/
theorem maxWeightFrom_le (w : Nat) (s : Finset α) (q : List α) :
    maxWeightFrom w s q ≤ w := by
  induction q generalizing w with
  | nil => exact Nat.zero_le w
  | cons x xs ih =>
    simp only [maxWeightFrom_cons]
    split
    · exact (ih (w - 1)).trans (Nat.sub_le w 1)
    · exact Nat.le_refl w

/-- When every page of `q` is in `s`, `maxWeightFrom` vanishes. -/
theorem maxWeightFrom_eq_zero_of_subset {s : Finset α} {q : List α}
    (h : ∀ x ∈ q, x ∈ s) (w : Nat) : maxWeightFrom w s q = 0 := by
  induction q generalizing w with
  | nil => rfl
  | cons x xs ih =>
    simp only [maxWeightFrom_cons, h x List.mem_cons_self, ↓reduceIte]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) (w - 1)

/-- Taking a prefix cannot increase `maxWeightFrom`. -/
theorem maxWeightFrom_take_le (w : Nat) (s : Finset α) (q : List α) (n : Nat) :
    maxWeightFrom w s (q.take n) ≤ maxWeightFrom w s q := by
  induction q generalizing w n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.take_succ_cons, maxWeightFrom_cons]
      split
      · exact ih (w - 1) n
      · exact Nat.le_refl w

/-- Removing a resident page `p ∈ s` from `q` and decrementing the starting weight does not
increase `maxWeightFrom`. -/
theorem maxWeightFrom_erase_of_mem {s : Finset α} {p : α} (hp : p ∈ s) (w : Nat) (q : List α) :
    maxWeightFrom (w - 1) s (q.erase p) ≤ maxWeightFrom w s q := by
  induction q generalizing w with
  | nil => simp
  | cons x xs ih =>
    by_cases hxp : x = p
    · subst hxp
      simp only [List.erase_cons_head, maxWeightFrom_cons, hp, ↓reduceIte, le_refl]
    · rw [List.erase_cons_tail (by simp [hxp])]
      simp only [maxWeightFrom_cons]
      split
      · exact ih (w - 1)
      · omega

/-- Decrementing the starting weight either yields `0` or decreases `maxWeightFrom` by at least
`1`. -/
theorem maxWeightFrom_pred_zero_or_lt (w : Nat) (s : Finset α) (q : List α) :
    maxWeightFrom (w - 1) s q = 0 ∨ maxWeightFrom (w - 1) s q + 1 ≤ maxWeightFrom w s q := by
  induction q generalizing w with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    simp only [maxWeightFrom_cons]
    split
    · exact ih (w - 1)
    · by_cases hw : w = 0
      · subst hw
        exact Or.inl rfl
      · exact Or.inr (by omega)

/-- Erasing a page `x ∉ q` from `s` leaves `maxWeightFrom w s q` unchanged. -/
private theorem maxWeightFrom_erase_finset_of_notMem {s : Finset α} {x : α} {q : List α}
    (hx : x ∉ q) (w : Nat) :
    maxWeightFrom w (s.erase x) q = maxWeightFrom w s q := by
  induction q generalizing w with
  | nil => rfl
  | cons y ys ih =>
    have hyx : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    have hmem : (y ∈ s.erase x) ↔ (y ∈ s) := Finset.mem_erase.trans (and_iff_right hyx)
    simp only [maxWeightFrom_cons, hmem,
      ih (fun h => hx (List.mem_cons_of_mem y h)) (w - 1)]

/-- Structural bound when a full LRU list `init ++ [last]` evicts a page `last ∈ s` on a miss
`p ∈ s \ (init ++ [last])`: at least one element of `init` outside `s` sits high enough in recency
order to dominate `1 + (s \ (p :: init).toFinset).card`. -/
private theorem one_add_sdiff_le_maxWeightFrom_snoc :
    ∀ (init : List α) {last p : α} {s : Finset α},
      (init ++ [last]).Nodup →
      s.card ≤ init.length + 1 →
      p ∈ s →
      p ∉ init ++ [last] →
      last ∈ s →
      1 + (s \ (p :: init).toFinset).card ≤
        maxWeightFrom (init.length + 1) s (init ++ [last])
  | [], last, p, s, _, hcard, hps, hpnot, hlast => by
    have hne : p ≠ last := fun h => hpnot (by simp [h])
    have hsub : ({p, last} : Finset α) ⊆ s := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have h2 : 2 ≤ s.card := by
      have hc := Finset.card_le_card hsub
      rw [Finset.card_pair hne] at hc
      exact hc
    simp only [List.length_nil, Nat.zero_add] at hcard
    omega
  | x :: xs, last, p, s, hnodup, hcard, hps, hpnot, hlast => by
    simp only [List.cons_append, List.length_cons, maxWeightFrom_cons] at hnodup hcard hpnot ⊢
    rcases List.nodup_cons.mp hnodup with ⟨hxnot, hnodup'⟩
    simp only [List.mem_cons, not_or] at hpnot
    rcases hpnot with ⟨hpx, hpnot'⟩
    split
    · next hxs =>
      have hlx : last ≠ x := fun h => hxnot (by simp [h])
      have hcard' : (s.erase x).card ≤ xs.length + 1 := by
        rw [Finset.card_erase_of_mem hxs]
        have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨x, hxs⟩
        omega
      have hps' : p ∈ s.erase x := Finset.mem_erase.mpr ⟨hpx, hps⟩
      have hlast' : last ∈ s.erase x := Finset.mem_erase.mpr ⟨hlx, hlast⟩
      have ih := one_add_sdiff_le_maxWeightFrom_snoc xs hnodup' hcard' hps' hpnot' hlast'
      rw [maxWeightFrom_erase_finset_of_notMem hxnot] at ih
      have hsdiff : s \ (p :: x :: xs).toFinset = s.erase x \ (p :: xs).toFinset := by
        ext z
        simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, Finset.mem_erase]
        tauto
      rw [hsdiff]
      simpa only [Nat.add_sub_cancel] using ih
    · have hsub : s \ (p :: x :: xs).toFinset ⊆ s.erase p := by
        intro z hz
        rw [Finset.mem_sdiff, List.mem_toFinset] at hz
        exact Finset.mem_erase.mpr ⟨fun h => hz.2 (h ▸ List.mem_cons_self), hz.1⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hps] at hc
      have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨p, hps⟩
      omega

/-- `lruPotential k s q` never exceeds `k` when `s.card ≤ k`. -/
theorem lruPotential_le {k : Nat} {s : Finset α} (hs : s.card ≤ k) (q : List α) :
    lruPotential k s q ≤ k := by
  apply max_le (maxWeightFrom_le k s q)
  exact (Finset.card_le_card Finset.sdiff_subset).trans hs

/-- `lruPotential k s q` vanishes whenever `q` represents the exact same page set as `s`. -/
theorem lruPotential_eq_zero_of_toFinset_eq (k : Nat) {s : Finset α} {q : List α}
    (h : q.toFinset = s) : lruPotential k s q = 0 := by
  unfold lruPotential
  have h1 : maxWeightFrom k s q = 0 := by
    apply maxWeightFrom_eq_zero_of_subset
    intro x hx
    rw [← h, List.mem_toFinset]
    exact hx
  have h2 : (s \ q.toFinset).card = 0 := by
    simp only [h, Finset.sdiff_self, Finset.card_empty]
  rw [h1, h2, max_self]

/-- Single-step competitive potential inequality for LRU (`0 < k`). -/
theorem lruPotential_step {k : Nat} (hk : 0 < k) {s s' : Finset α} {q : List α} {p : α}
    (hq : q.Nodup ∧ q.length ≤ k) (hv : ValidStep k s p s') :
    stepCost q.toFinset p (lruNext k q p).toFinset + lruPotential k s' (lruNext k q p) ≤
      k * stepCost s p s' + lruPotential k s q := by
  rcases hq with ⟨hnodup, hlen⟩
  have hs_card : s.card ≤ k := hv.1
  have hs'_card : s'.card ≤ k := hv.2.1
  have hps' : p ∈ s' := hv.2.2.1
  by_cases hps : p ∈ s
  · -- Offline hit (`stepCost s p s' = 0`, `s' = s`)
    have hs'_eq : s' = s := validStep_hit_eq hv hps
    subst s'
    rw [stepCost_of_mem hps, Nat.mul_zero, Nat.zero_add]
    by_cases hpq : p ∈ q
    · -- Online hit (`p ∈ q`)
      have hpqs : p ∈ q.toFinset := List.mem_toFinset.mpr hpq
      rw [stepCost_of_mem hpqs, Nat.zero_add]
      unfold lruPotential
      apply max_le
      · simp only [lruNext, hpq, ↓reduceIte, maxWeightFrom_cons, hps]
        exact (maxWeightFrom_erase_of_mem hps k q).trans (le_max_left _ _)
      · rw [toFinset_lruNext_of_mem hpq]
        exact le_max_right _ _
    · -- Online miss (`p ∉ q`) while offline hits (`p ∈ s`)
      have hpqs : p ∉ q.toFinset := by simpa only [List.mem_toFinset] using hpq
      rw [stepCost_of_notMem hpqs]
      have htake_eq : lruNext k q p = p :: q.take (k - 1) := by
        cases k with
        | zero => omega
        | succ k' => simp only [lruNext, hpq, ↓reduceIte, List.take_succ_cons, Nat.add_sub_cancel]
      rw [htake_eq]
      have hp_sdiff : 1 ≤ (s \ q.toFinset).card :=
        Finset.one_le_card.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hps, hpqs⟩⟩
      have hmaxW : 1 + maxWeightFrom k s (p :: q.take (k - 1)) ≤ lruPotential k s q := by
        simp only [maxWeightFrom_cons, hps, ↓reduceIte]
        have hle := maxWeightFrom_take_le (k - 1) s q (k - 1)
        rcases maxWeightFrom_pred_zero_or_lt k s q with hz | hlt
        · rw [hz] at hle
          have hz' : maxWeightFrom (k - 1) s (q.take (k - 1)) = 0 := Nat.eq_zero_of_le_zero hle
          rw [hz', Nat.add_zero]
          exact hp_sdiff.trans (le_max_right _ _)
        · have h1 : 1 + maxWeightFrom (k - 1) s (q.take (k - 1)) ≤ maxWeightFrom k s q := by omega
          exact h1.trans (le_max_left _ _)
      have hsdiff : 1 + (s \ (p :: q.take (k - 1)).toFinset).card ≤ lruPotential k s q := by
        by_cases hfull : q.length < k
        · have htake_all : q.take (k - 1) = q := List.take_of_length_le (by omega)
          rw [htake_all]
          have herase : s \ (p :: q).toFinset = (s \ q.toFinset).erase p := by
            ext z
            simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, Finset.mem_erase]
            tauto
          rw [herase, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hps, hpqs⟩)]
          have : 1 + ((s \ q.toFinset).card - 1) = (s \ q.toFinset).card := by omega
          rw [this]
          exact le_max_right _ _
        · have hqlen : q.length = k := by omega
          have hqne : q ≠ [] := by
            intro hnil
            rw [hnil, List.length_nil] at hqlen
            omega
          have hsnoc : q.dropLast ++ [q.getLast hqne] = q := List.dropLast_append_getLast hqne
          set init := q.dropLast
          set last := q.getLast hqne
          have hinit_len : init.length = k - 1 := by
            simp only [init, List.length_dropLast, hqlen]
          have htake_init : q.take (k - 1) = init := by
            rw [← hsnoc, ← hinit_len, List.take_left]
          rw [htake_init]
          by_cases hlast : last ∈ s
          · rw [← hsnoc] at hnodup hpq ⊢
            have hk_eq : k = init.length + 1 := by omega
            rw [hk_eq] at hs_card ⊢
            exact (one_add_sdiff_le_maxWeightFrom_snoc init hnodup hs_card hps hpq hlast).trans
              (le_max_left _ _)
          · have herase : s \ (p :: init).toFinset = (s \ q.toFinset).erase p := by
              rw [← hsnoc]
              ext z
              simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, List.mem_append,
                List.not_mem_nil, or_false, Finset.mem_erase]
              constructor
              · rintro ⟨hzs, hnot⟩
                refine ⟨fun hzp => hnot (Or.inl hzp), hzs, ?_⟩
                rintro (hzi | hzl)
                · exact hnot (Or.inr hzi)
                · subst z
                  exact hlast hzs
              · rintro ⟨hzp, hzs, hzq⟩
                exact ⟨hzs, fun h => h.elim hzp (fun hzi => hzq (Or.inl hzi))⟩
            rw [herase, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hps, hpqs⟩)]
            have : 1 + ((s \ q.toFinset).card - 1) = (s \ q.toFinset).card := by omega
            rw [this]
            exact le_max_right _ _
      have hcases :
          lruPotential k s (p :: q.take (k - 1)) = maxWeightFrom k s (p :: q.take (k - 1)) ∨
          lruPotential k s (p :: q.take (k - 1)) = (s \ (p :: q.take (k - 1)).toFinset).card :=
        max_choice _ _
      rcases hcases with heq | heq <;> omega
  · -- Offline miss (`stepCost s p s' = 1`, `p ∈ s'`)
    rw [stepCost_of_notMem hps, Nat.mul_one]
    by_cases hpq : p ∈ q
    · -- Online hit (`p ∈ q`)
      have hpqs : p ∈ q.toFinset := List.mem_toFinset.mpr hpq
      rw [stepCost_of_mem hpqs, Nat.zero_add]
      have hpot := lruPotential_le hs'_card (lruNext k q p)
      omega
    · -- Online miss (`p ∉ q`)
      have hpqs : p ∉ q.toFinset := by simpa only [List.mem_toFinset] using hpq
      rw [stepCost_of_notMem hpqs]
      have htake_eq : lruNext k q p = p :: q.take (k - 1) := by
        cases k with
        | zero => omega
        | succ k' => simp only [lruNext, hpq, ↓reduceIte, List.take_succ_cons, Nat.add_sub_cancel]
      rw [htake_eq]
      have hmaxW : maxWeightFrom k s' (p :: q.take (k - 1)) ≤ k - 1 := by
        simp only [maxWeightFrom_cons, hps', ↓reduceIte]
        exact maxWeightFrom_le (k - 1) s' (q.take (k - 1))
      have hsdiff : (s' \ (p :: q.take (k - 1)).toFinset).card ≤ k - 1 := by
        have hsub : s' \ (p :: q.take (k - 1)).toFinset ⊆ s'.erase p := by
          intro z hz
          rw [Finset.mem_sdiff, List.mem_toFinset] at hz
          exact Finset.mem_erase.mpr ⟨fun h => hz.2 (h ▸ List.mem_cons_self), hz.1⟩
        have hc := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hps'] at hc
        have hpos : 1 ≤ s'.card := Finset.one_le_card.mpr ⟨p, hps'⟩
        omega
      have hpot : lruPotential k s' (p :: q.take (k - 1)) ≤ k - 1 := max_le hmaxW hsdiff
      omega

/-! ### `Cslib.Stateful.Amortized` certificate and competitive theorems -/

/-- Native `Cslib.Stateful.Amortized` potential certificate for `lruStrategy k hk` against `k`
times the offline demand-paging step cost. -/
theorem lruAmortized (k : Nat) (hk : 0 < k) :
    Amortized (lruStrategy (α := α) k hk).realization id (lruPotential k)
      (fun s o => k * stepCost s o.1 o.2) where
  step {s q o _ q' w} hrep hv hexec := by
    rcases hexec with ⟨rfl, rfl⟩
    simpa only [id_eq, lruStrategy, problem, Problem.offlineSpec] using
      lruPotential_step hk hrep hv

/-- Computable-list telescoping bound for LRU: for any valid recency list `q` and any valid offline
schedule `(s_off, reqs, offStates)`, `lruFaults k q reqs` plus final potential is at most `k` times
offline faults plus initial potential. -/
theorem lruFaults_amortized_bound {k : Nat} (hk : 0 < k) {s_off : Finset α} {q : List α}
    {reqs : List α} {offStates : List (Finset α)}
    (hq : q.Nodup ∧ q.length ≤ k) (hv : (problem α k).ValidSchedule s_off reqs offStates) :
    lruFaults k q reqs +
        lruPotential k ((problem α k).finalState s_off offStates) (lruRun k q reqs) ≤
      k * (problem α k).scheduleCost s_off reqs offStates + lruPotential k s_off q := by
  have h := (lruStrategy (α := α) k hk).amortized_bound (lruAmortized k hk) hq hv
  simpa only [lruStrategy_costFrom_eq, lruStrategy_runMem_eq] using h

/-- **LRU `k`-competitiveness from a common initial cache** ([SleatorTarjan1985], Theorem 6 at
`n_LRU = n_MIN = k` with identical initial caches): when online and offline algorithms start from
the same valid cache `s₀` (including `∅`), `lruStrategy k hk` incurs at most `k` times the faults
of any valid offline schedule, with zero additive constant. -/
theorem lruStrategy_isCompetitive (k : Nat) (hk : 0 < k) :
    (lruStrategy (α := α) k hk).IsCompetitive k 0 := by
  apply (lruStrategy (α := α) k hk).competitive_of_amortized (lruAmortized k hk)
  intro s₀ _
  simp only [lruPotential_eq_zero_of_toFinset_eq k (Finset.toList_toFinset s₀), le_refl]

/-- **LRU `k`-competitiveness across arbitrary initial caches** ([SleatorTarjan1985], Theorem 6 at
`n_LRU = n_MIN = k`): for any valid initial caches `s₀` and `s_off` of size at most `k`,
`lruStrategy k hk` incurs at most `k * optCost + k` faults. -/
theorem lruStrategy_isCompetitiveAnyInit (k : Nat) (hk : 0 < k) :
    (lruStrategy (α := α) k hk).IsCompetitiveAnyInit k k := by
  apply (lruStrategy (α := α) k hk).competitiveAnyInit_of_amortized (lruAmortized k hk)
  intro s₀ s_off _ hs_off
  exact lruPotential_le hs_off s₀.toList

end Cslib.Algorithms.Lean.Paging
