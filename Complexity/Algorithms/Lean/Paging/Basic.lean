/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Online.Basic
public import Mathlib.Data.Finset.Card

/-!
# The demand-paging action and cost model

This file instantiates `Cslib.Algorithms.Lean.Online.Problem` for the classical unweighted
demand-paging (cache replacement) problem of
[Sleator and Tarjan, *Amortized Efficiency of List Update and Paging Rules*, Section 4 ("Paging"),
pp. 207–208][SleatorTarjan1985] and [Cormen, Leiserson, Rivest, and Stein, *Introduction to
Algorithms*, third edition, Problem 16-5 ("Off-line caching")][CLRS2009].

Over a page universe `α` (`[DecidableEq α]`) and cache capacity `k : Nat`:

* An observable cache configuration is a finite set `s : Finset α` satisfying `ValidCache k s`
  (`s.card ≤ k`).
* On request `p : α`:
  * **Cache hit (`p ∈ s`):** `p` is already resident; no fault is charged (`stepCost = 0`) and the
    cache remains unchanged (`s' = s`).
  * **Cache miss (`p ∉ s`):** `p` must be loaded into the new cache (`p ∈ s'`, `s'.card ≤ k`) while
    retaining only pages from `insert p s` (`s' ⊆ insert p s`, retaining any subset of `insert p s`
    of size at most `k` — in particular single-page replacement when `s.card = k` and non-evicting
    insertion when `s.card < k`), incurring one page fault (`stepCost = 1`).

Both online paging strategies (`Online.DetStrategy (problem α k)`) and offline reference schedules
(`(problem α k).ValidSchedule`) share this exact transition and fault-counting specification,
including initial cache configurations.

## Main definitions

* `Cslib.Algorithms.Lean.Paging.ValidCache`: capacity bound `s.card ≤ k`.
* `Cslib.Algorithms.Lean.Paging.ValidStep`: valid demand-paging transition `s ↦ s'` on request `p`.
* `Cslib.Algorithms.Lean.Paging.stepCost`: unit fault cost (`0` on hit, `1` on miss).
* `Cslib.Algorithms.Lean.Paging.problem`: the `Online.Problem` instance for demand paging.

## Main results

* `validStep_hit`, `validStep_insert`, `validStep_replace`: constructors for cache hits, non-full
  insertions, and single-page evictions.
* `scheduleCost_le_length`: total page faults over any trajectory never exceed the number of
  requests.
* `validSchedule_replicate_of_forall_mem`, `scheduleCost_replicate_of_forall_mem`: serving a
  sequence of resident pages keeps the cache constant at zero fault cost.

## References

* [D. D. Sleator and R. E. Tarjan, *Amortized Efficiency of List Update and Paging
  Rules*][SleatorTarjan1985]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Paging

open Cslib.Algorithms.Lean.Online

/-- A cache configuration is admissible for capacity `k` when it holds at most `k` pages. -/
@[expose]
def ValidCache {α : Type} (k : Nat) (s : Finset α) : Prop :=
  s.card ≤ k

@[simp]
theorem validCache_empty {α : Type} (k : Nat) : ValidCache k (∅ : Finset α) :=
  Nat.zero_le k

section Decidable

variable {α : Type} [DecidableEq α]

/-- Valid single-request demand-paging transition `s ↦ s'` on page `p`: both caches hold at most
`k` pages, `p` resides in `s'`, cache hits preserve `s' = s`, and cache misses satisfy
`s' ⊆ insert p s`. -/
@[expose]
def ValidStep (k : Nat) (s : Finset α) (p : α) (s' : Finset α) : Prop :=
  s.card ≤ k ∧ s'.card ≤ k ∧ p ∈ s' ∧
    if p ∈ s then s' = s else s' ⊆ insert p s

/-- Standard paging cost: `0` on a cache hit (`p ∈ s`) and `1` on a cache miss (`p ∉ s`). -/
@[expose]
def stepCost (s : Finset α) (p : α) (_ : Finset α) : Nat :=
  if p ∈ s then 0 else 1

/-- The demand-paging `Online.Problem` over page type `α` and cache capacity `k`. -/
abbrev problem (α : Type) [DecidableEq α] (k : Nat) : Problem where
  State := Finset α
  Req := α
  ValidInit := ValidCache k
  ValidStep := ValidStep k
  stepCost := stepCost

@[simp]
theorem stepCost_of_mem {s s' : Finset α} {p : α} (hp : p ∈ s) :
    stepCost s p s' = 0 := by
  simp only [stepCost, hp, ↓reduceIte]

@[simp]
theorem stepCost_of_notMem {s s' : Finset α} {p : α} (hp : p ∉ s) :
    stepCost s p s' = 1 := by
  simp only [stepCost, hp, ↓reduceIte]

/-- Every single-step paging transition charges at most one fault. -/
theorem stepCost_le_one (s : Finset α) (p : α) (s' : Finset α) :
    stepCost s p s' ≤ 1 := by
  unfold stepCost
  split <;> omega

/-- A cache hit keeps `s` unchanged as a valid transition. -/
theorem validStep_hit {k : Nat} {s : Finset α} {p : α} (hs : s.card ≤ k) (hp : p ∈ s) :
    ValidStep k s p s := by
  refine ⟨hs, hs, hp, ?_⟩
  simp only [hp, ↓reduceIte]

/-- Every valid transition on a resident page `p ∈ s` leaves the cache unchanged. -/
theorem validStep_hit_eq {k : Nat} {s s' : Finset α} {p : α}
    (hv : ValidStep k s p s') (hp : p ∈ s) : s' = s := by
  have h := hv.2.2.2
  simp only [hp, ↓reduceIte] at h
  exact h

/-- Every valid transition on a missing page `p ∉ s` satisfies `s' ⊆ insert p s`. -/
theorem validStep_miss_subset {k : Nat} {s s' : Finset α} {p : α}
    (hv : ValidStep k s p s') (hp : p ∉ s) : s' ⊆ insert p s := by
  have h := hv.2.2.2
  simp only [hp, ↓reduceIte] at h
  exact h

/-- Loading a missing page into a non-full cache (`s.card < k`) without eviction is valid. -/
theorem validStep_insert {k : Nat} {s : Finset α} {p : α}
    (hs : s.card < k) (hp : p ∉ s) :
    ValidStep k s p (insert p s) := by
  have hcard : (insert p s).card ≤ k := by
    rw [Finset.card_insert_of_notMem hp]
    omega
  refine ⟨Nat.le_of_lt hs, hcard, Finset.mem_insert_self p s, ?_⟩
  simp only [hp, ↓reduceIte, Finset.Subset.refl]

/-- Evicting a resident page `e ∈ s` to load a missing page `p ∉ s` preserves cardinality. -/
theorem card_insert_erase_of_notMem {s : Finset α} {p e : α} (hp : p ∉ s) (he : e ∈ s) :
    (insert p (s.erase e)).card = s.card := by
  have hp' : p ∉ s.erase e := fun h => hp (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hp', Finset.card_erase_of_mem he]
  have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨e, he⟩
  omega

/-- Evicting a resident page `e ∈ s` to load a missing page `p ∉ s` is a valid paging step. -/
theorem validStep_replace {k : Nat} {s : Finset α} {p e : α}
    (hs : s.card ≤ k) (hp : p ∉ s) (he : e ∈ s) :
    ValidStep k s p (insert p (s.erase e)) := by
  refine ⟨hs, ?_, Finset.mem_insert_self p _, ?_⟩
  · rw [card_insert_erase_of_notMem hp he]
    exact hs
  · simp only [hp, ↓reduceIte]
    exact Finset.insert_subset_insert p (Finset.erase_subset e s)

/-- Total faults along any schedule are at most the number of requests. -/
theorem scheduleCost_le_length (k : Nat) (s : Finset α) (reqs : List α)
    (states : List (Finset α)) :
    (problem α k).scheduleCost s reqs states ≤ reqs.length := by
  induction reqs generalizing s states with
  | nil =>
    cases states <;> exact Nat.zero_le _
  | cons p rs ih =>
    cases states with
    | nil => exact Nat.zero_le _
    | cons s' ss =>
      change stepCost s p s' + (problem α k).scheduleCost s' rs ss ≤ rs.length + 1
      have h1 := stepCost_le_one s p s'
      have h2 := ih s' ss
      omega

/-- Serving a request sequence whose pages are all already in `s` keeps `s` unchanged. -/
theorem validSchedule_replicate_of_forall_mem {k : Nat} {s : Finset α} {reqs : List α}
    (hs : s.card ≤ k) (hmem : ∀ p ∈ reqs, p ∈ s) :
    (problem α k).ValidSchedule s reqs (List.replicate reqs.length s) := by
  induction reqs with
  | nil => trivial
  | cons p rs ih =>
    exact ⟨validStep_hit hs (hmem p List.mem_cons_self),
      ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))⟩

/-- Serving a request sequence whose pages are all already in `s` incurs zero faults. -/
theorem scheduleCost_replicate_of_forall_mem {k : Nat} {s : Finset α} {reqs : List α}
    (hmem : ∀ p ∈ reqs, p ∈ s) :
    (problem α k).scheduleCost s reqs (List.replicate reqs.length s) = 0 := by
  induction reqs with
  | nil => rfl
  | cons p rs ih =>
    change stepCost s p s + (problem α k).scheduleCost s rs (List.replicate rs.length s) = 0
    rw [stepCost_of_mem (hmem p List.mem_cons_self), Nat.zero_add]
    exact ih (fun q hq => hmem q (List.mem_cons_of_mem p hq))

end Decidable

/-- Repeating `s` along any list ends in `s`. -/
@[simp]
theorem finalState_replicate {α : Type} [DecidableEq α] (k : Nat) (s : Finset α) (n : Nat) :
    (problem α k).finalState s (List.replicate n s) = s := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Every valid demand-paging schedule starting from a valid cache ends in a valid cache. -/
theorem validCache_finalState {α : Type} [DecidableEq α] {k : Nat} {s₀ : Finset α}
    {reqs : List α} {states : List (Finset α)} (hs₀ : ValidCache k s₀)
    (hv : (problem α k).ValidSchedule s₀ reqs states) :
    ValidCache k ((problem α k).finalState s₀ states) :=
  (problem α k).validInit_finalState (fun _ h => h.2.1) hs₀ hv

end Cslib.Algorithms.Lean.Paging
