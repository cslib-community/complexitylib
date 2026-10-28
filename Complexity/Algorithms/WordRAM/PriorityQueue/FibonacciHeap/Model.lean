/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.IndexedMinPQ
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Relation

/-!
# Mathematical model of a static-array Fibonacci heap

This file develops the pure-Lean invariants and structural lemmas underlying the static-array
Word-RAM Fibonacci heap [Fredman and Tarjan][FredmanTarjan1987]
[Cormen et al., Chapter 19][CLRS2009]:

1. **Circular doubly-linked lists (`ChainLinks`, `IsCircList`):** Pointer-level invariants over
   `Fin n → ℕ` supporting `O(1)` singleton creation, post-head insertion, cyclic rotation, arbitrary
   node removal, and disjoint-support framing without modular index arithmetic.
2. **Pure-`ℕ` Fibonacci rank and degree bound:** Proves the sum identity
   `1 + ∑_{i < k} fib ((i - 1) + 2) = fib (k + 2)` and `2 ^ m ≤ fib (2 * m + 2)`, deriving
   `d ≤ 2 * Nat.log 2 n + 1` from `fib (d + 2) ≤ n` without real numbers or floating-point
   logarithms.

## Main definitions

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.ChainLinks`, `IsCircList`: pointer-level
  invariants for circular doubly-linked lists over `Fin n → ℕ`.

## Main results

* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.IsCircList.singleton`,
  `IsCircList.insertAfter`, `IsCircList.rotate_to`, `IsCircList.remove`: circular-list operations.
* `Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap.fib_sum_pred_add_two`,
  `deg_le_two_mul_log_add_one`: pure-`ℕ` Fibonacci child-rank sum and `2 * Nat.log 2 n + 1` degree
  bound.

## References

* [M. L. Fredman and R. E. Tarjan, *Fibonacci Heaps and Their Uses in Improved Network Optimization
  Algorithms*][FredmanTarjan1987]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap

open Cslib.Algorithms.Lean

/-! ## Circular doubly-linked lists over `Fin n` -/

/-- Pointer chain from `prev` through `xs` closing back to `first`. -/
def ChainLinks {n : ℕ} (left right : Fin n → ℕ) (first prev : Fin n) : List (Fin n) → Prop
  | [] => right prev = first.val ∧ left first = prev.val
  | x :: xs => right prev = x.val ∧ left x = prev.val ∧ ChainLinks left right first x xs

/-- `L` is represented as a circular doubly-linked list by `left` and `right` (with `[]` vacuously
valid and `h :: tail` forming a `Nodup` cycle starting at `h`). -/
def IsCircList {n : ℕ} (left right : Fin n → ℕ) : List (Fin n) → Prop
  | [] => True
  | h :: tail => (h :: tail).Nodup ∧ ChainLinks left right h h tail

theorem ChainLinks.frame {n : ℕ} {left left' right right' : Fin n → ℕ} {first prev : Fin n}
    {xs : List (Fin n)} (hc : ChainLinks left right first prev xs)
    (hfirst : left' first = left first)
    (hprev : right' prev = right prev)
    (hxs : ∀ x ∈ xs, left' x = left x ∧ right' x = right x) :
    ChainLinks left' right' first prev xs := by
  induction xs generalizing prev with
  | nil =>
    simp only [ChainLinks] at hc ⊢
    exact ⟨hprev.trans hc.1, hfirst.trans hc.2⟩
  | cons x xs ih =>
    simp only [ChainLinks] at hc ⊢
    have hx := hxs x List.mem_cons_self
    refine ⟨hprev.trans hc.1, hx.1.trans hc.2.1,
      ih hc.2.2 hx.2 (fun y hy => hxs y (List.mem_cons_of_mem x hy))⟩

/-- `IsCircList` depends only on `left` and `right` at members of `L`. -/
theorem IsCircList.frame {n : ℕ} {left left' right right' : Fin n → ℕ} {L : List (Fin n)}
    (hL : IsCircList left right L)
    (heq : ∀ x ∈ L, left' x = left x ∧ right' x = right x) :
    IsCircList left' right' L := by
  cases L with
  | nil => trivial
  | cons h tail =>
    obtain ⟨hnodup, hc⟩ := hL
    have hh := heq h List.mem_cons_self
    exact ⟨hnodup, hc.frame hh.1 hh.2 (fun x hx => heq x (List.mem_cons_of_mem h hx))⟩

/-- Forming a singleton circular list `[u]`. -/
theorem IsCircList.singleton {n : ℕ} (left right : Fin n → ℕ) (u : Fin n) :
    IsCircList (Function.update left u u.val) (Function.update right u u.val) [u] := by
  simp only [IsCircList, ChainLinks, List.nodup_singleton, Function.update_self, and_self]

/-- In a non-empty circular list `h :: tail`, `right h` is the index of `(tail ++ [h])[0]`, hence
strictly less than `n` and a member of `h :: tail`. -/
theorem IsCircList.right_head {n : ℕ} {left right : Fin n → ℕ} {h : Fin n} {tail : List (Fin n)}
    (hL : IsCircList left right (h :: tail)) :
    ∃ r : Fin n, right h = r.val ∧ r ∈ h :: tail := by
  rcases tail with _ | ⟨a, _⟩
  · exact ⟨h, hL.2.1, List.mem_cons_self⟩
  · exact ⟨a, hL.2.1, List.mem_cons_of_mem h List.mem_cons_self⟩

/-- Inserting a fresh node `u ∉ h :: tail` immediately after `h` yields `h :: u :: tail`. -/
theorem IsCircList.insertAfter {n : ℕ} {left right : Fin n → ℕ} {h u : Fin n} {tail : List (Fin n)}
    (hL : IsCircList left right (h :: tail)) (hu : u ∉ h :: tail)
    {r : Fin n} (hr : right h = r.val) :
    let left₁ := Function.update (Function.update left u h.val) r u.val
    let right₁ := Function.update (Function.update right u r.val) h u.val
    IsCircList left₁ right₁ (h :: u :: tail) := by
  obtain ⟨hnodup, hc⟩ := hL
  have huh : u ≠ h := fun e => hu (e ▸ List.mem_cons_self)
  have hu_tail : u ∉ tail := fun m => hu (List.mem_cons_of_mem h m)
  have hnodup' : (h :: u :: tail).Nodup := by
    rw [List.nodup_cons] at hnodup ⊢
    refine ⟨?_, List.nodup_cons.mpr ⟨hu_tail, hnodup.2⟩⟩
    simp only [List.mem_cons, not_or]
    exact ⟨huh.symm, hnodup.1⟩
  rcases tail with _ | ⟨a, rest⟩
  · simp only [ChainLinks] at hc
    have hrh : r = h := Fin.ext (hr.symm.trans hc.1)
    subst hrh
    refine ⟨hnodup', ?_⟩
    simp only [ChainLinks, Function.update_self, Function.update_of_ne huh, and_self]
  · simp only [ChainLinks] at hc
    have hra : r = a := Fin.ext (hr.symm.trans hc.1)
    subst hra
    have hr_ne_h : r ≠ h := fun e => (List.nodup_cons.mp hnodup).1 (e ▸ List.mem_cons_self)
    have hu_ne_r : u ≠ r := fun e => hu_tail (e ▸ List.mem_cons_self)
    have hr_not_rest : r ∉ rest := (List.nodup_cons.mp (List.nodup_cons.mp hnodup).2).1
    have hh_not_rest : h ∉ rest := fun m =>
      (List.nodup_cons.mp hnodup).1 (List.mem_cons_of_mem r m)
    have hu_not_rest : u ∉ rest := fun m => hu_tail (List.mem_cons_of_mem r m)
    refine ⟨hnodup', ?_⟩
    dsimp only [ChainLinks]
    refine ⟨by simp [Function.update_self],
      by simp [Function.update_of_ne hu_ne_r, Function.update_self],
      by simp [Function.update_of_ne huh, Function.update_self],
      by simp [Function.update_self],
      hc.2.2.frame ?_ ?_ ?_⟩
    · simp only [Function.update_of_ne hr_ne_h.symm, Function.update_of_ne huh.symm]
    · simp only [Function.update_of_ne hr_ne_h, Function.update_of_ne hu_ne_r.symm]
    · intro x hx
      have hxr : x ≠ r := fun e => hr_not_rest (e ▸ hx)
      have hxu : x ≠ u := fun e => hu_not_rest (e ▸ hx)
      have hxh : x ≠ h := fun e => hh_not_rest (e ▸ hx)
      simp only [Function.update_of_ne hxr, Function.update_of_ne hxu, Function.update_of_ne hxh,
        and_self]

private theorem ChainLinks.snoc {n : ℕ} {left right : Fin n → ℕ} {h a prev : Fin n}
    {xs : List (Fin n)} (hc : ChainLinks left right h prev xs)
    (h1 : right h = a.val) (h2 : left a = h.val) :
    ChainLinks left right a prev (xs ++ [h]) := by
  induction xs generalizing prev with
  | nil =>
    simp only [ChainLinks, List.nil_append] at hc ⊢
    exact ⟨hc.1, hc.2, h1, h2⟩
  | cons x xs ih =>
    simp only [ChainLinks, List.cons_append] at hc ⊢
    exact ⟨hc.1, hc.2.1, ih hc.2.2⟩

/-- Rotating a circular list by one element preserves `IsCircList`. -/
theorem IsCircList.rotate_one {n : ℕ} {left right : Fin n → ℕ} {h : Fin n} {tail : List (Fin n)}
    (hL : IsCircList left right (h :: tail)) :
    IsCircList left right (tail ++ [h]) := by
  rcases tail with _ | ⟨a, rest⟩
  · simpa only [List.nil_append] using hL
  · obtain ⟨hnodup, hc⟩ := hL
    simp only [ChainLinks] at hc
    have hperm : (a :: (rest ++ [h])).Perm (h :: a :: rest) := by
      simpa only [List.cons_append] using List.perm_append_singleton h (a :: rest)
    exact ⟨hperm.nodup_iff.mpr hnodup, hc.2.2.snoc hc.1 hc.2.1⟩

/-- Splitting a circular list `L₁ ++ v :: L₂` rotates `v` to the front as `v :: (L₂ ++ L₁)`. -/
theorem IsCircList.rotate_to {n : ℕ} {left right : Fin n → ℕ} {L₁ L₂ : List (Fin n)} {v : Fin n}
    (hL : IsCircList left right (L₁ ++ v :: L₂)) :
    IsCircList left right (v :: (L₂ ++ L₁)) := by
  induction L₁ generalizing L₂ with
  | nil => simpa only [List.append_nil, List.nil_append] using hL
  | cons x xs ih =>
    have hrot : IsCircList left right ((xs ++ v :: L₂) ++ [x]) := hL.rotate_one
    have heq : (xs ++ v :: L₂) ++ [x] = xs ++ v :: (L₂ ++ [x]) := by simp
    rw [heq] at hrot
    have hih := ih hrot
    simpa only [List.append_assoc, List.singleton_append] using hih

/-- Any member `v ∈ L` of a circular list can be rotated to the head while preserving `Perm`. -/
theorem IsCircList.exists_head {n : ℕ} {left right : Fin n → ℕ} {L : List (Fin n)} {v : Fin n}
    (hL : IsCircList left right L) (hv : v ∈ L) :
    ∃ tail, IsCircList left right (v :: tail) ∧ (v :: tail).Perm L := by
  obtain ⟨L₁, L₂, rfl⟩ := List.append_of_mem hv
  refine ⟨L₂ ++ L₁, hL.rotate_to, ?_⟩
  have h1 : (v :: (L₂ ++ L₁)).Perm ((v :: L₂) ++ L₁) := List.Perm.refl _
  exact h1.trans List.perm_append_comm

private theorem ChainLinks.end_eq {n : ℕ} {left right : Fin n → ℕ} {first : Fin n} :
    ∀ (u : Fin n) (us : List (Fin n)) (hne : u :: us ≠ []),
      ChainLinks left right first u us →
      right ((u :: us).getLast hne) = first.val ∧ left first = ((u :: us).getLast hne).val
  | u, [], _, hc => hc
  | u, w :: ws, hne, hc => by
    rw [List.getLast_cons (List.cons_ne_nil w ws)]
    exact ChainLinks.end_eq w ws (List.cons_ne_nil w ws) hc.2.2

private theorem ChainLinks.reclose {n : ℕ} {left right : Fin n → ℕ} {first target : Fin n} :
    ∀ (u : Fin n) (us : List (Fin n)) (hne : u :: us ≠ []),
      (u :: us).Nodup →
      u ≠ target → (∀ z ∈ us, z ≠ target) →
      ChainLinks left right first u us →
      ChainLinks (Function.update left target ((u :: us).getLast hne).val)
        (Function.update right ((u :: us).getLast hne) target.val) target u us
  | u, [], _, _, _, _, _ => by
    simp only [List.getLast_singleton, ChainLinks, Function.update_self, and_self]
  | u, w :: ws, hne, hnd, _, hz_ne, hc => by
    have hw_ne : w ≠ target := hz_ne w List.mem_cons_self
    have hu_not : u ∉ w :: ws := (List.nodup_cons.mp hnd).1
    have hlast : (u :: w :: ws).getLast hne = (w :: ws).getLast (List.cons_ne_nil w ws) :=
      List.getLast_cons (List.cons_ne_nil w ws)
    rw [hlast]
    have hu_ne_last : u ≠ (w :: ws).getLast (List.cons_ne_nil w ws) := fun e =>
      hu_not (e ▸ List.getLast_mem (List.cons_ne_nil w ws))
    simp only [ChainLinks, Function.update_of_ne hu_ne_last, Function.update_of_ne hw_ne]
    exact ⟨hc.1, hc.2.1, ChainLinks.reclose w ws (List.cons_ne_nil w ws)
      (List.nodup_cons.mp hnd).2 hw_ne (fun z hz => hz_ne z (List.mem_cons_of_mem w hz)) hc.2.2⟩

/-- Removing `v` from a circular list `L` of length `≥ 2` (`v ∈ L`) by setting
`right[left[v]] ← right[v]` and `left[right[v]] ← left[v]` produces a circular list starting at
`r` (`right v = r.val`) that is a permutation of `L.erase v`. -/
theorem IsCircList.remove {n : ℕ} {left right : Fin n → ℕ} {L : List (Fin n)} {v : Fin n}
    (hL : IsCircList left right L) (hv : v ∈ L) (hlen : 2 ≤ L.length) :
    ∃ (r l : Fin n) (rest : List (Fin n)),
      right v = r.val ∧ left v = l.val ∧
      r ∈ L ∧ l ∈ L ∧ r ≠ v ∧
      IsCircList (Function.update left r l.val) (Function.update right l r.val) (r :: rest) ∧
      (r :: rest).Perm (L.erase v) := by
  obtain ⟨tail, hrot, hperm⟩ := hL.exists_head hv
  have htlen : 1 ≤ tail.length := by
    have := hperm.length_eq
    simp only [List.length_cons] at this
    omega
  rcases tail with _ | ⟨r, rest⟩
  · simp at htlen
  obtain ⟨hnodup, hc⟩ := hrot
  simp only [ChainLinks] at hc
  have hne_rr : r :: rest ≠ [] := List.cons_ne_nil r rest
  let l := (r :: rest).getLast hne_rr
  have hend := ChainLinks.end_eq r rest hne_rr hc.2.2
  have hnd_tail : (r :: rest).Nodup := (List.nodup_cons.mp hnodup).2
  have hv_not_tail : v ∉ r :: rest := (List.nodup_cons.mp hnodup).1
  have hr_ne_v : r ≠ v := fun e => hv_not_tail (e ▸ List.mem_cons_self)
  have hl_mem_rr : l ∈ r :: rest := List.getLast_mem hne_rr
  have hr_mem : r ∈ L := hperm.subset (List.mem_cons_of_mem v List.mem_cons_self)
  have hl_mem_L : l ∈ L := hperm.subset (List.mem_cons_of_mem v hl_mem_rr)
  have hperm_erase : (r :: rest).Perm (L.erase v) := by
    have := hperm.erase v
    simpa only [List.erase_cons_head] using this
  have hreclose : ChainLinks (Function.update left r l.val) (Function.update right l r.val)
      r r rest := by
    rcases rest with _ | ⟨x, xs⟩
    · simp only [l, List.getLast_singleton, ChainLinks, Function.update_self, and_self]
    · have hne_xxs : x :: xs ≠ [] := List.cons_ne_nil x xs
      have hlast_eq : l = (x :: xs).getLast hne_xxs := List.getLast_cons hne_xxs
      have hr_not_xxs : r ∉ x :: xs := (List.nodup_cons.mp hnd_tail).1
      have hr_ne_l : r ≠ l := fun e => hr_not_xxs (e ▸ hlast_eq ▸ List.getLast_mem hne_xxs)
      have hx_ne_r : x ≠ r := fun e => hr_not_xxs (e ▸ List.mem_cons_self)
      simp only [ChainLinks] at hc ⊢
      rw [Function.update_of_ne hr_ne_l, Function.update_of_ne hx_ne_r]
      refine ⟨hc.2.2.1, hc.2.2.2.1, ?_⟩
      rw [hlast_eq]
      exact ChainLinks.reclose x xs hne_xxs (List.nodup_cons.mp hnd_tail).2 hx_ne_r
        (fun z hz e => hr_not_xxs (e ▸ List.mem_cons_of_mem x hz)) hc.2.2.2.2
  exact ⟨r, l, rest, hc.1, hend.2, hr_mem, hl_mem_L, hr_ne_v, ⟨hnd_tail, hreclose⟩, hperm_erase⟩

/-! ## Pure-`ℕ` Fibonacci rank and degree bounds -/

/-- Fundamental Fibonacci rank identity (used in the proof of
[Fredman and Tarjan][FredmanTarjan1987], Corollary 1, p. 604; [Cormen et al.][CLRS2009],
Lemma 19.2): `1 + ∑_{i < k} fib ((i - 1) + 2) = fib (k + 2)` in `ℕ` (where `0 - 1 = 0`). -/
theorem fib_sum_pred_add_two (k : ℕ) :
    1 + ∑ i ∈ Finset.range k, Nat.fib ((i - 1) + 2) = Nat.fib (k + 2) := by
  induction k with
  | zero => decide
  | succ m ih =>
    rcases m with _ | m
    · decide
    · rw [Finset.sum_range_succ, ← Nat.add_assoc, ih]
      have hsub : (m + 1 - 1) + 2 = m + 2 := by omega
      have h1 : m + 1 + 2 = (m + 2) + 1 := by omega
      have h2 : m + 1 + 1 + 2 = (m + 2) + 2 := by omega
      have hfib : Nat.fib ((m + 2) + 2) = Nat.fib (m + 2) + Nat.fib ((m + 2) + 1) :=
        Nat.fib_add_two
      rw [hsub, h1, h2, hfib]
      exact Nat.add_comm _ _

/-- Exponential lower bound on even-index Fibonacci numbers without golden-ratio reals:
`2 ^ m ≤ fib (2 * m + 2)` for all `m : ℕ`. -/
theorem two_pow_le_fib (m : ℕ) : 2 ^ m ≤ Nat.fib (2 * m + 2) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have hstep : 2 * (m + 1) + 2 = (2 * m + 2) + 2 := by omega
    rw [hstep, Nat.fib_add_two, Nat.pow_succ]
    have hmono : Nat.fib (2 * m + 2) ≤ Nat.fib (2 * m + 2 + 1) := Nat.fib_mono (by omega)
    omega

/-- Any node degree `d` satisfying `Nat.fib (d + 2) ≤ n` obeys the pure-`ℕ` logarithmic upper bound
`d ≤ 2 * Nat.log 2 n + 1`. -/
theorem deg_le_two_mul_log_add_one {d n : ℕ} (hfib : Nat.fib (d + 2) ≤ n) :
    d ≤ 2 * Nat.log 2 n + 1 := by
  have h1 : 2 * (d / 2) + 2 ≤ d + 2 := by omega
  have hpow : 2 ^ (d / 2) ≤ n :=
    (two_pow_le_fib (d / 2)).trans ((Nat.fib_mono h1).trans hfib)
  have hlog : d / 2 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by omega) hpow
  omega

end Cslib.Algorithms.WordRAM.PriorityQueue.FibonacciHeap
