/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Chain
import Mathlib.Data.List.Range

/-!
# Lists of blocks indexed by a natural-number range

Facts about `(List.range n).flatMap f` and `(List.range n).reverse.flatMap f`: the list of
blocks `f 0, …, f (n - 1)`, in increasing or decreasing order.

## Main results

* `List.isChain_flatMap_range`, `List.isChain_flatMap_reverse_range`: nonempty chained blocks,
  each linked to the next one, form a chain.
* `List.head?_flatMap_range`, `List.getLast?_flatMap_range`,
  `List.head?_flatMap_reverse_range`, `List.getLast?_flatMap_reverse_range`: the first and last
  entries come from the first and last nonempty end blocks.
-/

public section

namespace List

variable {α : Type*} {R : α → α → Prop} {f : ℕ → List α} {n : ℕ}

/-- Nonempty chains indexed by `0, …, n - 1`, each linked to the next, form a chain. -/
theorem isChain_flatMap_range (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f a).getLast?, ∀ y ∈ (f (a + 1)).head?, R x y) :
    ((range n).flatMap f).IsChain R := by
  rw [flatMap_def, isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mem_map.1 hl
    exact hblock a (mem_range.1 ha)
  · rw [isChain_map, isChain_range]
    exact fun a ha => hlink a (by omega)

/-- Nonempty chains indexed by `n - 1, …, 0`, each linked to the previous, form a chain. -/
theorem isChain_flatMap_reverse_range (hne : ∀ a < n, f a ≠ [])
    (hblock : ∀ a < n, (f a).IsChain R)
    (hlink : ∀ a, a + 1 < n → ∀ x ∈ (f (a + 1)).getLast?, ∀ y ∈ (f a).head?, R x y) :
    ((range n).reverse.flatMap f).IsChain R := by
  rw [flatMap_def, isChain_flatten (by simpa using hne)]
  refine ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := mem_map.1 hl
    exact hblock a (mem_range.1 (mem_reverse.1 ha))
  · rw [isChain_map, isChain_reverse, isChain_range]
    exact fun a ha => hlink a (by omega)

/-- With a nonempty first block, the blocks in increasing order start with its head. -/
theorem head?_flatMap_range (hn : 0 < n) (h : f 0 ≠ []) :
    ((range n).flatMap f).head? = (f 0).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, range_succ_eq_map, flatMap_cons, head?_append_of_ne_nil _ h]

/-- With a nonempty last block, the blocks in increasing order end with its last entry. -/
theorem getLast?_flatMap_range (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((range n).flatMap f).getLast? = (f (n - 1)).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [range_succ, flatMap_append, flatMap_singleton, getLast?_append_of_ne_nil _ h]

/-- With a nonempty block `n - 1`, the blocks in decreasing order start with its head. -/
theorem head?_flatMap_reverse_range (hn : 0 < n) (h : f (n - 1) ≠ []) :
    ((range n).reverse.flatMap f).head? = (f (n - 1)).head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, Nat.add_sub_cancel] at h ⊢
  rw [range_succ, reverse_append, reverse_singleton, singleton_append, flatMap_cons,
    head?_append_of_ne_nil _ h]

/-- With a nonempty block `0`, the blocks in decreasing order end with its last entry. -/
theorem getLast?_flatMap_reverse_range (hn : 0 < n) (h : f 0 ≠ []) :
    ((range n).reverse.flatMap f).getLast? = (f 0).getLast? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [Nat.zero_add, range_succ_eq_map, reverse_cons, flatMap_append, flatMap_singleton,
    getLast?_append_of_ne_nil _ h]

end List
