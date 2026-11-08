/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Batteries.Data.List.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.Fin.Fold

/-!
# Indexed left folds

`l.foldlIdx f init start` folds `f` over the list `l` from the left, passing the index of each
element plus `start`. Read as an automaton, it is the run of the time-dependent transition function
`f : ℕ → S → X → S` on the letters of `l`, started at time `start` in the state `init`. This file
adds the lemmas for splitting such runs to the basic `List.foldlIdx` API of Batteries.

## Main results

* `List.foldlIdx_append`: folding over `l₁ ++ l₂` continues from the end of the fold over `l₁`.
* `List.foldlIdx_map`: folding over a mapped list precomposes the map.
* `List.foldlIdx_flatten`: folding over a concatenation of blocks of length `n` folds the blocks.
* `List.foldlIdx_ofFn`: folding over the list of a tuple is `Fin.foldl` with shifted indices.
-/

public section

namespace List

variable {α β γ : Type*}

/-- **Splitting an indexed fold**: the fold over `l₁ ++ l₂` is the fold over `l₂`, started at the
index and value where the fold over `l₁` ends. -/
theorem foldlIdx_append (f : ℕ → α → β → α) (init : α) (l₁ l₂ : List β) (start : ℕ) :
    (l₁ ++ l₂).foldlIdx f init start =
      l₂.foldlIdx f (l₁.foldlIdx f init start) (start + l₁.length) := by
  induction l₁ generalizing init start with
  | nil => rfl
  | cons a l ih =>
    rw [cons_append, foldlIdx_cons, ih, foldlIdx_cons, length_cons, Nat.add_assoc,
      Nat.add_comm 1]

/-- An indexed fold over a mapped list is the fold of the function precomposed with the map. -/
theorem foldlIdx_map (f : ℕ → α → β → α) (g : γ → β) (init : α) (l : List γ) (start : ℕ) :
    (l.map g).foldlIdx f init start = l.foldlIdx (fun i a c => f i a (g c)) init start := by
  induction l generalizing init start with
  | nil => rfl
  | cons c l ih => exact ih _ _

/-- **Indexed folds over blocks**: if every block of `L` has length `n`, the fold over the
concatenated blocks is the fold over the list of blocks that folds a whole block at each index,
the `i`-th block from index `n * i` on. -/
theorem foldlIdx_flatten (f : ℕ → α → β → α) {n : ℕ} (L : List (List β))
    (hL : ∀ l ∈ L, l.length = n) (init : α) (start : ℕ) :
    L.flatten.foldlIdx f init (n * start) =
      L.foldlIdx (fun i a l => l.foldlIdx f a (n * i)) init start := by
  induction L generalizing init start with
  | nil => rfl
  | cons l L ih =>
    rw [flatten_cons, foldlIdx_append, hL l mem_cons_self, foldlIdx_cons, ← Nat.mul_succ,
      ih (fun l' hl' => hL l' (mem_cons_of_mem _ hl'))]

/-- An indexed fold over the list of a tuple is a fold over its positions, with the indices
shifted by `start`. -/
theorem foldlIdx_ofFn (f : ℕ → α → β → α) (init : α) {m : ℕ} (x : Fin m → β) (start : ℕ) :
    (ofFn x).foldlIdx f init start = Fin.foldl m (fun a i => f (start + i) a (x i)) init := by
  induction m generalizing init start with
  | zero => rfl
  | succ m ih =>
    rw [Fin.foldl_succ, ofFn_succ, foldlIdx_cons, ih]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_assoc, Nat.add_comm 1]

end List
