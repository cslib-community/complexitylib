/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Loops in the time monad

Return values and costs of two loop combinators run in `Cslib.Algorithms.Lean.TimeM`:
`Vector.ofFnM`, which fills a vector cell by cell, and `List.foldlM`. The return value of either
loop is the corresponding pure loop over the return values. The cost of `Vector.ofFnM` is the sum
of the cell costs, and a `List.foldlM` whose step always costs `c` costs `c` per element; more
generally, if the cost of a step depends only on the element, the fold costs the sum of the element
costs.

## Main results

* `Cslib.Algorithms.Lean.TimeM.ret_vectorOfFnM`, `time_vectorOfFnM`.
* `Cslib.Algorithms.Lean.TimeM.ret_foldlM`, `time_foldlM_of_time_eq`, `time_foldlM_eq_sum`.
-/

public section

namespace Cslib.Algorithms.Lean.TimeM

/-- The vector filled by `Vector.ofFnM` in the time monad is the vector of the return values. -/
@[simp] theorem ret_vectorOfFnM {α : Type*} : ∀ {n : ℕ} (f : Fin n → TimeM ℕ α),
    (Vector.ofFnM f).ret = Vector.ofFn fun i => (f i).ret
  | 0, f => by
    rw [Vector.ofFnM_zero]
    ext i hi
    exact absurd hi (Nat.not_lt_zero i)
  | n + 1, f => by
    rw [Vector.ofFnM_succ]
    simp only [ret_bind, ret_pure]
    rw [ret_vectorOfFnM]
    ext i hi
    rw [Vector.getElem_push, Vector.getElem_ofFn]
    split_ifs with h
    · rw [Vector.getElem_ofFn]
      rfl
    · have : i = n := by omega
      subst this
      rfl

/-- Filling a vector by `Vector.ofFnM` costs the sum of the costs of its cells. -/
@[simp] theorem time_vectorOfFnM {α : Type*} : ∀ {n : ℕ} (f : Fin n → TimeM ℕ α),
    (Vector.ofFnM f).time = ∑ i, (f i).time
  | 0, f => by
    rw [Vector.ofFnM_zero]
    rfl
  | n + 1, f => by
    rw [Vector.ofFnM_succ]
    simp only [time_bind, time_pure, add_zero]
    rw [time_vectorOfFnM, Fin.sum_univ_castSucc]

/-- A fold in the time monad returns the pure fold of the return values. -/
@[simp] theorem ret_foldlM {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α) (b : β) :
    (l.foldlM f b).ret = l.foldl (fun acc a => (f acc a).ret) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldlM_cons, ret_bind, ih]
    rfl

/-- A fold in the time monad whose step always costs `c` costs `c` per element. -/
theorem time_foldlM_of_time_eq {α β : Type*} (f : β → α → TimeM ℕ β) (l : List α) (b : β)
    {c : ℕ} (hf : ∀ acc a, (f acc a).time = c) : (l.foldlM f b).time = l.length * c := by
  induction l generalizing b with
  | nil => simp only [List.foldlM_nil, time_pure, List.length_nil, zero_mul]
  | cons a l ih =>
    rw [List.foldlM_cons, time_bind, ih, hf, List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- A fold in the time monad whose step cost depends only on the element costs the sum of those
costs. -/
theorem time_foldlM_eq_sum {α β : Type*} (f : β → α → TimeM ℕ β) (c : α → ℕ)
    (hf : ∀ acc a, (f acc a).time = c a) (l : List α) (b : β) :
    (l.foldlM f b).time = (l.map c).sum := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => rw [List.foldlM_cons, time_bind, ih, hf, List.map_cons, List.sum_cons]

end Cslib.Algorithms.Lean.TimeM
