/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Basic

/-!
# List fold invariants and selection

## Main results

* `List.foldl_take_invariant`: an index-dependent invariant holds after every prefix of a fold.
* `List.foldl_keep_fst`: folding a step that keeps the first component of a pair preserves that
  component and folds over the second.
* `List.foldr_ite_eq_of_mem`: a chain of equality tests selects the branch of a contained tag,
  regardless of duplicates or fallback. Used by finite-control certificates.

## References

Adapts the selection identity from Computability/Probabilistic/Finite.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

/-- An invariant depending on the number of consumed elements holds after every bounded prefix
fold if it holds initially and is preserved by the next list element. Unlike `List.foldlRecOn`,
preservation may depend on the position. This is a semantic rule with no resource assumptions. -/
theorem List.foldl_take_invariant {α β : Type*} (l : List α) (step : β → α → β) (init : β)
    (P : ℕ → β → Prop) (hbase : P 0 init)
    (hstep : ∀ i (hi : i < l.length) state, P i state → P (i + 1) (step state l[i])) :
    ∀ i, i ≤ l.length → P i ((l.take i).foldl step init) := by
  intro i
  induction i with
  | zero => intro _; simpa only [List.take_zero, List.foldl_nil] using hbase
  | succ i ih =>
    intro hi
    have hlt : i < l.length := Nat.lt_of_succ_le hi
    simpa only [List.take_succ_eq_append_getElem hlt, List.foldl_append,
      List.foldl_cons, List.foldl_nil] using hstep i hlt _ (ih (Nat.le_of_lt hlt))

/-- Folding a step that keeps the first component of a pair preserves that component and folds
over the second. -/
theorem List.foldl_keep_fst {ι π α : Type*} (step : π → α → ι → α)
    (par : π) (xs : List ι) (init : α) :
    xs.foldl (fun pa i => (pa.1, step pa.1 pa.2 i)) (par, init) =
      (par, xs.foldl (step par) init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons _ _ ih => exact ih _

/-- A chain of equality tests selects a contained tag, regardless of duplicates or fallback. -/
theorem List.foldr_ite_eq_of_mem {Tag Value : Type*} [DecidableEq Tag]
    (tags : List Tag) (tag : Tag) (branch : Tag → Value) (fallback : Value) (h : tag ∈ tags) :
    tags.foldr (fun candidate rest => if tag = candidate then branch candidate else rest)
      fallback = branch tag := by
  induction tags with
  | nil => simp at h
  | cons candidate tags ih =>
    by_cases heq : tag = candidate
    · simp [heq]
    · simp only [List.foldr_cons, heq, ↓reduceIte]
      exact ih (List.mem_cons.mp h |>.resolve_left heq)
