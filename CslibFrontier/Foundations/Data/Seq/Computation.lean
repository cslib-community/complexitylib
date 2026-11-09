/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, addition to `Data/Seq/Computation.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Seq.Computation

/-!
# Running a computation for a bounded number of steps

`Computation.runFor s n` is the result of the computation `s` after `n` steps, or `none` if `s` has
not terminated by then. Once `s` has terminated it keeps its result, so `a ∈ s.runFor n` exactly
when `s` terminates with result `a` within `n` steps (`Computation.mem_runFor_iff_exists_results`).
The steps add up along `bind` (`Computation.mem_runFor_bind`), and `map` takes no steps of its own
(`Computation.runFor_map`).

## Main results

* `Computation.mem_runFor_of_le`: a result available after `m` steps is available after `n ≥ m`
  steps.
* `Computation.mem_iff_exists_mem_runFor`, `Computation.mem_runFor_iff_exists_results`: results
  of a computation and their times.
* `Computation.runFor_map`, `Computation.mem_runFor_bind`: `map` and `bind` against the clock.
-/

@[expose] public section

namespace Computation

variable {α β : Type*} {s : Computation α} {f : α → Computation β} {a a' : α} {b : β} {m n : ℕ}

/-- A pure computation has its result after any number of steps. -/
@[simp]
theorem runFor_pure (a : α) (n : ℕ) : (pure a).runFor n = some a :=
  rfl

/-- The nonterminating computation has no result after any number of steps. -/
@[simp]
theorem runFor_empty (n : ℕ) : (empty α).runFor n = none :=
  rfl

/-- A result available after `m` steps is available after `n ≥ m` steps. -/
theorem mem_runFor_of_le (h : m ≤ n) (ha : a ∈ s.runFor m) : a ∈ s.runFor n :=
  s.le_stable h ha

/-- A result available after `n` steps is a result of the computation. -/
theorem mem_of_mem_runFor (h : a ∈ s.runFor n) : a ∈ s :=
  ⟨n, h.symm⟩

/-- `a` is a result of `s` exactly when it is available after some number of steps. -/
theorem mem_iff_exists_mem_runFor : a ∈ s ↔ ∃ n, a ∈ s.runFor n :=
  ⟨fun ⟨n, h⟩ => ⟨n, h.symm⟩, fun ⟨_, h⟩ => mem_of_mem_runFor h⟩

/-- Two results of the same computation, at any two times, are equal. -/
theorem eq_of_mem_runFor (h : a ∈ s.runFor m) (h' : a' ∈ s.runFor n) : a = a' :=
  mem_unique (mem_of_mem_runFor h) (mem_of_mem_runFor h')

/-- A computation terminating after exactly `n` steps has its result after `n` steps. -/
theorem Results.mem_runFor (h : s.Results a n) : a ∈ s.runFor n := by
  obtain ⟨hmem, rfl⟩ := h
  have : Terminates s := terminates_of_mem hmem
  have hget : get s ∈ s.runFor s.length :=
    Option.eq_some_of_isSome (Nat.find_spec ((terminates_def s).1 this))
  exact get_eq_of_mem s hmem ▸ hget

/-- A computation has the result `a` after `n` steps exactly when it terminates with result `a`
after at most `n` steps. -/
theorem mem_runFor_iff_exists_results : a ∈ s.runFor n ↔ ∃ m ≤ n, s.Results a m := by
  refine ⟨fun h => ?_, fun ⟨_, hm, h⟩ => mem_runFor_of_le hm h.mem_runFor⟩
  have hmem := mem_of_mem_runFor h
  have : Terminates s := terminates_of_mem hmem
  refine ⟨s.length, Nat.find_min' _ ?_, results_of_terminates' s hmem⟩
  change (s.runFor n).isSome
  rw [Option.mem_def.mp h]
  rfl

/-- For a computation terminating after exactly `m` steps with result `a`, the result after `n`
steps is `a` exactly when `m ≤ n`. -/
theorem Results.mem_runFor_iff (h : s.Results a m) : a' ∈ s.runFor n ↔ a' = a ∧ m ≤ n := by
  rw [mem_runFor_iff_exists_results]
  refine ⟨fun ⟨k, hk, h'⟩ => ⟨h'.val_unique h, h.len_unique h' ▸ hk⟩, ?_⟩
  rintro ⟨rfl, hm⟩
  exact ⟨m, hm, h⟩

/-- `map` takes no steps of its own. -/
@[simp]
theorem runFor_map (f : α → β) (s : Computation α) (n : ℕ) :
    (s.map f).runFor n = (s.runFor n).map f := by
  obtain ⟨s, hs⟩ := s
  change Option.casesOn (s n) none (some ∘ f) = Option.map f (s n)
  cases s n <;> rfl

/-- If `a` is available from `s` after `n` steps, then `f a` is available from `s.map f` after `n`
steps. -/
theorem mem_runFor_map (f : α → β) (h : a ∈ s.runFor n) : f a ∈ (s.map f).runFor n := by
  rw [runFor_map, Option.mem_def.mp h]
  rfl

/-- The steps of a computation and of its continuation add up along `bind`. -/
theorem mem_runFor_bind (ha : a ∈ s.runFor m) (hb : b ∈ (f a).runFor n) :
    b ∈ (s.bind f).runFor (m + n) := by
  obtain ⟨m', hm', ha⟩ := mem_runFor_iff_exists_results.mp ha
  obtain ⟨n', hn', hb⟩ := mem_runFor_iff_exists_results.mp hb
  exact mem_runFor_of_le (by omega) (results_bind ha hb).mem_runFor

end Computation
