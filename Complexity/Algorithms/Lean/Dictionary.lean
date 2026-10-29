/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Semantics.Stateful.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Bounded-capacity dictionary specification

This file defines a deterministic abstract specification
(`Cslib.Algorithms.Lean.Dictionary.spec`) for a bounded-capacity dictionary mapping keys from a
finite universe `Fin U` to natural-number values bounded by `V`, supporting at most `n_max`
distinct stored keys at any point in time.

States map each key `u : Fin U` to `Option ℕ` (`none` when absent, `some v` when present with
value `v`). Following `Cslib.Algorithms.Lean.IndexedMinPQ`, values are represented as `ℕ` with the
bound `v < V` enforced by operation admissibility (`valid`), so Word-RAM realizations can encode
`Option ℕ` in a single machine register (`0` for `none` and `v + 1` for `some v`) without carrying
dependent `Fin V` proof obligations inside register decoding.

An insertion `insert u v` is admissible whenever `v < V` and either the current number of stored
keys `(dom s).card` is strictly below the capacity bound `n_max`, or `u` is already present in `s`
(in which case updating `s u` to `some v` overwrites the existing value in place without increasing
`(dom s).card`). This specification models lookup-and-insert dictionaries without a deletion
operation.

## Main definitions

* `Cslib.Algorithms.Lean.Dictionary.Op`: dictionary operations (`get`, `insert`).
* `Cslib.Algorithms.Lean.Dictionary.State`, `empty`, `dom`: abstract map state, empty dictionary,
  and finite set of present keys.
* `Cslib.Algorithms.Lean.Dictionary.ValuesBounded`: invariant that all stored values lie below `V`.
* `Cslib.Algorithms.Lean.Dictionary.spec`: the `Cslib.Stateful.Spec` with universe `U`, value bound
  `V`, and capacity bound `n_max`.

## Main results

* `dom_empty`, `card_dom_empty`, `dom_insert`: domain evolution under initialization and insertion.
* `card_dom_insert_le`, `card_dom_insert_eq_of_isSome`, `card_dom_insert_eq_of_eq_none`:
  cardinality laws for `dom` under in-place updates and new-key insertions.
* `card_dom_step_le_of_valid`, `card_dom_run_le_of_validHistory`, `card_dom_run_empty_le`:
  any admissible operation history starting from `empty U` maintains `(dom s).card ≤ n_max`.
* `valuesBounded_empty`, `valuesBounded_step_of_valid`, `valuesBounded_run_of_validHistory`:
  any admissible operation history maintains `ValuesBounded V s`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 11][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.Dictionary

/-- Lookup and insertion operations on a dictionary over keys `Fin U` and natural-number values. -/
inductive Op (U : ℕ) where
  /-- Look up the value associated with key `u`, if present. -/
  | get (u : Fin U)
  /-- Associate key `u` with value `v`, inserting `u` if absent or overwriting its value if
  present. -/
  | insert (u : Fin U) (v : ℕ)
  deriving DecidableEq, Repr

/-- Abstract state of a dictionary over universe `Fin U`. -/
abbrev State (U : ℕ) := Fin U → Option ℕ

/-- The empty dictionary on `Fin U`. -/
@[expose]
def empty (U : ℕ) : State U := fun _ => none

/-- The finite set of keys currently present in state `s`. -/
@[expose]
def dom {U : ℕ} (s : State U) : Finset (Fin U) :=
  Finset.univ.filter fun u => (s u).isSome

/-- Predicate asserting that every value stored in state `s` is strictly less than `V`. -/
@[expose]
def ValuesBounded {U : ℕ} (V : ℕ) (s : State U) : Prop :=
  ∀ u v, s u = some v → v < V

/-- Bounded-capacity dictionary specification over key universe `Fin U`, value bound `V`, and
maximum key count `n_max`. -/
@[expose]
def spec (U V n_max : ℕ) : Cslib.Stateful.Spec where
  State := State U
  Op := Op U
  Result
    | .get _ => Option ℕ
    | .insert _ _ => Unit
  step s
    | .get u => (s, s u)
    | .insert u v => (Function.update s u (some v), ())
  valid s
    | .get _ => True
    | .insert u v => ((dom s).card < n_max ∨ (s u).isSome) ∧ v < V

/-! ### Domain, capacity, and value-bound lemmas -/

/-- A key belongs to `dom s` if and only if `(s u).isSome`. -/
@[simp]
theorem mem_dom_iff_isSome {U : ℕ} {s : State U} {u : Fin U} :
    u ∈ dom s ↔ (s u).isSome := by
  simp [dom]

/-- A key belongs to `dom s` if and only if `s u = some v` for some value `v`. -/
theorem mem_dom_iff {U : ℕ} {s : State U} {u : Fin U} :
    u ∈ dom s ↔ ∃ v, s u = some v := by
  simp [dom, Option.isSome_iff_exists]

/-- A key is outside `dom s` if and only if `s u = none`. -/
theorem notMem_dom_iff {U : ℕ} {s : State U} {u : Fin U} :
    u ∉ dom s ↔ s u = none := by
  simp [dom]

/-- The empty dictionary has empty domain. -/
@[simp]
theorem dom_empty (U : ℕ) : dom (empty U) = ∅ := by
  ext u
  simp [dom, empty]

/-- The empty dictionary stores `0` keys. -/
theorem card_dom_empty (U : ℕ) : (dom (empty U)).card = 0 := by
  simp

/-- Updating `u` to `some v` inserts `u` into `dom s`. -/
@[simp]
theorem dom_insert {U : ℕ} (s : State U) (u : Fin U) (v : ℕ) :
    dom (Function.update s u (some v)) = insert u (dom s) := by
  ext x
  by_cases hxu : x = u
  · subst hxu; simp [dom]
  · simp [dom, hxu]

/-- Updating a key `u` already in `dom s` preserves `dom s`. -/
theorem dom_insert_of_mem {U : ℕ} {s : State U} {u : Fin U} (hu : u ∈ dom s) (v : ℕ) :
    dom (Function.update s u (some v)) = dom s := by
  rw [dom_insert, Finset.insert_eq_of_mem hu]

/-- Updating a key `u` with `(s u).isSome` preserves `dom s`. -/
theorem dom_insert_of_isSome {U : ℕ} {s : State U} {u : Fin U} (hu : (s u).isSome) (v : ℕ) :
    dom (Function.update s u (some v)) = dom s :=
  dom_insert_of_mem (mem_dom_iff_isSome.mpr hu) v

/-- Updating `u` to `some v` increases `(dom s).card` by at most `1`. -/
theorem card_dom_insert_le {U : ℕ} (s : State U) (u : Fin U) (v : ℕ) :
    (dom (Function.update s u (some v))).card ≤ (dom s).card + 1 := by
  rw [dom_insert]
  exact Finset.card_insert_le u (dom s)

/-- Updating a present key `u` (`(s u).isSome`) leaves `(dom s).card` unchanged. -/
theorem card_dom_insert_eq_of_isSome {U : ℕ} {s : State U} {u : Fin U}
    (hu : (s u).isSome) (v : ℕ) :
    (dom (Function.update s u (some v))).card = (dom s).card := by
  rw [dom_insert_of_isSome hu]

/-- Inserting an absent key `u` (`s u = none`) increases `(dom s).card` by `1`. -/
theorem card_dom_insert_eq_of_eq_none {U : ℕ} {s : State U} {u : Fin U}
    (hu : s u = none) (v : ℕ) :
    (dom (Function.update s u (some v))).card = (dom s).card + 1 := by
  rw [dom_insert, Finset.card_insert_of_notMem (notMem_dom_iff.mpr hu)]

/-- Any single admissible dictionary operation preserves the capacity bound
`(dom s).card ≤ n_max`. -/
theorem card_dom_step_le_of_valid {U V n_max : ℕ} {s : State U} {o : Op U}
    (hs : (dom s).card ≤ n_max) (hval : (spec U V n_max).valid s o) :
    (dom ((spec U V n_max).step s o).1).card ≤ n_max := by
  cases o with
  | get u => exact hs
  | insert u v =>
    rcases hval.1 with hlt | hisSome
    · have hle := card_dom_insert_le s u v
      dsimp only [spec]
      omega
    · dsimp only [spec]
      rw [card_dom_insert_eq_of_isSome hisSome]
      exact hs

/-- Any admissible operation history preserves `(dom s).card ≤ n_max`. -/
theorem card_dom_run_le_of_validHistory {U V n_max : ℕ} {s : State U} {os : List (Op U)}
    (hs : (dom s).card ≤ n_max) (hvh : (spec U V n_max).ValidHistory s os) :
    (dom ((spec U V n_max).run s os).1).card ≤ n_max := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    exact ih (card_dom_step_le_of_valid hs hvh.1) hvh.2

/-- Any admissible operation history starting from `empty U` reaches a state with at most `n_max`
keys. -/
theorem card_dom_run_empty_le {U V n_max : ℕ} {os : List (Op U)}
    (hvh : (spec U V n_max).ValidHistory (empty U) os) :
    (dom ((spec U V n_max).run (empty U) os).1).card ≤ n_max :=
  card_dom_run_le_of_validHistory (by simp) hvh

/-- The empty dictionary satisfies `ValuesBounded V`. -/
theorem valuesBounded_empty (U V : ℕ) : ValuesBounded V (empty U) := by
  intro u v h
  simp [empty] at h

/-- Any single admissible dictionary operation preserves `ValuesBounded V`. -/
theorem valuesBounded_step_of_valid {U V n_max : ℕ} {s : State U} {o : Op U}
    (hs : ValuesBounded V s) (hval : (spec U V n_max).valid s o) :
    ValuesBounded V ((spec U V n_max).step s o).1 := by
  cases o with
  | get u => exact hs
  | insert u v =>
    intro x w hxw
    dsimp only [spec] at hxw
    by_cases hxu : x = u
    · subst hxu
      rw [Function.update_self] at hxw
      injection hxw with hvw
      subst hvw
      exact hval.2
    · rw [Function.update_of_ne hxu] at hxw
      exact hs x w hxw

/-- Any admissible operation history preserves `ValuesBounded V`. -/
theorem valuesBounded_run_of_validHistory {U V n_max : ℕ} {s : State U} {os : List (Op U)}
    (hs : ValuesBounded V s) (hvh : (spec U V n_max).ValidHistory s os) :
    ValuesBounded V ((spec U V n_max).run s os).1 := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    exact ih (valuesBounded_step_of_valid hs hvh.1) hvh.2

end Cslib.Algorithms.Lean.Dictionary
