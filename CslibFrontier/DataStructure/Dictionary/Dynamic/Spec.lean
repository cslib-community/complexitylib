/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Spec
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log

/-!
# Dynamic dictionary specification with deletions and succinct space bounds

This file defines a deterministic abstract specification
(`Cslib.DataStructure.Dictionary.Dynamic.spec`)
for a bounded-capacity dynamic dictionary mapping keys from a finite universe `Fin U` to
natural-number values bounded by `V`, supporting `query`, `insert` (with in-place value overwrite),
and `delete`, with at most `n_max` distinct keys present at any point in time.

Unlike the insert-only interface `Cslib.DataStructure.Dictionary.spec` (which provides `query` and
`insert`), `Cslib.DataStructure.Dictionary.Dynamic.Op` includes key deletion (`delete u`, removing
`u` if present and acting as a no-op if absent) while sharing the underlying state representation
`Dictionary.State U = Fin U → Option ℕ`, empty state `Dictionary.empty U`, active key set
`Dictionary.dom`, and value-bound invariant `Dictionary.ValuesBounded`. When `U ≤ n_max`, the
capacity condition `(dom s).card < n_max ∨ (s u).isSome` holds automatically for every state `s`
and key `u`, so `spec U V n_max` also covers unbounded-capacity dynamic dictionaries over `Fin U`
(`valid_insert_iff_of_le`).

This file also defines the information-theoretic bit bound
`optBits U V n = ⌈log₂ C(U, n)⌉ + n * ⌈log₂ V⌉` for `n` keys. When `0 < V` and `n ≤ U`,
`optBits U V n` equals the exact minimum `⌈log₂ (C(U, n) * V^n)⌉` when `V` is a power of two and
exceeds it by at most `n` bits otherwise. When `n > U`, `C(U, n) = 0`; when `V = 0`, there are no
valued non-empty dictionaries. From `optBits`, `succinctWords C C₀ U V w n_max` defines the word
bound `⌈(optBits U V n_max + C * n_max * ⌈log₂ ⌈log₂ (max n_max 4)⌉⌉) / w⌉ + C₀` on the `w`-bit
Word RAM.

## Main definitions

* `Cslib.DataStructure.Dictionary.Dynamic.Op`: dynamic dictionary operations (`query`, `insert`,
  `delete`).
* `Cslib.DataStructure.Dictionary.Dynamic.step`, `valid`, `spec`: pure transition function,
  admissibility predicate, and `StateTransitionSpec` for bounded-capacity dynamic dictionaries.
* `Cslib.DataStructure.Dictionary.Dynamic.optBits`, `logLogFactor`, `succinctWords`:
  information-theoretic bit bound and succinct Word-RAM space bound.

## Main results

* `dom_delete`, `dom_delete_of_notMem`, `dom_delete_of_eq_none`, `card_dom_delete_le`,
  `card_dom_delete_eq_of_isSome`, `card_dom_delete_eq_of_eq_none`: domain and cardinality laws
  under key deletion.
* `card_dom_le_univ`, `valid_insert_iff_of_le`: every state has at most `U` present keys, so any
  capacity bound `n_max ≥ U` imposes no capacity restriction on insertions.
* `card_dom_step_le_of_valid`, `card_dom_run_le_of_validHistory`, `card_dom_run_empty_le`: any
  admissible operation history starting from `empty U` maintains `(dom s).card ≤ n_max`.
* `valuesBounded_delete`, `valuesBounded_step_of_valid`, `valuesBounded_run_of_validHistory`,
  `valuesBounded_run_empty`: any admissible operation history maintains `ValuesBounded V s`.
* `optBits_zero_right`, `one_le_logLogFactor`, `logLogFactor_mono`: basic properties of the
  succinct space-bound quantities.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Section 2.1][BenderFarachColtonKuszmaulKuszmaul2024]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 11][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Dictionary.Dynamic

open Cslib.DataStructure

/-- Lookup, insertion (with in-place value overwrite), and deletion operations on a dynamic
dictionary over keys `Fin U` and natural-number values. -/
inductive Op (U : ℕ) where
  /-- Look up the value associated with key `u`, returning `some v` if present with value `v`
  or `none` if absent. -/
  | query (u : Fin U)
  /-- Associate key `u` with value `v`, inserting `u` if absent or overwriting its existing value
  in place if present. -/
  | insert (u : Fin U) (v : ℕ)
  /-- Remove key `u` from the dictionary if present, or leave the dictionary unchanged if `u` is
  absent. -/
  | delete (u : Fin U)
  deriving DecidableEq, Repr

/-- Return type for each `Op U`. -/
abbrev Op.Result {U : ℕ} : Op U → Type
  | .query _ => Option ℕ
  | .insert _ _ => Unit
  | .delete _ => Unit

/-- Pure transition function for dynamic dictionary operations. -/
abbrev step {U : ℕ} (s : State U) : (o : Op U) → State U × o.Result
  | .query u => (s, s u)
  | .insert u v => (Function.update s u (some v), ())
  | .delete u => (Function.update s u none, ())

/-- Admissibility precondition for bounded-capacity dynamic dictionary operations:
`query` and `delete` are always admissible; `insert u v` is admissible whenever `v < V` and
either `(dom s).card < n_max` or `u` is already present in `s` (`(s u).isSome`, in which case
updating `s u` overwrites its value in place without increasing `(dom s).card`). -/
abbrev valid {U : ℕ} (V n_max : ℕ) (s : State U) : Op U → Prop
  | .query _ => True
  | .insert u v => ((dom s).card < n_max ∨ (s u).isSome) ∧ v < V
  | .delete _ => True

/-- Bounded-capacity dynamic dictionary specification over key universe `Fin U`, value bound `V`,
and maximum key count `n_max`. -/
abbrev spec (U V n_max : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State U) (Op := Op U) (Result := Op.Result)
    step (valid V n_max)

/-! ### Domain, deletion, capacity, and value-bound lemmas -/

/-- Deleting `u` removes `u` from `dom s`. -/
@[simp]
theorem dom_delete {U : ℕ} (s : State U) (u : Fin U) :
    dom (Function.update s u none) = (dom s).erase u := by
  ext x
  by_cases hxu : x = u
  · subst hxu; simp [Dictionary.dom]
  · simp [Dictionary.dom, hxu]

/-- Deleting an absent key `u ∉ dom s` leaves `dom s` unchanged. -/
theorem dom_delete_of_notMem {U : ℕ} {s : State U} {u : Fin U} (hu : u ∉ dom s) :
    dom (Function.update s u none) = dom s := by
  rw [dom_delete, Finset.erase_eq_of_notMem hu]

/-- Deleting a key `u` with `s u = none` leaves `dom s` unchanged. -/
theorem dom_delete_of_eq_none {U : ℕ} {s : State U} {u : Fin U} (hu : s u = none) :
    dom (Function.update s u none) = dom s :=
  dom_delete_of_notMem (Dictionary.notMem_dom_iff.mpr hu)

/-- Deleting `u` never increases `(dom s).card`. -/
theorem card_dom_delete_le {U : ℕ} (s : State U) (u : Fin U) :
    (dom (Function.update s u none)).card ≤ (dom s).card := by
  rw [dom_delete]
  exact Finset.card_erase_le

/-- Deleting a present key `u` (`(s u).isSome`) decreases `(dom s).card` by `1`. -/
theorem card_dom_delete_eq_of_isSome {U : ℕ} {s : State U} {u : Fin U}
    (hu : (s u).isSome) :
    (dom (Function.update s u none)).card = (dom s).card - 1 := by
  rw [dom_delete, Finset.card_erase_of_mem (Dictionary.mem_dom_iff_isSome.mpr hu)]

/-- Deleting an absent key `u` (`s u = none`) leaves `(dom s).card` unchanged. -/
theorem card_dom_delete_eq_of_eq_none {U : ℕ} {s : State U} {u : Fin U}
    (hu : s u = none) :
    (dom (Function.update s u none)).card = (dom s).card := by
  rw [dom_delete_of_eq_none hu]

/-- The number of present keys in any state `s : State U` is at most `U`. -/
theorem card_dom_le_univ {U : ℕ} (s : State U) :
    (dom s).card ≤ U := by
  simpa using Finset.card_le_univ (dom s)

/-- When `U ≤ n_max`, every key insertion into `s : State U` satisfies the capacity condition
`(dom s).card < n_max ∨ (s u).isSome` automatically, so insertion admissibility reduces to
`v < V`. -/
theorem valid_insert_iff_of_le {U V n_max : ℕ} (hU : U ≤ n_max) (s : State U)
    (u : Fin U) (v : ℕ) :
    (spec U V n_max).valid s (.insert u v) ↔ v < V := by
  dsimp only [spec, StateTransitionSpec.ofFn, valid]
  refine ⟨And.right, fun hv => ⟨?_, hv⟩⟩
  by_cases hu : (s u).isSome
  · exact Or.inr hu
  · refine Or.inl ?_
    have hnot : u ∉ dom s := by grind [Dictionary.mem_dom_iff_isSome]
    have hcard : (dom s).card + 1 = (insert u (dom s)).card :=
      (Finset.card_insert_of_notMem hnot).symm
    have hle : (insert u (dom s)).card ≤ U := by
      simpa using Finset.card_le_univ (insert u (dom s))
    omega

/-- Any single admissible dynamic dictionary operation preserves the capacity bound
`(dom s).card ≤ n_max`. -/
theorem card_dom_step_le_of_valid {U V n_max : ℕ} {s : State U} {o : Op U}
    (hs : (dom s).card ≤ n_max) (hval : (spec U V n_max).valid s o) :
    (dom ((spec U V n_max).stepFn s o).1).card ≤ n_max := by
  cases o with
  | query u => exact hs
  | insert u v =>
    exact Dictionary.card_dom_step_le_of_valid (V := V) (o := .insert u v) hs hval
  | delete u =>
    dsimp only [spec, StateTransitionSpec.stepFn, step]
    exact (card_dom_delete_le s u).trans hs

/-- Any admissible dynamic dictionary operation history preserves `(dom s).card ≤ n_max`. -/
theorem card_dom_run_le_of_validHistory {U V n_max : ℕ} {s : State U} {os : List (Op U)}
    (hs : (dom s).card ≤ n_max) (hvh : (spec U V n_max).ValidHistory s os) :
    (dom ((spec U V n_max).run s os).1).card ≤ n_max := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    exact ih (card_dom_step_le_of_valid hs hvh.1) hvh.2

/-- Any admissible dynamic dictionary operation history starting from `empty U` reaches a state
with at most `n_max` keys. -/
theorem card_dom_run_empty_le {U V n_max : ℕ} {os : List (Op U)}
    (hvh : (spec U V n_max).ValidHistory (empty U) os) :
    (dom ((spec U V n_max).run (empty U) os).1).card ≤ n_max :=
  card_dom_run_le_of_validHistory (by simp) hvh

/-- Deleting a key `u` preserves `ValuesBounded V`. -/
theorem valuesBounded_delete {U V : ℕ} {s : State U} (hs : ValuesBounded V s) (u : Fin U) :
    ValuesBounded V (Function.update s u none) := by
  intro x w hxw
  by_cases hxu : x = u
  · subst hxu
    simp at hxw
  · rw [Function.update_of_ne hxu] at hxw
    exact hs x w hxw

/-- Any single admissible dynamic dictionary operation preserves `ValuesBounded V`. -/
theorem valuesBounded_step_of_valid {U V n_max : ℕ} {s : State U} {o : Op U}
    (hs : ValuesBounded V s) (hval : (spec U V n_max).valid s o) :
    ValuesBounded V ((spec U V n_max).stepFn s o).1 := by
  cases o with
  | query u => exact hs
  | insert u v =>
    exact Dictionary.valuesBounded_step_of_valid (n_max := n_max) (o := .insert u v) hs hval
  | delete u =>
    dsimp only [spec, StateTransitionSpec.stepFn, step]
    exact valuesBounded_delete hs u

/-- Any admissible dynamic dictionary operation history preserves `ValuesBounded V`. -/
theorem valuesBounded_run_of_validHistory {U V n_max : ℕ} {s : State U} {os : List (Op U)}
    (hs : ValuesBounded V s) (hvh : (spec U V n_max).ValidHistory s os) :
    ValuesBounded V ((spec U V n_max).run s os).1 := by
  induction os generalizing s with
  | nil => exact hs
  | cons o os ih =>
    exact ih (valuesBounded_step_of_valid hs hvh.1) hvh.2

/-- Any admissible dynamic dictionary operation history starting from `empty U` reaches a state
satisfying `ValuesBounded V`. -/
theorem valuesBounded_run_empty {U V n_max : ℕ} {os : List (Op U)}
    (hvh : (spec U V n_max).ValidHistory (empty U) os) :
    ValuesBounded V ((spec U V n_max).run (empty U) os).1 :=
  valuesBounded_run_of_validHistory (Dictionary.valuesBounded_empty U V) hvh

/-! ### Information-theoretic minimum bits and succinct word bounds -/

/-- Information-theoretic bit bound `OPT(U, V, n) = ⌈log₂ C(U, n)⌉ + n * ⌈log₂ V⌉`
for representing `n` keys in `Fin U` with values in `Fin V`. When `0 < V` and `n ≤ U`, this equals
the exact minimum `⌈log₂ (C(U, n) * V^n)⌉` when `V` is a power of two and exceeds it by at most `n`
bits otherwise. When `n > U`, `U.choose n = 0`; when `V = 0`, there are no valued non-empty
dictionaries. -/
@[expose]
def optBits (U V n : ℕ) : ℕ :=
  Nat.clog 2 (U.choose n) + n * Nat.clog 2 V

/-- Iterated logarithmic factor `⌈log₂ ⌈log₂ (max n 4)⌉⌉ ≥ 1`. -/
@[expose]
def logLogFactor (n : ℕ) : ℕ :=
  Nat.clog 2 (Nat.clog 2 (max n 4))

/-- Succinct space bound `⌈(OPT(U, V, n_max) + C * n_max * ⌈log₂ ⌈log₂ (max n_max 4)⌉⌉) / w⌉ + C₀`
in `w`-bit machine words. -/
@[expose]
def succinctWords (C C₀ U V w n_max : ℕ) : ℕ :=
  (optBits U V n_max + C * n_max * logLogFactor n_max + w - 1) / w + C₀

/-- For `n = 0` keys, `optBits U V 0 = 0`. -/
@[simp]
theorem optBits_zero_right (U V : ℕ) : optBits U V 0 = 0 := by
  simp [optBits]

/-- For every `n : ℕ`, `1 ≤ logLogFactor n`. -/
theorem one_le_logLogFactor (n : ℕ) : 1 ≤ logLogFactor n := by
  have h4 : 4 ≤ max n 4 := le_max_right n 4
  have hc1 : 2 ≤ Nat.clog 2 (max n 4) := by
    have : Nat.clog 2 4 = 2 := by decide
    rw [← this]
    exact Nat.clog_mono_right 2 h4
  have hc2 : 1 ≤ Nat.clog 2 (Nat.clog 2 (max n 4)) := by
    have : Nat.clog 2 2 = 1 := by decide
    rw [← this]
    exact Nat.clog_mono_right 2 hc1
  exact hc2

/-- `logLogFactor` is monotone. -/
theorem logLogFactor_mono {m n : ℕ} (h : m ≤ n) : logLogFactor m ≤ logLogFactor n := by
  unfold logLogFactor
  exact Nat.clog_mono_right 2 (Nat.clog_mono_right 2 (max_le_max_right 4 h))

end Cslib.DataStructure.Dictionary.Dynamic
