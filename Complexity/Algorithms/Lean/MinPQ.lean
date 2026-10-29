/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Semantics.Stateful.Relational
public import Complexity.Algorithms.Lean.IndexedMinPQ

/-!
# Relational Priority Queue with Handles

This module defines the pure relational specification `Cslib.Algorithms.Lean.MinPQ` of a
bounded-capacity min-priority queue storing key–value entries `(u, v)` (`u < U`, `v < V`) addressed
by handles `h : Fin n_max` allocated by the data structure.

Unlike `Cslib.Algorithms.Lean.IndexedMinPQ`, where the caller chooses the vertex index `v : Fin n`
on `insert v k` (as required by graph algorithms such as Dijkstra's algorithm), here the caller
passes only a key–value pair `(u, v)` to `insert u v` and receives a handle `h : Fin n_max` chosen
by the data structure:

* `insert u v` (`size s < n_max ∧ u < U ∧ v < V`): nondeterministically selects *any* unused handle
  `h : Fin n_max` (`s h = none`), stores `some (u, v)` at `h`, and returns `some h`;
* `extractMin`: returns `none` when the queue is empty (`dom s = ∅`), or nondeterministically
  selects *any* stored element `(u, v, h)` attaining the minimum key (`isMinEntry s h u v`),
  removes `h`, and returns `some (u, v, h)`;
* `decreaseKey h u'` (`∃ u v, s h = some (u, v) ∧ u' ≤ u`): lowers the key of active handle `h` to
  `u'` while preserving its satellite value `v`;
* `isEmpty` and `get h`: read-only queries returning `decide (dom s = ∅)` and `s h`.

This module also defines the deterministic free-list handle allocator (`AllocState`, `stepAlloc`),
proves that `stepAlloc` refines `MinPQ.spec` while preserving `AllocState.WellFormed`, and provides
the key-projection lemmas `toIndexed_update_some` and `toIndexed_update_none` connecting `State` to
`IndexedMinPQ.State`.

## Main definitions

* `Cslib.Algorithms.Lean.MinPQ.State`: abstract priority-queue state `Fin n_max → Option (ℕ × ℕ)`.
* `Cslib.Algorithms.Lean.MinPQ.dom`, `size`: active handle set and current number of stored
  elements.
* `Cslib.Algorithms.Lean.MinPQ.Op`, `Op.Result`: priority-queue operations and return types.
* `Cslib.Algorithms.Lean.MinPQ.isMinEntry`: predicate that a stored handle `h` attains the minimum
  key in `s`.
* `Cslib.Algorithms.Lean.MinPQ.spec`: relational specification (`Stateful.RelSpec`).
* `Cslib.Algorithms.Lean.MinPQ.AllocState`, `stepAlloc`: deterministic free-list handle allocator
  and lexicographic tie-breaking transition refining `spec`.

## Main results

* `Cslib.Algorithms.Lean.MinPQ.instTotalSpec`: `MinPQ.spec n_max U V` is total (`RelSpec.Total`).
* `Cslib.Algorithms.Lean.MinPQ.stepAlloc_refines_spec`: every valid `stepAlloc` transition satisfies
  `(spec n_max U V).step` and preserves `AllocState.WellFormed`.
* `Cslib.Algorithms.Lean.MinPQ.toIndexed_update_some`, `toIndexed_update_none`: `toIndexed`
  commutes with `Function.update` on active and cleared handles.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MinPQ

open Cslib.Stateful

/-- Abstract state of a min-priority queue of capacity `n_max`: each handle `h : Fin n_max` is
either unused (`none`) or stores a key–value pair `some (u, v)`. -/
abbrev State (n_max : ℕ) : Type := Fin n_max → Option (ℕ × ℕ)

/-- Initial empty priority queue with all handles unused. -/
def empty (n_max : ℕ) : State n_max := fun _ => none

/-- The finite set of currently active handles in `s`. -/
def dom {n_max : ℕ} (s : State n_max) : Finset (Fin n_max) :=
  Finset.univ.filter fun h => (s h).isSome

/-- The current number of stored elements in `s`. -/
def size {n_max : ℕ} (s : State n_max) : ℕ :=
  (dom s).card

/-- Operations of a min-priority queue with handles of capacity `n_max`. -/
inductive Op (n_max : ℕ) : Type where
  /-- Test whether the priority queue currently stores no elements. -/
  | isEmpty
  /-- Query the `(key, value)` pair currently stored at handle `h` (`none` if `h` is inactive). -/
  | get (h : Fin n_max)
  /-- Insert a new entry with key `u` and value `v`, returning its allocated handle `some h`. -/
  | insert (u v : ℕ)
  /-- Decrease the key at active handle `h` to `u'`. -/
  | decreaseKey (h : Fin n_max) (u' : ℕ)
  /-- Remove and return a minimum-key entry `some (u, v, h)`, or `none` if empty. -/
  | extractMin
  deriving DecidableEq

/-- Operation return types for `Op n_max`. -/
abbrev Op.Result {n_max : ℕ} : Op n_max → Type
  | .isEmpty => Bool
  | .get _ => Option (ℕ × ℕ)
  | .insert _ _ => Option (Fin n_max)
  | .decreaseKey _ _ => Unit
  | .extractMin => Option (ℕ × ℕ × Fin n_max)

/-! ## Domain, element count, and minimum-entry lemmas -/

@[simp]
theorem empty_apply (n_max : ℕ) (h : Fin n_max) : empty n_max h = none := rfl

@[simp]
theorem mem_dom {n_max : ℕ} {s : State n_max} {h : Fin n_max} :
    h ∈ dom s ↔ (s h).isSome = true := by
  simp only [dom, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_dom_iff {n_max : ℕ} {s : State n_max} {h : Fin n_max} :
    h ∈ dom s ↔ ∃ u v, s h = some (u, v) := by
  rw [mem_dom, Option.isSome_iff_exists]
  exact ⟨fun ⟨⟨u, v⟩, H⟩ => ⟨u, v, H⟩, fun ⟨u, v, H⟩ => ⟨(u, v), H⟩⟩

theorem notMem_dom_iff {n_max : ℕ} {s : State n_max} {h : Fin n_max} :
    h ∉ dom s ↔ s h = none := by
  rw [mem_dom, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

@[simp]
theorem dom_empty (n_max : ℕ) : dom (empty n_max) = ∅ := by
  ext h
  simp only [mem_dom, empty_apply, Option.isSome_none, Bool.false_eq_true,
    Finset.notMem_empty]

@[simp]
theorem size_empty (n_max : ℕ) : size (empty n_max) = 0 := by
  simp only [size, dom_empty, Finset.card_empty]

theorem size_le {n_max : ℕ} (s : State n_max) : size s ≤ n_max := by
  simpa only [size, Fintype.card_fin] using (dom s).card_le_univ

theorem dom_eq_empty_iff {n_max : ℕ} {s : State n_max} :
    dom s = ∅ ↔ ∀ h, s h = none := by
  rw [Finset.eq_empty_iff_forall_notMem]
  exact forall_congr' fun _ => notMem_dom_iff

@[simp]
theorem size_eq_zero_iff {n_max : ℕ} {s : State n_max} :
    size s = 0 ↔ dom s = ∅ :=
  Finset.card_eq_zero

theorem dom_update_some {n_max : ℕ} (s : State n_max) (h : Fin n_max) (u v : ℕ) :
    dom (Function.update s h (some (u, v))) = insert h (dom s) := by
  ext x
  simp only [mem_dom, Finset.mem_insert]
  by_cases hxh : x = h
  · subst hxh; simp only [Function.update_self, Option.isSome_some, true_or]
  · simp only [Function.update_of_ne hxh, hxh, false_or]

theorem dom_update_none {n_max : ℕ} (s : State n_max) (h : Fin n_max) :
    dom (Function.update s h none) = (dom s).erase h := by
  ext x
  simp only [mem_dom, Finset.mem_erase]
  by_cases hxh : x = h
  · subst hxh
    simp only [Function.update_self, Option.isSome_none, Bool.false_eq_true, ne_eq,
      not_true_eq_false, false_and]
  · simp only [Function.update_of_ne hxh, ne_eq, hxh, not_false_eq_true, true_and]

theorem size_update_some_of_none {n_max : ℕ} {s : State n_max} {h : Fin n_max}
    (hh : s h = none) (u v : ℕ) :
    size (Function.update s h (some (u, v))) = size s + 1 := by
  simp only [size, dom_update_some]
  exact Finset.card_insert_of_notMem (notMem_dom_iff.mpr hh)

theorem size_update_some_of_some {n_max : ℕ} {s : State n_max} {h : Fin n_max} {u v : ℕ}
    (hh : s h = some (u, v)) (u' v' : ℕ) :
    size (Function.update s h (some (u', v'))) = size s := by
  simp only [size, dom_update_some]
  rw [Finset.insert_eq_of_mem (mem_dom_iff.mpr ⟨u, v, hh⟩)]

theorem size_update_none_of_some {n_max : ℕ} {s : State n_max} {h : Fin n_max} {u v : ℕ}
    (hh : s h = some (u, v)) :
    size (Function.update s h none) = size s - 1 := by
  simp only [size, dom_update_none]
  exact Finset.card_erase_of_mem (mem_dom_iff.mpr ⟨u, v, hh⟩)

/-- If the current number of stored elements `size s` is strictly below `n_max`, at least one handle
`h : Fin n_max` is unused (`s h = none`). -/
theorem exists_none_of_size_lt {n_max : ℕ} {s : State n_max} (h : size s < n_max) :
    ∃ i : Fin n_max, s i = none := by
  by_contra hall
  have huniv : dom s = Finset.univ := by
    ext i
    simp only [mem_dom, Finset.mem_univ, iff_true, Option.isSome_iff_ne_none]
    exact fun hi => hall ⟨i, hi⟩
  have hcard : size s = n_max := by
    simp only [size, huniv, Finset.card_univ, Fintype.card_fin]
  omega

/-- Project a key–value priority-queue state to an `IndexedMinPQ.State n_max` by retaining only the
key at each handle. -/
def toIndexed {n_max : ℕ} (s : State n_max) : IndexedMinPQ.State n_max :=
  fun h => (s h).map Prod.fst

@[simp]
theorem toIndexed_empty (n_max : ℕ) : toIndexed (empty n_max) = IndexedMinPQ.empty n_max :=
  rfl

@[simp]
theorem toIndexed_apply {n_max : ℕ} (s : State n_max) (h : Fin n_max) :
    toIndexed s h = (s h).map Prod.fst := rfl

@[simp]
theorem dom_toIndexed {n_max : ℕ} (s : State n_max) :
    IndexedMinPQ.dom (toIndexed s) = dom s := by
  ext h
  simp only [IndexedMinPQ.dom, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_dom, toIndexed_apply, Option.isSome_map]

theorem toIndexed_update_some {n_max : ℕ} (s : State n_max) (h : Fin n_max) (u v : ℕ) :
    toIndexed (Function.update s h (some (u, v))) =
      Function.update (toIndexed s) h (some u) := by
  ext x
  by_cases hxh : x = h
  · subst hxh; simp only [toIndexed_apply, Function.update_self, Option.map_some]
  · simp only [toIndexed_apply, Function.update_of_ne hxh]

theorem toIndexed_update_none {n_max : ℕ} (s : State n_max) (h : Fin n_max) :
    toIndexed (Function.update s h none) = Function.update (toIndexed s) h none := by
  ext x
  by_cases hxh : x = h
  · subst hxh; simp only [toIndexed_apply, Function.update_self, Option.map_none]
  · simp only [toIndexed_apply, Function.update_of_ne hxh]

/-- Handle `h` is active in `s` with entry `(u, v)` and `u` is less than or equal to the key of
every active entry in `s`. -/
def isMinEntry {n_max : ℕ} (s : State n_max) (h : Fin n_max) (u v : ℕ) : Prop :=
  s h = some (u, v) ∧ ∀ h' u' v', s h' = some (u', v') → u ≤ u'

/-- Deterministic minimum-entry selector breaking key ties by smallest handle index via
`IndexedMinPQ.findMin (toIndexed s)`. -/
def findMin {n_max : ℕ} (s : State n_max) : Option (ℕ × ℕ × Fin n_max) :=
  match IndexedMinPQ.findMin (toIndexed s) with
  | none => none
  | some (h, u) =>
    match s h with
    | some (_, v) => some (u, v, h)
    | none => none

@[simp]
theorem findMin_eq_none_iff {n_max : ℕ} {s : State n_max} :
    findMin s = none ↔ dom s = ∅ := by
  unfold findMin
  rcases hfm : IndexedMinPQ.findMin (toIndexed s) with _ | ⟨h, u⟩
  · simp only [true_iff]
    rw [← dom_toIndexed, ← IndexedMinPQ.findMin_eq_none_iff]
    exact hfm
  · have hmem : toIndexed s h = some u := (IndexedMinPQ.findMin_eq_some_iff.mp hfm).1
    simp only [toIndexed_apply, Option.map_eq_some_iff] at hmem
    obtain ⟨⟨_, v⟩, hsh, rfl⟩ := hmem
    dsimp only
    rw [hsh]
    simp only [reduceCtorEq, false_iff]
    intro hemp
    have : h ∉ dom s := hemp ▸ Finset.notMem_empty h
    exact this (mem_dom_iff.mpr ⟨_, v, hsh⟩)

theorem findMin_eq_some_of_indexed {n_max : ℕ} {s : State n_max} {h : Fin n_max} {u : ℕ}
    (hfm : IndexedMinPQ.findMin (toIndexed s) = some (h, u)) :
    ∃ v, s h = some (u, v) ∧ findMin s = some (u, v, h) ∧ isMinEntry s h u v := by
  obtain ⟨hmem, hle⟩ := IndexedMinPQ.findMin_eq_some_iff.mp hfm
  simp only [toIndexed_apply, Option.map_eq_some_iff] at hmem
  obtain ⟨⟨u₀, v⟩, hsh, rfl⟩ := hmem
  refine ⟨v, hsh, ?_, hsh, ?_⟩
  · simp only [findMin, hfm, hsh]
  · intro h' u' v' hsh'
    have hidx' : toIndexed s h' = some u' := by simp only [toIndexed_apply, hsh', Option.map_some]
    rcases hle h' u' hidx' with hlt | ⟨rfl, _⟩
    · exact Nat.le_of_lt hlt
    · exact le_rfl

theorem exists_isMinEntry_of_dom_ne_empty {n_max : ℕ} {s : State n_max} (hne : dom s ≠ ∅) :
    ∃ h u v, isMinEntry s h u v := by
  have hfm_ne : IndexedMinPQ.findMin (toIndexed s) ≠ none := by
    rw [ne_eq, IndexedMinPQ.findMin_eq_none_iff, dom_toIndexed]
    exact hne
  obtain ⟨⟨h, u⟩, hfm⟩ := Option.ne_none_iff_exists'.mp hfm_ne
  obtain ⟨v, _, _, hmin⟩ := findMin_eq_some_of_indexed hfm
  exact ⟨h, u, v, hmin⟩

/-! ## Relational specification `MinPQ.spec` and totality -/

/-- Pure relational specification of a capacity-`n_max` min-priority queue with handles storing keys
`u < U` and values `v < V`:
* `insert u v` nondeterministically chooses *any* unused handle `h : Fin n_max` (`s h = none`);
* `extractMin` nondeterministically removes and returns *any* stored entry `(u, v, h)` attaining
  the minimum key (`isMinEntry s h u v`), or `none` when `dom s = ∅`. -/
def spec (n_max U V : ℕ) : RelSpec where
  State := State n_max
  Op := Op n_max
  Result := Op.Result (n_max := n_max)
  valid s
    | .isEmpty => True
    | .get _ => True
    | .insert u v => size s < n_max ∧ u < U ∧ v < V
    | .decreaseKey h u' => ∃ u v, s h = some (u, v) ∧ u' ≤ u
    | .extractMin => True
  step s o s' res :=
    match o with
    | .isEmpty => s' = s ∧ res = decide (dom s = ∅)
    | .get h => s' = s ∧ res = s h
    | .insert u v =>
      ∃ h : Fin n_max, s h = none ∧ s' = Function.update s h (some (u, v)) ∧ res = some h
    | .decreaseKey h u' =>
      ∃ u v, s h = some (u, v) ∧ s' = Function.update s h (some (u', v)) ∧ res = ()
    | .extractMin =>
      (dom s = ∅ ∧ s' = s ∧ res = none) ∨
        ∃ h u v, isMinEntry s h u v ∧ s' = Function.update s h none ∧ res = some (u, v, h)

/-- Every admissible `MinPQ` operation has at least one valid relational transition:
`insert` finds an unused handle by pigeonhole (`exists_none_of_size_lt`), and `extractMin` on a
nonempty queue selects a minimum-key entry (`exists_isMinEntry_of_dom_ne_empty`). -/
instance instTotalSpec (n_max U V : ℕ) : (spec n_max U V).Total where
  step_total s o hv := by
    cases o with
    | isEmpty => exact ⟨s, decide (dom s = ∅), rfl, rfl⟩
    | get h => exact ⟨s, s h, rfl, rfl⟩
    | insert u v =>
      obtain ⟨h, hh⟩ := exists_none_of_size_lt hv.1
      exact ⟨Function.update s h (some (u, v)), some h, h, hh, rfl, rfl⟩
    | decreaseKey h u' =>
      obtain ⟨u, v, hh, _⟩ := hv
      exact ⟨Function.update s h (some (u', v)), (), u, v, hh, rfl, rfl⟩
    | extractMin =>
      by_cases hemp : dom s = ∅
      · exact ⟨s, none, Or.inl ⟨hemp, rfl, rfl⟩⟩
      · obtain ⟨h, u, v, hmin⟩ := exists_isMinEntry_of_dom_ne_empty hemp
        exact ⟨Function.update s h none, some (u, v, h), Or.inr ⟨h, u, v, hmin, rfl, rfl⟩⟩

/-! ## Deterministic free-list handle allocator refining `MinPQ.spec` -/

/-- Internal deterministic allocator state refining `State n_max`: combines the active entry map
`entries` with a LIFO recycled-handle stack `freeList` and a bump pointer `fresh ≤ n_max`. -/
structure AllocState (n_max : ℕ) where
  /-- Active key–value entries indexed by handle `h : Fin n_max`. -/
  entries : State n_max
  /-- Recycled unused handles `< fresh`, ordered from top of stack (`head`) to bottom. -/
  freeList : List (Fin n_max)
  /-- Bump pointer: all handles `h` with `fresh ≤ h.val` are unused and absent from `freeList`. -/
  fresh : ℕ

/-- Initial empty allocator state (`entries = empty n_max`, `freeList = []`, `fresh = 0`). -/
def AllocState.empty (n_max : ℕ) : AllocState n_max :=
  ⟨MinPQ.empty n_max, [], 0⟩

/-- Invariant of the free-list + bump-pointer handle allocator:
1. `s.fresh ≤ n_max`;
2. `s.freeList.Nodup`;
3. every `h ∈ s.freeList` has `h.val < s.fresh` and `s.entries h = none`;
4. every `h : Fin n_max` with `s.fresh ≤ h.val` has `s.entries h = none`;
5. `size s.entries + s.freeList.length = s.fresh`. -/
def AllocState.WellFormed {n_max : ℕ} (s : AllocState n_max) : Prop :=
  s.fresh ≤ n_max ∧
  s.freeList.Nodup ∧
  (∀ h ∈ s.freeList, h.val < s.fresh ∧ s.entries h = none) ∧
  (∀ h : Fin n_max, s.fresh ≤ h.val → s.entries h = none) ∧
  size s.entries + s.freeList.length = s.fresh

theorem AllocState.wellFormed_empty (n_max : ℕ) : (AllocState.empty n_max).WellFormed :=
  ⟨Nat.zero_le _, List.nodup_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ _ => rfl, by simp only [AllocState.empty, size_empty, List.length_nil, Nat.add_zero]⟩

/-- Deterministic handle allocation: pops the head of `s.freeList` when nonempty, or allocates the
bump-pointer handle `⟨s.fresh, _⟩` and increments `fresh` when `s.freeList = []` and
`s.fresh < n_max`. -/
def allocHandle {n_max : ℕ} (s : AllocState n_max) :
    Option (Fin n_max × List (Fin n_max) × ℕ) :=
  match s.freeList with
  | h :: tl => some (h, tl, s.fresh)
  | [] =>
    if hlt : s.fresh < n_max then
      some (⟨s.fresh, hlt⟩, [], s.fresh + 1)
    else
      none

/-- Deterministic transition on `AllocState n_max` using `allocHandle` for `insert` and
`findMin s.entries` (lexicographic `(key, handle)` tie-breaking) for `extractMin`. -/
def stepAlloc {n_max : ℕ} (s : AllocState n_max) (o : Op n_max) :
    AllocState n_max × o.Result :=
  match o with
  | .isEmpty => (s, decide (dom s.entries = ∅))
  | .get h => (s, s.entries h)
  | .insert u v =>
    match allocHandle s with
    | some (h, freeList', fresh') =>
      (⟨Function.update s.entries h (some (u, v)), freeList', fresh'⟩, some h)
    | none => (s, none)
  | .decreaseKey h u' =>
    match s.entries h with
    | some (_, v) => (⟨Function.update s.entries h (some (u', v)), s.freeList, s.fresh⟩, ())
    | none => (s, ())
  | .extractMin =>
    match findMin s.entries with
    | none => (s, none)
    | some (u, v, h) =>
      (⟨Function.update s.entries h none, h :: s.freeList, s.fresh⟩, some (u, v, h))

/-- On any well-formed `AllocState` with `size s.entries < n_max`, `allocHandle s` succeeds,
returns an unused handle `h` (`s.entries h = none`), and preserves `AllocState.WellFormed` after
storing `some (u, v)` at `h`. -/
theorem allocHandle_spec {n_max : ℕ} {s : AllocState n_max}
    (hwf : s.WellFormed) (hsz : size s.entries < n_max) (u v : ℕ) :
    ∃ h freeList' fresh',
      allocHandle s = some (h, freeList', fresh') ∧
      s.entries h = none ∧
      (AllocState.mk (Function.update s.entries h (some (u, v))) freeList' fresh').WellFormed := by
  obtain ⟨hfr_le, hnd, hfree, hbump, hsum⟩ := hwf
  rcases hfl : s.freeList with _ | ⟨h, tl⟩
  · have hfr_lt : s.fresh < n_max := by
      rw [hfl, List.length_nil, Nat.add_zero] at hsum
      omega
    let hfin : Fin n_max := ⟨s.fresh, hfr_lt⟩
    have hh_none : s.entries hfin = none := hbump hfin le_rfl
    refine ⟨hfin, [], s.fresh + 1, ?_, hh_none, ?_⟩
    · simp only [allocHandle, hfl, hfr_lt, ↓reduceDIte, hfin]
    · dsimp only [AllocState.WellFormed]
      refine ⟨by omega, List.nodup_nil, fun _ hm => absurd hm List.not_mem_nil, ?_, ?_⟩
      · intro x hx
        have hxh : x ≠ hfin := fun e => by subst e; change s.fresh + 1 ≤ s.fresh at hx; omega
        rw [Function.update_of_ne hxh]
        exact hbump x (by omega)
      · rw [size_update_some_of_none hh_none, List.length_nil, Nat.add_zero]
        rw [hfl, List.length_nil, Nat.add_zero] at hsum
        omega
  · have hh_mem : h ∈ s.freeList := hfl ▸ List.mem_cons_self
    obtain ⟨hh_lt, hh_none⟩ := hfree h hh_mem
    obtain ⟨hh_not_tl, htl_nd⟩ := List.nodup_cons.mp (hfl ▸ hnd)
    refine ⟨h, tl, s.fresh, ?_, hh_none, ?_⟩
    · simp only [allocHandle, hfl]
    · dsimp only [AllocState.WellFormed]
      refine ⟨hfr_le, htl_nd, ?_, ?_, ?_⟩
      · intro x hx
        have hxh : x ≠ h := fun e => hh_not_tl (e ▸ hx)
        have hx_mem : x ∈ s.freeList := hfl ▸ List.mem_cons_of_mem h hx
        exact ⟨(hfree x hx_mem).1, by rw [Function.update_of_ne hxh]; exact (hfree x hx_mem).2⟩
      · intro x hx
        have hxh : x ≠ h := fun e => by subst e; omega
        rw [Function.update_of_ne hxh]
        exact hbump x hx
      · rw [size_update_some_of_none hh_none]
        rw [hfl, List.length_cons] at hsum
        omega

/-- Every valid operation on a well-formed `AllocState` stepped by `stepAlloc`:
1. satisfies the relational transition `(spec n_max U V).step s.entries o (stepAlloc s o).1.entries
   (stepAlloc s o).2`, and
2. preserves `AllocState.WellFormed`. -/
theorem stepAlloc_refines_spec {n_max U V : ℕ} {s : AllocState n_max} (hwf : s.WellFormed)
    (o : Op n_max) (hv : (spec n_max U V).valid s.entries o) :
    (spec n_max U V).step s.entries o (stepAlloc s o).1.entries (stepAlloc s o).2 ∧
      (stepAlloc s o).1.WellFormed := by
  cases o with
  | isEmpty =>
    exact ⟨⟨rfl, rfl⟩, hwf⟩
  | get h =>
    exact ⟨⟨rfl, rfl⟩, hwf⟩
  | insert u v =>
    obtain ⟨h, freeList', fresh', halloc, hh_none, hwf'⟩ := allocHandle_spec hwf hv.1 u v
    simp only [stepAlloc, halloc]
    exact ⟨⟨h, hh_none, rfl, rfl⟩, hwf'⟩
  | decreaseKey h u' =>
    obtain ⟨u, v, hsh, _⟩ := hv
    obtain ⟨hfr_le, hnd, hfree, hbump, hsum⟩ := hwf
    simp only [stepAlloc, hsh]
    dsimp only [AllocState.WellFormed]
    refine ⟨⟨u, v, hsh, rfl, rfl⟩, hfr_le, hnd, ?_, ?_, ?_⟩
    · intro x hx
      have hxh : x ≠ h := fun e => by
        subst e
        rw [(hfree x hx).2] at hsh
        cases hsh
      exact ⟨(hfree x hx).1, by rw [Function.update_of_ne hxh]; exact (hfree x hx).2⟩
    · intro x hx
      have hxh : x ≠ h := fun e => by
        subst e
        rw [hbump x hx] at hsh
        cases hsh
      rw [Function.update_of_ne hxh]
      exact hbump x hx
    · rw [size_update_some_of_some hsh]
      exact hsum
  | extractMin =>
    obtain ⟨hfr_le, hnd, hfree, hbump, hsum⟩ := hwf
    rcases hfm : IndexedMinPQ.findMin (toIndexed s.entries) with _ | ⟨h, u⟩
    · have hemp : dom s.entries = ∅ := by
        rw [← dom_toIndexed, ← IndexedMinPQ.findMin_eq_none_iff]
        exact hfm
      have hfm' : findMin s.entries = none := findMin_eq_none_iff.mpr hemp
      simp only [stepAlloc, hfm']
      exact ⟨Or.inl ⟨hemp, rfl, rfl⟩, hfr_le, hnd, hfree, hbump, hsum⟩
    · obtain ⟨v, hsh, hfm', hmin⟩ := findMin_eq_some_of_indexed hfm
      simp only [stepAlloc, hfm']
      have hh_not_free : h ∉ s.freeList := fun hm => by
        rw [(hfree h hm).2] at hsh
        cases hsh
      have hh_lt : h.val < s.fresh := by
        by_contra hge
        rw [hbump h (Nat.le_of_not_lt hge)] at hsh
        cases hsh
      have hsz_pos : 1 ≤ size s.entries :=
        Finset.card_pos.mpr ⟨h, mem_dom_iff.mpr ⟨u, v, hsh⟩⟩
      dsimp only [AllocState.WellFormed]
      refine ⟨Or.inr ⟨h, u, v, hmin, rfl, rfl⟩,
        hfr_le, List.nodup_cons.mpr ⟨hh_not_free, hnd⟩, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx_tl
        · exact ⟨hh_lt, Function.update_self _ _ _⟩
        · have hxh : x ≠ h := fun e => hh_not_free (e ▸ hx_tl)
          exact ⟨(hfree x hx_tl).1, by rw [Function.update_of_ne hxh]; exact (hfree x hx_tl).2⟩
      · intro x hx
        have hxh : x ≠ h := fun e => by subst e; omega
        rw [Function.update_of_ne hxh]
        exact hbump x hx
      · rw [size_update_none_of_some hsh, List.length_cons]
        omega

end Cslib.Algorithms.Lean.MinPQ
