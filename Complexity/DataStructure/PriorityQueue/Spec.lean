/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.StateTransition
public import Mathlib.Data.Fintype.Basic

/-!
# Min-priority queue state-transition specifications

This file defines two abstract state-transition specifications
(`Cslib.DataStructure.StateTransitionSpec`) for min-priority queues over finite handles:

1. `Cslib.DataStructure.PriorityQueue.indexedMinPQSpec n K_max`: a deterministic, graph-free
   specification for an indexed min-priority queue over caller-chosen handles `Fin n` and
   natural-number keys bounded by `K_max` (used by graph algorithms such as Dijkstra's algorithm).
   Equal-key ties in `extractMin` are broken deterministically by smallest handle index
   (`IndexedMinPQ.PrioLE`).
2. `Cslib.DataStructure.PriorityQueue.minPQSpec n_max U V`: a relational specification for a
   bounded-capacity min-priority queue storing key–value entries `(u, v)` (`u < U`, `v < V`)
   addressed by handles `h : Fin n_max` allocated by the data structure (`insert u v`
   nondeterministically chooses any unused handle `h` and `extractMin` nondeterministically removes
   any minimum-key entry), together with a deterministic free-list handle allocator
   (`MinPQ.AllocState`, `MinPQ.stepAlloc`) refining `minPQSpec`.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.IndexedMinPQ.Op`, `State`, `empty`, `dom`, `PrioLE`, `PrioLT`,
  `findMin`: operations, state, priority orders, and minimum selector for indexed min-priority
  queues.
* `Cslib.DataStructure.PriorityQueue.indexedMinPQSpec`: deterministic `StateTransitionSpec` for
  indexed min-priority queues with key bound `K_max`.
* `Cslib.DataStructure.PriorityQueue.MinPQ.State`, `dom`, `size`, `Op`, `Op.Result`, `isMinEntry`:
  operations, state, and minimum-entry predicate for handle-allocating min-priority queues.
* `Cslib.DataStructure.PriorityQueue.minPQSpec`: relational `StateTransitionSpec` for
  handle-allocating min-priority queues.
* `Cslib.DataStructure.PriorityQueue.MinPQ.AllocState`, `stepAlloc`: deterministic free-list handle
  allocator and lexicographic tie-breaking transition refining `minPQSpec`.

## Main results

* `Cslib.DataStructure.PriorityQueue.IndexedMinPQ.not_rawPrioLT_iff_rawPrioLE`,
  `not_prioLT_iff_prioLE`, `prioLT_or_prioLT_of_ne`: relationship between strict and weak
  lexicographic priority orders.
* `Cslib.DataStructure.PriorityQueue.IndexedMinPQ.dom_empty`, `dom_insert`, `dom_decreaseKey`,
  `dom_extractMin`: domain evolution under each indexed priority-queue operation.
* `Cslib.DataStructure.PriorityQueue.IndexedMinPQ.findMin_eq_none_iff`, `findMin_eq_some_iff`,
  `findMin_mem_dom`, `findMin_le`, `findMin_key_le`: characterization and optimality of
  `IndexedMinPQ.findMin`.
* `Cslib.DataStructure.PriorityQueue.MinPQ.instTotalSpec`: `minPQSpec n_max U V` is total
  (`StateTransitionSpec.Total`).
* `Cslib.DataStructure.PriorityQueue.MinPQ.stepAlloc_refines_spec`: every valid `stepAlloc`
  transition satisfies `(minPQSpec n_max U V).step` and preserves `AllocState.WellFormed`.
* `Cslib.DataStructure.PriorityQueue.MinPQ.toIndexed_update_some`, `toIndexed_update_none`:
  `toIndexed` commutes with `Function.update` on active and cleared handles.

## References

* [T. H. Cormen, C. E. Leiserson, C. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapters 6 and 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.DataStructure.PriorityQueue

namespace IndexedMinPQ

/-- Operations on an indexed min-priority queue over handles `Fin n` and natural-number keys. -/
inductive Op (n : ℕ) where
  /-- Test whether the queue holds no handles. -/
  | isEmpty
  /-- Query the current key of handle `v`, if present. -/
  | getKey (v : Fin n)
  /-- Insert an absent handle `v` with key `k`. -/
  | insert (v : Fin n) (k : ℕ)
  /-- Lower the key of a present handle `v` to `k`. -/
  | decreaseKey (v : Fin n) (k : ℕ)
  /-- Remove and return the present `(handle, key)` pair of minimum `(key, handle)`. -/
  | extractMin
  deriving DecidableEq, Repr

/-- Abstract state of an indexed min-priority queue on `Fin n`. -/
abbrev State (n : ℕ) := Fin n → Option ℕ

/-- The empty priority queue on `Fin n`. -/
def empty (n : ℕ) : State n := fun _ => none

/-- The finite set of handles currently present in state `s`. -/
def dom {n : ℕ} (s : State n) : Finset (Fin n) :=
  Finset.univ.filter fun v => (s v).isSome

/-- Lexicographic priority comparison on raw `(handle, key) : ℕ × ℕ` pairs: smaller key first,
breaking equal-key ties by smaller handle index. -/
abbrev RawPrioLE (a b : ℕ × ℕ) : Prop :=
  a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)

instance instDecidableRawPrioLE (a b : ℕ × ℕ) : Decidable (RawPrioLE a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Reflexivity of `RawPrioLE`. -/
theorem RawPrioLE.refl (a : ℕ × ℕ) : RawPrioLE a a :=
  Or.inr ⟨rfl, le_rfl⟩

/-- Transitivity of `RawPrioLE`. -/
theorem RawPrioLE.trans {a b c : ℕ × ℕ} (hab : RawPrioLE a b) (hbc : RawPrioLE b c) :
    RawPrioLE a c := by
  unfold RawPrioLE at hab hbc ⊢
  omega

/-- Lexicographic priority comparison on `(handle, key)` pairs: smaller key first, breaking
equal-key ties by smaller handle index. -/
def PrioLE {n : ℕ} (a b : Fin n × ℕ) : Prop :=
  RawPrioLE (a.1.val, a.2) (b.1.val, b.2)

instance instDecidablePrioLE {n : ℕ} (a b : Fin n × ℕ) : Decidable (PrioLE a b) :=
  inferInstanceAs (Decidable (RawPrioLE _ _))

/-- Reflexivity of `PrioLE`. -/
theorem PrioLE.refl {n : ℕ} (a : Fin n × ℕ) : PrioLE a a :=
  RawPrioLE.refl _

/-- Transitivity of `PrioLE`. -/
theorem PrioLE.trans {n : ℕ} {a b c : Fin n × ℕ} (hab : PrioLE a b) (hbc : PrioLE b c) :
    PrioLE a c :=
  RawPrioLE.trans hab hbc

/-- Antisymmetry of `PrioLE`. -/
theorem PrioLE.antisymm {n : ℕ} {a b : Fin n × ℕ} (hab : PrioLE a b) (hba : PrioLE b a) :
    a = b := by
  rcases a with ⟨ua, ka⟩
  rcases b with ⟨ub, kb⟩
  dsimp only [PrioLE, RawPrioLE] at hab hba
  have hk : ka = kb := by omega
  have hu : ua = ub := Fin.ext (by omega)
  rw [hu, hk]

/-- Totality of `PrioLE`. -/
theorem PrioLE.total {n : ℕ} (a b : Fin n × ℕ) : PrioLE a b ∨ PrioLE b a := by
  unfold PrioLE
  omega

/-- Strict lexicographic priority comparison on raw `(handle, key) : ℕ × ℕ` pairs: smaller key
first, breaking equal-key ties by strictly smaller handle index. -/
def RawPrioLT (a b : ℕ × ℕ) : Prop :=
  a.2 < b.2 ∨ (a.2 = b.2 ∧ a.1 < b.1)

instance instDecidableRawPrioLT (a b : ℕ × ℕ) : Decidable (RawPrioLT a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Irreflexivity of `RawPrioLT`. -/
theorem RawPrioLT.irrefl (a : ℕ × ℕ) : ¬RawPrioLT a a := by
  unfold RawPrioLT
  omega

/-- Transitivity of `RawPrioLT`. -/
theorem RawPrioLT.trans {a b c : ℕ × ℕ} (hab : RawPrioLT a b) (hbc : RawPrioLT b c) :
    RawPrioLT a c := by
  unfold RawPrioLT at hab hbc ⊢
  omega

/-- Strict priority order `RawPrioLT` implies weak priority order `RawPrioLE`. -/
theorem RawPrioLT.le {a b : ℕ × ℕ} (h : RawPrioLT a b) : RawPrioLE a b := by
  unfold RawPrioLT RawPrioLE at *
  omega

/-- Negation of `RawPrioLT` is the converse weak priority order `RawPrioLE`. -/
theorem not_rawPrioLT_iff_rawPrioLE {a b : ℕ × ℕ} : ¬RawPrioLT a b ↔ RawPrioLE b a := by
  unfold RawPrioLT RawPrioLE
  omega

/-- Strict lexicographic priority comparison on `(handle, key)` pairs: smaller key first, breaking
equal-key ties by strictly smaller handle index. -/
def PrioLT {n : ℕ} (a b : Fin n × ℕ) : Prop :=
  RawPrioLT (a.1.val, a.2) (b.1.val, b.2)

instance instDecidablePrioLT {n : ℕ} (a b : Fin n × ℕ) : Decidable (PrioLT a b) :=
  inferInstanceAs (Decidable (RawPrioLT _ _))

/-- Irreflexivity of `PrioLT`. -/
theorem PrioLT.irrefl {n : ℕ} (a : Fin n × ℕ) : ¬PrioLT a a :=
  RawPrioLT.irrefl _

/-- Transitivity of `PrioLT`. -/
theorem PrioLT.trans {n : ℕ} {a b c : Fin n × ℕ} (hab : PrioLT a b) (hbc : PrioLT b c) :
    PrioLT a c :=
  RawPrioLT.trans hab hbc

/-- Asymmetry of `PrioLT`. -/
theorem PrioLT.asymm {n : ℕ} {a b : Fin n × ℕ} (hab : PrioLT a b) : ¬PrioLT b a :=
  fun hba => PrioLT.irrefl a (hab.trans hba)

/-- `PrioLT` implies `PrioLE`. -/
theorem PrioLT.le {n : ℕ} {a b : Fin n × ℕ} (h : PrioLT a b) : PrioLE a b :=
  RawPrioLT.le h

/-- `PrioLT` mixed with `PrioLE` on the left. -/
theorem PrioLT.of_le_of_lt {n : ℕ} {a b c : Fin n × ℕ}
    (hab : PrioLE a b) (hbc : PrioLT b c) : PrioLT a c := by
  dsimp only [PrioLE, PrioLT, RawPrioLE, RawPrioLT] at hab hbc ⊢
  omega

/-- `PrioLT` mixed with `PrioLE` on the right. -/
theorem PrioLT.of_lt_of_le {n : ℕ} {a b c : Fin n × ℕ}
    (hab : PrioLT a b) (hbc : PrioLE b c) : PrioLT a c := by
  dsimp only [PrioLE, PrioLT, RawPrioLE, RawPrioLT] at hab hbc ⊢
  omega

/-- Negation of `PrioLT` is reverse `PrioLE`. -/
theorem not_prioLT_iff_prioLE {n : ℕ} {a b : Fin n × ℕ} :
    ¬PrioLT a b ↔ PrioLE b a :=
  not_rawPrioLT_iff_rawPrioLE

/-- Any two pairs with distinct handles are strictly comparable under `PrioLT`. -/
theorem prioLT_or_prioLT_of_ne {n : ℕ} {u v : Fin n} (huv : u ≠ v) (ku kv : ℕ) :
    PrioLT (u, ku) (v, kv) ∨ PrioLT (v, kv) (u, ku) := by
  have hval : u.val ≠ v.val := fun h => huv (Fin.ext h)
  dsimp only [PrioLT, RawPrioLT]
  omega

/-- Pick the lexicographically smaller `(handle, key)` pair. -/
def chooseMin {n : ℕ} (a b : Fin n × ℕ) : Fin n × ℕ :=
  if PrioLE a b then a else b

/-- Minimum `(handle, key)` pair of a list under `PrioLE`, or `none` on the empty list. -/
def foldMin {n : ℕ} : List (Fin n × ℕ) → Option (Fin n × ℕ)
  | [] => none
  | a :: l =>
    match foldMin l with
    | none => some a
    | some b => some (chooseMin a b)

private theorem foldMin_eq_none_iff {n : ℕ} {l : List (Fin n × ℕ)} :
    foldMin l = none ↔ l = [] := by
  cases l with
  | nil => simp [foldMin]
  | cons a l =>
    simp only [foldMin, List.cons_ne_nil, iff_false]
    cases foldMin l <;> simp

private theorem foldMin_mem_and_le {n : ℕ} {l : List (Fin n × ℕ)} {uk : Fin n × ℕ}
    (h : foldMin l = some uk) : uk ∈ l ∧ ∀ uk' ∈ l, PrioLE uk uk' := by
  induction l generalizing uk with
  | nil => simp [foldMin] at h
  | cons a l ih =>
    simp only [foldMin] at h
    cases hl : foldMin l with
    | none =>
      rw [hl] at h
      injection h with h
      subst h
      rw [foldMin_eq_none_iff.mp hl]
      exact ⟨List.mem_singleton.mpr rfl, fun uk' huk' => by
        rw [List.mem_singleton.mp huk']; exact PrioLE.refl _⟩
    | some b =>
      rw [hl] at h
      injection h with h
      subst h
      obtain ⟨hb_mem, hb_le⟩ := ih hl
      unfold chooseMin
      split_ifs with hab
      · refine ⟨List.mem_cons_self, fun uk' huk' => ?_⟩
        rcases List.mem_cons.mp huk' with rfl | huk'
        · exact PrioLE.refl _
        · exact hab.trans (hb_le uk' huk')
      · have hba : PrioLE b a := (PrioLE.total a b).resolve_left hab
        refine ⟨List.mem_cons_of_mem a hb_mem, fun uk' huk' => ?_⟩
        rcases List.mem_cons.mp huk' with rfl | huk'
        · exact hba
        · exact hb_le uk' huk'

/-- Unique present `(u, k)` minimizing `(k, u.val)` lexicographically, or `none` if empty. -/
def findMin {n : ℕ} (s : State n) : Option (Fin n × ℕ) :=
  foldMin ((List.finRange n).filterMap fun v => (s v).map (v, ·))

/-- Operation return types for `Op n`. -/
abbrev Op.Result {n : ℕ} : Op n → Type
  | .isEmpty => Bool
  | .getKey _ => Option ℕ
  | .insert _ _ => Unit
  | .decreaseKey _ _ => Unit
  | .extractMin => Option (Fin n × ℕ)

/-- Pure transition function of an indexed min-priority queue on `Fin n`. -/
def step {n : ℕ} (s : State n) : (o : Op n) → State n × o.Result
  | .isEmpty => (s, decide (dom s = ∅))
  | .getKey v => (s, s v)
  | .insert v k => (Function.update s v (some k), ())
  | .decreaseKey v k => (Function.update s v (some k), ())
  | .extractMin =>
    match findMin s with
    | none => (s, none)
    | some (u, k) => (Function.update s u none, some (u, k))

/-- Admissibility predicate for `Op n` with key upper bound `K_max`. -/
def valid {n : ℕ} (K_max : ℕ) (s : State n) : Op n → Prop
  | .isEmpty | .getKey _ | .extractMin => True
  | .insert v k => s v = none ∧ k ≤ K_max
  | .decreaseKey v k => (∃ k₀, s v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max

end IndexedMinPQ

/-- Graph-free indexed min-priority queue specification with key upper bound `K_max`. -/
abbrev indexedMinPQSpec (n K_max : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := IndexedMinPQ.State n) (Op := IndexedMinPQ.Op n)
    (Result := IndexedMinPQ.Op.Result) IndexedMinPQ.step (IndexedMinPQ.valid K_max)

namespace IndexedMinPQ

/-! ### Domain and `findMin` lemmas -/

/-- A handle belongs to `dom s` if and only if `s v` is `some k` for some key `k`. -/
theorem mem_dom_iff {n : ℕ} {s : State n} {v : Fin n} :
    v ∈ dom s ↔ ∃ k, s v = some k := by
  simp [dom, Option.isSome_iff_exists]

/-- A handle is outside `dom s` if and only if `s v = none`. -/
@[simp]
theorem notMem_dom_iff {n : ℕ} {s : State n} {v : Fin n} :
    v ∉ dom s ↔ s v = none := by
  simp [dom]

/-- The empty priority queue has empty domain. -/
@[simp]
theorem dom_empty (n : ℕ) : dom (empty n) = ∅ := by
  ext v
  simp [dom, empty]

/-- Updating `v` to `some k` inserts `v` into `dom s`. -/
@[simp]
theorem dom_insert {n : ℕ} (s : State n) (v : Fin n) (k : ℕ) :
    dom (Function.update s v (some k)) = insert v (dom s) := by
  ext u
  by_cases huv : u = v
  · subst huv; simp [dom]
  · simp [dom, huv]

/-- Lowering the key of a handle already in `dom s` preserves `dom s`. -/
theorem dom_decreaseKey {n : ℕ} {s : State n} {v : Fin n} (hv : v ∈ dom s) (k : ℕ) :
    dom (Function.update s v (some k)) = dom s := by
  rw [dom_insert, Finset.insert_eq_of_mem hv]

/-- Clearing `u` to `none` erases `u` from `dom s`. -/
@[simp]
theorem dom_erase_update {n : ℕ} (s : State n) (u : Fin n) :
    dom (Function.update s u none) = (dom s).erase u := by
  ext v
  by_cases hvu : v = u
  · subst hvu; simp [dom]
  · simp [dom, hvu]

private theorem mem_entries_iff {n : ℕ} {s : State n} {uk : Fin n × ℕ} :
    uk ∈ ((List.finRange n).filterMap fun v => (s v).map (v, ·)) ↔ s uk.1 = some uk.2 := by
  rcases uk with ⟨u, k⟩
  simp only [List.mem_filterMap, List.mem_finRange, true_and, Option.map_eq_some_iff]
  constructor
  · rintro ⟨v, k', hsv, heq⟩
    injection heq with hv hk
    subst hv hk
    exact hsv
  · intro hsu
    exact ⟨u, k, hsu, rfl⟩

/-- `findMin s` returns `none` if and only if `dom s` is empty. -/
@[simp]
theorem findMin_eq_none_iff {n : ℕ} {s : State n} :
    findMin s = none ↔ dom s = ∅ := by
  rw [findMin, foldMin_eq_none_iff, List.filterMap_eq_nil_iff, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h v
    rw [notMem_dom_iff]
    simpa using h v (List.mem_finRange v)
  · intro h v _
    have hv := notMem_dom_iff.mp (h v)
    simp [hv]

/-- If `findMin s = some (u, k)`, then `s u = some k`. -/
theorem findMin_eq_some_state {n : ℕ} {s : State n} {u : Fin n} {k : ℕ}
    (h : findMin s = some (u, k)) : s u = some k :=
  mem_entries_iff.mp (foldMin_mem_and_le h).1

/-- Any handle returned by `findMin` belongs to `dom s`. -/
theorem findMin_mem_dom {n : ℕ} {s : State n} {u : Fin n} {k : ℕ}
    (h : findMin s = some (u, k)) : u ∈ dom s :=
  mem_dom_iff.mpr ⟨k, findMin_eq_some_state h⟩

/-- `findMin` minimizes `(k, u.val)` lexicographically among all present handles. -/
theorem findMin_le {n : ℕ} {s : State n} {u : Fin n} {k : ℕ}
    (h : findMin s = some (u, k)) :
    ∀ v k', s v = some k' → k < k' ∨ (k = k' ∧ u.val ≤ v.val) := by
  intro v k' hsv
  exact (foldMin_mem_and_le h).2 (v, k') (mem_entries_iff.mpr hsv)

/-- The key returned by `findMin` is at most the key of every present handle. -/
theorem findMin_key_le {n : ℕ} {s : State n} {u : Fin n} {k : ℕ}
    (h : findMin s = some (u, k)) {v : Fin n} {k' : ℕ} (hv : s v = some k') :
    k ≤ k' := by
  rcases findMin_le h v k' hv with hlt | ⟨heq, _⟩ <;> omega

/-- Complete characterization of `findMin`: `findMin s = some (u, k)` if and only if `s u = some k`
and `(u, k)` precedes every present `(v, k')` under `PrioLE`. -/
theorem findMin_eq_some_iff {n : ℕ} {s : State n} {u : Fin n} {k : ℕ} :
    findMin s = some (u, k) ↔
      s u = some k ∧ ∀ v k', s v = some k' → k < k' ∨ (k = k' ∧ u.val ≤ v.val) := by
  constructor
  · intro h
    exact ⟨findMin_eq_some_state h, findMin_le h⟩
  · rintro ⟨hsu, hle⟩
    cases hm : findMin s with
    | none =>
      have hemp := findMin_eq_none_iff.mp hm
      have hmem : u ∈ dom s := mem_dom_iff.mpr ⟨k, hsu⟩
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty u)
    | some uk =>
      rcases uk with ⟨u', k'⟩
      have h1 : PrioLE (u', k') (u, k) := findMin_le hm u k hsu
      have h2 : PrioLE (u, k) (u', k') := hle u' k' (findMin_eq_some_state hm)
      have heq := PrioLE.antisymm h2 h1
      rw [heq]

/-- Domain evolution of `extractMin` when `findMin s = some (u, k)`. -/
theorem dom_extractMin {n K_max : ℕ} {s : State n} {u : Fin n} {k : ℕ}
    (h : findMin s = some (u, k)) :
    dom ((indexedMinPQSpec n K_max).stepFn s .extractMin).1 = (dom s).erase u := by
  simp [indexedMinPQSpec, step, h]

end IndexedMinPQ

namespace MinPQ

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

end MinPQ

/-! ## Relational specification `minPQSpec` and totality -/

/-- Pure relational specification of a capacity-`n_max` min-priority queue with handles storing keys
`u < U` and values `v < V`:
* `insert u v` nondeterministically chooses *any* unused handle `h : Fin n_max` (`s h = none`);
* `extractMin` nondeterministically removes and returns *any* stored entry `(u, v, h)` attaining
  the minimum key (`MinPQ.isMinEntry s h u v`), or `none` when `MinPQ.dom s = ∅`. -/
def minPQSpec (n_max U V : ℕ) : StateTransitionSpec where
  State := MinPQ.State n_max
  Op := MinPQ.Op n_max
  Result := MinPQ.Op.Result (n_max := n_max)
  valid s
    | .isEmpty => True
    | .get _ => True
    | .insert u v => MinPQ.size s < n_max ∧ u < U ∧ v < V
    | .decreaseKey h u' => ∃ u v, s h = some (u, v) ∧ u' ≤ u
    | .extractMin => True
  step s o s' res :=
    match o with
    | .isEmpty => s' = s ∧ res = decide (MinPQ.dom s = ∅)
    | .get h => s' = s ∧ res = s h
    | .insert u v =>
      ∃ h : Fin n_max, s h = none ∧ s' = Function.update s h (some (u, v)) ∧ res = some h
    | .decreaseKey h u' =>
      ∃ u v, s h = some (u, v) ∧ s' = Function.update s h (some (u', v)) ∧ res = ()
    | .extractMin =>
      (MinPQ.dom s = ∅ ∧ s' = s ∧ res = none) ∨
        ∃ h u v, MinPQ.isMinEntry s h u v ∧ s' = Function.update s h none ∧ res = some (u, v, h)

namespace MinPQ

/-- Every admissible `MinPQ` operation has at least one valid relational transition:
`insert` finds an unused handle by pigeonhole (`exists_none_of_size_lt`), and `extractMin` on a
nonempty queue selects a minimum-key entry (`exists_isMinEntry_of_dom_ne_empty`). -/
instance instTotalSpec (n_max U V : ℕ) : (minPQSpec n_max U V).Total where
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

/-! ## Deterministic free-list handle allocator refining `minPQSpec` -/

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
1. satisfies the relational transition
   `(minPQSpec n_max U V).step s.entries o (stepAlloc s o).1.entries (stepAlloc s o).2`, and
2. preserves `AllocState.WellFormed`. -/
theorem stepAlloc_refines_spec {n_max U V : ℕ} {s : AllocState n_max} (hwf : s.WellFormed)
    (o : Op n_max) (hv : (minPQSpec n_max U V).valid s.entries o) :
    (minPQSpec n_max U V).step s.entries o (stepAlloc s o).1.entries (stepAlloc s o).2 ∧
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

end MinPQ

end Cslib.DataStructure.PriorityQueue
