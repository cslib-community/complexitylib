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
# Indexed min-priority queue specification

This file defines a deterministic, graph-free abstract specification
(`Cslib.Algorithms.Lean.IndexedMinPQ.spec`) for an indexed min-priority queue over finite handles
`Fin n` and natural-number keys bounded by `K_max`.

States map each handle `v : Fin n` to `Option ℕ` (`none` when absent, `some k` when present with
key `k`). To make `extractMin` a deterministic state transition (`Cslib.Stateful.Spec.step`) that
depends only on the abstract state and not on insertion history, `findMin` breaks equal-key ties by
choosing the smallest handle index (`PrioLE`). Both binary heaps and Fibonacci heaps over the word
RAM can realize this exact specification.

## Main definitions

* `Cslib.Algorithms.Lean.IndexedMinPQ.Op`: priority-queue operations (`isEmpty`, `getKey`,
  `insert`, `decreaseKey`, `extractMin`).
* `Cslib.Algorithms.Lean.IndexedMinPQ.State`, `empty`, `dom`: abstract map state, empty queue, and
  present-handle set.
* `Cslib.Algorithms.Lean.IndexedMinPQ.RawPrioLE`, `PrioLE`, `RawPrioLT`, `PrioLT`, `findMin`:
  weak and strict lexicographic `(key, handle)` priority orders and deterministic minimum
  selection.
* `Cslib.Algorithms.Lean.IndexedMinPQ.spec`: the `Cslib.Stateful.Spec` with key bound `K_max`.

## Main results

* `not_rawPrioLT_iff_rawPrioLE`, `not_prioLT_iff_prioLE`, `prioLT_or_prioLT_of_ne`: relationship
  between strict and weak lexicographic priority orders.
* `dom_empty`, `dom_insert`, `dom_decreaseKey`, `dom_extractMin`: domain evolution under each
  operation.
* `findMin_eq_none_iff`, `findMin_eq_some_iff`, `findMin_mem_dom`, `findMin_le`,
  `findMin_key_le`: characterization and optimality of `findMin`.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapters 6 and 19][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.IndexedMinPQ

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

/-- Graph-free indexed min-priority queue specification with key upper bound `K_max`. -/
def spec (n K_max : ℕ) : Cslib.Stateful.Spec where
  State := State n
  Op := Op n
  Result
    | .isEmpty => Bool
    | .getKey _ => Option ℕ
    | .insert _ _ => Unit
    | .decreaseKey _ _ => Unit
    | .extractMin => Option (Fin n × ℕ)
  step s
    | .isEmpty => (s, decide (dom s = ∅))
    | .getKey v => (s, s v)
    | .insert v k => (Function.update s v (some k), ())
    | .decreaseKey v k => (Function.update s v (some k), ())
    | .extractMin =>
      match findMin s with
      | none => (s, none)
      | some (u, k) => (Function.update s u none, some (u, k))
  valid s
    | .isEmpty | .getKey _ | .extractMin => True
    | .insert v k => s v = none ∧ k ≤ K_max
    | .decreaseKey v k => (∃ k₀, s v = some k₀ ∧ k ≤ k₀) ∧ k ≤ K_max

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
    dom ((spec n K_max).step s .extractMin).1 = (dom s).erase u := by
  simp [spec, h]

end Cslib.Algorithms.Lean.IndexedMinPQ
