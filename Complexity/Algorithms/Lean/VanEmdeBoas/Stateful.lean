/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Elements
public import Complexity.Foundations.Data.OrderedSet.Spec
public import Complexity.Foundations.Semantics.Stateful.Resource
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Order.Fin.Basic

/-!
# Stateful ordered-set realization by recursive van Emde Boas trees

This module realizes the shared `Cslib.OrderedSet.spec (Fin (universeSize d))` interface
(`contains`, `insert`, `erase`, `minimum`, `successor`) using recursive minimum-excluded
van Emde Boas trees `Tree d` over the bounded universe `Fin (universeSize d)` of size
`universeSize d = 2 ^ (2 ^ d)`, and supplies an active-recursive-call depth certificate
`callDepthBound` of `d + 1` per operation ([Demaine2015VanEmdeBoas], pp. 4–5; [CLRS2009],
Section 20.3).

Alongside `Cslib.Algorithms.Lean.SearchTree` (linear worst-case bound `s.card`), this provides a
bounded-universe realization of `Cslib.OrderedSet.spec` with doubly-logarithmic recursion depth
`d + 1` on bounded integer keys.

## Cost model and limitations

Native operation traces count **active recursive van Emde Boas calls** (`1` at the root plus the
active calls of the single recursive subcall, if any, at each internal level; at most `d + 1` per
operation). In particular:
* Empty-node insertion (`bounds = none`) and singleton-node deletion (`bounds = some (m, m)`)
  terminate in `1` active call without recursing into children.
* Non-recursive `O(1)` child-header reads and updates (`bounds`, `minimum`, `maximum`,
  `withBounds`, `eraseTarget`, `clusterMax`), immutable `Function.update` cluster-array updates,
  initial tree allocation (`Tree.empty d`, whose span is `O(universeSize d)`), division/modulo
  coordinate arithmetic, `Fin` bounds wrapping, and pure client continuations are **not** charged
  here. See `Complexity.Algorithms.WordRAM.VanEmdeBoas.Model` (and its companion initialization,
  membership, insertion, and successor modules; Word-RAM deletion and predecessor remain separate)
  for explicit Word-RAM memory and instruction accounting.

## Main definitions

* `Tree.memberVisits`, `Tree.insertVisits`, `Tree.eraseVisits`, `Tree.minimumVisits`,
  `Tree.successorVisits`, `Tree.predecessorVisits`: active recursive-call counts for `Tree d`
  operations.
* `Tree.finElements`, `Tree.finMinimum`, `Tree.finSuccessor`, `Tree.finPredecessor`: typed
  `Fin (universeSize d)` observations and queries.
* `step`, `Exec`, `run`: concrete `OrderedSet.Op (Fin (universeSize d))` step, native execution
  relation, and executable client interpreter.
* `Rep`, `realization`, `callDepthBound`: representation relation, semantic realization of
  `OrderedSet.spec (Fin (universeSize d))`, and uniform `d + 1` per-operation resource bound.

## Main results

* `Tree.memberVisits_le`, `Tree.insertVisits_le`, `Tree.eraseVisits_le`,
  `Tree.minimumVisits_le`, `Tree.successorVisits_le`, `Tree.predecessorVisits_le`: each operation
  makes at most `d + 1` active recursive calls.
* `Tree.insertVisits_of_bounds_none`, `Tree.eraseVisits_of_bounds_eq`: `O(1)` single-call base
  cases on empty insertion and singleton deletion.
* `Rep.valid`, `Rep.finElements_eq`, `rep_empty`, `realization_rep`: representation projections
  and empty-set initialization.
* `callDepthBound`, `realized_client`, `run_correct`: adaptive `OrderedSet` clients execute with
  finite-set correctness and total active-call cost at most `history.length * (d + 1)`.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 20.3][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.VanEmdeBoas

open Cslib.Stateful Cslib.OrderedSet

/-- Every van Emde Boas universe size is nonzero, enabling `OfNat (Fin (universeSize d))` numerals
for bounded-key clients. -/
instance instNeZeroUniverseSize (d : ℕ) : NeZero (universeSize d) :=
  ⟨(universeSize_pos d).ne'⟩

namespace Tree

variable {d : ℕ}

/-- Active recursive calls performed by `Tree.minimum` (`1` root header read). -/
@[expose] def minimumVisits (_ : Tree d) : ℕ := 1

/-- Active recursive calls performed by `Tree.member`. -/
@[expose] def memberVisits : {d : ℕ} → Tree d → ℕ → ℕ
  | 0, .leaf _, _ => 1
  | d + 1, .node b _ c, x => match b with
    | none => 1
    | some (m, _) =>
      if x = m then 1
      else if h : x / universeSize d < universeSize d then
        1 + memberVisits (c ⟨x / universeSize d, h⟩) (x % universeSize d)
      else 1

/-- Active recursive calls performed by `Tree.insert`. -/
@[expose] def insertVisits : {d : ℕ} → Tree d → ℕ → ℕ
  | 0, .leaf _, _ => 1
  | d + 1, .node b s c, x => match b with
    | none => 1
    | some (m, _) =>
      if x = m then 1
      else
        let displaced := max m x
        if h : displaced / universeSize d < universeSize d then
          let i : Fin (universeSize d) := ⟨displaced / universeSize d, h⟩
          match (c i).bounds with
          | none => 1 + insertVisits s i.val
          | some _ => 1 + insertVisits (c i) (displaced % universeSize d)
        else 1

/-- Active recursive calls performed by `Tree.erase`. -/
@[expose] def eraseVisits : {d : ℕ} → Tree d → ℕ → ℕ
  | 0, .leaf _, _ => 1
  | _ + 1, .node b s c, x => match b with
    | none => 1
    | some (m, M) =>
      if x < m ∨ M < x then 1
      else if m = M then 1
      else
        match eraseTarget m x s c with
        | none => 1
        | some ⟨_, i, low⟩ =>
          match (c i).bounds with
          | none => 1
          | some (cm, cM) =>
            if cm = cM then
              if low = cm then 1 + eraseVisits s i.val else 1
            else 1 + eraseVisits (c i) low

/-- Active recursive calls performed by `Tree.successor`. -/
@[expose] def successorVisits : {d : ℕ} → Tree d → ℕ → ℕ
  | 0, .leaf _, _ => 1
  | d + 1, .node b s c, x => match b with
    | none => 1
    | some (m, M) =>
      if x < m then 1
      else if M ≤ x then 1
      else if h : x / universeSize d < universeSize d then
        let i : Fin (universeSize d) := ⟨x / universeSize d, h⟩
        let low := x % universeSize d
        if (c i).maximum.any (low < ·) then
          1 + successorVisits (c i) low
        else
          1 + successorVisits s i.val
      else 1

/-- Active recursive calls performed by `Tree.predecessor`. -/
@[expose] def predecessorVisits : {d : ℕ} → Tree d → ℕ → ℕ
  | 0, .leaf _, _ => 1
  | d + 1, .node b s c, x => match b with
    | none => 1
    | some (m, M) =>
      if M < x then 1
      else if x ≤ m then 1
      else if h : x / universeSize d < universeSize d then
        let i : Fin (universeSize d) := ⟨x / universeSize d, h⟩
        let low := x % universeSize d
        if (c i).minimum.any (· < low) then
          1 + predecessorVisits (c i) low
        else
          1 + predecessorVisits s i.val
      else 1

/-- `minimum` performs `1 ≤ d + 1` active calls. -/
theorem minimumVisits_le (t : Tree d) : t.minimumVisits ≤ d + 1 :=
  Nat.succ_le_succ (Nat.zero_le d)

/-- `member` performs at most `d + 1` active recursive calls. -/
theorem memberVisits_le (t : Tree d) (x : ℕ) : t.memberVisits x ≤ d + 1 := by
  induction d generalizing x with
  | zero => cases t; exact le_rfl
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [memberVisits]
        split_ifs with hm hi
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · have := ih (c ⟨x / universeSize d, hi⟩) (x % universeSize d)
          omega
        · exact Nat.succ_le_succ (Nat.zero_le _)

/-- Inserting into an empty node performs only `1` active call at any depth. -/
theorem insertVisits_of_bounds_none {t : Tree d} (hb : t.bounds = none) (x : ℕ) :
    t.insertVisits x = 1 := by
  cases t with
  | leaf b => rfl
  | node b s c =>
    simp only [bounds] at hb
    subst b
    rfl

/-- `insert` performs at most `d + 1` active recursive calls. -/
theorem insertVisits_le (t : Tree d) (x : ℕ) : t.insertVisits x ≤ d + 1 := by
  induction d generalizing x with
  | zero => cases t; exact le_rfl
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [insertVisits]
        split_ifs with hm hi
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · cases (c ⟨max m x / universeSize d, hi⟩).bounds with
          | none =>
            dsimp only
            have := ih s (max m x / universeSize d)
            omega
          | some _ =>
            dsimp only
            have := ih (c ⟨max m x / universeSize d, hi⟩) (max m x % universeSize d)
            omega
        · exact Nat.succ_le_succ (Nat.zero_le _)

/-- Deleting from a singleton node (`bounds = some (m, m)`) performs only `1` active call at any
depth. -/
theorem eraseVisits_of_bounds_eq {t : Tree d} {m : ℕ} (hb : t.bounds = some (m, m)) (x : ℕ) :
    t.eraseVisits x = 1 := by
  cases t with
  | leaf b => rfl
  | node b s c =>
    simp only [bounds] at hb
    subst b
    simp [eraseVisits]

/-- `erase` performs at most `d + 1` active recursive calls. -/
theorem eraseVisits_le (t : Tree d) (x : ℕ) : t.eraseVisits x ≤ d + 1 := by
  induction d generalizing x with
  | zero => cases t; exact le_rfl
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [eraseVisits]
        split_ifs with hout heq
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · cases eraseTarget m x s c with
          | none =>
            dsimp only
            exact Nat.succ_le_succ (Nat.zero_le _)
          | some tgt =>
            obtain ⟨newMin, i, low⟩ := tgt
            dsimp only
            cases (c i).bounds with
            | none =>
              dsimp only
              exact Nat.succ_le_succ (Nat.zero_le _)
            | some cb =>
              obtain ⟨cm, cM⟩ := cb
              dsimp only
              split_ifs
              · have := ih s i.val
                omega
              · exact Nat.succ_le_succ (Nat.zero_le _)
              · have := ih (c i) low
                omega

/-- `successor` performs at most `d + 1` active recursive calls. -/
theorem successorVisits_le (t : Tree d) (x : ℕ) : t.successorVisits x ≤ d + 1 := by
  induction d generalizing x with
  | zero => cases t; exact le_rfl
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [successorVisits]
        split_ifs with hm hM hi hc
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · have := ih (c ⟨x / universeSize d, hi⟩) (x % universeSize d)
          omega
        · have := ih s (x / universeSize d)
          omega
        · exact Nat.succ_le_succ (Nat.zero_le _)

/-- `predecessor` performs at most `d + 1` active recursive calls. -/
theorem predecessorVisits_le (t : Tree d) (x : ℕ) : t.predecessorVisits x ≤ d + 1 := by
  induction d generalizing x with
  | zero => cases t; exact le_rfl
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => exact Nat.succ_le_succ (Nat.zero_le _)
      | some b =>
        obtain ⟨m, M⟩ := b
        simp only [predecessorVisits]
        split_ifs with hM hm hi hc
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · exact Nat.succ_le_succ (Nat.zero_le _)
        · have := ih (c ⟨x / universeSize d, hi⟩) (x % universeSize d)
          omega
        · have := ih s (x / universeSize d)
          omega
        · exact Nat.succ_le_succ (Nat.zero_le _)

/-- Mathematical finite-set observation in `Fin (universeSize d)`. -/
@[expose] def finElements (t : Tree d) : Finset (Fin (universeSize d)) :=
  Finset.univ.filter fun x => t.member x.val

/-- Membership in `finElements` agrees with `Tree.Contains` on valid trees. -/
theorem mem_finElements_iff {t : Tree d} (ht : t.Valid) (x : Fin (universeSize d)) :
    x ∈ t.finElements ↔ t.Contains x.val := by
  simp only [finElements, Finset.mem_filter, Finset.mem_univ, true_and, member_iff_contains ht]

/-- Membership in `finElements` agrees with `Tree.elements` on `x.val`. -/
theorem mem_finElements_iff_val_mem_elements {t : Tree d} (ht : t.Valid)
    (x : Fin (universeSize d)) : x ∈ t.finElements ↔ x.val ∈ t.elements := by
  rw [mem_finElements_iff ht, mem_elements_iff ht]

/-- The empty tree represents the empty finite set of bounded keys. -/
@[simp] theorem finElements_empty (d : ℕ) : (empty d).finElements = ∅ := by
  ext x
  simp only [mem_finElements_iff (valid_empty d), contains_empty, Finset.notMem_empty]

/-- Bounded insertion commutes with `finElements`. -/
theorem finElements_insert {t : Tree d} (ht : t.Valid) (x : Fin (universeSize d)) :
    (t.insert x.val).finElements = Insert.insert x t.finElements := by
  ext y
  simp only [mem_finElements_iff (valid_insert ht x.isLt), Finset.mem_insert,
    mem_finElements_iff ht, contains_insert ht x.isLt, Fin.ext_iff]

/-- Deletion commutes with `finElements`. -/
theorem finElements_erase {t : Tree d} (ht : t.Valid) (x : Fin (universeSize d)) :
    (t.erase x.val).finElements = t.finElements.erase x := by
  ext y
  simp only [mem_finElements_iff (valid_erase ht x.val), Finset.mem_erase,
    mem_finElements_iff ht, contains_erase ht, ne_eq, Fin.ext_iff]

/-- Typed `Fin (universeSize d)` minimum read from the cached root bounds. -/
@[expose] def finMinimum (t : Tree d) : Option (Fin (universeSize d)) :=
  match t.minimum with
  | none => none
  | some m => if hm : m < universeSize d then some ⟨m, hm⟩ else none

/-- Typed `Fin (universeSize d)` strict successor query. -/
@[expose] def finSuccessor (t : Tree d) (x : Fin (universeSize d)) :
    Option (Fin (universeSize d)) :=
  match t.successor x.val with
  | none => none
  | some y => if hy : y < universeSize d then some ⟨y, hy⟩ else none

/-- Typed `Fin (universeSize d)` strict predecessor query. -/
@[expose] def finPredecessor (t : Tree d) (x : Fin (universeSize d)) :
    Option (Fin (universeSize d)) :=
  match t.predecessor x.val with
  | none => none
  | some y => if hy : y < universeSize d then some ⟨y, hy⟩ else none

/-- `finMinimum` satisfies the optional-minimum contract for `t.finElements`. -/
theorem finMinimum_spec {t : Tree d} (ht : t.Valid) :
    LeastResult t.finElements t.finMinimum := by
  cases hb : t.bounds with
  | none =>
    simp only [finMinimum, minimum, hb, Option.map_none, LeastResult]
    ext x
    simp only [mem_finElements_iff ht, Finset.notMem_empty, iff_false]
    exact not_contains_of_bounds_none hb x.val
  | some b =>
    obtain ⟨m, M⟩ := b
    have he := ht.extrema
    simp only [Extrema, hb] at he
    have hm : m < universeSize d := ht.contains_lt he.2.2.1
    simp only [finMinimum, minimum, hb, Option.map_some, dite_eq_left hm, LeastResult,
      mem_finElements_iff ht]
    exact ⟨he.2.2.1, fun z hz => (he.2.2.2.2 z.val hz).1⟩

/-- `finSuccessor` satisfies the optional-minimum contract for keys strictly above `x`. -/
theorem finSuccessor_spec {t : Tree d} (ht : t.Valid) (x : Fin (universeSize d)) :
    LeastResult (t.finElements.filter (x < ·)) (t.finSuccessor x) := by
  cases hs : t.successor x.val with
  | none =>
    simp only [finSuccessor, hs, LeastResult]
    have hnone := (successor_eq_none_iff ht x.val).mp hs
    ext z
    simp only [Finset.mem_filter, mem_finElements_iff ht, Finset.notMem_empty, iff_false, not_and]
    intro hz
    have hle := hnone z.val hz
    exact not_lt_of_ge hle
  | some y =>
    have hy_spec := (successor_eq_some_iff ht x.val y).mp hs
    have hy : y < universeSize d := ht.contains_lt hy_spec.1
    simp only [finSuccessor, hs, dite_eq_left hy, LeastResult, Finset.mem_filter,
      mem_finElements_iff ht]
    refine ⟨⟨hy_spec.1, hy_spec.2.1⟩, ?_⟩
    intro z ⟨hz, hxz⟩
    exact hy_spec.2.2 z.val hz hxz

/-- A successful `finPredecessor` returns the greatest element of `t.finElements` strictly below
`x`. -/
theorem finPredecessor_eq_some_iff {t : Tree d} (ht : t.Valid)
    (x y : Fin (universeSize d)) :
    t.finPredecessor x = some y ↔
      y ∈ t.finElements ∧ y < x ∧ ∀ z ∈ t.finElements, z < x → z ≤ y := by
  constructor
  · intro h
    unfold finPredecessor at h
    cases hp : t.predecessor x.val with
    | none => simp [hp] at h
    | some w =>
      simp only [hp] at h
      split_ifs at h with hw
      cases h
      have hspec := (predecessor_eq_some_iff ht x.val w).mp hp
      simp only [mem_finElements_iff ht]
      exact ⟨hspec.1, hspec.2.1, fun z hz hzx => hspec.2.2 z.val hz hzx⟩
  · rintro ⟨hy, hyx, hmax⟩
    rw [mem_finElements_iff ht] at hy
    have hp : t.predecessor x.val = some y.val := by
      rw [predecessor_eq_some_iff ht]
      refine ⟨hy, hyx, fun z hz hzx => ?_⟩
      let z' : Fin (universeSize d) := ⟨z, ht.contains_lt hz⟩
      exact hmax z' ((mem_finElements_iff ht z').mpr hz) hzx
    simp [finPredecessor, hp, y.isLt]

/-- `finPredecessor` returns `none` iff every element of `t.finElements` is at least `x`. -/
theorem finPredecessor_eq_none_iff {t : Tree d} (ht : t.Valid) (x : Fin (universeSize d)) :
    t.finPredecessor x = none ↔ ∀ z ∈ t.finElements, x ≤ z := by
  cases hp : t.predecessor x.val with
  | none =>
    simp only [finPredecessor, hp, true_iff, mem_finElements_iff ht]
    have hnone := (predecessor_eq_none_iff ht x.val).mp hp
    exact fun z hz => hnone z.val hz
  | some y =>
    have hspec := (predecessor_eq_some_iff ht x.val y).mp hp
    have hy : y < universeSize d := ht.contains_lt hspec.1
    simp only [finPredecessor, hp, dite_eq_left hy, reduceCtorEq, false_iff, not_forall]
    exact ⟨⟨y, hy⟩, (mem_finElements_iff ht ⟨y, hy⟩).mpr hspec.1, not_le_of_gt hspec.2.1⟩

end Tree

section OrderedSetRealization

variable {d : ℕ}

/-- Execute a single `OrderedSet.Op (Fin (universeSize d))` on `t : Tree d`, returning the updated
tree, result, and active recursive-call count. -/
@[expose] def step (t : Tree d) (o : Op (Fin (universeSize d))) :
    Tree d × (spec (Fin (universeSize d))).Result o × ℕ :=
  match o with
  | .contains x => (t, t.member x.val, t.memberVisits x.val)
  | .insert x => (t.insert x.val, (), t.insertVisits x.val)
  | .erase x => (t.erase x.val, (), t.eraseVisits x.val)
  | .minimum => (t, t.finMinimum, t.minimumVisits)
  | .successor x => (t, t.finSuccessor x, t.successorVisits x.val)

/-- Native execution relation for `OrderedSet.spec (Fin (universeSize d))` over `Tree d`. -/
@[expose] def Exec (d : ℕ) : Execution (spec (Fin (universeSize d))) (Tree d) ℕ :=
  fun t o a t' n => step t o = (t', a, n)

/-- Representation relation coupling a finite set `s : Finset (Fin (universeSize d))` with a valid
van Emde Boas tree `t : Tree d`. -/
@[expose] def Rep (s : Finset (Fin (universeSize d))) (t : Tree d) : Prop :=
  t.Valid ∧ t.finElements = s

/-- Extract `Tree.Valid` from `Rep`. -/
theorem Rep.valid {s : Finset (Fin (universeSize d))} {t : Tree d} (hr : Rep s t) :
    t.Valid := hr.1

/-- Extract the `finElements` equality from `Rep`. -/
theorem Rep.finElements_eq {s : Finset (Fin (universeSize d))} {t : Tree d} (hr : Rep s t) :
    t.finElements = s := hr.2

/-- `Tree.empty d` represents the empty `Finset (Fin (universeSize d))`. -/
theorem rep_empty (d : ℕ) : Rep (∅ : Finset (Fin (universeSize d))) (Tree.empty d) :=
  ⟨Tree.valid_empty d, Tree.finElements_empty d⟩

/-- Semantic realization of `OrderedSet.spec (Fin (universeSize d))` by `Tree d`. -/
@[expose] def realization (d : ℕ) :
    Realization (spec (Fin (universeSize d))) (Exec d) where
  rep := Rep
  total {_ t} o _ _ :=
    match h : step t o with
    | (t', a, n) => ⟨a, t', n, h⟩
  correct {s t o a t' n} hr _ he := by
    obtain ⟨ht, rfl⟩ := hr
    cases o with
    | contains x =>
      cases he
      refine ⟨?_, ht, rfl⟩
      have h := (Tree.member_iff_contains ht x.val).trans (Tree.mem_finElements_iff ht x).symm
      by_cases hx : x ∈ t.finElements <;> simp_all
    | insert x =>
      cases he
      exact ⟨rfl, Tree.valid_insert ht x.isLt, Tree.finElements_insert ht x⟩
    | erase x =>
      cases he
      exact ⟨rfl, Tree.valid_erase ht x.val, Tree.finElements_erase ht x⟩
    | minimum =>
      cases he
      exact ⟨(Tree.finMinimum_spec ht).eq_least, ht, rfl⟩
    | successor x =>
      cases he
      exact ⟨(Tree.finSuccessor_spec ht x).eq_least, ht, rfl⟩

/-- `(realization d).rep` is definitionally `Rep`. -/
@[simp] theorem realization_rep (d : ℕ) : (realization d).rep = Rep := rfl

/-- Every native `OrderedSet` operation on `Tree d` performs at most `d + 1` active recursive
calls. -/
theorem exec_visits_le {t t' : Tree d} {o : Op (Fin (universeSize d))}
    {a : (spec (Fin (universeSize d))).Result o} {n : ℕ} (he : Exec d t o a t' n) :
    n ≤ d + 1 := by
  cases o with
  | contains x => cases he; exact Tree.memberVisits_le t x.val
  | insert x => cases he; exact Tree.insertVisits_le t x.val
  | erase x => cases he; exact Tree.eraseVisits_le t x.val
  | minimum => cases he; exact Tree.minimumVisits_le t
  | successor x => cases he; exact Tree.successorVisits_le t x.val

/-- Uniform `d + 1` active-call depth bound (`O(log log U)` since `universeSize d = 2 ^ (2 ^ d)`)
for `VanEmdeBoas.realization d`. -/
theorem callDepthBound (d : ℕ) : Bound (realization d) id (fun _ _ => d + 1) := by
  intro _ _ _ _ _ _ _ _ he
  exact exec_visits_le he

/-- Every adaptive `OrderedSet` client over `Fin (universeSize d)` executes on `Tree d` with
finite-set correctness and total active recursive calls at most `history.length * (d + 1)`. -/
theorem realized_client {β : Type} (p : (spec (Fin (universeSize d))).Client β)
    {s : Finset (Fin (universeSize d))} {t : Tree d} (hr : Rep s t) :
    ∃ t' ns, Executes (Exec d) p t ((spec (Fin (universeSize d))).runClient s p).1 t' ns ∧
      Rep ((spec (Fin (universeSize d))).runClient s p).2.1 t' ∧
      total id ns ≤ ((spec (Fin (universeSize d))).runClient s p).2.2.length * (d + 1) := by
  have hv := (spec (Fin (universeSize d))).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec (Fin (universeSize d))).runClient s p).2.2
  exact Bound.exists_executes_const (callDepthBound d) p hr hv

/-- Execute an `OrderedSet` client concretely on `Tree d`, recording active recursive-call counts
per operation. -/
@[expose] def run {β : Type} (t : Tree d) :
    (spec (Fin (universeSize d))).Client β → β × Tree d × List ℕ
  | .pure a => (a, t, [])
  | .liftBind o k =>
      let (t', a, c) := step t o
      let (res, t'', cs) := run t' (k a)
      (res, t'', c :: cs)

/-- The concrete runner produces a valid `Executes (Exec d)` derivation. -/
theorem run_exec {β : Type} (p : (spec (Fin (universeSize d))).Client β) (t : Tree d) :
    Executes (Exec d) p t (run t p).1 (run t p).2.1 (run t p).2.2 := by
  induction p generalizing t with
  | pure a => exact .pure a t
  | liftBind o k ih => exact .call rfl (ih _ _)

/-- Running the concrete vEB interpreter agrees with abstract `Finset (Fin (universeSize d))`
semantics, preserves `Rep`, and satisfies the `history.length * (d + 1)` active-call bound. -/
theorem run_correct {β : Type} (p : (spec (Fin (universeSize d))).Client β)
    {s : Finset (Fin (universeSize d))} {t : Tree d} (hr : Rep s t) :
    (run t p).1 = ((spec (Fin (universeSize d))).runClient s p).1 ∧
      Rep ((spec (Fin (universeSize d))).runClient s p).2.1 (run t p).2.1 ∧
      total id (run t p).2.2 ≤
        ((spec (Fin (universeSize d))).runClient s p).2.2.length * (d + 1) := by
  have hv := (spec (Fin (universeSize d))).validHistory_of_forall_valid (fun _ _ => trivial)
    s ((spec (Fin (universeSize d))).runClient s p).2.2
  have hexec := run_exec p t
  have hc := (realization d).correct_client hr hv hexec
  exact ⟨hc.1, hc.2, Bound.client_const (callDepthBound d) hr hv hexec⟩

end OrderedSetRealization

end Cslib.Algorithms.Lean.VanEmdeBoas
