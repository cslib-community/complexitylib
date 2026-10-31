/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.FenwickTree.Lowbit
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Fenwick Trees (Binary Indexed Trees)

This module implements universe-polymorphic Fenwick trees (binary indexed trees, `[Fenwick1994]`,
pp. 328–332) in `Cslib.Algorithms.Lean.TimeM`:

* Over any `[AddCommMonoid α]`: zero-initialized trees `zeros`, point increments `addM`/`add`,
  prefix queries `prefixSumM`/`prefixSum`, and `a.size`-tick immediate-parent construction
  `ofArrayM`/`ofArray` and `ofListM`/`ofList`.
* Over any `[AddCommGroup α]`: half-open range queries `rangeSumM`/`rangeSum`, point reads
  `getM`/`get`, and point assignments `setM`/`set`.

Unlike the power-of-two bounded-word segment tree in `Cslib.Algorithms.WordRAM.PrefixSums`, a
Fenwick tree represents any list `s : List α` of arbitrary length `n` in exact `n` array entries,
without word-width side conditions.

## Source Conventions

* **Indexing:** `[Fenwick1994]` indexes frequencies from `0`, using nodes `1 .. n` (where `V[m]`
  holds `F[m - lowbit m + 1 .. m]`) with element `0` held separately (`V[0] = F[0]`, p. 328). Here
  a length-`n` sequence `s : List α` (`0`-indexed positions `0 .. n - 1`) is shifted by `1` into
  nodes `m ∈ [1, n]` (`[Fenwick1994]`, "PRINCIPLES", pp. 328–329, Figure 1 on p. 328 and
  Figures 2–3 on p. 329), stored at `0`-based array slot `t.tree[m - 1]` and aggregating
  `((s.take m).drop (m - lowbit m)).sum`.
* **Out-of-bounds totality:** `prefixSum t len` clamps `len` to `t.size` (matching
  `(s.take len).sum` for all `len : ℕ`), and `add t pos δ` / `set t pos v` leave `t` unchanged
  when `pos ≥ t.size` (matching `addAt s pos δ` and `s.set pos v`).
* **Algebraic generality and standard extensions:** `[Fenwick1994]` presents cumulative prefix
  queries (`GetCumul`, "THE CUMULATIVE FREQUENCY", Figure 4, p. 330) and upward point increments
  ("UPDATING THE TABLE", pp. 331–332, Figures 5–6 on p. 331) over integer frequencies (plus
  specialized single-frequency extraction in "READING A SINGLE FREQUENCY", Figure 7, p. 332).
  Here `zeros`, `prefixSumM`, `addM`, and `ofArrayM` require only `[AddCommMonoid α]`;
  immediate-parent propagation `ofArrayM`/`ofListM` (`m ↦ m + lowbit m`) is standard BIT folklore,
  and `rangeSumM`, `getM`, and `setM` are standard `[AddCommGroup α]` subtraction corollaries of
  `prefixSumM` and `addM`.

## Cost Model

* **Charged (`1` `TimeM` tick):** each visited Fenwick tree node along a downward query chain in
  `prefixSumM` (`m ↦ m - lowbit m`), each updated ancestor node along an upward update chain in
  `addM` (`m ↦ m + lowbit m`), and each of the `a.size` immediate-parent propagation steps in
  `ofArrayM`.
* **Uncharged (`0` `TimeM` ticks) and model boundaries:** `TimeM ℕ` is an abstract step-counting
  monad, not a Word-RAM instruction model. Index arithmetic (including `O(log n)` binary recursion
  in `lowbit` on `ℕ`, modeling hardware `m & -m`), bounds checks, monoid/group `+` and `-`
  operations (`sr - sl` in `rangeSumM`, `v - cur` in `setM`), `zeros` allocation, and
  `List.toArray` conversion in `ofListM` carry `0` ticks. Moreover, `FenwickTree α` wraps a pure
  functional `Array α`: `Array.modify` mutates in-place in `O(1)` at runtime only under unique
  reference ownership (reference count `1`) and copies the underlying `n`-element array if shared
  non-linearly (for example, `setM` reads `t` via `getM` before calling `addM t`).

## Main definitions

* `Cslib.Algorithms.Lean.FenwickTree`: array-backed Fenwick tree of size `t.size`.
* `Cslib.Algorithms.Lean.FenwickTree.Valid`: invariant coupling `t` to `s : List α`.
* `Cslib.Algorithms.Lean.FenwickTree.addAt`: point increment on `List α` (`no-op` out of bounds).
* `Cslib.Algorithms.Lean.FenwickTree.zeros`, `ofArrayM`, `ofArray`, `ofListM`, `ofList`:
  zero initialization and `a.size`-tick immediate-parent construction.
* `Cslib.Algorithms.Lean.FenwickTree.prefixSumM`, `prefixSum`, `addM`, `add`: logarithmic prefix
  queries and point increments over `[AddCommMonoid α]`.
* `Cslib.Algorithms.Lean.FenwickTree.rangeSumM`, `rangeSum`, `getM`, `get`, `setM`, `set`:
  logarithmic range sums, point reads, and point assignments over `[AddCommGroup α]`.

## Main results

* `Cslib.Algorithms.Lean.FenwickTree.Valid.unique`: `Valid t s` uniquely determines `t` (so any
  valid construction, including `ofList s` and incremental `add` from `zeros`, produces the exact
  same tree).
* `Cslib.Algorithms.Lean.FenwickTree.ret_prefixSumM_eq` and `prefixSumM_time_le_clog` /
  `prefixSumM_time_le_log`: `prefixSum` computes `(s.take len).sum` in at most
  `⌈log₂ (t.size + 1)⌉` (`≤ ⌊log₂ t.size⌋ + 1`) ticks.
* `Cslib.Algorithms.Lean.FenwickTree.valid_add`, `addM_time_eq_upChain`, and
  `addM_time_le_clog` / `addM_time_le_log`: `add` preserves `Valid` for `addAt s pos δ` in at most
  `⌈log₂ (t.size + 1)⌉` ticks.
* `Cslib.Algorithms.Lean.FenwickTree.valid_ofArray` and `ofArrayM_time_eq`: `ofArray` builds a
  valid Fenwick tree for `a.toList` in `a.size` parent-propagation ticks.
* `Cslib.Algorithms.Lean.FenwickTree.ret_rangeSumM_eq`, `ret_getM_eq`, `valid_set`, and their
  logarithmic `TimeM` bounds.

## References

* [P. M. Fenwick, *A New Data Structure for Cumulative Frequency Tables*, pp. 328–332][Fenwick1994]
-/

public section

namespace Cslib.Algorithms.Lean

open Cslib.Algorithms.Lean.TimeM

/-- Array-backed Fenwick tree (binary indexed tree) over `α`. -/
structure FenwickTree (α : Type*) where
  /-- Internal `0`-indexed storage array where entry `m - 1` holds node `m`'s interval sum. -/
  tree : Array α
  deriving DecidableEq, Repr

namespace FenwickTree

/-- Logical length of the represented sequence. -/
@[expose] def size {α : Type*} (t : FenwickTree α) : ℕ :=
  t.tree.size

/-- Point increment on a list at `0`-based index `pos` (no-op when `s.length ≤ pos`). -/
@[expose] def addAt {α : Type*} [AddZeroClass α] (s : List α) (pos : ℕ) (δ : α) : List α :=
  s.set pos (s.getD pos 0 + δ)

@[simp]
theorem length_addAt {α : Type*} [AddZeroClass α] (s : List α) (pos : ℕ) (δ : α) :
    (addAt s pos δ).length = s.length :=
  List.length_set

theorem addAt_of_length_le {α : Type*} [AddZeroClass α] {s : List α} {pos : ℕ} (δ : α)
    (h : s.length ≤ pos) : addAt s pos δ = s :=
  List.set_eq_of_length_le h

theorem getD_addAt {α : Type*} [AddZeroClass α] (s : List α) {pos : ℕ} (δ : α)
    (hpos : pos < s.length) (i : ℕ) :
    (addAt s pos δ).getD i 0 = if i = pos then s.getD i 0 + δ else s.getD i 0 := by
  unfold addAt
  rcases le_or_gt s.length i with hge | hilt
  · have hne : i ≠ pos := by omega
    simp only [hne, ↓reduceIte, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [List.length_set]; exact hge), List.getElem?_eq_none hge]
  · have hilt' : i < (s.set pos (s.getD pos 0 + δ)).length := by
      rw [List.length_set]; exact hilt
    rw [List.getD_eq_getElem?_getD, getElem?_pos _ i hilt', Option.getD_some]
    split_ifs with heq
    · subst heq
      rw [List.getElem_set_self]
    · rw [List.getElem_set_ne (Ne.symm heq)]
      conv_rhs => rw [List.getD_eq_getElem?_getD, getElem?_pos s i hilt, Option.getD_some]

/-- Fenwick tree representation invariant: `t` has length `s.length` and each `1`-based node `m`
(`1 ≤ m ≤ t.tree.size`) stores the interval sum `((s.take m).drop (m - lowbit m)).sum`. -/
@[expose] def Valid {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (s : List α) : Prop :=
  t.tree.size = s.length ∧
    ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m ≤ t.tree.size),
      t.tree[m - 1]'(by omega) = ((s.take m).drop (m - lowbit m)).sum

theorem Valid.size_eq {α : Type*} [AddCommMonoid α] {t : FenwickTree α} {s : List α}
    (hv : Valid t s) : t.size = s.length :=
  hv.1

/-- Canonical representation uniqueness: `Valid t s` uniquely determines `t`. -/
theorem Valid.unique {α : Type*} [AddCommMonoid α]
    {t₁ t₂ : FenwickTree α} {s : List α} (h₁ : Valid t₁ s) (h₂ : Valid t₂ s) : t₁ = t₂ := by
  cases t₁ with
  | mk a₁ =>
    cases t₂ with
    | mk a₂ =>
      congr 1
      refine Array.ext (h₁.1.trans h₂.1.symm) fun i hi₁ hi₂ => ?_
      have hval₁ := h₁.2 (i + 1) (by omega) (Nat.succ_le_of_lt hi₁)
      have hval₂ := h₂.2 (i + 1) (by omega) (Nat.succ_le_of_lt hi₂)
      simpa only [Nat.add_sub_cancel] using hval₁.trans hval₂.symm

/-! ## Bridging `List` slice sums and `Finset.Ico` sums -/

private theorem sum_drop_take_eq_sum_Ico {α : Type*} [AddCommMonoid α]
    (s : List α) {l r : ℕ} (hr : r ≤ s.length) :
    ((s.take r).drop l).sum = ∑ i ∈ Finset.Ico l r, s.getD i 0 := by
  induction r with
  | zero =>
    rw [List.take_zero, List.drop_nil, List.sum_nil, Finset.Ico_eq_empty (by omega),
      Finset.sum_empty]
  | succ r ih =>
    rcases le_or_gt (r + 1) l with hle | hlt
    · have hdrop : (s.take (r + 1)).drop l = [] :=
        List.drop_eq_nil_of_le ((List.length_take_le (r + 1) s).trans hle)
      rw [hdrop, List.sum_nil, Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    · have hrl : l ≤ r := by omega
      have hrs : r < s.length := by omega
      have htake : s.take (r + 1) = s.take r ++ [s[r]'hrs] := by
        rw [List.take_add_one, getElem?_pos s r hrs, Option.toList_some]
      have hlen_r : (s.take r).length = r := List.length_take_of_le (Nat.le_of_lt hrs)
      have hico : Finset.Ico l (r + 1) = insert r (Finset.Ico l r) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hr_not : r ∉ Finset.Ico l r := by
        simp only [Finset.mem_Ico]
        omega
      rw [htake, List.drop_append_of_le_length (by rw [hlen_r]; exact hrl),
        List.sum_append, List.sum_singleton, ih (Nat.le_of_lt hrs),
        hico, Finset.sum_insert hr_not, add_comm]
      congr 1
      rw [List.getD_eq_getElem?_getD, getElem?_pos s r hrs, Option.getD_some]

private theorem valid_iff_sum_Ico {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} :
    Valid t s ↔ t.tree.size = s.length ∧
      ∀ (m : ℕ) (_ : 1 ≤ m) (_ : m ≤ t.tree.size),
        t.tree[m - 1]'(by omega) = ∑ i ∈ Finset.Ico (m - lowbit m) m, s.getD i 0 := by
  unfold Valid
  constructor
  · rintro ⟨hsz, hval⟩
    exact ⟨hsz, fun m hm1 hm => (hval m hm1 hm).trans (sum_drop_take_eq_sum_Ico s (hsz ▸ hm))⟩
  · rintro ⟨hsz, hval⟩
    exact ⟨hsz,
      fun m hm1 hm => (hval m hm1 hm).trans (sum_drop_take_eq_sum_Ico s (hsz ▸ hm)).symm⟩

/-! ## Zero-initialized Fenwick tree -/

/-- All-zero Fenwick tree of length `n`. -/
@[expose] def zeros {α : Type*} [Zero α] (n : ℕ) : FenwickTree α :=
  ⟨Array.replicate n 0⟩

@[simp]
theorem size_zeros {α : Type*} [Zero α] (n : ℕ) : (zeros n : FenwickTree α).size = n := by
  simp only [size, zeros, Array.size_replicate]

theorem valid_zeros {α : Type*} [AddCommMonoid α] (n : ℕ) :
    Valid (zeros n : FenwickTree α) (List.replicate n 0) := by
  rw [valid_iff_sum_Ico]
  refine ⟨by simp only [zeros, Array.size_replicate, List.length_replicate],
    fun m _ _ => ?_⟩
  simp only [zeros, Array.getElem_replicate]
  symm
  apply Finset.sum_eq_zero
  intro i _
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with hilt | hige
  · rw [getElem?_pos _ i (by rw [List.length_replicate]; exact hilt),
      List.getElem_replicate, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact hige), Option.getD_none]

/-! ## Prefix queries (`prefixSumM`, `prefixSum`) -/

private def prefixSumLoopM {α : Type*} [AddCommMonoid α]
    (tree : Array α) (m : ℕ) (acc : α) : TimeM ℕ α :=
  if hm : 0 < m ∧ m ≤ tree.size then do
    ✓ prefixSumLoopM tree (m - lowbit m) (acc + tree[m - 1]'(by omega))
  else
    return acc
termination_by m
decreasing_by exact Nat.sub_lt hm.1 (lowbit_pos hm.1)

/-- Prefix sum of the first `len` elements in `TimeM ℕ`, charging `1` tick per visited Fenwick
node (`[Fenwick1994]`, "THE CUMULATIVE FREQUENCY", Figure 4, p. 330). Clamps `len` to `t.size`. -/
def prefixSumM {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (len : ℕ) : TimeM ℕ α :=
  prefixSumLoopM t.tree (min len t.tree.size) 0

/-- Pure prefix sum `(prefixSumM t len).ret`. -/
@[expose] def prefixSum {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (len : ℕ) : α :=
  (prefixSumM t len).ret

@[simp]
theorem ret_prefixSumM {α : Type*} [AddCommMonoid α] (t : FenwickTree α) (len : ℕ) :
    (prefixSumM t len).ret = prefixSum t len := rfl

private theorem prefixSumLoopM_time_eq {α : Type*} [AddCommMonoid α]
    (tree : Array α) {m : ℕ} (hm : m ≤ tree.size) (acc : α) :
    (prefixSumLoopM tree m acc).time = (downChain m).length := by
  induction m using Nat.strongRecOn generalizing acc with
  | ind m ih =>
    rw [prefixSumLoopM, downChain]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [Nat.lt_irrefl, false_and, ↓reduceDIte, TimeM.time_pure, List.length_nil]
    · simp only [hpos, hm, and_self, ↓reduceDIte, TimeM.time_bind, TimeM.time_tick,
        List.length_cons]
      have hlt : m - lowbit m < m := Nat.sub_lt hpos (lowbit_pos hpos)
      have hsub := ih (m - lowbit m) hlt (by omega) (acc + tree[m - 1]'(by omega))
      omega

theorem prefixSumM_time_eq_downChain {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (len : ℕ) :
    (prefixSumM t len).time = (downChain (min len t.size)).length :=
  prefixSumLoopM_time_eq t.tree (Nat.min_le_right len t.tree.size) 0

@[simp]
theorem prefixSumM_time_zero {α : Type*} [AddCommMonoid α] (t : FenwickTree α) :
    (prefixSumM t 0).time = 0 := by
  rw [prefixSumM_time_eq_downChain, Nat.zero_min, downChain_zero, List.length_nil]

/-- `prefixSumM t len` visits at most `⌈log₂ (t.size + 1)⌉` Fenwick nodes
(`0` when `t.size = 0`). -/
theorem prefixSumM_time_le_clog {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (len : ℕ) :
    (prefixSumM t len).time ≤ Nat.clog 2 (t.size + 1) := by
  rw [prefixSumM_time_eq_downChain]
  exact length_downChain_le_clog (Nat.min_le_right len t.size)

/-- `prefixSumM t len` visits at most `⌊log₂ t.size⌋ + 1` Fenwick nodes. -/
theorem prefixSumM_time_le_log {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (len : ℕ) :
    (prefixSumM t len).time ≤ Nat.log 2 t.size + 1 := by
  rw [prefixSumM_time_eq_downChain]
  rcases Nat.eq_zero_or_pos (min len t.size) with hk0 | hkpos
  · rw [hk0, downChain_zero, List.length_nil]
    omega
  · have h1 := length_downChain_le_log hkpos
    have h2 := Nat.log_mono_right (b := 2) (Nat.min_le_right len t.size)
    omega

private theorem prefixSumLoopM_ret {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s)
    {m : ℕ} (hms : m ≤ s.length) (acc : α) :
    (prefixSumLoopM t.tree m acc).ret = acc + (s.take m).sum := by
  induction m using Nat.strongRecOn generalizing acc with
  | ind m ih =>
    rw [prefixSumLoopM]
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simp only [Nat.lt_irrefl, false_and, ↓reduceDIte, TimeM.ret_pure, List.take_zero,
        List.sum_nil, add_zero]
    · have hmt : m ≤ t.tree.size := hv.1 ▸ hms
      simp only [hpos, hmt, and_self, ↓reduceDIte, TimeM.ret_bind]
      have hlt : m - lowbit m < m := Nat.sub_lt hpos (lowbit_pos hpos)
      rw [ih (m - lowbit m) hlt (by omega) (acc + t.tree[m - 1]'(by omega)),
        hv.2 m hpos hmt]
      have hsplit : s.take m = s.take (m - lowbit m) ++ (s.take m).drop (m - lowbit m) := by
        have h := (List.take_append_drop (m - lowbit m) (s.take m)).symm
        rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)] at h
      conv_rhs => rw [hsplit, List.sum_append]
      rw [add_assoc, add_comm ((s.take m).drop (m - lowbit m)).sum]

/-- Functional correctness of `prefixSum` (`[Fenwick1994]`, "THE CUMULATIVE FREQUENCY", Figure 4,
p. 330): on any valid tree for `s`, `prefixSum t len` equals `(s.take len).sum` for all
`len : ℕ`. -/
theorem prefixSum_eq {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (len : ℕ) :
    prefixSum t len = (s.take len).sum := by
  unfold prefixSum prefixSumM
  rw [hv.1, prefixSumLoopM_ret hv (Nat.min_le_right len s.length) 0, zero_add]
  rcases le_or_gt len s.length with hle | hgt
  · rw [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right (Nat.le_of_lt hgt), List.take_length,
      List.take_of_length_le (Nat.le_of_lt hgt)]

theorem ret_prefixSumM_eq {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (len : ℕ) :
    (prefixSumM t len).ret = (s.take len).sum :=
  prefixSum_eq hv len

/-! ## Point increments (`addM`, `add`) -/

private def addLoopM {α : Type*} [AddCommMonoid α]
    (n : ℕ) (m : ℕ) (δ : α) (tree : Array α) : TimeM ℕ (Array α) :=
  if _hm : 0 < m ∧ m ≤ n then do
    ✓ addLoopM n (m + lowbit m) δ (tree.modify (m - 1) (· + δ))
  else
    return tree
termination_by n + 1 - m
decreasing_by
  have := lowbit_pos _hm.1
  omega

/-- Add `δ` at `0`-based index `pos` in `TimeM ℕ`, charging `1` tick per updated Fenwick node
(`[Fenwick1994]`, "UPDATING THE TABLE", pp. 331–332, Figures 5–6 on p. 331). Leaves `t` unchanged
with `0` ticks when `t.size ≤ pos`. -/
def addM {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) : TimeM ℕ (FenwickTree α) :=
  if pos < t.tree.size then do
    let tree' ← addLoopM t.tree.size (pos + 1) δ t.tree
    return ⟨tree'⟩
  else
    return t

/-- Pure point increment `(addM t pos δ).ret`. -/
@[expose] def add {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) : FenwickTree α :=
  (addM t pos δ).ret

@[simp]
theorem ret_addM {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (addM t pos δ).ret = add t pos δ := rfl

private theorem addLoopM_time_eq {α : Type*} [AddCommMonoid α]
    (n m : ℕ) (δ : α) (tree : Array α) :
    (addLoopM n m δ tree).time = (upChain n m).length := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m tree with
  | ind rem ih =>
    rw [addLoopM, upChain]
    split_ifs with hm
    · simp only [TimeM.time_bind, TimeM.time_tick, List.length_cons]
      have hlb_pos : 0 < lowbit m := lowbit_pos hm.1
      have hsub := @ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m)
        (tree.modify (m - 1) (· + δ)) rfl
      omega
    · simp only [TimeM.time_pure, List.length_nil]

/-- Exact tick count of `addM`: `(upChain t.size (pos + 1)).length` in bounds, `0` out of
bounds. -/
theorem addM_time_eq_upChain {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (addM t pos δ).time = if pos < t.size then (upChain t.size (pos + 1)).length else 0 := by
  unfold addM size
  split_ifs with hpos
  · simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero, addLoopM_time_eq]
  · simp only [TimeM.time_pure]

/-- `addM t pos δ` updates at most `⌈log₂ (t.size + 1)⌉` Fenwick nodes (`0` when `t.size = 0`). -/
theorem addM_time_le_clog {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (addM t pos δ).time ≤ Nat.clog 2 (t.size + 1) := by
  unfold addM
  split_ifs with hpos
  · simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero, addLoopM_time_eq]
    exact length_upChain_le_clog t.size (pos + 1)
  · simp only [TimeM.time_pure, Nat.zero_le]

/-- `addM t pos δ` updates at most `⌊log₂ t.size⌋ + 1` Fenwick nodes. -/
theorem addM_time_le_log {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (addM t pos δ).time ≤ Nat.log 2 t.size + 1 := by
  unfold addM
  split_ifs with hpos
  · simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero, addLoopM_time_eq]
    exact length_upChain_le_log (by omega) (Nat.succ_le_of_lt hpos)
  · simp only [TimeM.time_pure]
    omega

private theorem addLoopM_size {α : Type*} [AddCommMonoid α]
    (n m : ℕ) (δ : α) (tree : Array α) :
    (addLoopM n m δ tree).ret.size = tree.size := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m tree with
  | ind rem ih =>
    rw [addLoopM]
    split_ifs with hm
    · simp only [TimeM.ret_bind]
      have hlb_pos : 0 < lowbit m := lowbit_pos hm.1
      rw [@ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m)
        (tree.modify (m - 1) (· + δ)) rfl, Array.size_modify]
    · simp only [TimeM.ret_pure]

private theorem addLoopM_getElem {α : Type*} [AddCommMonoid α]
    (n m : ℕ) (δ : α) (tree : Array α)
    {idx : ℕ} (hidx1 : 1 ≤ idx) (hidx_sz : idx ≤ tree.size) :
    ((addLoopM n m δ tree).ret)[idx - 1]'(by rw [addLoopM_size]; omega) =
      if idx ∈ upChain n m then tree[idx - 1]'(by omega) + δ
      else tree[idx - 1]'(by omega) := by
  generalize hrem : n + 1 - m = rem
  induction rem using Nat.strongRecOn generalizing m tree with
  | ind rem ih =>
    generalize_proofs pf_ret pf_tree
    revert pf_ret
    rw [addLoopM]
    split_ifs with hm
    · simp only [TimeM.ret_bind]
      intro pf_ret
      have hlb_pos : 0 < lowbit m := lowbit_pos hm.1
      have hidx_sz' : idx ≤ (tree.modify (m - 1) (· + δ)).size := by
        rw [Array.size_modify]; exact hidx_sz
      rw [@ih (n + 1 - (m + lowbit m)) (by omega) (m + lowbit m)
        (tree.modify (m - 1) (· + δ)) hidx_sz' rfl]
      simp only [Array.getElem_modify]
      conv_rhs => rw [upChain]
      simp only [hm.1, hm.2, and_self, ↓reduceDIte, List.mem_cons]
      by_cases heq : idx = m
      · subst heq
        have hnot_tail : idx ∉ upChain n (idx + lowbit idx) := by
          intro hmem
          have hpw := pairwise_lt_upChain n idx
          rw [upChain] at hpw
          simp only [hm.1, hm.2, and_self, ↓reduceDIte, List.pairwise_cons] at hpw
          exact Nat.lt_irrefl idx (hpw.1 idx hmem)
        simp only [true_or, ↓reduceIte, hnot_tail]
      · have hne_sub : m - 1 ≠ idx - 1 := by omega
        simp only [heq, false_or, hne_sub, ↓reduceIte]
    · simp only [TimeM.ret_pure]
      intro _
      rw [upChain]
      simp only [hm, ↓reduceDIte, List.not_mem_nil, ↓reduceIte]

/-- `add t pos δ` preserves `Valid` with respect to `addAt s pos δ` (`[Fenwick1994]`,
"UPDATING THE TABLE", pp. 331–332, Figures 5–6 on p. 331). -/
theorem valid_add {α : Type*} [AddCommMonoid α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) (δ : α) :
    Valid (add t pos δ) (addAt s pos δ) := by
  unfold add addM
  split_ifs with hpos
  · simp only [TimeM.ret_bind, TimeM.ret_pure]
    have hpos_s : pos < s.length := hv.1 ▸ hpos
    rw [valid_iff_sum_Ico] at hv ⊢
    refine ⟨by rw [addLoopM_size, hv.1, length_addAt], fun idx hidx1 hidx_sz => ?_⟩
    rw [addLoopM_size] at hidx_sz
    rw [addLoopM_getElem t.tree.size (pos + 1) δ t.tree hidx1 hidx_sz, hv.2 idx hidx1 hidx_sz]
    have hmem_ico : idx ∈ upChain t.tree.size (pos + 1) ↔
        pos ∈ Finset.Ico (idx - lowbit idx) idx := by
      rw [mem_upChain_iff (by omega : 0 < pos + 1), Finset.mem_Ico]
      omega
    simp only [hmem_ico]
    have hsum_eq : ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, (addAt s pos δ).getD i 0 =
        ∑ i ∈ Finset.Ico (idx - lowbit idx) idx,
          (s.getD i 0 + if i = pos then δ else 0) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [getD_addAt s δ hpos_s i]
      split_ifs <;> simp only [add_zero]
    rw [hsum_eq, Finset.sum_add_distrib]
    by_cases hmem : pos ∈ Finset.Ico (idx - lowbit idx) idx
    · simp only [hmem, ↓reduceIte]
      have hsingle : ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, (if i = pos then δ else 0) = δ := by
        rw [Finset.sum_eq_single pos (fun i _ hne => by simp only [hne, ↓reduceIte])
          (fun hnot => False.elim (hnot hmem))]
        simp only [↓reduceIte]
      rw [hsingle]
    · simp only [hmem, ↓reduceIte]
      have hzero : ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, (if i = pos then δ else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hne : i ≠ pos := fun h => hmem (h ▸ hi)
        simp only [hne, ↓reduceIte]
      rw [hzero, add_zero]
  · simp only [TimeM.ret_pure]
    have hge : s.length ≤ pos := by have := hv.1; omega
    rwa [addAt_of_length_le δ hge]

@[simp]
theorem size_add {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) (pos : ℕ) (δ : α) :
    (add t pos δ).size = t.size := by
  unfold add addM size
  split_ifs with hpos
  · simp only [TimeM.ret_bind, TimeM.ret_pure, addLoopM_size]
  · simp only [TimeM.ret_pure]

theorem add_of_size_le {α : Type*} [AddCommMonoid α]
    (t : FenwickTree α) {pos : ℕ} (δ : α) (h : t.size ≤ pos) :
    add t pos δ = t := by
  unfold add addM
  have hnot : ¬ pos < t.tree.size := by unfold size at h; omega
  simp only [hnot, ↓reduceIte, TimeM.ret_pure]

/-! ## Immediate-parent propagation construction (`ofArrayM`, `ofArray`, `ofList`) -/

private def buildLoopM {α : Type*} [AddCommMonoid α]
    (n : ℕ) (m : ℕ) (tree : Array α) : TimeM ℕ (Array α) :=
  if hm : 1 ≤ m ∧ m ≤ n ∧ tree.size = n then do
    let p := m + lowbit m
    let tree' :=
      if p ≤ n then
        let val := tree[m - 1]'(by omega)
        tree.modify (p - 1) (· + val)
      else
        tree
    ✓ buildLoopM n (m + 1) tree'
  else
    return tree
termination_by n + 1 - m

/-- Construct a Fenwick tree from `a : Array α` in `a.size` parent-propagation `TimeM` ticks by
adding each node `m` once into its immediate Fenwick parent `m + lowbit m` (corresponding to
linear-time in-place construction when the array is uniquely owned). -/
def ofArrayM {α : Type*} [AddCommMonoid α] (a : Array α) : TimeM ℕ (FenwickTree α) := do
  let tree ← buildLoopM a.size 1 a
  return ⟨tree⟩

/-- Pure immediate-parent-constructed Fenwick tree `(ofArrayM a).ret`. -/
@[expose] def ofArray {α : Type*} [AddCommMonoid α] (a : Array α) : FenwickTree α :=
  (ofArrayM a).ret

/-- Construct a Fenwick tree from `s : List α` in `TimeM ℕ`. -/
def ofListM {α : Type*} [AddCommMonoid α] (s : List α) : TimeM ℕ (FenwickTree α) :=
  ofArrayM s.toArray

/-- Pure Fenwick tree constructed from `s : List α`. -/
@[expose] def ofList {α : Type*} [AddCommMonoid α] (s : List α) : FenwickTree α :=
  (ofListM s).ret

private theorem buildLoopM_time_eq {α : Type*} [AddCommMonoid α]
    (n m : ℕ) {tree : Array α} (hsz : tree.size = n) (hm1 : 1 ≤ m) (hmn : m ≤ n + 1) :
    (buildLoopM n m tree).time = n + 1 - m := by
  generalize hrem : n + 1 - m = rem
  induction rem generalizing m tree with
  | zero =>
    rw [buildLoopM]
    have hnot : ¬ (1 ≤ m ∧ m ≤ n ∧ tree.size = n) := by omega
    simp only [hnot, ↓reduceDIte, TimeM.time_pure]
  | succ rem ih =>
    have hms : m ≤ n := by omega
    rw [buildLoopM]
    simp only [hm1, hms, hsz, and_self, ↓reduceDIte, TimeM.time_bind, TimeM.time_tick]
    set p := m + lowbit m
    set tree' :=
      if p ≤ n then tree.modify (p - 1) (· + tree[m - 1]'(by omega)) else tree
    have hsz' : tree'.size = n := by
      dsimp only [tree']
      split_ifs <;> simp only [Array.size_modify, hsz]
    have hsub := ih (m + 1) hsz' (by omega) (by omega) (by omega)
    omega

/-- `ofArrayM a` performs exactly `a.size` parent-propagation steps (`0` on `#[]`). -/
theorem ofArrayM_time_eq {α : Type*} [AddCommMonoid α] (a : Array α) :
    (ofArrayM a).time = a.size := by
  unfold ofArrayM
  simp only [TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  have h := buildLoopM_time_eq a.size 1 rfl (Nat.le_refl 1) (by omega)
  omega

theorem ofListM_time_eq {α : Type*} [AddCommMonoid α] (s : List α) :
    (ofListM s).time = s.length := by
  unfold ofListM
  rw [ofArrayM_time_eq, List.size_toArray]

private structure BuildInv {α : Type*} [AddCommMonoid α]
    (s : List α) (m : ℕ) (tree : Array α) : Prop where
  size_eq : tree.size = s.length
  done_eq : ∀ (idx : ℕ) (_ : 1 ≤ idx) (_ : idx < m) (_ : idx ≤ tree.size),
    tree[idx - 1]'(by omega) = ∑ i ∈ Finset.Ico (idx - lowbit idx) idx, s.getD i 0
  todo_eq : ∀ (idx : ℕ) (_ : 1 ≤ idx) (_ : m ≤ idx) (_ : idx ≤ tree.size),
    tree[idx - 1]'(by omega) = s.getD (idx - 1) 0 +
      ∑ c ∈ (fenwickChildren idx).filter (· < m),
        ∑ i ∈ Finset.Ico (c - lowbit c) c, s.getD i 0

private theorem buildLoopM_spec {α : Type*} [AddCommMonoid α]
    (s : List α) (m : ℕ) {tree : Array α}
    (hm1 : 1 ≤ m) (hmn : m ≤ s.length + 1) (hinv : BuildInv s m tree) :
    BuildInv s (s.length + 1) (buildLoopM s.length m tree).ret := by
  generalize hrem : s.length + 1 - m = rem
  induction rem generalizing m tree with
  | zero =>
    have hmeq : m = s.length + 1 := by omega
    subst hmeq
    rw [buildLoopM]
    have hnot : ¬ (1 ≤ s.length + 1 ∧ s.length + 1 ≤ s.length ∧ tree.size = s.length) := by omega
    simp only [hnot, ↓reduceDIte, TimeM.ret_pure]
    exact hinv
  | succ rem ih =>
    have hms : m ≤ s.length := by omega
    have hmt : m ≤ tree.size := hinv.size_eq ▸ hms
    have hm_val : tree[m - 1]'(by omega) =
        ∑ i ∈ Finset.Ico (m - lowbit m) m, s.getD i 0 := by
      rw [hinv.todo_eq m hm1 (Nat.le_refl m) hmt]
      have hfilt : (fenwickChildren m).filter (· < m) = fenwickChildren m := by
        apply Finset.filter_true_of_mem
        intro c hc
        simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc
        omega
      rw [hfilt]
      conv_rhs =>
        rw [← insert_biUnion_fenwickChildren hm1,
          Finset.sum_insert (notMem_biUnion_fenwickChildren m),
          Finset.sum_biUnion (pairwiseDisjoint_fenwickChildren m)]
    set p := m + lowbit m
    have hp_gt : m < p := by
      have := lowbit_pos hm1
      omega
    set tree' :=
      if p ≤ s.length then tree.modify (p - 1) (· + tree[m - 1]'(by omega)) else tree
    have hsz' : tree'.size = s.length := by
      dsimp only [tree']
      split_ifs <;> simp only [Array.size_modify, hinv.size_eq]
    have hinv' : BuildInv s (m + 1) tree' := by
      refine ⟨hsz', fun idx hidx1 hidx_lt hidx_sz' => ?_,
        fun idx hidx1 hidx_ge hidx_sz' => ?_⟩
      · have hidx_sz : idx ≤ tree.size := by rw [hinv.size_eq, ← hsz']; exact hidx_sz'
        have htree'_eq : tree'[idx - 1]'(by omega) = tree[idx - 1]'(by omega) := by
          generalize_proofs pf1 pf2
          revert pf1
          dsimp only [tree']
          split_ifs with hp
          · intro pf1
            have hne : p - 1 ≠ idx - 1 := by omega
            simp only [Array.getElem_modify, hne, ↓reduceIte]
          · intro _
            rfl
        rw [htree'_eq]
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx_lt) with hlt | rfl
        · exact hinv.done_eq idx hidx1 hlt hidx_sz
        · exact hm_val
      · have hidx_sz : idx ≤ tree.size := by rw [hinv.size_eq, ← hsz']; exact hidx_sz'
        by_cases hpeq : idx = p
        · subst hpeq
          have hp_le : p ≤ s.length := hsz' ▸ hidx_sz'
          have htree'_p : tree'[p - 1]'(by omega) =
              tree[p - 1]'(by omega) + tree[m - 1]'(by omega) := by
            generalize_proofs pf1 pf2 pf3
            revert pf1
            dsimp only [tree']
            simp only [hp_le, ↓reduceIte]
            intro pf1
            simp only [Array.getElem_modify, ↓reduceIte]
          rw [htree'_p, hinv.todo_eq p hidx1 (by omega) hidx_sz, hm_val]
          have hm_mem : m ∈ fenwickChildren p := by
            simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc]
            exact ⟨⟨hm1, by omega⟩, rfl⟩
          have hfilt_eq : (fenwickChildren p).filter (· < m + 1) =
              insert m ((fenwickChildren p).filter (· < m)) := by
            ext c
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hc, hclt⟩
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hclt) with hlt | rfl
              · exact Or.inr ⟨hc, hlt⟩
              · exact Or.inl rfl
            · rintro (rfl | ⟨hc, hlt⟩)
              · exact ⟨hm_mem, by omega⟩
              · exact ⟨hc, by omega⟩
          have hm_not : m ∉ (fenwickChildren p).filter (· < m) := by
            simp only [Finset.mem_filter, Nat.lt_irrefl, and_false, not_false_eq_true]
          rw [hfilt_eq, Finset.sum_insert hm_not, add_assoc]
          congr 1
          rw [add_comm]
        · have htree'_ne : tree'[idx - 1]'(by omega) = tree[idx - 1]'(by omega) := by
            generalize_proofs pf1 pf2
            revert pf1
            dsimp only [tree']
            split_ifs with hp
            · intro pf1
              have hne : p - 1 ≠ idx - 1 := by omega
              simp only [Array.getElem_modify, hne, ↓reduceIte]
            · intro _
              rfl
          rw [htree'_ne, hinv.todo_eq idx hidx1 (by omega) hidx_sz]
          have hfilt_eq : (fenwickChildren idx).filter (· < m + 1) =
              (fenwickChildren idx).filter (· < m) := by
            ext c
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hc, hclt⟩
              refine ⟨hc, ?_⟩
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hclt) with hlt | rfl
              · exact hlt
              · simp only [fenwickChildren, Finset.mem_filter] at hc
                exact False.elim (hpeq hc.2.symm)
            · rintro ⟨hc, hlt⟩
              exact ⟨hc, by omega⟩
          rw [hfilt_eq]
    rw [buildLoopM]
    simp only [hm1, hms, hinv.size_eq, and_self, ↓reduceDIte, TimeM.ret_bind]
    exact ih (m + 1) (by omega) (by omega) hinv' (by omega)

/-- `ofArray a` constructs a valid Fenwick tree representing `a.toList`. -/
theorem valid_ofArray {α : Type*} [AddCommMonoid α] (a : Array α) :
    Valid (ofArray a) a.toList := by
  unfold ofArray ofArrayM
  simp only [TimeM.ret_bind, TimeM.ret_pure, ← Array.length_toList (xs := a)]
  have hinv0 : BuildInv a.toList 1 a := by
    refine ⟨Array.length_toList.symm, fun idx h1 hlt _ => by omega,
      fun idx hidx1 _ hidx_sz => ?_⟩
    have hfilt0 : (fenwickChildren idx).filter (· < 1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c hc
      simp only [fenwickChildren, Finset.mem_filter, Finset.mem_Icc] at hc
      omega
    rw [hfilt0, Finset.sum_empty, add_zero]
    have hlt : idx - 1 < a.toList.length := by rw [Array.length_toList]; omega
    rw [List.getD_eq_getElem?_getD, getElem?_pos a.toList (idx - 1) hlt, Option.getD_some,
      Array.getElem_toList]
  have hend := buildLoopM_spec a.toList 1 (Nat.le_refl 1) (by omega) hinv0
  rw [valid_iff_sum_Ico]
  refine ⟨hend.size_eq, fun m hm1 hm => ?_⟩
  dsimp only at hm
  exact hend.done_eq m hm1 (by have := hend.size_eq; omega) hm

@[simp]
theorem size_ofArray {α : Type*} [AddCommMonoid α] (a : Array α) :
    (ofArray a).size = a.size := by
  have hv := (valid_ofArray a).1
  simpa only [size, Array.length_toList] using hv

theorem valid_ofList {α : Type*} [AddCommMonoid α] (s : List α) :
    Valid (ofList s) s := by
  change Valid (ofArray s.toArray) s
  simpa only [List.toList_toArray] using valid_ofArray s.toArray

@[simp]
theorem size_ofList {α : Type*} [AddCommMonoid α] (s : List α) :
    (ofList s).size = s.length :=
  (valid_ofList s).size_eq

@[simp]
theorem ofList_nil {α : Type*} [AddCommMonoid α] :
    ofList ([] : List α) = zeros 0 :=
  (valid_ofList []).unique (valid_zeros 0)

/-! ## Group operations (`rangeSumM`, `getM`, `setM`) -/

/-- Half-open range sum `((s.take r).drop l).sum` in `TimeM ℕ` over `[AddCommGroup α]`, computed as
the difference `prefixSumM t r - prefixSumM t l` when `l < r`. -/
def rangeSumM {α : Type*} [AddCommGroup α] (t : FenwickTree α) (l r : ℕ) : TimeM ℕ α :=
  if l < r then do
    let sr ← prefixSumM t r
    let sl ← prefixSumM t l
    return sr - sl
  else
    return 0

/-- Pure half-open range sum `(rangeSumM t l r).ret`. -/
@[expose] def rangeSum {α : Type*} [AddCommGroup α] (t : FenwickTree α) (l r : ℕ) : α :=
  (rangeSumM t l r).ret

theorem rangeSum_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (l r : ℕ) :
    rangeSum t l r = ((s.take r).drop l).sum := by
  unfold rangeSum rangeSumM
  split_ifs with hlt
  · simp only [TimeM.ret_bind, TimeM.ret_pure, ret_prefixSumM_eq hv]
    have hsplit : s.take r = s.take l ++ (s.take r).drop l := by
      have h := (List.take_append_drop l (s.take r)).symm
      rwa [List.take_take, Nat.min_eq_left (Nat.le_of_lt hlt)] at h
    conv_lhs => rw [hsplit, List.sum_append]
    exact add_sub_cancel_left _ _
  · simp only [TimeM.ret_pure]
    have hdrop : (s.take r).drop l = [] :=
      List.drop_eq_nil_of_le ((List.length_take_le r s).trans (by omega))
    rw [hdrop, List.sum_nil]

theorem ret_rangeSumM_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (l r : ℕ) :
    (rangeSumM t l r).ret = ((s.take r).drop l).sum :=
  rangeSum_eq hv l r

theorem rangeSumM_time_le_clog {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (l r : ℕ) :
    (rangeSumM t l r).time ≤ 2 * Nat.clog 2 (t.size + 1) := by
  unfold rangeSumM
  split_ifs with hlt
  · simp only [TimeM.time_bind, TimeM.time_pure]
    have h1 := prefixSumM_time_le_clog t r
    have h2 := prefixSumM_time_le_clog t l
    omega
  · simp only [TimeM.time_pure, Nat.zero_le]

/-- Point query at `0`-based index `pos` (`0` out of bounds) in `TimeM ℕ`. -/
def getM {α : Type*} [AddCommGroup α] (t : FenwickTree α) (pos : ℕ) : TimeM ℕ α :=
  rangeSumM t pos (pos + 1)

/-- Pure point read `(getM t pos).ret`. -/
@[expose] def get {α : Type*} [AddCommGroup α] (t : FenwickTree α) (pos : ℕ) : α :=
  (getM t pos).ret

theorem get_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) :
    get t pos = s.getD pos 0 := by
  unfold get getM
  rw [ret_rangeSumM_eq hv]
  rcases lt_or_ge pos s.length with hlt | hge
  · have htake : s.take (pos + 1) = s.take pos ++ [s[pos]'hlt] := by
      rw [List.take_add_one, getElem?_pos s pos hlt, Option.toList_some]
    have hlen : (s.take pos).length = pos := List.length_take_of_le (Nat.le_of_lt hlt)
    rw [htake, List.drop_append_of_le_length (by rw [hlen]),
      List.drop_eq_nil_of_le (by rw [hlen]), List.nil_append, List.sum_singleton,
      List.getD_eq_getElem?_getD, getElem?_pos s pos hlt, Option.getD_some]
  · have hdrop : (s.take (pos + 1)).drop pos = [] :=
      List.drop_eq_nil_of_le ((List.length_take_le' (pos + 1) s).trans hge)
    rw [hdrop, List.sum_nil, List.getD_eq_getElem?_getD, List.getElem?_eq_none hge,
      Option.getD_none]

theorem ret_getM_eq {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) :
    (getM t pos).ret = s.getD pos 0 :=
  get_eq hv pos

theorem getM_time_le_clog {α : Type*} [AddCommGroup α] (t : FenwickTree α) (pos : ℕ) :
    (getM t pos).time ≤ 2 * Nat.clog 2 (t.size + 1) :=
  rangeSumM_time_le_clog t pos (pos + 1)

/-- Point assignment setting `s[pos] := v` (`no-op` when `t.size ≤ pos`) in `TimeM ℕ`. -/
def setM {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) : TimeM ℕ (FenwickTree α) :=
  if pos < t.tree.size then do
    let cur ← getM t pos
    addM t pos (v - cur)
  else
    return t

/-- Pure point assignment `(setM t pos v).ret`. -/
@[expose] def set {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) : FenwickTree α :=
  (setM t pos v).ret

theorem valid_set {α : Type*} [AddCommGroup α]
    {t : FenwickTree α} {s : List α} (hv : Valid t s) (pos : ℕ) (v : α) :
    Valid (set t pos v) (s.set pos v) := by
  unfold set setM
  split_ifs with hpos
  · simp only [TimeM.ret_bind, ret_getM_eq hv, ret_addM]
    have hadd := valid_add hv pos (v - s.getD pos 0)
    unfold addAt at hadd
    rwa [add_sub_cancel] at hadd
  · simp only [TimeM.ret_pure]
    have hge : s.length ≤ pos := by have := hv.1; omega
    rwa [List.set_eq_of_length_le hge]

@[simp]
theorem size_set {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) :
    (set t pos v).size = t.size := by
  unfold set setM
  split_ifs with hpos
  · simp only [TimeM.ret_bind, ret_addM, size_add]
  · simp only [TimeM.ret_pure]

theorem setM_time_le_clog {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) (pos : ℕ) (v : α) :
    (setM t pos v).time ≤ 3 * Nat.clog 2 (t.size + 1) := by
  unfold setM
  split_ifs with hpos
  · simp only [TimeM.time_bind]
    have h1 := getM_time_le_clog t pos
    have h2 := addM_time_le_clog t pos (v - (getM t pos).ret)
    omega
  · simp only [TimeM.time_pure, Nat.zero_le]

theorem set_of_size_le {α : Type*} [AddCommGroup α]
    (t : FenwickTree α) {pos : ℕ} (v : α) (h : t.size ≤ pos) :
    set t pos v = t := by
  unfold set setM
  have hnot : ¬ pos < t.tree.size := by unfold size at h; omega
  simp only [hnot, ↓reduceIte, TimeM.ret_pure]

end FenwickTree

end Cslib.Algorithms.Lean
