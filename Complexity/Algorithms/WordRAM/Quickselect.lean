/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Quicksort
import Mathlib.Data.List.Sort

/-!
# In-place randomized quickselect on the word RAM

Iterative in-place 3-way randomized quickselect over `Cslib.WordRAM.Basis.standard`. Given an
`n`-word slice starting at address `base` and a `0`-indexed target rank `k < n`, the algorithm
selects the `k`-th smallest element `input.mergeSort[k]` in place using zero auxiliary memory
words (`O(1)` registers only).

The selection loop maintains a single active subarray `[lo, hi)` of length `m = hi - lo`
containing the target address `target = base + k` (`lo ≤ target < hi`). When `2 ≤ m`, each
iteration samples a uniform pivot offset `off ← rand (m - 1)` with pivot value
`piv = mem (lo + off)` and applies Dutch National Flag 3-way partitioning to split `[lo, hi)` into
`< piv` on `[lo, lt)`, `= piv` on `[lt, gt)`, and `> piv` on `[gt, hi)`:
1. **Pathwise correctness and zero auxiliary space:** Every execution path halts cleanly and
   returns `input.mergeSort[k]`. The final memory permutes `[base, base + n)` in place so that
   `mem (base + k) = input.mergeSort[k]`, `mem (base + i) ≤ mem (base + k)` for `i < k`, and
   `mem (base + k) ≤ mem (base + i)` for `k < i < n`. All memory outside
   `Finset.Ico base (base + n)` is unchanged.
2. **Strict worst-case bounds:** Because the `= piv` region `[lt, gt)` contains the sampled pivot,
   `lt < gt` holds and each iteration strictly decreases `m = hi - lo`. Every execution path
   makes at most `n - 1` `rand` calls and executes at most `10 * n ^ 2 + 15` instructions.
3. **Unconditional linear expected running time (including duplicates):** All copies of `piv` in
   `[lo, hi)` land in `[lt, gt)`. When `lt ≤ target < gt`, the active range collapses immediately
   to length `1`; otherwise, for a sampled pivot of sorted rank `r < m` in `[lo, hi)`, the next
   active subarray has length at most `max r (m - 1 - r)`. The identity
   `4 * ∑_{r < m} max r (m - 1 - r) ≤ 3 * m ^ 2` gives a `(3 / 4)`-shrinking linear potential
   `80 * m` on the active subarray length `m`, proving
   `expectedTime w program (.init (k :: input)) ≤ 80 * n + 15` uniformly over all `k < n` and all
   duplicate-key patterns.
4. **Total out-of-range handling:** On `State.init (k :: input)` satisfying
   `InputFits w (k :: input)` with `n ≤ k`, `program` skips `selectSlice` and halts
   deterministically in `8` instructions with output `0`, `0` `rand` calls, and unchanged memory.

## Main definitions

* `Cslib.Algorithms.WordRAM.Quickselect.samplePivot`,
  `Cslib.Algorithms.WordRAM.Quickselect.narrowRange`,
  `Cslib.Algorithms.WordRAM.Quickselect.partitionAndNarrow`,
  `Cslib.Algorithms.WordRAM.Quickselect.selectStep`,
  `Cslib.Algorithms.WordRAM.Quickselect.selectSetup`,
  `Cslib.Algorithms.WordRAM.Quickselect.loadHeader`: structured building blocks of the selection
  loop and `Data.init` header.
* `Cslib.Algorithms.WordRAM.Quickselect.selectSlice`: reusable 16-register structured subroutine
  selecting rank `regs rk` in `[regs base, regs base + regs len)` in place.
* `Cslib.Algorithms.WordRAM.Quickselect.code`, `Cslib.Algorithms.WordRAM.Quickselect.program`:
  structured and compiled 16-register randomized quickselect on `State.init (k :: input)`.
* `Cslib.Algorithms.WordRAM.Quickselect.worstCaseTime`: quadratic worst-case step bound
  `10 * n ^ 2 + 15`.
* `Cslib.Algorithms.WordRAM.Quickselect.expectedTimeBound`: linear expected step bound
  `80 * n + 15`.

## Main results

* `Cslib.Algorithms.WordRAM.Quickselect.selectSlice_spec`: `ExecRandWithin` and linear
  `expectedCodeTime` specification for `selectSlice` on an arbitrary slice `[base, base + n)`.
* `Cslib.Algorithms.WordRAM.Quickselect.loadHeader_spec`,
  `Cslib.Algorithms.WordRAM.Quickselect.code_spec`,
  `Cslib.Algorithms.WordRAM.Quickselect.code_out_of_range_spec`: structured `loadHeader` and `code`
  specifications for `k < input.length` and `input.length ≤ k`.
* `Cslib.Algorithms.WordRAM.Quickselect.quickselect_correct_and_bounds`: joint certificate of
  `RandHaltsWithin`, `RandCallsBounded` (`≤ n - 1`), pathwise order-statistic output, in-place
  partition order, zero-auxiliary-memory `Modifies` frame, and `O(n)` `expectedTime` at word size
  `w ≥ logWidth 2 input.length`.
* `Cslib.Algorithms.WordRAM.Quickselect.quickselect_out_of_range`: deterministic `8`-step halting
  when `input.length ≤ k`.

Classical randomized selection (`RANDOMIZED-SELECT`) appears in [CLRS2009], Section 9.2; see also
[MitzenmacherUpfal2017], Section 3.5 (sampling-based median selection, related background). The
3-way Dutch National Flag word-RAM formulation, zero-auxiliary-memory frame, pure-`ℕ` linear drift
potential `80 * m`, and duplicate-key rank domination are original to this formalization.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 9.2.
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017], Section 3.5.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.Algorithms.WordRAM.Quickselect

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.Quicksort (memSlice length_memSlice getElem_memSlice
  mem_memSlice_iff memSlice_congr memSlice_append partition_counts_and_lt sorted_countP_bounds)

/-! ## Expected-selection linear potential recurrence -/

/-- Elementary sum bound for randomized selection: `4 * ∑_{r < m} max r (m - 1 - r) ≤ 3 * m ^ 2`
for every `m : ℕ`. -/
private theorem four_mul_sum_max_le : ∀ m : ℕ,
    4 * ∑ r ∈ Finset.range m, max r (m - 1 - r) ≤ 3 * m ^ 2
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    have ih := four_mul_sum_max_le m
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hmid : ∑ r ∈ Finset.range m, max (r + 1) (m + 2 - 1 - (r + 1)) =
        (∑ r ∈ Finset.range m, max r (m - 1 - r)) + m := by
      have hcongr : ∑ r ∈ Finset.range m, max (r + 1) (m + 2 - 1 - (r + 1)) =
          ∑ r ∈ Finset.range m, (max r (m - 1 - r) + 1) := by
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        omega
      rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        mul_one]
    have h0 : max 0 (m + 2 - 1 - 0) = m + 1 := by omega
    have hlast : max (m + 1) (m + 2 - 1 - (m + 1)) = m + 1 := by omega
    rw [hmid, h0, hlast]
    have hsq : (m + 2) ^ 2 = m ^ 2 + 4 * m + 4 := by ring
    rw [hsq]
    omega

/-- Linear expected-time potential `Φ(m) = 0` for `m < 2` and `80 * m` for `m ≥ 2`. -/
private def expSubCost (m : ℕ) : ℕ :=
  if m < 2 then 0 else 80 * m

private theorem expSubCost_of_lt_two {m : ℕ} (h : m < 2) : expSubCost m = 0 := by
  simp only [expSubCost, h, ↓reduceIte]

private theorem expSubCost_le (m : ℕ) : expSubCost m ≤ 80 * m := by
  unfold expSubCost
  split_ifs <;> omega

private theorem expSubCost_mono {a b : ℕ} (hab : a ≤ b) : expSubCost a ≤ expSubCost b := by
  unfold expSubCost
  split_ifs <;> omega

private theorem list_map_sum_nat_eq_sum_range (l : List ℕ) (g : ℕ → ℕ) :
    (l.map g).sum = ∑ r ∈ Finset.range l.length, g (l.getD r 0) := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ih]
    simp only [List.getD_cons_zero, List.getD_cons_succ, add_comm]

/-- Sum of `max (countP (· < piv)) (countP (piv < ·))` over all `m = u.length` uniform pivot
positions is bounded by `∑_{r < m} max r (m - 1 - r)`, even with duplicate keys. -/
private theorem sum_max_pivot_le (u : List ℕ) :
    ∑ k : Fin u.length,
      max (u.countP (· < u[k.val])) (u.countP (u[k.val] < ·)) ≤
        ∑ r ∈ Finset.range u.length, max r (u.length - 1 - r) := by
  have hperm : u.Perm u.mergeSort := (List.mergeSort_perm u _).symm
  have hlen : u.mergeSort.length = u.length := hperm.length_eq.symm
  let g : ℕ → ℕ := fun piv => max (u.countP (· < piv)) (u.countP (piv < ·))
  have hsum_u : ∑ k : Fin u.length, g u[k.val] = (u.map g).sum := by
    rw [Finset.sum_fin_eq_sum_range, list_map_sum_nat_eq_sum_range]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    simp only [hr, ↓reduceDIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
      Option.getD_some]
  rw [hsum_u, (hperm.map g).sum_eq, list_map_sum_nat_eq_sum_range, hlen]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [Finset.mem_range] at hr
  have hr_zs : r < u.mergeSort.length := by omega
  have hgetD : u.mergeSort.getD r 0 = u.mergeSort[r] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr_zs]
    rfl
  have hb := sorted_countP_bounds (List.pairwise_mergeSort' (· ≤ ·) u) hr_zs
  have hc1 : u.countP (· < u.mergeSort[r]) = u.mergeSort.countP (· < u.mergeSort[r]) :=
    hperm.countP_eq _
  have hc2 : u.countP (u.mergeSort[r] < ·) = u.mergeSort.countP (u.mergeSort[r] < ·) :=
    hperm.countP_eq _
  dsimp only [g]
  rw [hgetD, hc1, hc2]
  have hb1 := hb.1
  have hb2 : u.mergeSort.countP (u.mergeSort[r] < ·) ≤ u.length - 1 - r := hlen ▸ hb.2
  omega

/-! ## Order-statistic characterization and word-size bound -/

private theorem countP_ge_succ_of_prefix {l : List ℕ} {k : ℕ} (hk : k < l.length) {p : ℕ → Bool}
    (h : ∀ i (hi : i < l.length), i ≤ k → p (l[i]'hi) = true) :
    k + 1 ≤ l.countP p := by
  have hsplit : l.countP p = (l.take (k + 1)).countP p + (l.drop (k + 1)).countP p := by
    conv_lhs => rw [← List.take_append_drop (k + 1) l]
    exact List.countP_append
  have htake : (l.take (k + 1)).countP p = k + 1 := by
    rw [List.countP_eq_length.mpr]
    · simp only [List.length_take]
      omega
    · intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [List.getElem_take]
      have hi_le : i ≤ k := by simp only [List.length_take] at hi; omega
      exact h i (by omega) hi_le
  omega

private theorem countP_le_of_suffix {l : List ℕ} (k : ℕ) {p : ℕ → Bool}
    (h : ∀ i (hi : i < l.length), k ≤ i → p (l[i]'hi) = false) :
    l.countP p ≤ k := by
  have hsplit : l.countP p = (l.take k).countP p + (l.drop k).countP p := by
    conv_lhs => rw [← List.take_append_drop k l]
    exact List.countP_append
  have hdrop : (l.drop k).countP p = 0 := by
    rw [List.countP_eq_zero]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    rw [List.getElem_drop]
    have hkj : k + j < l.length := by simp only [List.length_drop] at hj; omega
    simp only [h (k + j) hkj (by omega), Bool.false_eq_true, not_false_eq_true]
  have htake : (l.take k).countP p ≤ k :=
    List.countP_le_length.trans (by simp only [List.length_take]; exact Nat.min_le_left _ _)
  omega

/-- If `xs` is a permutation of `ys` partitioned around index `k < ys.length` so that
`xs[i] ≤ xs[k]` for `i < k` and `xs[k] ≤ xs[i]` for `k < i < xs.length`, then `xs[k]` equals the
`k`-th sorted element `ys.mergeSort[k]` (regardless of duplicate keys). -/
private theorem eq_mergeSort_getElem_of_perm_of_partitioned {xs ys : List ℕ} {k : ℕ}
    (hperm : xs.Perm ys) (hk : k < ys.length)
    (hleft : ∀ i (hi : i < k),
      xs[i]'(by have := hperm.length_eq; omega) ≤ xs[k]'(by have := hperm.length_eq; omega))
    (hright : ∀ i, k < i → (hi : i < xs.length) →
      xs[k]'(by have := hperm.length_eq; omega) ≤ xs[i]'hi) :
    xs[k]'(by rw [hperm.length_eq]; exact hk) =
      ys.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) := by
  have hkx : k < xs.length := by rw [hperm.length_eq]; exact hk
  have hks : k < ys.mergeSort.length := by rw [List.length_mergeSort]; exact hk
  have hp_sort : xs.Perm ys.mergeSort := hperm.trans (List.mergeSort_perm ys _).symm
  have hp_pw := List.pairwise_iff_getElem.mp (List.pairwise_mergeSort' (· ≤ ·) ys)
  set v := xs[k]'hkx
  set s := ys.mergeSort[k]'hks
  apply Nat.le_antisymm
  · by_contra hnot
    have hlt : s < v := Nat.lt_of_not_ge hnot
    have hge_sort : k + 1 ≤ ys.mergeSort.countP (· < v) := by
      refine countP_ge_succ_of_prefix hks fun i hi hik => decide_eq_true ?_
      rcases eq_or_lt_of_le hik with rfl | hik_lt
      · exact hlt
      · exact (hp_pw i k hi hks hik_lt).trans_lt hlt
    have hle_xs : xs.countP (· < v) ≤ k := by
      refine countP_le_of_suffix k fun i hi hki => decide_eq_false (Nat.not_lt.mpr ?_)
      rcases eq_or_lt_of_le hki with rfl | hki_lt
      · exact le_rfl
      · exact hright i hki_lt hi
    have heq := hp_sort.countP_eq (· < v)
    omega
  · by_contra hnot
    have hlt : v < s := Nat.lt_of_not_ge hnot
    have hge_xs : k + 1 ≤ xs.countP (· ≤ v) := by
      refine countP_ge_succ_of_prefix hkx fun i hi hik => decide_eq_true ?_
      rcases eq_or_lt_of_le hik with rfl | hik_lt
      · exact le_rfl
      · exact hleft i hik_lt
    have hle_sort : ys.mergeSort.countP (· ≤ v) ≤ k := by
      refine countP_le_of_suffix k fun i hi hki => decide_eq_false (Nat.not_le.mpr ?_)
      rcases eq_or_lt_of_le hki with rfl | hki_lt
      · exact hlt
      · exact hlt.trans_le (hp_pw k i hks hi hki_lt)
    have heq := hp_sort.countP_eq (· ≤ v)
    omega

/-- `logWidth 2 n ≤ w` suffices to fit every address up to `n + 2` for all `n : ℕ`. -/
private theorem fits_add_two {n w : ℕ} (hw : logWidth 2 n ≤ w) :
    Fits w (n + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hw2 : 2 ≤ w := by simpa only [logWidth, Nat.log_zero_right, zero_add, mul_one] using hw
    exact Fits.mono (w := 2) (by decide) hw2
  · have hsq : n + 2 < (n + 1) ^ 2 := by
      have hexp : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
      rw [hexp]
      nlinarith
    exact (fits_of_lt_pow hsq).mono hw

/-! ## Structured WordRAM quickselect program (`r = 16`) -/

namespace Reg

/-- Output register (also `0` initially in `Data.init`). -/
@[simp] abbrev ans : Fin 16 := 0
/-- Constant `1` (`Quicksort.Reg.one`). -/
@[simp] abbrev one : Fin 16 := Quicksort.Reg.one
/-- Target `0`-indexed rank `k`. -/
@[simp] abbrev rk : Fin 16 := 2
/-- Slice length `n`. -/
@[simp] abbrev len : Fin 16 := 3
/-- Slice base address `base`. -/
@[simp] abbrev base : Fin 16 := 4
/-- Target cell address `base + k`. -/
@[simp] abbrev target : Fin 16 := 5
/-- Maintained value `lo + 1` for the loop test `lo + 1 < hi`. -/
@[simp] abbrev lo1 : Fin 16 := 6
/-- Active subarray start address `lo` (`Quicksort.Reg.lo`). -/
@[simp] abbrev lo : Fin 16 := Quicksort.Reg.lo
/-- Active subarray exclusive end address `hi` (`Quicksort.Reg.hi`). -/
@[simp] abbrev hi : Fin 16 := Quicksort.Reg.hi
/-- 3-way partition `< piv` boundary `lt` (`Quicksort.Reg.lt`). -/
@[simp] abbrev lt : Fin 16 := Quicksort.Reg.lt
/-- 3-way partition scan cursor `cur` (`Quicksort.Reg.cur`). -/
@[simp] abbrev cur : Fin 16 := Quicksort.Reg.cur
/-- 3-way partition `> piv` boundary `gt` (`Quicksort.Reg.gt`). -/
@[simp] abbrev gt : Fin 16 := Quicksort.Reg.gt
/-- Pivot value `piv` (`Quicksort.Reg.piv`). -/
@[simp] abbrev piv : Fin 16 := Quicksort.Reg.piv
/-- Element scratch `val` (`Quicksort.Reg.val`). -/
@[simp] abbrev val : Fin 16 := Quicksort.Reg.val
/-- Swap scratch `val2` (`Quicksort.Reg.val2`). -/
@[simp] abbrev val2 : Fin 16 := Quicksort.Reg.val2
/-- Offset / address scratch `tmp` (`Quicksort.Reg.tmp`). -/
@[simp] abbrev tmp : Fin 16 := Quicksort.Reg.tmp

end Reg

open Reg

/-- Sample a uniform pivot offset `tmp ← rand (hi - (lo + 1))` (`2` instructions, `1` `rand`
call). -/
def samplePivot : Code .standard 16 := ram[
  tmp ← hi - lo1;
  tmp ← rand tmp ]

/-- Narrow `[lo, hi)` (alongside `lo1 = lo + 1`) to the unique 3-way partition region containing
`target` (`≤ 6` instructions, zero `.sub`/`.div`/`.mod` operations). -/
def narrowRange : Code .standard 16 := ram[
  if target < lt then [
    hi ← lt
  ] else [
    if target < gt then [
      lo ← target;
      lo1 ← target + one;
      hi ← lo1
    ] else [
      lo ← gt;
      lo1 ← lo + one
    ]
  ] ]

/-- Partition `[lo, hi)` around the pivot at `lo + tmp` and narrow `[lo, hi)` around `target`. -/
def partitionAndNarrow : Code .standard 16 := ram[
  ⟪Quicksort.partInit⟫;
  while cur < gt do [ ⟪Quicksort.partStep⟫ ];
  ⟪narrowRange⟫ ]

/-- One iteration of the quickselect loop on `[lo, hi)` (`lo + 1 < hi`). -/
def selectStep : Code .standard 16 := ram[
  ⟪samplePivot⟫;
  ⟪partitionAndNarrow⟫ ]

/-- Deterministic `5`-instruction setup of `selectSlice`. -/
def selectSetup : Code .standard 16 := ram[
  one ← #1;
  target ← base + rk;
  lo ← base;
  lo1 ← lo + one;
  hi ← base + len ]

/-- Reusable structured in-place quickselect subroutine on `[regs base, regs base + regs len)`:
permutes the slice in place around rank `regs rk` and stores the selected element in `ans`. -/
def selectSlice : Code .standard 16 := ram[
  ⟪selectSetup⟫;
  while lo1 < hi do [ ⟪selectStep⟫ ];
  ans ← *target ]

/-- Deterministic `4`-instruction header reading `len = M[0] - 1` and `rk = M[1]` on
`Data.init (k :: input)`. -/
def loadHeader : Code .standard 16 := ram[
  len ← *ans;
  one ← #1;
  rk ← *one;
  len ← len - one ]

/-- Structured 16-register quickselect on `Data.init (k :: input)`: selects `input.mergeSort[k]`
in `[2, input.length + 2)` when `k < input.length`, and sets `ans ← 0` otherwise. -/
def code : Code .standard 16 := ram[
  ⟪loadHeader⟫;
  if rk < len then [
    base ← one + one;
    ⟪selectSlice⟫
  ] else [
    ans ← #0
  ] ]

/-- Compiled flat 16-register randomized quickselect program halting with `ans`. -/
def program : Program .standard 16 :=
  code.program ans

/-- Quadratic worst-case instruction budget `10 * n ^ 2 + 15`. -/
def worstCaseTime (n : ℕ) : ℕ :=
  10 * n ^ 2 + 15

/-- Linear expected instruction budget `80 * n + 15`. -/
def expectedTimeBound (n : ℕ) : ℕ :=
  80 * n + 15

/-! ## Selection invariant and subroutine specifications -/

/-- Cut property at address `cut` across `[vbase, vbase + n)`: every element before `cut` is at
most every element from `cut` onward. -/
private def IsCut (vbase n cut : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ a b, vbase ≤ a → a < cut → cut ≤ b → b < vbase + n → mem a ≤ mem b

/-- Outer loop invariant of `selectSlice` on `[vbase, vbase + n)` for rank `k < n`. -/
private structure SelectInv (w vbase n k : ℕ) (s₀ : List ℕ) (mem₀ : ℕ → ℕ)
    (x : Data 16) : Prop where
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `target` holds `vbase + k`. -/
  target_eq : x.regs target = vbase + k
  /-- Register `lo1` holds `lo + 1`. -/
  lo1_eq : x.regs lo1 = x.regs lo + 1
  /-- `vbase + n` fits in a `w`-bit word. -/
  fits_end : Fits w (vbase + n)
  /-- `vbase ≤ lo`. -/
  base_le_lo : vbase ≤ x.regs lo
  /-- `lo ≤ vbase + k`. -/
  lo_le_target : x.regs lo ≤ vbase + k
  /-- `vbase + k < hi`. -/
  target_lt_hi : vbase + k < x.regs hi
  /-- `hi ≤ vbase + n`. -/
  hi_le_end : x.regs hi ≤ vbase + n
  /-- `mem[vbase .. vbase + n)` is a permutation of `s₀`. -/
  perm : (memSlice vbase (vbase + n) x.mem).Perm s₀
  /-- Only `Finset.Ico vbase (vbase + n)` has been modified since `mem₀`. -/
  modifies : Modifies (Finset.Ico vbase (vbase + n)) mem₀ x.mem
  /-- `lo` is an order cut of `[vbase, vbase + n)`. -/
  cut_lo : IsCut vbase n (x.regs lo) x.mem
  /-- `hi` is an order cut of `[vbase, vbase + n)`. -/
  cut_hi : IsCut vbase n (x.regs hi) x.mem

private theorem perm_global_of_sub {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hlo : vbase ≤ vlo) (hhi : vhi ≤ vbase + n) (hle : vlo ≤ vhi)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂) :
    (memSlice vbase (vbase + n) mem₂).Perm (memSlice vbase (vbase + n) mem₁) := by
  have hdecomp : ∀ m : ℕ → ℕ, memSlice vbase (vbase + n) m =
      memSlice vbase vlo m ++ (memSlice vlo vhi m ++ memSlice vhi (vbase + n) m) := by
    intro m
    rw [memSlice_append (by omega) hhi, memSlice_append hlo hle, List.append_assoc]
  have hleft_eq : memSlice vbase vlo mem₂ = memSlice vbase vlo mem₁ :=
    memSlice_congr fun a _ ha2 => hmod a (by rw [Finset.mem_Ico]; omega)
  have hright_eq : memSlice vhi (vbase + n) mem₂ = memSlice vhi (vbase + n) mem₁ :=
    memSlice_congr fun a ha1 _ => hmod a (by rw [Finset.mem_Ico]; omega)
  rw [hdecomp mem₂, hdecomp mem₁, hleft_eq, hright_eq]
  exact List.Perm.append_left _ (hperm.append_right _)

private theorem cut_preserved_lo {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hhi : vhi ≤ vbase + n)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂)
    (hcut : IsCut vbase n vlo mem₁) :
    IsCut vbase n vlo mem₂ := by
  intro a b ha1 ha2 hb1 hb2
  have ha_eq : mem₂ a = mem₁ a := hmod a (by rw [Finset.mem_Ico]; omega)
  rw [ha_eq]
  by_cases hb_hi : b < vhi
  · have hmem₂ : mem₂ b ∈ memSlice vlo vhi mem₂ :=
      mem_memSlice_iff.mpr ⟨b, hb1, hb_hi, rfl⟩
    obtain ⟨b', hb'1, hb'2, hb'_eq⟩ := mem_memSlice_iff.mp (hperm.mem_iff.mp hmem₂)
    rw [← hb'_eq]
    exact hcut a b' ha1 ha2 hb'1 (by omega)
  · have hb_eq : mem₂ b = mem₁ b := hmod b (by rw [Finset.mem_Ico]; omega)
    rw [hb_eq]
    exact hcut a b ha1 ha2 hb1 hb2

private theorem cut_preserved_hi {vbase n vlo vhi : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hlo : vbase ≤ vlo)
    (hperm : (memSlice vlo vhi mem₂).Perm (memSlice vlo vhi mem₁))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₁ mem₂)
    (hcut : IsCut vbase n vhi mem₁) :
    IsCut vbase n vhi mem₂ := by
  intro a b ha1 ha2 hb1 hb2
  have hb_eq : mem₂ b = mem₁ b := hmod b (by rw [Finset.mem_Ico]; omega)
  rw [hb_eq]
  by_cases ha_lo : vlo ≤ a
  · have hmem₂ : mem₂ a ∈ memSlice vlo vhi mem₂ :=
      mem_memSlice_iff.mpr ⟨a, ha_lo, ha2, rfl⟩
    obtain ⟨a', ha'1, ha'2, ha'_eq⟩ := mem_memSlice_iff.mp (hperm.mem_iff.mp hmem₂)
    rw [← ha'_eq]
    exact hcut a' b (by omega) ha'2 hb1 hb2
  · have ha_eq : mem₂ a = mem₁ a := hmod a (by rw [Finset.mem_Ico]; omega)
    rw [ha_eq]
    exact hcut a b ha1 ha2 hb1 hb2

/-- Any boundary `t` inside `[vlt, vgt]` after 3-way partitioning `[vlo, vhi)` is a global cut of
`[vbase, vbase + n)`. -/
private theorem cut_of_between_lt_gt {vbase n vlo vlt vgt vhi vpiv t : ℕ} {mem : ℕ → ℕ}
    (hbnd : vlo ≤ vlt ∧ vlt ≤ t ∧ t ≤ vgt ∧ vgt ≤ vhi)
    (hcut_lo : IsCut vbase n vlo mem)
    (hcut_hi : IsCut vbase n vhi mem)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → mem a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → mem a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < mem a) :
    IsCut vbase n t mem := by
  intro a b ha1 ha2 hb1 hb2
  by_cases ha_lo : a < vlo
  · exact hcut_lo a b ha1 ha_lo (by omega) hb2
  · by_cases hb_hi : vhi ≤ b
    · exact hcut_hi a b ha1 (by omega) hb_hi hb2
    · have ha_le : mem a ≤ vpiv := by
        by_cases ha_lt : a < vlt
        · exact Nat.le_of_lt (hlt_z a (by omega) ha_lt)
        · exact Nat.le_of_eq (heq_z a (by omega) (by omega))
      have hb_ge : vpiv ≤ mem b := by
        by_cases hb_gt : b < vgt
        · exact Nat.le_of_eq (heq_z b (by omega) hb_gt).symm
        · exact Nat.le_of_lt (hgt_z b (by omega) (by omega))
      exact ha_le.trans hb_ge

/-- Deterministic execution of `narrowRange` after 3-way partition exit (`≤ 6` steps). -/
private theorem narrowRange_spec {w vbase n k vlo vlt vgt vhi vpiv : ℕ}
    {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hone : x.regs one = 1) (htarget : x.regs target = vbase + k)
    (hlo : x.regs lo = vlo) (hlo1 : x.regs lo1 = vlo + 1) (hhi : x.regs hi = vhi)
    (hlt_r : x.regs lt = vlt) (hgt_r : x.regs gt = vgt)
    (hfit : Fits w (vbase + n))
    (hbase_lo : vbase ≤ vlo) (hlo_t : vlo ≤ vbase + k)
    (ht_hi : vbase + k < vhi) (hhi_end : vhi ≤ vbase + n)
    (hlg : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi)
    (hperm : (memSlice vbase (vbase + n) x.mem).Perm s₀)
    (hmod : Modifies (Finset.Ico vbase (vbase + n)) mem₀ x.mem)
    (hcut_lo : IsCut vbase n vlo x.mem) (hcut_hi : IsCut vbase n vhi x.mem)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → x.mem a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → x.mem a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < x.mem a) :
    ∃ y t_nr, Exec w narrowRange x y t_nr ∧ t_nr ≤ 6 ∧
      SelectInv w vbase n k s₀ mem₀ y ∧
      (y.regs hi - y.regs lo = vlt - vlo ∨
       y.regs hi - y.regs lo = 1 ∨
       y.regs hi - y.regs lo = vhi - vgt) := by
  by_cases hc1 : vbase + k < vlt
  · have hc1_holds : (Cond.lt target lt).Holds x := by
      simp only [Cond.holds_lt, htarget, hlt_r]; exact hc1
    set y := x.set hi vlt
    have e_hi : Exec (B := .standard) w (.op (.copy hi lt)) x y 1 := by
      simpa only [y, hlt_r] using Exec.copy (w := w) (d := hi) (s := lt) (x := x)
    have e_nr : Exec w narrowRange x y 2 := e_hi.branch_pos hc1_holds
    have hcut_vlt : IsCut vbase n vlt x.mem :=
      cut_of_between_lt_gt ⟨hlg.1, le_rfl, Nat.le_of_lt hlg.2.1, hlg.2.2⟩
        hcut_lo hcut_hi hlt_z heq_z hgt_z
    refine ⟨y, 2, e_nr, by omega, ?_, Or.inl (by simp only [y, Data.set_regs,
      Function.update_self, Function.update_of_ne (by decide : lo ≠ hi), hlo])⟩
    exact ⟨by simp only [y, Data.set_regs, Function.update_of_ne (by decide : one ≠ hi), hone],
      by simp only [y, Data.set_regs, Function.update_of_ne (by decide : target ≠ hi), htarget],
      by simp only [y, Data.set_regs, Function.update_of_ne (by decide : lo1 ≠ hi),
        Function.update_of_ne (by decide : lo ≠ hi), hlo1, hlo],
      hfit,
      by simp only [y, Data.set_regs, Function.update_of_ne (by decide : lo ≠ hi), hlo]; omega,
      by simp only [y, Data.set_regs, Function.update_of_ne (by decide : lo ≠ hi), hlo]; omega,
      by simp only [y, Data.set_regs, Function.update_self]; exact hc1,
      by simp only [y, Data.set_regs, Function.update_self]; omega,
      hperm, hmod,
      by simpa only [y, Data.set_mem, Data.set_regs,
        Function.update_of_ne (by decide : lo ≠ hi), hlo] using hcut_lo,
      by simpa only [y, Data.set_mem, Data.set_regs, Function.update_self] using hcut_vlt⟩
  · have hc1_neg : ¬(Cond.lt target lt).Holds x := by
      simp only [Cond.holds_lt, htarget, hlt_r]; exact hc1
    by_cases hc2 : vbase + k < vgt
    · have hc2_holds : (Cond.lt target gt).Holds x := by
        simp only [Cond.holds_lt, htarget, hgt_r]; exact hc2
      set s₁ := x.set lo (vbase + k)
      set s₂ := s₁.set lo1 (vbase + k + 1)
      set y := s₂.set hi (vbase + k + 1)
      have e₁ : Exec (B := .standard) w (.op (.copy lo target)) x s₁ 1 := by
        simpa only [s₁, htarget] using Exec.copy (w := w) (d := lo) (s := target) (x := x)
      have e₂ : Exec w (.op (.bin .add lo1 target one)) s₁ s₂ 1 := by
        have ht₁ : s₁.regs target = vbase + k := by
          simp only [s₁, Data.set_regs, Function.update_of_ne (by decide : target ≠ lo), htarget]
        have ho₁ : s₁.regs one = 1 := by
          simp only [s₁, Data.set_regs, Function.update_of_ne (by decide : one ≠ lo), hone]
        simpa only [s₂, ht₁, ho₁, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := lo1)
          (i := target) (j := one) (x := s₁)
          (hfit.of_le (by simp only [ht₁, ho₁, BinOp.eval]; omega))
      have e₃ : Exec (B := .standard) w (.op (.copy hi lo1)) s₂ y 1 := by
        have hl₂ : s₂.regs lo1 = vbase + k + 1 := by simp only [s₂, Data.set_regs,
          Function.update_self]
        simpa only [y, hl₂] using Exec.copy (w := w) (d := hi) (s := lo1) (x := s₂)
      have e_nr : Exec w narrowRange x y 6 :=
        ((e₁.seq (e₂.seq e₃)).branch_pos hc2_holds).branch_neg hc1_neg
      have hcut_t : IsCut vbase n (vbase + k) x.mem :=
        cut_of_between_lt_gt ⟨hlg.1, by omega, by omega, hlg.2.2⟩
          hcut_lo hcut_hi hlt_z heq_z hgt_z
      have hcut_t1 : IsCut vbase n (vbase + k + 1) x.mem :=
        cut_of_between_lt_gt ⟨hlg.1, by omega, by omega, hlg.2.2⟩
          hcut_lo hcut_hi hlt_z heq_z hgt_z
      have hy_lo : y.regs lo = vbase + k := by
        simp only [y, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : lo ≠ hi),
          Function.update_of_ne (by decide : lo ≠ lo1), Function.update_self]
      have hy_hi : y.regs hi = vbase + k + 1 := by
        simp only [y, Data.set_regs, Function.update_self]
      refine ⟨y, 6, e_nr, le_rfl, ?_, Or.inr (Or.inl (by rw [hy_hi, hy_lo]; omega))⟩
      exact ⟨by simp only [y, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : one ≠ hi),
          Function.update_of_ne (by decide : one ≠ lo1),
          Function.update_of_ne (by decide : one ≠ lo), hone],
        by simp only [y, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : target ≠ hi),
          Function.update_of_ne (by decide : target ≠ lo1),
          Function.update_of_ne (by decide : target ≠ lo), htarget],
        by simp only [y, s₂, Data.set_regs, Function.update_of_ne (by decide : lo1 ≠ hi),
          Function.update_self, hy_lo],
        hfit,
        by rw [hy_lo]; omega,
        by rw [hy_lo],
        by rw [hy_hi]; omega,
        by rw [hy_hi]; omega,
        hperm, hmod,
        by rw [hy_lo]; exact hcut_t,
        by rw [hy_hi]; exact hcut_t1⟩
    · have hc2_neg : ¬(Cond.lt target gt).Holds x := by
        simp only [Cond.holds_lt, htarget, hgt_r]; exact hc2
      set s₁ := x.set lo vgt
      set y := s₁.set lo1 (vgt + 1)
      have e₁ : Exec (B := .standard) w (.op (.copy lo gt)) x s₁ 1 := by
        simpa only [s₁, hgt_r] using Exec.copy (w := w) (d := lo) (s := gt) (x := x)
      have e₂ : Exec w (.op (.bin .add lo1 lo one)) s₁ y 1 := by
        have hl₁ : s₁.regs lo = vgt := by simp only [s₁, Data.set_regs, Function.update_self]
        have ho₁ : s₁.regs one = 1 := by
          simp only [s₁, Data.set_regs, Function.update_of_ne (by decide : one ≠ lo), hone]
        simpa only [y, hl₁, ho₁, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := lo1)
          (i := lo) (j := one) (x := s₁)
          (hfit.of_le (by simp only [hl₁, ho₁, BinOp.eval]; omega))
      have e_nr : Exec w narrowRange x y 6 :=
        ((e₁.seq e₂).branch_neg hc2_neg).branch_neg hc1_neg
      have hcut_vgt : IsCut vbase n vgt x.mem :=
        cut_of_between_lt_gt ⟨hlg.1, Nat.le_of_lt hlg.2.1, le_rfl, hlg.2.2⟩
          hcut_lo hcut_hi hlt_z heq_z hgt_z
      have hy_lo : y.regs lo = vgt := by
        simp only [y, s₁, Data.set_regs, Function.update_of_ne (by decide : lo ≠ lo1),
          Function.update_self]
      have hy_hi : y.regs hi = vhi := by
        simp only [y, s₁, Data.set_regs, Function.update_of_ne (by decide : hi ≠ lo1),
          Function.update_of_ne (by decide : hi ≠ lo), hhi]
      refine ⟨y, 6, e_nr, le_rfl, ?_, Or.inr (Or.inr (by rw [hy_hi, hy_lo]))⟩
      exact ⟨by simp only [y, s₁, Data.set_regs, Function.update_of_ne (by decide : one ≠ lo1),
          Function.update_of_ne (by decide : one ≠ lo), hone],
        by simp only [y, s₁, Data.set_regs, Function.update_of_ne (by decide : target ≠ lo1),
          Function.update_of_ne (by decide : target ≠ lo), htarget],
        by simp only [y, Data.set_regs, Function.update_self, hy_lo],
        hfit,
        by rw [hy_lo]; omega,
        by rw [hy_lo]; omega,
        by rw [hy_hi]; exact ht_hi,
        by rw [hy_hi]; exact hhi_end,
        hperm, hmod,
        by rw [hy_lo]; exact hcut_vgt,
        by rw [hy_hi]; exact hcut_hi⟩

/-- Deterministic specification of `partitionAndNarrow` for a sampled pivot offset
`off : Fin (x.regs hi - x.regs lo)` when `2 ≤ x.regs hi - x.regs lo`
(`≤ 11 * (x.regs hi - x.regs lo) + 13` steps). -/
private theorem partitionAndNarrow_spec {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hm2 : 2 ≤ x.regs hi - x.regs lo)
    (off : Fin (x.regs hi - x.regs lo)) (htmp : x.regs tmp = off.val) :
    ∃ y t_pn, Exec w partitionAndNarrow x y t_pn ∧
      t_pn ≤ 11 * (x.regs hi - x.regs lo) + 13 ∧
      SelectInv w vbase n k s₀ mem₀ y ∧
      let u := memSlice (x.regs lo) (x.regs hi) x.mem
      let pivVal := u[off.val]'(by rw [length_memSlice]; exact off.isLt)
      (y.regs hi - y.regs lo = u.countP (· < pivVal) ∨
       y.regs hi - y.regs lo = 1 ∨
       y.regs hi - y.regs lo = u.countP (pivVal < ·)) ∧
      y.regs hi - y.regs lo < x.regs hi - x.regs lo := by
  let vlo := x.regs lo
  let vhi := x.regs hi
  have hoff_lt : off.val < vhi - vlo := off.isLt
  have hfit_end := hI.fits_end
  have hhi_end := hI.hi_le_end
  have hbase_lo := hI.base_le_lo
  -- 1. Execute `Quicksort.partInit` (`5` steps)
  let vpiv := x.mem (vlo + off.val)
  let i₁ := x.set tmp (vlo + off.val)
  let i₂ := i₁.set piv vpiv
  let i₃ := i₂.set lt vlo
  let i₄ := i₃.set cur vlo
  let p₀ := i₄.set gt vhi
  have ei₁ : Exec w (.op (.bin .add tmp lo tmp)) x i₁ 1 := by
    simpa only [i₁, vlo, htmp, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := tmp)
      (i := lo) (j := tmp) (x := x)
      (hfit_end.of_le (by simp only [htmp, BinOp.eval]; omega))
  have ei₂ : Exec (B := .standard) w (.op (.load piv tmp)) i₁ i₂ 1 := by
    have ht₁ : i₁.regs tmp = vlo + off.val := by simp only [i₁, Data.set_regs, Function.update_self]
    simpa only [i₂, vpiv, ht₁, i₁, Data.set_mem] using
      Exec.load (w := w) (d := piv) (a := tmp) (x := i₁)
  have ei₃ : Exec (B := .standard) w (.op (.copy lt lo)) i₂ i₃ 1 := by
    have hl₂ : i₂.regs lo = vlo := by
      simp only [i₂, i₁, Data.set_regs, Function.update_of_ne (by decide : lo ≠ piv),
        Function.update_of_ne (by decide : lo ≠ tmp)]
      rfl
    simpa only [i₃, hl₂] using Exec.copy (w := w) (d := lt) (s := lo) (x := i₂)
  have ei₄ : Exec (B := .standard) w (.op (.copy cur lo)) i₃ i₄ 1 := by
    have hl₃ : i₃.regs lo = vlo := by
      simp only [i₃, i₂, i₁, Data.set_regs, Function.update_of_ne (by decide : lo ≠ lt),
        Function.update_of_ne (by decide : lo ≠ piv),
        Function.update_of_ne (by decide : lo ≠ tmp)]
      rfl
    simpa only [i₄, hl₃] using Exec.copy (w := w) (d := cur) (s := lo) (x := i₃)
  have ei₅ : Exec (B := .standard) w (.op (.copy gt hi)) i₄ p₀ 1 := by
    have hh₄ : i₄.regs hi = vhi := by
      simp only [i₄, i₃, i₂, i₁, Data.set_regs, Function.update_of_ne (by decide : hi ≠ cur),
        Function.update_of_ne (by decide : hi ≠ lt),
        Function.update_of_ne (by decide : hi ≠ piv),
        Function.update_of_ne (by decide : hi ≠ tmp)]
      rfl
    simpa only [p₀, hh₄] using Exec.copy (w := w) (d := gt) (s := hi) (x := i₄)
  have e_init : Exec w Quicksort.partInit x p₀ 5 :=
    ei₁.seq (ei₂.seq (ei₃.seq (ei₄.seq ei₅)))
  -- 2. Establish `Quicksort.PartInv` at `p₀` and run `Quicksort.partLoop_spec`
  have hp₀_inv : Quicksort.PartInv w vlo vhi vpiv p₀.mem p₀ :=
    ⟨(e_init.regs_eq (by decide)).trans hI.one_eq,
     e_init.regs_eq (by decide),
     e_init.regs_eq (by decide),
     by simp only [p₀, i₄, i₃, i₂, Data.set_regs, Function.update_of_ne (by decide : piv ≠ gt),
       Function.update_of_ne (by decide : piv ≠ cur),
       Function.update_of_ne (by decide : piv ≠ lt), Function.update_self],
     hfit_end.of_le hhi_end,
     by simp only [p₀, i₄, i₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ gt),
       Function.update_of_ne (by decide : lt ≠ cur), Function.update_self, le_rfl],
     by simp only [p₀, i₄, i₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ gt),
       Function.update_of_ne (by decide : lt ≠ cur),
       Function.update_of_ne (by decide : cur ≠ gt), Function.update_self, le_rfl],
     by simp only [p₀, i₄, Data.set_regs, Function.update_of_ne (by decide : cur ≠ gt),
       Function.update_self]; omega,
     by simp only [p₀, Data.set_regs, Function.update_self, le_rfl],
     List.Perm.refl _,
     Modifies.refl _ _,
     fun a ha1 ha2 => by
       simp only [p₀, i₄, i₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ gt),
         Function.update_of_ne (by decide : lt ≠ cur), Function.update_self] at ha2
       omega,
     fun a ha1 ha2 => by
       simp only [p₀, i₄, i₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ gt),
         Function.update_of_ne (by decide : lt ≠ cur),
         Function.update_of_ne (by decide : cur ≠ gt), Function.update_self] at ha1 ha2
       omega,
     fun a ha1 ha2 => by
       simp only [p₀, Data.set_regs, Function.update_self] at ha1
       omega⟩
  obtain ⟨y_p, ⟨t_loop, ht_loop, e_loop⟩, hIp, hcg_eq⟩ := Quicksort.partLoop_spec hp₀_inv
    (by simp only [p₀, i₄, i₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ gt),
      Function.update_of_ne (by decide : lt ≠ cur), Function.update_self])
    (by simp only [p₀, i₄, Data.set_regs, Function.update_of_ne (by decide : cur ≠ gt),
      Function.update_self])
    (by simp only [p₀, Data.set_regs, Function.update_self])
  have hp₀_mem : p₀.mem = x.mem := rfl
  rw [hp₀_mem] at hIp
  have htarget_yp : y_p.regs target = vbase + k :=
    (e_loop.regs_eq (by decide)).trans ((e_init.regs_eq (by decide)).trans hI.target_eq)
  have hlo1_yp : y_p.regs lo1 = vlo + 1 :=
    (e_loop.regs_eq (by decide)).trans ((e_init.regs_eq (by decide)).trans hI.lo1_eq)
  let vlt := y_p.regs lt
  let vgt := y_p.regs gt
  have heq_zone_gt : ∀ a, vlt ≤ a → a < vgt → y_p.mem a = vpiv := by
    intro a ha1 ha2
    exact hIp.eq_zone a ha1 (by rw [hcg_eq]; exact ha2)
  have hpiv_in : vpiv ∈ memSlice vlo vhi x.mem :=
    mem_memSlice_iff.mpr ⟨vlo + off.val, by omega, by omega, rfl⟩
  have hbounds_p : vlo ≤ vlt ∧ vlt ≤ vgt ∧ vgt ≤ vhi :=
    ⟨hIp.lo_le_lt, hIp.lt_le_cur.trans_eq hcg_eq, hIp.gt_le_hi⟩
  obtain ⟨hlt_gt, hcnt_lt, hcnt_gt⟩ :=
    partition_counts_and_lt hbounds_p hIp.perm hIp.lt_zone heq_zone_gt hIp.gt_zone hpiv_in
  have hperm_yp : (memSlice vbase (vbase + n) y_p.mem).Perm s₀ :=
    (perm_global_of_sub hbase_lo hhi_end (by omega) hIp.perm hIp.modifies).trans hI.perm
  have hmod_yp : Modifies (Finset.Ico vbase (vbase + n)) mem₀ y_p.mem := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have ha_sub : a ∉ Finset.Ico vlo vhi := by rw [Finset.mem_Ico]; omega
    exact (hIp.modifies a ha_sub).trans (hI.modifies a (by rw [Finset.mem_Ico]; exact ha))
  have hcut_lo_yp : IsCut vbase n vlo y_p.mem :=
    cut_preserved_lo hhi_end hIp.perm hIp.modifies hI.cut_lo
  have hcut_hi_yp : IsCut vbase n vhi y_p.mem :=
    cut_preserved_hi hbase_lo hIp.perm hIp.modifies hI.cut_hi
  -- 3. Execute `narrowRange` (`≤ 6` steps)
  obtain ⟨y, t_nr, e_nr, ht_nr, hIy, hcases⟩ := narrowRange_spec
    hIp.one_eq htarget_yp hIp.lo_eq hlo1_yp hIp.hi_eq rfl rfl
    hfit_end hbase_lo hI.lo_le_target hI.target_lt_hi hhi_end
    ⟨hbounds_p.1, hlt_gt, hbounds_p.2.2⟩
    hperm_yp hmod_yp hcut_lo_yp hcut_hi_yp hIp.lt_zone heq_zone_gt hIp.gt_zone
  have e_all : Exec w partitionAndNarrow x y (5 + (t_loop + t_nr)) :=
    e_init.seq (e_loop.seq e_nr)
  have hu_get : (memSlice vlo vhi x.mem)[off.val]'(by rw [length_memSlice]; exact off.isLt) =
      vpiv := getElem_memSlice off.isLt
  refine ⟨y, 5 + (t_loop + t_nr), e_all, by dsimp only [vhi, vlo] at ht_loop; omega, hIy, ?_, ?_⟩
  · rw [hu_get, ← hcnt_lt, ← hcnt_gt]
    exact hcases
  · have hlo_lt : vlo ≤ vlt := hbounds_p.1
    have hgt_hi : vgt ≤ vhi := hbounds_p.2.2
    dsimp only [vlo, vhi, vlt, vgt, lt, gt, Quicksort.Reg.lt, Quicksort.Reg.gt]
      at hlo_lt hgt_hi hlt_gt hcases hm2 ⊢
    rcases hcases with h1 | h2 | h3 <;> omega

/-- Randomized specification of `selectStep` when `lo1 < hi` holds (`2 ≤ hi - lo`). -/
private theorem selectStep_spec {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ (y : Fin (x.regs hi - x.regs lo - 1 + 1) → Data 16)
      (t : Fin (x.regs hi - x.regs lo - 1 + 1) → ℕ),
      ExecRand w selectStep x
        ((fun off => (y off, 2 + t off)) <$> ProbComp.unifFin (x.regs hi - x.regs lo - 1)) ∧
      ∀ off : Fin (x.regs hi - x.regs lo - 1 + 1),
        t off ≤ 11 * (x.regs hi - x.regs lo) + 13 ∧
        SelectInv w vbase n k s₀ mem₀ (y off) ∧
        (let u := memSlice (x.regs lo) (x.regs hi) x.mem
         let pivVal := u[off.val]'(by
           rw [length_memSlice]
           have hlt : x.regs lo1 < x.regs hi := by simpa only [Cond.holds_lt] using hc
           rw [hI.lo1_eq] at hlt
           have := off.isLt
           omega)
         ((y off).regs hi - (y off).regs lo = u.countP (· < pivVal) ∨
          (y off).regs hi - (y off).regs lo = 1 ∨
          (y off).regs hi - (y off).regs lo = u.countP (pivVal < ·))) ∧
        (y off).regs hi - (y off).regs lo < x.regs hi - x.regs lo := by
  have hm2 : 2 ≤ x.regs hi - x.regs lo := by
    have hlt : x.regs lo1 < x.regs hi := by simpa only [Cond.holds_lt] using hc
    rw [hI.lo1_eq] at hlt; omega
  let vlo := x.regs lo
  let vhi := x.regs hi
  let s₁ := x.set tmp (vhi - vlo - 1)
  have hsub_eq : vhi - (vlo + 1) = vhi - vlo - 1 := by omega
  have esub : Exec w (.op (.bin .sub tmp hi lo1)) x s₁ 1 := by
    have hhi_le := hI.hi_le_end
    simpa only [s₁, vhi, hI.lo1_eq, vlo, BinOp.eval, hsub_eq] using
      Exec.bin (w := w) (f := .sub) (d := tmp) (i := hi) (j := lo1) (x := x)
        (hI.fits_end.of_le (by simp only [hI.lo1_eq, BinOp.eval]; omega))
  have hs₁_tmp : s₁.regs tmp = vhi - vlo - 1 := by
    simp only [s₁, Data.set_regs, Function.update_self]
  have hfit_rand : Fits w (s₁.regs tmp) :=
    hI.fits_end.of_le (by rw [hs₁_tmp]; have := hI.hi_le_end; omega)
  have erand : ExecRand (B := .standard) w (.rand tmp tmp) s₁
      (do
        let off ← ProbComp.unifFin (vhi - vlo - 1)
        pure (s₁.set tmp off.val, 1)) := by
    rw [← hs₁_tmp]
    exact ExecRand.rand hfit_rand
  have esamp_raw := esub.seqRand erand
  have hsamp_eq :
      ((fun z : Data 16 × ℕ => (z.1, 1 + z.2)) <$> (do
        let off ← ProbComp.unifFin (vhi - vlo - 1)
        pure (s₁.set tmp off.val, 1))) =
      ((fun off : Fin (vhi - vlo - 1 + 1) => (x.set tmp off.val, 2)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine congrArg (ProbComp.unifFin (vhi - vlo - 1) >>= ·) (funext fun off => ?_)
    refine congrArg pure (Prod.ext (Data.ext ?_ rfl) rfl)
    simp only [s₁, Data.set_regs, Function.update_idem]
  rw [hsamp_eq] at esamp_raw
  have hpn_all : ∀ off : Fin (vhi - vlo - 1 + 1),
      ∃ y t_pn, Exec w partitionAndNarrow (x.set tmp off.val) y t_pn ∧
        t_pn ≤ 11 * (vhi - vlo) + 13 ∧
        SelectInv w vbase n k s₀ mem₀ y ∧
        (let u := memSlice vlo vhi x.mem
         let pivVal := u[off.val]'(by rw [length_memSlice]; have := off.isLt; omega)
         (y.regs hi - y.regs lo = u.countP (· < pivVal) ∨
          y.regs hi - y.regs lo = 1 ∨
          y.regs hi - y.regs lo = u.countP (pivVal < ·))) ∧
        y.regs hi - y.regs lo < vhi - vlo := by
    intro off
    have hI_off : SelectInv w vbase n k s₀ mem₀ (x.set tmp off.val) :=
      ⟨hI.one_eq, hI.target_eq, hI.lo1_eq, hI.fits_end, hI.base_le_lo, hI.lo_le_target,
       hI.target_lt_hi, hI.hi_le_end, hI.perm, hI.modifies, hI.cut_lo, hI.cut_hi⟩
    have hhi_set : (x.set tmp off.val).regs hi = vhi := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : hi ≠ tmp)]
      rfl
    have hlo_set : (x.set tmp off.val).regs lo = vlo := by
      simp only [Data.set_regs, Function.update_of_ne (by decide : lo ≠ tmp)]
      rfl
    obtain ⟨y, t_pn, hex, ht, hIy, hcases, hlt_m⟩ :=
      partitionAndNarrow_spec hI_off (by rw [hhi_set, hlo_set]; exact hm2)
        ⟨off.val, by rw [hhi_set, hlo_set]; have := off.isLt; omega⟩
        (by simp only [Data.set_regs, Function.update_self])
    simp only [hhi_set, hlo_set, Data.set_mem] at ht hcases hlt_m
    exact ⟨y, t_pn, hex, ht, hIy, hcases, hlt_m⟩
  choose y t hspec using hpn_all
  refine ⟨y, t, ?_, fun off => (hspec off).2⟩
  let m₂_fn : Data 16 → ProbComp (Data 16 × ℕ) := fun d =>
    if h : d.regs tmp < vhi - vlo - 1 + 1 then
      pure (y ⟨d.regs tmp, h⟩, t ⟨d.regs tmp, h⟩)
    else pure (d, 0)
  have hseq := ExecRand.seq esamp_raw (m₂ := m₂_fn) fun z hz => by
    obtain ⟨off, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hreg : (x.set tmp off.val).regs tmp = off.val := by
      simp only [Data.set_regs, Function.update_self]
    dsimp only [m₂_fn]
    simp only [hreg, off.isLt, ↓reduceDIte]
    exact (hspec off).1.execRand
  have hm_eq : (do
      let z₁ ← (fun off : Fin (vhi - vlo - 1 + 1) => (x.set tmp off.val, 2)) <$>
        ProbComp.unifFin (vhi - vlo - 1)
      let z₂ ← m₂_fn z₁.1
      pure (z₂.1, z₁.2 + z₂.2)) =
      ((fun off : Fin (vhi - vlo - 1 + 1) => (y off, 2 + t off)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine congrArg (ProbComp.unifFin (vhi - vlo - 1) >>= ·) (funext fun off => ?_)
    have hreg : (x.set tmp off.val).regs tmp = off.val := by
      simp only [Data.set_regs, Function.update_self]
    dsimp only [m₂_fn]
    simp only [hreg, off.isLt, ↓reduceDIte, pure_bind]
  rw [selectStep, ← hm_eq]
  exact hseq

/-- Quadratic worst-case potential `0` for `m < 2` and `10 * m ^ 2` for `m ≥ 2`. -/
private def stepPotential (x : Data 16) : ℕ :=
  let m := x.regs hi - x.regs lo
  if m < 2 then 0 else 10 * m ^ 2

/-- `rand`-call potential `hi - lo - 1`. -/
private def callPotential (x : Data 16) : ℕ :=
  x.regs hi - x.regs lo - 1

/-- Linear expected-time potential `(expSubCost (hi - lo) : ℝ≥0∞)`. -/
private def expPotential (x : Data 16) : ℝ≥0∞ :=
  (expSubCost (x.regs hi - x.regs lo) : ℝ≥0∞)

private theorem selectStep_worstCase {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ T_b R_b, ExecRandWithin w selectStep x
      (fun y => SelectInv w vbase n k s₀ mem₀ y ∧
        T_b + 2 + stepPotential y ≤ stepPotential x ∧
        R_b + callPotential y ≤ callPotential x) T_b R_b := by
  have hm2 : 2 ≤ x.regs hi - x.regs lo := by
    have hlt : x.regs lo1 < x.regs hi := by simpa only [Cond.holds_lt] using hc
    rw [hI.lo1_eq] at hlt; omega
  obtain ⟨y, t, hexec, hspec⟩ := selectStep_spec hI hc
  let m := x.regs hi - x.regs lo
  refine ⟨11 * m + 15, 1, ⟨_, hexec, ?_, ?_⟩⟩
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbComp.isQueryBounded_unifFin (m - 1))
  · intro z hz
    obtain ⟨off, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    dsimp only
    obtain ⟨ht_le, hIy, -, hm_lt⟩ := hspec off
    let m' := (y off).regs hi - (y off).regs lo
    have hstep_le : (11 * m + 15) + 2 + stepPotential (y off) ≤ stepPotential x := by
      have hpot_x : stepPotential x = 10 * m ^ 2 := by
        change (if m < 2 then 0 else 10 * m ^ 2) = 10 * m ^ 2
        split_ifs <;> omega
      rw [hpot_x]
      by_cases hm'2 : m' < 2
      · have hpot_y : stepPotential (y off) = 0 := by
          change (if m' < 2 then 0 else 10 * m' ^ 2) = 0
          simp only [hm'2, ↓reduceIte]
        rw [hpot_y]
        have hsq : 4 ≤ m ^ 2 := by nlinarith
        nlinarith
      · have hpot_y : stepPotential (y off) = 10 * m' ^ 2 := by
          change (if m' < 2 then 0 else 10 * m' ^ 2) = 10 * m' ^ 2
          simp only [hm'2, ↓reduceIte]
        rw [hpot_y]
        have hm3 : 3 ≤ m := by omega
        obtain ⟨d, hd⟩ : ∃ d, m = d + 3 := ⟨m - 3, by omega⟩
        have hm'_sq : m' ^ 2 ≤ (d + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        rw [hd]
        nlinarith
    have hcall_le : 1 + callPotential (y off) ≤ callPotential x := by
      simp only [callPotential]; omega
    exact ⟨⟨hIy, hstep_le, hcall_le⟩, by omega⟩

private theorem selectStep_drift {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : SelectInv w vbase n k s₀ mem₀ x) (hc : (Cond.lt lo1 hi).Holds x) :
    ∃ mb, ExecRand w selectStep x mb ∧
      (∀ z ∈ mb.support,
        SelectInv w vbase n k s₀ mem₀ z.1 ∧ callPotential z.1 < callPotential x) ∧
      ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + expPotential z.1) ≤ expPotential x := by
  have hm2 : 2 ≤ x.regs hi - x.regs lo := by
    have hlt : x.regs lo1 < x.regs hi := by simpa only [Cond.holds_lt] using hc
    rw [hI.lo1_eq] at hlt; omega
  obtain ⟨y, t, hexec, hspec⟩ := selectStep_spec hI hc
  let m := x.regs hi - x.regs lo
  have hm_eq : x.regs hi - x.regs lo - 1 + 1 = m := by omega
  refine ⟨_, hexec, ?_, ?_⟩
  · intro z hz
    obtain ⟨off, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    dsimp only
    obtain ⟨-, hIy, -, hm_lt⟩ := hspec off
    refine ⟨hIy, ?_⟩
    simp only [callPotential]
    omega
  · rw [ProbComp.expect_map, ProbComp.expect_unifFin]
    dsimp only
    let u := memSlice (x.regs lo) (x.regs hi) x.mem
    have hlen_u : u.length = m := length_memSlice _ _ _
    have hterm_nat : ∀ off : Fin (x.regs hi - x.regs lo - 1 + 1),
        (2 + t off) + 2 + expSubCost ((y off).regs hi - (y off).regs lo) ≤
          20 * m + 80 *
            max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
                (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·)) := by
      intro off
      obtain ⟨ht_le, -, hcases, -⟩ := hspec off
      let m₁ := u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega))
      let m₂ := u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·)
      have hcost_le : expSubCost ((y off).regs hi - (y off).regs lo) ≤ 80 * max m₁ m₂ := by
        rcases hcases with h1 | h2 | h3
        · rw [h1]
          exact (expSubCost_mono (le_max_left m₁ m₂)).trans (expSubCost_le _)
        · rw [h2, expSubCost_of_lt_two (by omega)]
          exact Nat.zero_le _
        · rw [h3]
          exact (expSubCost_mono (le_max_right m₁ m₂)).trans (expSubCost_le _)
      omega
    have hsum_nat :
        ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
          ((2 + t off) + 2 + expSubCost ((y off).regs hi - (y off).regs lo)) ≤
        expSubCost m * m := by
      have hfin_eq :
          ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
            max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
                (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·)) =
          ∑ off : Fin u.length,
            max (u.countP (· < u[off.val])) (u.countP (u[off.val] < ·)) :=
        Fintype.sum_equiv (finCongr (hm_eq.trans hlen_u.symm)) _ _ fun _ => rfl
      have hpiv_le :
          ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
            max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
                (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·)) ≤
          ∑ r ∈ Finset.range m, max r (m - 1 - r) := by
        rw [hfin_eq]
        simpa only [hlen_u] using sum_max_pivot_le u
      have hfour := four_mul_sum_max_le m
      calc
        ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
            ((2 + t off) + 2 + expSubCost ((y off).regs hi - (y off).regs lo))
          ≤ ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
              (20 * m + 80 *
                max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
                    (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·))) :=
            Finset.sum_le_sum fun off _ => hterm_nat off
        _ = (x.regs hi - x.regs lo - 1 + 1) * (20 * m) +
              80 * ∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
                max (u.countP (· < u[off.val]'(by rw [hlen_u]; have := off.isLt; omega)))
                    (u.countP (u[off.val]'(by rw [hlen_u]; have := off.isLt; omega) < ·)) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, Finset.mul_sum]
        _ ≤ m * (20 * m) + 80 * ∑ r ∈ Finset.range m, max r (m - 1 - r) :=
            Nat.add_le_add (by rw [hm_eq]) (Nat.mul_le_mul_left 80 hpiv_le)
        _ ≤ 80 * m * m := by nlinarith
        _ = expSubCost m * m := by
            change 80 * m * m = (if m < 2 then 0 else 80 * m) * m
            split_ifs <;> omega
    have hnum_eq :
        (∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
          (((2 + t off : ℕ) : ℝ≥0∞) + 2 + expPotential (y off))) =
        ((∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
          ((2 + t off) + 2 + expSubCost ((y off).regs hi - (y off).regs lo)) : ℕ) : ℝ≥0∞) := by
      unfold expPotential
      push_cast
      rfl
    have hden_eq : (((x.regs hi - x.regs lo - 1 : ℕ) : ℝ≥0∞) + 1) = (m : ℝ≥0∞) := by
      norm_cast
    rw [hnum_eq, hden_eq, expPotential]
    calc
      ((∑ off : Fin (x.regs hi - x.regs lo - 1 + 1),
          ((2 + t off) + 2 + expSubCost ((y off).regs hi - (y off).regs lo)) : ℕ) : ℝ≥0∞) /
          (m : ℝ≥0∞)
        ≤ ((expSubCost m * m : ℕ) : ℝ≥0∞) / (m : ℝ≥0∞) := by gcongr
      _ = (expSubCost m : ℝ≥0∞) * (m : ℝ≥0∞) / (m : ℝ≥0∞) := by
          rw [Nat.cast_mul]
      _ = (expSubCost m : ℝ≥0∞) :=
          ENNReal.mul_div_cancel_right (by positivity) (ENNReal.natCast_ne_top m)

/-- Deterministic `5`-step execution of `selectSetup`. -/
private theorem selectSetup_spec {w : ℕ} {x : Data 16}
    (hk : x.regs rk < x.regs len) (hfit : Fits w (x.regs base + x.regs len)) :
    ∃ x_init, Exec w selectSetup x x_init 5 ∧
      x_init.mem = x.mem ∧
      x_init.regs lo = x.regs base ∧
      x_init.regs hi = x.regs base + x.regs len ∧
      SelectInv w (x.regs base) (x.regs len) (x.regs rk)
        (memSlice (x.regs base) (x.regs base + x.regs len) x.mem) x.mem x_init := by
  let vbase := x.regs base
  let n := x.regs len
  let k := x.regs rk
  have hfit1 : Fits w 1 := hfit.of_le (by omega)
  let s₁ := x.set one 1
  let s₂ := s₁.set target (vbase + k)
  let s₃ := s₂.set lo vbase
  let s₄ := s₃.set lo1 (vbase + 1)
  let x_init := s₄.set hi (vbase + n)
  have e₁ : Exec (B := .standard) w (.op (.const one 1)) x s₁ 1 := Exec.const hfit1
  have e₂ : Exec w (.op (.bin .add target base rk)) s₁ s₂ 1 := by
    have hb₁ : s₁.regs base = vbase := by
      simp only [s₁, Data.set_regs, Function.update_of_ne (by decide : base ≠ one)]; rfl
    have hk₁ : s₁.regs rk = k := by
      simp only [s₁, Data.set_regs, Function.update_of_ne (by decide : rk ≠ one)]; rfl
    simpa only [s₂, hb₁, hk₁, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := target)
      (i := base) (j := rk) (x := s₁)
      (hfit.of_le (by simp only [hb₁, hk₁, BinOp.eval]; omega))
  have e₃ : Exec (B := .standard) w (.op (.copy lo base)) s₂ s₃ 1 := by
    have hb₂ : s₂.regs base = vbase := by
      simp only [s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : base ≠ target),
        Function.update_of_ne (by decide : base ≠ one)]; rfl
    simpa only [s₃, hb₂] using Exec.copy (w := w) (d := lo) (s := base) (x := s₂)
  have e₄ : Exec w (.op (.bin .add lo1 lo one)) s₃ s₄ 1 := by
    have hl₃ : s₃.regs lo = vbase := by simp only [s₃, Data.set_regs, Function.update_self]
    have ho₃ : s₃.regs one = 1 := by
      simp only [s₃, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : one ≠ lo),
        Function.update_of_ne (by decide : one ≠ target), Function.update_self]
    simpa only [s₄, hl₃, ho₃, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := lo1)
      (i := lo) (j := one) (x := s₃)
      (hfit.of_le (by simp only [hl₃, ho₃, BinOp.eval]; omega))
  have e₅ : Exec w (.op (.bin .add hi base len)) s₄ x_init 1 := by
    have hb₄ : s₄.regs base = vbase := by
      simp only [s₄, s₃, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : base ≠ lo1),
        Function.update_of_ne (by decide : base ≠ lo),
        Function.update_of_ne (by decide : base ≠ target),
        Function.update_of_ne (by decide : base ≠ one)]; rfl
    have hn₄ : s₄.regs len = n := by
      simp only [s₄, s₃, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : len ≠ lo1),
        Function.update_of_ne (by decide : len ≠ lo),
        Function.update_of_ne (by decide : len ≠ target),
        Function.update_of_ne (by decide : len ≠ one)]; rfl
    simpa only [x_init, hb₄, hn₄, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := hi)
      (i := base) (j := len) (x := s₄)
      (by simpa only [hb₄, hn₄, BinOp.eval] using hfit)
  have hx_lo : x_init.regs lo = vbase := by
    simp only [x_init, s₄, s₃, Data.set_regs, Function.update_of_ne (by decide : lo ≠ hi),
      Function.update_of_ne (by decide : lo ≠ lo1), Function.update_self]
  have hx_hi : x_init.regs hi = vbase + n := by
    simp only [x_init, Data.set_regs, Function.update_self]
  refine ⟨x_init, e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))), rfl, hx_lo, hx_hi, ?_⟩
  exact ⟨by simp only [x_init, s₄, s₃, s₂, s₁, Data.set_regs,
      Function.update_of_ne (by decide : one ≠ hi), Function.update_of_ne (by decide : one ≠ lo1),
      Function.update_of_ne (by decide : one ≠ lo),
      Function.update_of_ne (by decide : one ≠ target), Function.update_self],
    by simp only [x_init, s₄, s₃, s₂, Data.set_regs,
      Function.update_of_ne (by decide : target ≠ hi),
      Function.update_of_ne (by decide : target ≠ lo1),
      Function.update_of_ne (by decide : target ≠ lo), Function.update_self]; rfl,
    by simp only [x_init, s₄, Data.set_regs, Function.update_of_ne (by decide : lo1 ≠ hi),
      Function.update_self, hx_lo],
    hfit,
    by rw [hx_lo],
    by rw [hx_lo]; omega,
    by rw [hx_hi]; omega,
    by rw [hx_hi],
    List.Perm.refl _,
    Modifies.refl _ _,
    fun a _ ha1 ha2 _ _ => by rw [hx_lo] at ha2; omega,
    fun _ b _ _ hb1 hb2 => by rw [hx_hi] at hb1; omega⟩

/-- Extracting order-statistic and partition-order properties from `SelectInv` at loop exit
(`¬(lo1 < hi)`). -/
private theorem SelectInv.exit_post {w vbase n k : ℕ} {s₀ : List ℕ} {mem₀ : ℕ → ℕ} {y : Data 16}
    (hIy : SelectInv w vbase n k s₀ mem₀ y) (hnc : ¬(Cond.lt lo1 hi).Holds y)
    (hs₀_len : s₀.length = n) (hk : k < n) :
    y.mem (vbase + k) = s₀.mergeSort[k]'(by rw [List.length_mergeSort, hs₀_len]; exact hk) ∧
    (∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k)) ∧
    (∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i)) := by
  have hnlt : ¬(y.regs lo + 1 < y.regs hi) := by
    simpa only [Cond.holds_lt, hIy.lo1_eq] using hnc
  have hlo_eq : y.regs lo = vbase + k := by
    have := hIy.lo_le_target; have := hIy.target_lt_hi; omega
  have hhi_eq : y.regs hi = vbase + k + 1 := by
    have := hIy.lo_le_target; have := hIy.target_lt_hi; omega
  have hleft : ∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k) := by
    intro i hik
    exact hIy.cut_lo (vbase + i) (vbase + k) (by omega) (by rw [hlo_eq]; omega)
      (by rw [hlo_eq]) (by omega)
  have hright : ∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i) := by
    intro i hki hin
    exact hIy.cut_hi (vbase + k) (vbase + i) (by omega) (by rw [hhi_eq]; omega)
      (by rw [hhi_eq]; omega) (by omega)
  have hval : y.mem (vbase + k) =
      s₀.mergeSort[k]'(by rw [List.length_mergeSort, hs₀_len]; exact hk) := by
    have hget_k : (memSlice vbase (vbase + n) y.mem)[k]'(by rw [length_memSlice]; omega) =
        y.mem (vbase + k) := getElem_memSlice (by omega)
    rw [← hget_k]
    refine eq_mergeSort_getElem_of_perm_of_partitioned hIy.perm (by omega)
      (fun i hik => ?_) (fun i hki hi_len => ?_)
    · rw [getElem_memSlice (by omega), getElem_memSlice (by omega)]
      exact hleft i hik
    · rw [length_memSlice] at hi_len
      rw [getElem_memSlice (by omega), getElem_memSlice hi_len]
      exact hright i hki (by omega)
  exact ⟨hval, hleft, hright⟩

/-- **Specification of `selectSlice` on an arbitrary slice `[vbase, vbase + n)`.**
When `k = x.regs rk < x.regs len = n` and `Fits w (x.regs base + x.regs len)`:
1. `selectSlice` runs within `10 * n ^ 2 + 8` instructions and `n - 1` `rand` calls, permuting
   `[vbase, vbase + n)` in place, placing the `k`-th sorted element in both `y.mem (vbase + k)` and
   `y.regs ans`, partitioning `[vbase, vbase + n)` around `vbase + k`, and modifying only
   `Finset.Ico vbase (vbase + n)`;
2. Its expected instruction count satisfies `expectedCodeTime w selectSlice x ≤ 80 * n + 8`. -/
theorem selectSlice_spec {w : ℕ} {x : Data 16}
    (hk : x.regs rk < x.regs len) (hfit : Fits w (x.regs base + x.regs len)) :
    let vbase := x.regs base
    let n := x.regs len
    let k := x.regs rk
    let s₀ := memSlice vbase (vbase + n) x.mem
    ExecRandWithin w selectSlice x
      (fun y =>
        y.regs ans = s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
        (memSlice vbase (vbase + n) y.mem).Perm s₀ ∧
        y.mem (vbase + k) =
          s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
        (∀ i < k, y.mem (vbase + i) ≤ y.mem (vbase + k)) ∧
        (∀ i, k < i → i < n → y.mem (vbase + k) ≤ y.mem (vbase + i)) ∧
        Modifies (Finset.Ico vbase (vbase + n)) x.mem y.mem)
      (10 * n ^ 2 + 8) (n - 1) ∧
    expectedCodeTime w selectSlice x ≤ ((80 * n + 8 : ℕ) : ℝ≥0∞) := by
  dsimp only
  let vbase := x.regs base
  let n := x.regs len
  let k := x.regs rk
  let s₀ := memSlice vbase (vbase + n) x.mem
  obtain ⟨x_init, e_setup, _, hx_lo, hx_hi, hI_init⟩ := selectSetup_spec hk hfit
  -- 1. Worst-case `ExecRandWithin`
  have hloop_wc : ExecRandWithin w (ram[ while lo1 < hi do [ ⟪selectStep⟫ ] ]) x_init
      (fun y => SelectInv w vbase n k s₀ x.mem y ∧ ¬(Cond.lt lo1 hi).Holds y)
      (stepPotential x_init + 2) (callPotential x_init) :=
    ExecRandWithin.loop_potential (SelectInv w vbase n k s₀ x.mem) stepPotential callPotential
      (fun s hs hc => selectStep_worstCase hs hc) hI_init
  have hstep_init : stepPotential x_init ≤ 10 * n ^ 2 := by
    unfold stepPotential
    dsimp only
    rw [hx_hi, hx_lo, Nat.add_sub_cancel_left]
    split_ifs <;> nlinarith
  have hcall_init : callPotential x_init ≤ n - 1 := by
    simp only [callPotential, hx_hi, hx_lo, Nat.add_sub_cancel_left]
    exact le_rfl
  have hloop_wc' : ExecRandWithin w (ram[ while lo1 < hi do [ ⟪selectStep⟫ ] ]) x_init
      (fun y => SelectInv w vbase n k s₀ x.mem y ∧ ¬(Cond.lt lo1 hi).Holds y)
      (10 * n ^ 2 + 2) (n - 1) :=
    hloop_wc.mono (fun _ h => h) (by omega) hcall_init
  have hsetup_wc : ExecRandWithin w selectSetup x (· = x_init) 5 0 :=
    e_setup.within.execRandWithin rfl
  have hload_after : ∀ y : Data 16,
      SelectInv w vbase n k s₀ x.mem y ∧ ¬(Cond.lt lo1 hi).Holds y →
      ExecRandWithin (B := .standard) w (.op (.load ans target)) y
        (fun z =>
          z.regs ans = s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
          (memSlice vbase (vbase + n) z.mem).Perm s₀ ∧
          z.mem (vbase + k) =
            s₀.mergeSort[k]'(by rw [List.length_mergeSort, length_memSlice]; omega) ∧
          (∀ i < k, z.mem (vbase + i) ≤ z.mem (vbase + k)) ∧
          (∀ i, k < i → i < n → z.mem (vbase + k) ≤ z.mem (vbase + i)) ∧
          Modifies (Finset.Ico vbase (vbase + n)) x.mem z.mem) 1 0 := by
    rintro y ⟨hIy, hnc⟩
    obtain ⟨hval, hleft, hright⟩ := hIy.exit_post hnc (by simp only [s₀, length_memSlice]; omega) hk
    refine (ExecWithin.load (w := w) (d := ans) (a := target) (x := y)).execRandWithin ?_
    simp only [Data.set_regs, Function.update_self, Data.set_mem, hIy.target_eq]
    exact ⟨hval, hIy.perm, hval, hleft, hright, hIy.modifies⟩
  -- 2. Linear `expectedCodeTime`
  obtain ⟨⟨m_loop, hm_loop⟩, hloop_exp⟩ := expectedCodeTime_loop_le_of_drift
    (SelectInv w vbase n k s₀ x.mem) callPotential expPotential hI_init
    (fun s hs hc => selectStep_drift hs hc)
  have hexp_init : expPotential x_init ≤ (80 * n : ℕ) := by
    simp only [expPotential, hx_hi, hx_lo, Nat.add_sub_cancel_left]
    exact_mod_cast expSubCost_le n
  have hexp_slice : expectedCodeTime w selectSlice x ≤ ((80 * n + 8 : ℕ) : ℝ≥0∞) := by
    rw [selectSlice, expectedCodeTime_seq_of_exec e_setup, expectedCodeTime_seq hm_loop]
    have hload_exp : ProbComp.expect m_loop
        (fun z => expectedCodeTime (B := .standard) w (.op (.load ans target)) z.1) = 1 := by
      rw [← ProbComp.expect_const m_loop 1]
      refine ProbComp.expect_congr_on_support fun z _ => ?_
      exact expectedCodeTime_op rfl
    rw [hload_exp]
    calc
      ((5 : ℕ) : ℝ≥0∞) + (expectedCodeTime w (ram[ while lo1 < hi do [ ⟪selectStep⟫ ] ]) x_init + 1)
        ≤ ((5 : ℕ) : ℝ≥0∞) + (((80 * n : ℕ) : ℝ≥0∞) + 2 + 1) := by
          gcongr
          exact hloop_exp.trans (by gcongr)
      _ = ((80 * n + 8 : ℕ) : ℝ≥0∞) := by
          push_cast; ring
  refine ⟨?_, hexp_slice⟩
  have h12 := hsetup_wc.seq fun y hy => by subst hy; exact hloop_wc'.seq hload_after
  exact h12.mono (fun _ h => h) (by dsimp only [n]; omega) (by dsimp only [n]; omega)

/-! ## Top-level `program` specifications on `State.init (k :: input)` -/

/-- Deterministic `4`-step execution of `loadHeader` on `Data.init (k :: input)`. -/
theorem loadHeader_spec {w k : ℕ} {input : List ℕ} (hfit : InputFits w (k :: input)) :
    ∃ x_hdr : Data 16,
      Exec w loadHeader (Data.init (k :: input)) x_hdr 4 ∧
      x_hdr.mem = (Data.init (r := 16) (k :: input)).mem ∧
      x_hdr.regs one = 1 ∧
      x_hdr.regs rk = k ∧
      x_hdr.regs len = input.length := by
  let x₀ : Data 16 := Data.init (k :: input)
  have hfit_len1 : Fits w (input.length + 1) := by
    simpa only [List.length_cons] using hfit.1
  have hfit1 : Fits w 1 := hfit_len1.of_le (by omega)
  have hfit_len : Fits w input.length := hfit_len1.of_le (by omega)
  let s₁ := x₀.set len (input.length + 1)
  let s₂ := s₁.set one 1
  let s₃ := s₂.set rk k
  let x_hdr := s₃.set len input.length
  have e₁ : Exec (B := .standard) w (.op (.load len ans)) x₀ s₁ 1 := by
    simpa only [s₁, x₀, Data.init_regs, Data.init_mem_zero, List.length_cons] using
      Exec.load (w := w) (d := len) (a := ans) (x := x₀)
  have e₂ : Exec (B := .standard) w (.op (.const one 1)) s₁ s₂ 1 := Exec.const hfit1
  have e₃ : Exec (B := .standard) w (.op (.load rk one)) s₂ s₃ 1 := by
    have ho₂ : s₂.regs one = 1 := by simp only [s₂, Data.set_regs, Function.update_self]
    have hm₂ : s₂.mem 1 = k := by
      simp only [s₂, s₁, Data.set_mem, x₀, Data.init_mem_succ, List.getD_cons_zero]
    simpa only [s₃, ho₂, hm₂] using Exec.load (w := w) (d := rk) (a := one) (x := s₂)
  have e₄ : Exec w (.op (.bin .sub len len one)) s₃ x_hdr 1 := by
    have hl₃ : s₃.regs len = input.length + 1 := by
      simp only [s₃, s₂, s₁, Data.set_regs, Function.update_of_ne (by decide : len ≠ rk),
        Function.update_of_ne (by decide : len ≠ one), Function.update_self]
    have ho₃ : s₃.regs one = 1 := by
      simp only [s₃, s₂, Data.set_regs, Function.update_of_ne (by decide : one ≠ rk),
        Function.update_self]
    simpa only [x_hdr, hl₃, ho₃, BinOp.eval, Nat.add_sub_cancel] using
      Exec.bin (w := w) (f := .sub) (d := len) (i := len) (j := one) (x := s₃)
        (by simpa only [hl₃, ho₃, BinOp.eval, Nat.add_sub_cancel] using hfit_len)
  refine ⟨x_hdr, e₁.seq (e₂.seq (e₃.seq e₄)), rfl, ?_, ?_, ?_⟩
  · simp only [x_hdr, s₃, s₂, Data.set_regs, Function.update_of_ne (by decide : one ≠ len),
      Function.update_of_ne (by decide : one ≠ rk), Function.update_self]
  · simp only [x_hdr, s₃, Data.set_regs, Function.update_of_ne (by decide : rk ≠ len),
      Function.update_self]
  · simp only [x_hdr, Data.set_regs, Function.update_self]

/-- Structured `7`-step execution of `code` when `input.length ≤ k`. -/
theorem code_out_of_range_spec {w k : ℕ} {input : List ℕ}
    (hk : input.length ≤ k) (hfit : InputFits w (k :: input)) :
    ∃ y : Data 16,
      Exec w code (Data.init (k :: input)) y 7 ∧
      y.regs ans = 0 ∧
      y.mem = (Data.init (r := 16) (k :: input)).mem := by
  obtain ⟨x_hdr, e_hdr, hmem_hdr, _, hrk, hlen⟩ := loadHeader_spec hfit
  have hc_neg : ¬(Cond.lt rk len).Holds x_hdr := by
    simp only [Cond.holds_lt, hrk, hlen]
    omega
  have e_zero : Exec (B := .standard) w (.op (.const ans 0)) x_hdr (x_hdr.set ans 0) 1 :=
    Exec.const (fits_zero w)
  refine ⟨x_hdr.set ans 0, e_hdr.seq (e_zero.branch_neg hc_neg), ?_, hmem_hdr⟩
  simp only [Data.set_regs, Function.update_self]

/-- **Total out-of-range behavior (`input.length ≤ k`).**
Whenever `InputFits w (k :: input)` holds and `input.length ≤ k`, `program` executes
deterministically in `8` instructions returning `0`, making `0` `rand` calls and leaving memory
completely unchanged. -/
theorem quickselect_out_of_range {w k : ℕ} {input : List ℕ}
    (hk : input.length ≤ k) (hfit : InputFits w (k :: input)) :
    Executes w program (.init (k :: input)) 0 8 ∧
    RandHaltsWithin w program (.init (k :: input)) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init (k :: input)) (worstCaseTime input.length) 0 ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length)
        (.running (.init (k :: input)))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded w ∧
        y.mem = (Data.init (r := 16) (k :: input)).mem) ∧
    expectedTime w program (.init (k :: input)) = 8 := by
  obtain ⟨y_out, e_code, hy_ans, hmem_out⟩ := code_out_of_range_spec hk hfit
  have hexecutes : Executes w program (.init (k :: input)) 0 8 := by
    simpa only [program, State.init, hy_ans] using e_code.executes ans
  have hrun : runRand w program (worstCaseTime input.length) (.running (.init (k :: input))) =
      pure (.halted 0 y_out) := by
    simpa only [program, State.init, hy_ans] using
      e_code.runRand_program ans (T := worstCaseTime input.length)
        (by simp only [worstCaseTime]; omega)
  refine ⟨hexecutes, ?_, ?_, ?_, ?_⟩
  · intro cfg hcfg
    rw [hrun] at hcfg
    cases OracleComp.eq_of_mem_supportWith_pure hcfg
    exact ⟨0, y_out, rfl⟩
  · rw [RandCallsBounded, hrun]
    exact .pure _ 0
  · intro cfg hcfg
    have hbnd := runRand_bounded_init hfit hcfg
    rw [hrun] at hcfg
    cases OracleComp.eq_of_mem_supportWith_pure hcfg
    exact ⟨y_out, rfl, hbnd.2, hmem_out⟩
  · simpa only [Nat.cast_ofNat] using hexecutes.expectedTime_eq

/-- Structured `ExecRandWithin` and linear `expectedCodeTime` specification for `code` when
`k < input.length`. -/
theorem code_spec {w k : ℕ} {input : List ℕ}
    (hk : k < input.length) (hw : logWidth 2 input.length ≤ w)
    (hfit : InputFits w (k :: input)) :
    ExecRandWithin w code (Data.init (k :: input))
      (fun y =>
        y.regs ans = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (memSlice 2 (input.length + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < input.length → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (input.length + 2))
          (Data.init (r := 16) (k :: input)).mem y.mem)
      (10 * input.length ^ 2 + 14) (input.length - 1) ∧
    expectedCodeTime w code (Data.init (k :: input)) ≤
      ((80 * input.length + 14 : ℕ) : ℝ≥0∞) := by
  let n := input.length
  have hfit_end : Fits w (2 + n) := by
    rw [Nat.add_comm]
    exact fits_add_two hw
  obtain ⟨x_hdr, e_hdr, hmem_hdr, hone_hdr, hrk_hdr, hlen_hdr⟩ := loadHeader_spec hfit
  have hc_pos : (Cond.lt rk len).Holds x_hdr := by
    simp only [Cond.holds_lt, hrk_hdr, hlen_hdr]
    exact hk
  let x_base := x_hdr.set base 2
  have e_base : Exec w (.op (.bin .add base one one)) x_hdr x_base 1 := by
    simpa only [x_base, hone_hdr, BinOp.eval] using
      Exec.bin (w := w) (f := .add) (d := base) (i := one) (j := one) (x := x_hdr)
        (hfit_end.of_le (by simp only [hone_hdr, BinOp.eval]; omega))
  have hrk_base : x_base.regs rk = k := by
    simp only [x_base, Data.set_regs, Function.update_of_ne (by decide : rk ≠ base), hrk_hdr]
  have hlen_base : x_base.regs len = n := by
    simp only [x_base, Data.set_regs, Function.update_of_ne (by decide : len ≠ base), hlen_hdr]
    rfl
  have hbase_base : x_base.regs base = 2 := by
    simp only [x_base, Data.set_regs, Function.update_self]
  have hslice_init : memSlice 2 (n + 2) (Data.init (r := 16) (k :: input)).mem = input := by
    refine List.ext_getElem (by simp only [length_memSlice]; dsimp only [n]; omega)
      fun i h1 h2 => ?_
    rw [getElem_memSlice (by omega), show 2 + i = (i + 1) + 1 by omega]
    simp only [Data.init_mem_succ]
    rw [List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
      Option.getD_some]
  obtain ⟨hslice_wc, hslice_exp⟩ := selectSlice_spec (w := w) (x := x_base)
    (by rw [hrk_base, hlen_base]; exact hk)
    (by rw [hbase_base, hlen_base]; exact hfit_end)
  have hthen_wc : ExecRandWithin w (ram[ base ← one + one; ⟪selectSlice⟫ ]) x_hdr
      (fun y =>
        y.regs ans = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (memSlice 2 (n + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < n → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (n + 2)) (Data.init (r := 16) (k :: input)).mem y.mem)
      (10 * n ^ 2 + 9) (n - 1) := by
    have hb_wc : ExecRandWithin w (.op (.bin .add base one one)) x_hdr (· = x_base) 1 0 :=
      e_base.within.execRandWithin rfl
    have hseq := hb_wc.seq fun y hy => by subst hy; exact hslice_wc
    refine hseq.mono ?_ (by rw [hlen_base]; omega) (by rw [hlen_base]; omega)
    intro y hy
    have hx_mem : x_base.mem = (Data.init (r := 16) (k :: input)).mem := by
      simp only [x_base, Data.set_mem, hmem_hdr]
    simp only [hbase_base, hlen_base, hrk_base, hx_mem, Nat.add_comm 2 n, hslice_init] at hy
    exact hy
  have hcode_wc : ExecRandWithin w code (Data.init (k :: input))
      (fun y =>
        y.regs ans = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (memSlice 2 (n + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < n → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (n + 2)) (Data.init (r := 16) (k :: input)).mem y.mem)
      (10 * n ^ 2 + 14) (n - 1) := by
    have hhdr_wc : ExecRandWithin w loadHeader (Data.init (k :: input)) (· = x_hdr) 4 0 :=
      e_hdr.within.execRandWithin rfl
    have hbr_wc := ExecRandWithin.branch_pos (neg := ram[ ans ← #0 ]) hc_pos hthen_wc
    have hseq := hhdr_wc.seq fun y hy => by subst hy; exact hbr_wc
    exact hseq.mono (fun _ h => h) (by omega) (by omega)
  refine ⟨hcode_wc, ?_⟩
  rw [code, expectedCodeTime_seq_of_exec e_hdr, expectedCodeTime_branch_pos hc_pos,
    expectedCodeTime_seq_of_exec e_base]
  rw [hlen_base] at hslice_exp
  calc
    ((4 : ℕ) : ℝ≥0∞) + (((1 : ℕ) : ℝ≥0∞) + expectedCodeTime w selectSlice x_base + 1)
      ≤ ((4 : ℕ) : ℝ≥0∞) + (((1 : ℕ) : ℝ≥0∞) + ((80 * n + 8 : ℕ) : ℝ≥0∞) + 1) := by gcongr
    _ = ((80 * n + 14 : ℕ) : ℝ≥0∞) := by push_cast; ring

/-- **In-place randomized quickselect: correctness, zero auxiliary space, worst-case bounds,
`rand`-call bound, and linear expected running time.**

For any `input : List ℕ` of length `n`, target rank `k < n`, and word size `w ≥ logWidth 2 n` with
`InputFits w (k :: input)`:
1. `program` halts without faulting within `worstCaseTime n = 10 * n ^ 2 + 15` instructions on
   every execution path (`RandHaltsWithin`);
2. Every execution path makes at most `n - 1` `rand` calls (`RandCallsBounded`);
3. On every supported halting configuration, `program` returns `input.mergeSort[k]` with
   `y.Bounded w`, permutes `memSlice 2 (n + 2) y.mem` in place so that
   `y.mem (2 + k) = input.mergeSort[k]` with `y.mem (2 + i) ≤ y.mem (2 + k)` for `i < k` and
   `y.mem (2 + k) ≤ y.mem (2 + i)` for `k < i < n`, and leaves all memory outside
   `Finset.Ico 2 (n + 2)` untouched (`Modifies`, zero auxiliary heap words);
4. The expected instruction count satisfies
   `expectedTime w program (.init (k :: input)) ≤ expectedTimeBound n = 80 * n + 15`
   uniformly over all `k < n` and unconditionally across duplicate keys. -/
theorem quickselect_correct_and_bounds {w k : ℕ} {input : List ℕ}
    (hk : k < input.length) (hw : logWidth 2 input.length ≤ w)
    (hfit : InputFits w (k :: input)) :
    RandHaltsWithin w program (.init (k :: input)) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init (k :: input)) (worstCaseTime input.length)
      (input.length - 1) ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length)
        (.running (.init (k :: input)))).support,
      ∃ y : Data 16,
        cfg = .halted (input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk)) y ∧
        y.Bounded w ∧
        (memSlice 2 (input.length + 2) y.mem).Perm input ∧
        y.mem (2 + k) = input.mergeSort[k]'(by rw [List.length_mergeSort]; exact hk) ∧
        (∀ i < k, y.mem (2 + i) ≤ y.mem (2 + k)) ∧
        (∀ i, k < i → i < input.length → y.mem (2 + k) ≤ y.mem (2 + i)) ∧
        Modifies (Finset.Ico 2 (input.length + 2))
          (Data.init (r := 16) (k :: input)).mem y.mem) ∧
    expectedTime w program (.init (k :: input)) ≤
      (expectedTimeBound input.length : ℝ≥0∞) := by
  obtain ⟨hcode_wc, hcode_exp⟩ := code_spec hk hw hfit
  obtain ⟨hHalts, hCalls, hPost⟩ :=
    hcode_wc.program ans (T' := worstCaseTime input.length) (by simp only [worstCaseTime]; omega)
  obtain ⟨m_code, hm_code, -, -⟩ := hcode_wc
  have hexp_total :
      expectedTime w program (.init (k :: input)) ≤ (expectedTimeBound input.length : ℝ≥0∞) := by
    rw [program, State.init, expectedCodeTime_program hm_code ans]
    calc
      expectedCodeTime w code (Data.init (k :: input)) + 1
        ≤ ((80 * input.length + 14 : ℕ) : ℝ≥0∞) + 1 := by gcongr
      _ = (expectedTimeBound input.length : ℝ≥0∞) := by
          simp only [expectedTimeBound]
          push_cast
          ring
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, hexp_total⟩
  obtain ⟨y, hcfg_eq, hy_ans, hperm, hy_k, hleft, hright, hmod⟩ := hPost cfg hcfg
  rw [hy_ans] at hcfg_eq
  have hbnd : y.Bounded w := by
    have hb := runRand_bounded_init hfit hcfg
    rw [hcfg_eq] at hb
    exact hb.2
  exact ⟨y, hcfg_eq, hbnd, hperm, hy_k, hleft, hright, hmod⟩

end Cslib.Algorithms.WordRAM.Quickselect
