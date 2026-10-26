/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Allocation
public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.Notation
public import Complexity.Computability.WordRAM.Randomized.Expected
public import Complexity.Computability.WordRAM.Time
public import Complexity.Foundations.NumberTheory.Harmonic
import Mathlib.Data.List.Sort
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order

/-!
# In-place randomized quicksort on the word RAM

Iterative in-place 3-way randomized quicksort over `Cslib.WordRAM.Basis.standard`, sorting an
`n`-word input array in `Block.mk 1 n` using an explicit `2 * n`-word range stack allocated at
`[n + 1, 3 * n + 1)`.

Using Dutch National Flag 3-way partitioning (`< piv`, `= piv`, `> piv`) around a uniformly
sampled pivot `off ← rand (hi - lo - 1)` ensures that:
1. **Pathwise correctness:** every execution path halts cleanly with `Block.mk 1 n` holding
   `input.mergeSort` (a sorted permutation of `input`), modifying memory only within
   `Finset.Ico 1 (3 * n + 1)`;
2. **Strict worst-case bounds:** only subranges of length `≥ 2` are pushed, and every partition
   strictly eliminates at least the sampled pivot, so stack potential `∑ (hi - lo - 1)` drops on
   every iteration — bounding every path to at most `n - 1` `rand` calls and
   `20 * n ^ 2 + 8 * n + 32` instructions;
3. **Unconditional `O(n log n)` expected running time (including duplicates):** equal elements
   fall into the middle `= piv` region and are never recursed on, so the left and right recursive
   sizes on sorted rank `r` are at most `r` and `m - 1 - r` regardless of duplicate keys.
   Bounding Mathlib's `harmonic` numbers via `harmonic_le_log_add_one`
   (`harmonic n ≤ Nat.log 2 n + 1`) yields
   `expectedTime w program (.init input) ≤ 120 * n * (Nat.log 2 n + 1) + 32` without
   transcendental analysis.

## Main definitions

* `Cslib.Algorithms.WordRAM.Quicksort.code`, `Cslib.Algorithms.WordRAM.Quicksort.program`:
  structured and compiled 16-register randomized quicksort program.
* `Cslib.Algorithms.WordRAM.Quicksort.worstCaseTime`: quadratic worst-case step bound
  `20 * n ^ 2 + 8 * n + 32`.
* `Cslib.Algorithms.WordRAM.Quicksort.expectedTimeBound`: `O(n log n)` expected step bound
  `120 * n * (Nat.log 2 n + 1) + 32`.

## Main results

* `Cslib.Algorithms.WordRAM.Quicksort.quicksort_correct_and_bounds`: joint certificate of
  `RandHaltsWithin`, `RandCallsBounded` (`≤ n - 1`), pathwise sorted-array realization + `Modifies`
  frame, and `O(n log n)` `expectedTime` at word size `w ≥ logWidth 3 input.length`.

Classical background on randomized quicksort, equal-key partitioning and the expected-cost
recurrence appears in [CLRS2009], Section 7.3, Section 7.4.2 and Problems 7-2–7-3;
[MitzenmacherUpfal2017], Section 2.5, gives additional expected-cost background. The word-RAM
implementation and step constants, constant-56 explicit-stack potential, ranked-loop drift
formulation and duplicate-key rank-domination proof are original to this formalization.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 7.3, Section 7.4.2 and Problems 7-2–7-3.
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017], Section 2.5.
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.Algorithms.WordRAM.Quicksort

open Cslib.WordRAM

/-! ## Expected-partition potential recurrence -/

/-- Potential contribution of a subarray of length `m` in the expected-time drift argument. -/
noncomputable def subCost (m : ℕ) : ℝ :=
  if m < 2 then 0 else 56 * ((m : ℝ) + 1) * (harmonic m : ℝ)

theorem subCost_of_lt_two {m : ℕ} (h : m < 2) : subCost m = 0 := by
  simp [subCost, h]

theorem subCost_nonneg (m : ℕ) : 0 ≤ subCost m := by
  unfold subCost
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by positivity) (by exact_mod_cast harmonic_nonneg m)

theorem subCost_le_formula (m : ℕ) :
    subCost m ≤ 56 * ((m : ℝ) + 1) * (harmonic m : ℝ) := by
  unfold subCost
  split_ifs
  · exact mul_nonneg (by positivity) (by exact_mod_cast harmonic_nonneg m)
  · exact le_rfl

theorem subCost_mono {a b : ℕ} (hab : a ≤ b) : subCost a ≤ subCost b := by
  by_cases ha : a < 2
  · rw [subCost_of_lt_two ha]
    exact subCost_nonneg b
  · have hb : ¬b < 2 := by omega
    simp only [subCost, ha, hb, ↓reduceIte]
    have h1 : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity))
      (by exact_mod_cast harmonic_mono hab) (by exact_mod_cast harmonic_nonneg a) (by positivity)

/-- Key expected-quicksort recurrence: for `m ≥ 2`, `28 * m` plus the average over `r < m` of
`subCost r + subCost (m - 1 - r)` is at most `subCost m`. -/
theorem subCost_recurrence {m : ℕ} (hm : 2 ≤ m) :
    28 * (m : ℝ) +
      (∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r))) / (m : ℝ) ≤
        subCost m := by
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrefl : ∑ r ∈ Finset.range m, subCost (m - 1 - r) =
      ∑ r ∈ Finset.range m, subCost r :=
    Finset.sum_range_reflect subCost m
  have hsum_harm : 2 * ∑ r ∈ Finset.range m, ((r : ℝ) + 1) * (harmonic r : ℝ) =
      (m : ℝ) * ((m : ℝ) + 1) * (harmonic m : ℝ) - (m : ℝ) * ((m : ℝ) + 3) / 2 := by
    simpa [Rat.cast_sum] using congrArg (Rat.cast : ℚ → ℝ) (two_mul_sum_add_one_mul_harmonic m)
  have hsum_le : ∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r)) ≤
      56 * ((m : ℝ) * ((m : ℝ) + 1) * (harmonic m : ℝ) - (m : ℝ) * ((m : ℝ) + 3) / 2) := by
    rw [Finset.sum_add_distrib, hrefl, ← two_mul]
    calc
      2 * ∑ r ∈ Finset.range m, subCost r
        ≤ 2 * ∑ r ∈ Finset.range m, (56 * ((r : ℝ) + 1) * (harmonic r : ℝ)) := by
          gcongr with r
          exact subCost_le_formula r
      _ = 56 * (2 * ∑ r ∈ Finset.range m, ((r : ℝ) + 1) * (harmonic r : ℝ)) := by
          have hpull : ∑ r ∈ Finset.range m, 56 * ((r : ℝ) + 1) * (harmonic r : ℝ) =
              56 * ∑ r ∈ Finset.range m, ((r : ℝ) + 1) * (harmonic r : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun r _ => by ring
          rw [hpull]
          ring
      _ = 56 * ((m : ℝ) * ((m : ℝ) + 1) * (harmonic m : ℝ) - (m : ℝ) * ((m : ℝ) + 3) / 2) := by
          rw [hsum_harm]
  have hdiv : (∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r))) / (m : ℝ) ≤
      56 * ((m : ℝ) + 1) * (harmonic m : ℝ) - 28 * ((m : ℝ) + 3) := by
    rw [div_le_iff₀ hm_pos]
    calc
      ∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r))
        ≤ 56 * ((m : ℝ) * ((m : ℝ) + 1) * (harmonic m : ℝ) -
            (m : ℝ) * ((m : ℝ) + 3) / 2) := hsum_le
      _ = (56 * ((m : ℝ) + 1) * (harmonic m : ℝ) - 28 * ((m : ℝ) + 3)) * (m : ℝ) := by ring
  have hsub_eq : subCost m = 56 * ((m : ℝ) + 1) * (harmonic m : ℝ) := by
    simp [subCost, show ¬m < 2 by omega]
  linarith

/-! ## Memory slices, permutations, and 3-way partition rank bounds -/

/-- Read the subarray `mem[a .. b)` as a list of length `b - a`. -/
def memSlice (a b : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range (b - a)).map fun i => mem (a + i)

@[simp]
theorem length_memSlice (a b : ℕ) (mem : ℕ → ℕ) :
    (memSlice a b mem).length = b - a := by
  simp [memSlice]

theorem getElem_memSlice {a b : ℕ} {mem : ℕ → ℕ} {i : ℕ} (hi : i < b - a) :
    (memSlice a b mem)[i]'(by simp [hi]) = mem (a + i) := by
  simp [memSlice]

theorem mem_memSlice_iff {a b v : ℕ} {mem : ℕ → ℕ} :
    v ∈ memSlice a b mem ↔ ∃ addr, a ≤ addr ∧ addr < b ∧ mem addr = v := by
  simp only [memSlice, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨a + i, by omega, by omega, rfl⟩
  · rintro ⟨addr, hlo, hhi, rfl⟩
    exact ⟨addr - a, by omega, by congr 1; omega⟩

theorem memSlice_congr {a b : ℕ} {m₁ m₂ : ℕ → ℕ}
    (h : ∀ addr, a ≤ addr → addr < b → m₁ addr = m₂ addr) :
    memSlice a b m₁ = memSlice a b m₂ := by
  unfold memSlice
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  exact h (a + i) (by omega) (by omega)

theorem memSlice_append {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (mem : ℕ → ℕ) :
    memSlice a c mem = memSlice a b mem ++ memSlice b c mem := by
  refine List.ext_getElem (by simp; omega) fun i h₁ h₂ => ?_
  have hi_ac : i < c - a := by simpa using h₁
  rw [getElem_memSlice hi_ac]
  by_cases hi : i < b - a
  · rw [List.getElem_append_left (by simpa using hi), getElem_memSlice hi]
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hi)]
    simp only [length_memSlice]
    rw [getElem_memSlice (by omega)]
    congr 1
    omega

/-- Swapping two addresses inside `[a, b)` preserves `List.Perm` on `memSlice a b`. -/
theorem memSlice_swap_perm {a b p q : ℕ} (hp : a ≤ p ∧ p < b) (hq : a ≤ q ∧ q < b)
    (mem : ℕ → ℕ) :
    (memSlice a b (Function.update (Function.update mem p (mem q)) q (mem p))).Perm
      (memSlice a b mem) := by
  set m := b - a
  set ip : Fin m := ⟨p - a, by omega⟩
  set iq : Fin m := ⟨q - a, by omega⟩
  set σ : Equiv.Perm (Fin m) := Equiv.swap ip iq
  have hfn : ∀ l : ℕ → ℕ, memSlice a b l = List.ofFn (fun i : Fin m => l (a + i.val)) := by
    intro l
    refine List.ext_getElem (by simp [m]) fun i h₁ h₂ => ?_
    simp [memSlice]
  rw [hfn, hfn]
  have hfun : (fun i : Fin m =>
      Function.update (Function.update mem p (mem q)) q (mem p) (a + i.val)) =
      (fun i : Fin m => mem (a + (σ i).val)) := by
    funext i
    by_cases hiq : i = iq
    · subst hiq
      have h1 : a + iq.val = q := by simp [iq]; omega
      have h2 : a + (σ iq).val = p := by simp [σ, ip]; omega
      rw [h1, h2, Function.update_self]
    · have hneq_q : a + i.val ≠ q := by
        intro heq
        apply hiq
        ext
        simp only [iq]
        omega
      rw [Function.update_of_ne hneq_q]
      by_cases hip : i = ip
      · subst hip
        have h1 : a + ip.val = p := by simp [ip]; omega
        have h2 : a + (σ ip).val = q := by simp [σ, iq]; omega
        rw [h1, h2, Function.update_self]
      · have hneq_p : a + i.val ≠ p := by
          intro heq
          apply hip
          ext
          simp only [ip]
          omega
        have hfix : σ i = i := Equiv.swap_apply_of_ne_of_ne hip hiq
        rw [Function.update_of_ne hneq_p, hfix]
  rw [hfun]
  have hbij : ((List.finRange m).map σ).Perm (List.finRange m) := by
    refine (List.perm_ext_iff_of_nodup ?_ (List.nodup_finRange m)).mpr fun i => ?_
    · exact (List.nodup_finRange m).map σ.injective
    · simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
      exact ⟨σ.symm i, σ.apply_symm_apply i⟩
  simpa only [List.ofFn_eq_map, List.map_map, Function.comp_def] using
    hbij.map (fun i : Fin m => mem (a + i.val))

/-- At 3-way partition exit (`cur = gt`), `< piv` has exact count `lt - lo`, `> piv` has exact
count `hi - gt`, and `piv ∈ memSlice lo hi mem₀` implies `lt < gt`. -/
theorem partition_counts_and_lt {lo lt gt hi piv : ℕ} {mem₀ mem : ℕ → ℕ}
    (hbounds : lo ≤ lt ∧ lt ≤ gt ∧ gt ≤ hi)
    (hperm : (memSlice lo hi mem).Perm (memSlice lo hi mem₀))
    (hlt : ∀ a, lo ≤ a → a < lt → mem a < piv)
    (heq : ∀ a, lt ≤ a → a < gt → mem a = piv)
    (hgt : ∀ a, gt ≤ a → a < hi → piv < mem a)
    (hpiv : piv ∈ memSlice lo hi mem₀) :
    lt < gt ∧
      lt - lo = (memSlice lo hi mem₀).countP (· < piv) ∧
      hi - gt = (memSlice lo hi mem₀).countP (piv < ·) := by
  have hsplit : memSlice lo hi mem =
      memSlice lo lt mem ++ (memSlice lt gt mem ++ memSlice gt hi mem) := by
    rw [memSlice_append (by omega) hbounds.2.2, memSlice_append hbounds.1 hbounds.2.1,
      List.append_assoc]
  have hlt_lt : lt < gt := by
    have hpiv_mem : piv ∈ memSlice lo hi mem := hperm.mem_iff.mpr hpiv
    rw [hsplit, List.mem_append, List.mem_append] at hpiv_mem
    rcases hpiv_mem with h1 | h2 | h3
    · obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp h1
      exact absurd (hlt a ha1 ha2) (Nat.lt_irrefl _)
    · obtain ⟨a, ha1, ha2, -⟩ := mem_memSlice_iff.mp h2
      omega
    · obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp h3
      exact absurd (hgt a ha1 ha2) (Nat.lt_irrefl _)
  have hc1_left : (memSlice lo lt mem).countP (· < piv) = lt - lo := by
    rw [List.countP_eq_length.mpr, length_memSlice]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    exact decide_eq_true (hlt a ha1 ha2)
  have hc1_mid : (memSlice lt gt mem).countP (· < piv) = 0 := by
    rw [List.countP_eq_zero]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    have := heq a ha1 ha2
    simp [this]
  have hc1_right : (memSlice gt hi mem).countP (· < piv) = 0 := by
    rw [List.countP_eq_zero]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    have := hgt a ha1 ha2
    simp [Nat.not_lt.mpr (Nat.le_of_lt this)]
  have hc2_left : (memSlice lo lt mem).countP (piv < ·) = 0 := by
    rw [List.countP_eq_zero]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    have := hlt a ha1 ha2
    simp [Nat.not_lt.mpr (Nat.le_of_lt this)]
  have hc2_mid : (memSlice lt gt mem).countP (piv < ·) = 0 := by
    rw [List.countP_eq_zero]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    have := heq a ha1 ha2
    simp [this]
  have hc2_right : (memSlice gt hi mem).countP (piv < ·) = hi - gt := by
    rw [List.countP_eq_length.mpr, length_memSlice]
    intro v hv
    obtain ⟨a, ha1, ha2, rfl⟩ := mem_memSlice_iff.mp hv
    exact decide_eq_true (hgt a ha1 ha2)
  refine ⟨hlt_lt, ?_, ?_⟩
  · rw [← hperm.countP_eq, hsplit, List.countP_append, List.countP_append,
      hc1_left, hc1_mid, hc1_right, add_zero, add_zero]
  · rw [← hperm.countP_eq, hsplit, List.countP_append, List.countP_append,
      hc2_left, hc2_mid, hc2_right, zero_add, zero_add]

/-- On a sorted list `zs` (`Pairwise (· ≤ ·)`), at index `r < zs.length`, at most `r` elements are
strictly less than `zs[r]` and at most `zs.length - 1 - r` elements are strictly greater than
`zs[r]`. -/
theorem sorted_countP_bounds {zs : List ℕ} (hsorted : zs.Pairwise (· ≤ ·))
    {r : ℕ} (hr : r < zs.length) :
    zs.countP (· < zs[r]) ≤ r ∧ zs.countP (zs[r] < ·) ≤ zs.length - 1 - r := by
  have hp := List.pairwise_iff_getElem.mp hsorted
  let v := zs[r]
  change zs.countP (· < v) ≤ r ∧ zs.countP (v < ·) ≤ zs.length - 1 - r
  refine ⟨?_, ?_⟩
  · have hsplit : zs.countP (· < v) =
        (zs.take r).countP (· < v) + (zs.drop r).countP (· < v) := by
      conv_lhs => rw [← List.take_append_drop r zs]
      exact List.countP_append
    have hdrop0 : (zs.drop r).countP (· < v) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [List.getElem_drop]
      have hle : v ≤ zs[r + k]'(by simp only [List.length_drop] at hk; omega) := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp [v]
        · exact hp r (r + k) hr (by simp only [List.length_drop] at hk; omega) (by omega)
      simp [Nat.not_lt.mpr hle]
    rw [hsplit, hdrop0, add_zero]
    exact List.countP_le_length.trans (by simp [Nat.le_of_lt hr])
  · have hsplit : zs.countP (v < ·) =
        (zs.take (r + 1)).countP (v < ·) + (zs.drop (r + 1)).countP (v < ·) := by
      conv_lhs => rw [← List.take_append_drop (r + 1) zs]
      exact List.countP_append
    have htake0 : (zs.take (r + 1)).countP (v < ·) = 0 := by
      rw [List.countP_eq_zero]
      intro x hx
      rw [List.mem_iff_getElem] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [List.getElem_take]
      have hk_le : k ≤ r := by simp only [List.length_take] at hk; omega
      have hle : zs[k]'(by omega) ≤ v := by
        rcases eq_or_lt_of_le hk_le with rfl | hlt
        · exact le_rfl
        · exact hp k r (by omega) hr hlt
      simp [Nat.not_lt.mpr hle]
    rw [hsplit, htake0, zero_add]
    exact List.countP_le_length.trans (by simp; omega)

private theorem list_map_sum_eq_sum_range (l : List ℕ) (g : ℕ → ℝ) :
    (l.map g).sum = ∑ r ∈ Finset.range l.length, g (l.getD r 0) := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ih]
    simp [add_comm]

/-- Expected child `subCost` summed over all `m = u.length` uniform pivot choices is bounded by
`∑ r < m, (subCost r + subCost (m - 1 - r))`, even in the presence of duplicate keys. -/
theorem sum_subCost_pivot_le (u : List ℕ) :
    ∑ k : Fin u.length,
      (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))) ≤
        ∑ r ∈ Finset.range u.length, (subCost r + subCost (u.length - 1 - r)) := by
  have hperm : u.Perm u.mergeSort := (List.mergeSort_perm u _).symm
  have hlen : u.mergeSort.length = u.length := hperm.length_eq.symm
  let g : ℕ → ℝ := fun piv => subCost (u.countP (· < piv)) + subCost (u.countP (piv < ·))
  have hsum_u : ∑ k : Fin u.length, g u[k.val] = (u.map g).sum := by
    rw [Finset.sum_fin_eq_sum_range, list_map_sum_eq_sum_range]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    simp [hr, List.getD_eq_getElem?_getD]
  rw [hsum_u, (hperm.map g).sum_eq, list_map_sum_eq_sum_range, hlen]
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
  have hb2 : u.mergeSort.countP (u.mergeSort[r] < ·) ≤ u.length - 1 - r := hlen ▸ hb.2
  exact add_le_add (subCost_mono hb.1) (subCost_mono hb2)

/-! ## Word-size arithmetic (`logWidth 3 n ≤ w`) and work-stack invariants -/

/-- `logWidth 3 n ≤ w` suffices to fit every address and temporary up to `3 * n + 3` for all
`n : ℕ` (including `n = 0`). -/
theorem fits_three_mul_add_three {n w : ℕ} (hw : logWidth 3 n ≤ w) :
    Fits w (3 * n + 3) := by
  rcases lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · have hw3 : 3 ≤ w := by simpa [logWidth] using hw
      exact Fits.mono (w := 3) (by decide) hw3
    · have hw3 : 3 ≤ w := by simpa [logWidth] using hw
      exact Fits.mono (w := 3) (by decide) hw3
  · have hcube : 3 * n + 3 < (n + 1) ^ 3 := by
      have hexp : (n + 1) ^ 3 = (n + 1) * (n + 1) * (n + 1) := by ring
      rw [hexp]
      nlinarith
    exact (fits_of_lt_pow hcube).mono hw

/-- Two half-open intervals `[a₁, b₁)` and `[a₂, b₂)` are disjoint. -/
def IntervalDisjoint (p q : ℕ × ℕ) : Prop :=
  p.2 ≤ q.1 ∨ q.2 ≤ p.1

theorem IntervalDisjoint.symm {p q : ℕ × ℕ} (h : IntervalDisjoint p q) :
    IntervalDisjoint q p :=
  Or.symm h

private def stackFootprint (S : List (ℕ × ℕ)) : Finset ℕ :=
  S.foldr (fun q acc => Finset.Ico q.1 q.2 ∪ acc) ∅

private theorem mem_stackFootprint {x : ℕ} {S : List (ℕ × ℕ)}
    (hx : x ∈ stackFootprint S) : ∃ q ∈ S, x ∈ Finset.Ico q.1 q.2 := by
  induction S with
  | nil => simp [stackFootprint] at hx
  | cons q rest ih =>
    rw [stackFootprint, List.foldr_cons, Finset.mem_union] at hx
    rcases hx with hxq | hxrest
    · exact ⟨q, List.mem_cons_self, hxq⟩
    · obtain ⟨q', hq', hxq'⟩ := ih hxrest
      exact ⟨q', List.mem_cons_of_mem q hq', hxq'⟩

private theorem sum_len_eq_card_stackFootprint {S : List (ℕ × ℕ)}
    (hpwd : S.Pairwise IntervalDisjoint) :
    (S.map fun p => p.2 - p.1).sum = (stackFootprint S).card := by
  induction S with
  | nil => simp [stackFootprint]
  | cons p tl ih =>
    have hdisj : Disjoint (Finset.Ico p.1 p.2) (stackFootprint tl) := by
      rw [Finset.disjoint_left]
      intro x hxp hxtl
      obtain ⟨q, hq, hxq⟩ := mem_stackFootprint hxtl
      have hpq := List.rel_of_pairwise_cons hpwd hq
      rw [Finset.mem_Ico] at hxp hxq
      rcases hpq with h1 | h2 <;> omega
    have hunfold : stackFootprint (p :: tl) = Finset.Ico p.1 p.2 ∪ stackFootprint tl := rfl
    rw [hunfold, Finset.card_union_of_disjoint hdisj,
      Nat.card_Ico, List.map_cons, List.sum_cons, ih hpwd.of_cons]

/-- Every interval `(a, b) ∈ S` satisfies `1 ≤ a`, `a + 2 ≤ b`, and `b ≤ n + 1`, and the intervals
in `S` are pairwise disjoint. -/
def ValidStack (n : ℕ) (S : List (ℕ × ℕ)) : Prop :=
  (∀ p ∈ S, 1 ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 ≤ n + 1) ∧ S.Pairwise IntervalDisjoint

/-- Sum of lengths `∑ (b - a)` of intervals in `S` is at most `n` when `ValidStack n S` holds. -/
theorem ValidStack.sum_len_le {n : ℕ} {S : List (ℕ × ℕ)} (hS : ValidStack n S) :
    (S.map fun p => p.2 - p.1).sum ≤ n := by
  have hsub : stackFootprint S ⊆ Finset.Ico 1 (n + 1) := by
    intro x hx
    obtain ⟨q, hq, hxq⟩ := mem_stackFootprint hx
    have hb := hS.1 q hq
    rw [Finset.mem_Ico] at hxq ⊢
    omega
  calc
    (S.map fun p => p.2 - p.1).sum = (stackFootprint S).card :=
      sum_len_eq_card_stackFootprint hS.2
    _ ≤ (Finset.Ico 1 (n + 1)).card := Finset.card_le_card hsub
    _ = n := by simp

/-- Twice `S.length` is at most `n` when `ValidStack n S` holds. -/
theorem ValidStack.two_mul_length_le {n : ℕ} {S : List (ℕ × ℕ)} (hS : ValidStack n S) :
    2 * S.length ≤ n := by
  have htwo : 2 * S.length ≤ (S.map fun p => p.2 - p.1).sum := by
    obtain ⟨hbnd, -⟩ := hS
    induction S with
    | nil => simp
    | cons p tl ih =>
      have hp := hbnd p List.mem_cons_self
      have hih := ih fun q hq => hbnd q (List.mem_cons_of_mem p hq)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  exact htwo.trans hS.sum_len_le

/-- Global cross-interval order invariant: every pair `1 ≤ i < j < n + 1` not jointly contained in
any active stack interval `(a, b) ∈ S` is already ordered (`mem i ≤ mem j`). -/
def NoExternalInversions (n : ℕ) (mem : ℕ → ℕ) (S : List (ℕ × ℕ)) : Prop :=
  ∀ i j, 1 ≤ i → i < j → j < n + 1 →
    (∀ p ∈ S, ¬(p.1 ≤ i ∧ j < p.2)) → mem i ≤ mem j

/-! ## Structured WordRAM quicksort program (`r = 16`) -/

namespace Reg

/-- Constant `0`. -/
@[simp] abbrev zero : Fin 16 := 0
/-- Constant `1`. -/
@[simp] abbrev one : Fin 16 := 1
/-- Constant `2`. -/
@[simp] abbrev two : Fin 16 := 2
/-- Input array length `n`. -/
@[simp] abbrev len : Fin 16 := 3
/-- Base address `n + 1` of the `lo` work-stack array. -/
@[simp] abbrev stackLo : Fin 16 := 4
/-- Base address `2 * n + 1` of the `hi` work-stack array. -/
@[simp] abbrev stackHi : Fin 16 := 5
/-- Current stack pointer (`S.length`). -/
@[simp] abbrev sp : Fin 16 := 6
/-- Active subarray start address `lo`. -/
@[simp] abbrev lo : Fin 16 := 7
/-- Active subarray exclusive end address `hi`. -/
@[simp] abbrev hi : Fin 16 := 8
/-- 3-way partition `< piv` boundary `lt`. -/
@[simp] abbrev lt : Fin 16 := 9
/-- 3-way partition scan cursor `cur` (and `alloc` scratch during setup). -/
@[simp] abbrev cur : Fin 16 := 10
/-- 3-way partition `> piv` boundary `gt` (and `alloc` frontier during setup). -/
@[simp] abbrev gt : Fin 16 := 11
/-- Pivot value `piv`. -/
@[simp] abbrev piv : Fin 16 := 12
/-- Element scratch `val`. -/
@[simp] abbrev val : Fin 16 := 13
/-- Swap scratch `val2`. -/
@[simp] abbrev val2 : Fin 16 := 14
/-- Address / offset scratch `tmp`. -/
@[simp] abbrev tmp : Fin 16 := 15

end Reg

open Reg

/-- Swap memory cells `*a` and `*b` using scratch registers `v1, v2` (`4` instructions). -/
def swapCells (a b v1 v2 : Fin 16) : Code .standard 16 := ram[
  v1 ← *a;
  v2 ← *b;
  *a ← v2;
  *b ← v1 ]

/-- One Dutch National Flag 3-way partition step at cursor `cur` (`≤ 9` instructions). -/
def partStep : Code .standard 16 := ram[
  val ← *cur;
  if val < piv then [
    ⟪swapCells lt cur val val2⟫;
    lt ← lt + one;
    cur ← cur + one
  ] else [
    if piv < val then [
      gt ← gt - one;
      ⟪swapCells cur gt val val2⟫
    ] else [
      cur ← cur + one
    ]
  ] ]

/-- Push `[regs a, regs b)` onto `(stackLo, stackHi)` if `regs a + 2 ≤ regs b`. -/
def pushIfNonTrivial (a b : Fin 16) : Code .standard 16 := ram[
  tmp ← a + two;
  if b < tmp then [
    sp ← sp
  ] else [
    ⟪writeAt tmp stackLo sp a⟫;
    ⟪writeAt tmp stackHi sp b⟫;
    sp ← sp + one
  ] ]

/-- Deterministic prefix of `popAndSample`: decrement `sp`, load `lo` and `hi`, and compute
`tmp = hi - lo - 1` (`7` instructions). -/
def popPrefix : Code .standard 16 := ram[
  sp ← sp - one;
  ⟪readAt tmp lo stackLo sp⟫;
  ⟪readAt tmp hi stackHi sp⟫;
  tmp ← hi - lo;
  tmp ← tmp - one ]

/-- Pop the top range `[lo, hi)` from the stack and sample `tmp ← rand (hi - lo - 1)`. -/
def popAndSample : Code .standard 16 := ram[
  ⟪popPrefix⟫;
  tmp ← rand tmp ]

/-- Load pivot at `lo + tmp` and initialize `lt ← lo`, `cur ← lo`, `gt ← hi` (`5`
instructions). -/
def partInit : Code .standard 16 := ram[
  tmp ← lo + tmp;
  piv ← *tmp;
  lt ← lo;
  cur ← lo;
  gt ← hi ]

/-- Read the sampled pivot at `lo + tmp`, 3-way partition `[lo, hi)`, and push non-trivial
subranges `[lo, lt)` and `[gt, hi)`. -/
def partitionAndPush : Code .standard 16 := ram[
  ⟪partInit⟫;
  while cur < gt do [ ⟪partStep⟫ ];
  ⟪pushIfNonTrivial lo lt⟫;
  ⟪pushIfNonTrivial gt hi⟫ ]

/-- One iteration of the outer work-stack loop. -/
def outerBody : Code .standard 16 := ram[
  ⟪popAndSample⟫;
  ⟪partitionAndPush⟫ ]

/-- Allocate `stackLo` and `stackHi` of capacity `n` and push `[1, n + 1)` if `n ≥ 2`. -/
def setup : Code .standard 16 := ram[
  len ← *zero;
  one ← #1;
  gt ← len + one;
  ⟪alloc gt len stackLo cur zero one⟫;
  ⟪alloc gt len stackHi cur zero one⟫;
  two ← one + one;
  sp ← #0;
  lo ← one;
  hi ← len + one;
  ⟪pushIfNonTrivial lo hi⟫ ]

/-- Structured in-place 3-way randomized quicksort over 16 registers. -/
def code : Code .standard 16 := ram[
  ⟪setup⟫;
  while zero < sp do [ ⟪outerBody⟫ ] ]

/-- Compiled flat randomized quicksort program halting with `0` (in `zero`). -/
def program : Program .standard 16 :=
  code.program zero

/-- Quadratic worst-case instruction budget `20 * n ^ 2 + 8 * n + 32`. -/
def worstCaseTime (n : ℕ) : ℕ :=
  20 * n ^ 2 + 8 * n + 32

/-- `O(n log n)` expected instruction budget `120 * n * (⌊log₂ n⌋ + 1) + 32`. -/
def expectedTimeBound (n : ℕ) : ℕ :=
  120 * n * (Nat.log 2 n + 1) + 32

/-! ## Subroutine executions and partition invariants -/

/-- Swap two memory cells at addresses `p` and `q`. -/
def swapMem (mem : ℕ → ℕ) (p q : ℕ) : ℕ → ℕ :=
  Function.update (Function.update mem p (mem q)) q (mem p)

@[simp]
theorem swapMem_right (mem : ℕ → ℕ) (p q : ℕ) : swapMem mem p q q = mem p := by
  simp [swapMem]

@[simp]
theorem swapMem_left (mem : ℕ → ℕ) (p q : ℕ) : swapMem mem p q p = mem q := by
  by_cases hpq : p = q
  · subst hpq; simp [swapMem]
  · simp [swapMem, hpq]

theorem swapMem_of_ne {mem : ℕ → ℕ} {p q a : ℕ} (hap : a ≠ p) (haq : a ≠ q) :
    swapMem mem p q a = mem a := by
  simp [swapMem, hap, haq]

theorem modifies_swapMem {lo hi p q : ℕ} (hp : lo ≤ p ∧ p < hi) (hq : lo ≤ q ∧ q < hi)
    (mem : ℕ → ℕ) : Modifies (Finset.Ico lo hi) mem (swapMem mem p q) := by
  intro a ha
  rw [Finset.mem_Ico] at ha
  exact swapMem_of_ne (by omega) (by omega)

/-- `swapCells a b v1 v2` executes in `4` instructions, swapping `mem (regs a)` and `mem (regs b)`
and writing only scratch registers `v1, v2`. -/
theorem swapCells_exec {w : ℕ} {a b v1 v2 : Fin 16} {x : Data 16}
    (ha1 : a ≠ v1) (hb1 : b ≠ v1) (ha2 : a ≠ v2) (hb2 : b ≠ v2) (hv : v1 ≠ v2) :
    Exec w (swapCells a b v1 v2) x
      ⟨Function.update (Function.update x.regs v1 (x.mem (x.regs a))) v2 (x.mem (x.regs b)),
        swapMem x.mem (x.regs a) (x.regs b)⟩ 4 := by
  set x₁ := x.set v1 (x.mem (x.regs a))
  set x₂ := x₁.set v2 (x.mem (x.regs b))
  set x₃ := x₂.write (x.regs a) (x.mem (x.regs b))
  set x₄ := x₃.write (x.regs b) (x.mem (x.regs a))
  have e₁ : Exec (B := .standard) w (.op (.load v1 a)) x x₁ 1 := Exec.load
  have e₂ : Exec (B := .standard) w (.op (.load v2 b)) x₁ x₂ 1 := by
    have hb : x₁.regs b = x.regs b := by simp [x₁, hb1]
    simpa [x₂, hb, x₁] using Exec.load (w := w) (d := v2) (a := b) (x := x₁)
  have e₃ : Exec (B := .standard) w (.op (.store a v2)) x₂ x₃ 1 := by
    have ha : x₂.regs a = x.regs a := by simp [x₂, x₁, ha2, ha1]
    have hv2 : x₂.regs v2 = x.mem (x.regs b) := by simp [x₂]
    simpa [x₃, ha, hv2] using Exec.store (w := w) (a := a) (s := v2) (x := x₂)
  have e₄ : Exec (B := .standard) w (.op (.store b v1)) x₃ x₄ 1 := by
    have hb : x₃.regs b = x.regs b := by simp [x₃, x₂, x₁, hb2, hb1]
    have hv1 : x₃.regs v1 = x.mem (x.regs a) := by simp [x₃, x₂, x₁, hv]
    simpa [x₄, hb, hv1] using Exec.store (w := w) (a := b) (s := v1) (x := x₃)
  exact e₁.seq (e₂.seq (e₃.seq e₄))

/-- Dutch National Flag 3-way partition loop invariant on `[lo, hi)`. -/
structure PartInv (w vlo vhi vpiv : ℕ) (mem₀ : ℕ → ℕ) (x : Data 16) : Prop where
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `lo` holds `vlo`. -/
  lo_eq : x.regs lo = vlo
  /-- Register `hi` holds `vhi`. -/
  hi_eq : x.regs hi = vhi
  /-- Register `piv` holds `vpiv`. -/
  piv_eq : x.regs piv = vpiv
  /-- `vhi` fits in `w` bits. -/
  fits_hi : Fits w vhi
  /-- `vlo ≤ lt`. -/
  lo_le_lt : vlo ≤ x.regs lt
  /-- `lt ≤ cur`. -/
  lt_le_cur : x.regs lt ≤ x.regs cur
  /-- `cur ≤ gt`. -/
  cur_le_gt : x.regs cur ≤ x.regs gt
  /-- `gt ≤ vhi`. -/
  gt_le_hi : x.regs gt ≤ vhi
  /-- `mem[vlo .. vhi)` is a permutation of `mem₀[vlo .. vhi)`. -/
  perm : (memSlice vlo vhi x.mem).Perm (memSlice vlo vhi mem₀)
  /-- Only `Finset.Ico vlo vhi` has been modified since `mem₀`. -/
  modifies : Modifies (Finset.Ico vlo vhi) mem₀ x.mem
  /-- `[vlo, lt)` holds elements `< vpiv`. -/
  lt_zone : ∀ a, vlo ≤ a → a < x.regs lt → x.mem a < vpiv
  /-- `[lt, cur)` holds elements `= vpiv`. -/
  eq_zone : ∀ a, x.regs lt ≤ a → a < x.regs cur → x.mem a = vpiv
  /-- `[gt, vhi)` holds elements `> vpiv`. -/
  gt_zone : ∀ a, x.regs gt ≤ a → a < vhi → vpiv < x.mem a

private theorem partStep_lt {w vlo vhi vpiv : ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : PartInv w vlo vhi vpiv mem₀ x) (hcg : x.regs cur < x.regs gt)
    (hlt_piv : x.mem (x.regs cur) < vpiv) :
    ∃ y, ExecWithin w partStep x y 9 ∧
      PartInv w vlo vhi vpiv mem₀ y ∧ y.regs gt - y.regs cur < x.regs gt - x.regs cur := by
  have h1 := hI.lo_le_lt; have h2 := hI.lt_le_cur; have h3 := hI.gt_le_hi
  have h1' : vlo ≤ x.regs 9 := h1
  have h2' : x.regs 9 ≤ x.regs 10 := h2
  have h3' : x.regs 11 ≤ vhi := h3
  have hcg' : x.regs 10 < x.regs 11 := hcg
  have hgt_eq : x.regs gt = x.regs 11 := rfl
  set x₁ := x.set val (x.mem (x.regs cur))
  have e_load : ExecWithin (B := .standard) w (.op (.load val cur)) x x₁ 1 := ExecWithin.load
  have hc_pos : (Cond.lt val piv).Holds x₁ := by
    simp [Cond.holds_lt, x₁, hI.piv_eq, hlt_piv]
  have eswap := (swapCells_exec (w := w) (a := lt) (b := cur) (v1 := val) (v2 := val2) (x := x₁)
    (by decide) (by decide) (by decide) (by decide) (by decide)).within
  set x₂ : Data 16 :=
    ⟨Function.update (Function.update x₁.regs val (x₁.mem (x₁.regs lt))) val2
      (x₁.mem (x₁.regs cur)), swapMem x₁.mem (x₁.regs lt) (x₁.regs cur)⟩
  have hlt2 : x₂.regs lt = x.regs lt := by simp [x₂, x₁]
  have hcur2 : x₂.regs cur = x.regs cur := by simp [x₂, x₁]
  have hone2 : x₂.regs one = 1 := by simp [x₂, x₁, hI.one_eq]
  have e_lt : ExecWithin w (.op (.bin .add lt lt one)) x₂ (x₂.set lt (x.regs lt + 1)) 1 := by
    simpa [hlt2, hone2, BinOp.eval] using ExecWithin.bin (w := w) (f := .add) (d := lt)
      (i := lt) (j := one) (x := x₂)
      (hI.fits_hi.of_le (by simp [hlt2, hone2, BinOp.eval]; omega))
  set x₃ := x₂.set lt (x.regs lt + 1)
  have hcur3 : x₃.regs cur = x.regs cur := by simp [x₃, hcur2]
  have hone3 : x₃.regs one = 1 := by simp [x₃, hone2]
  have e_cur : ExecWithin w (.op (.bin .add cur cur one)) x₃ (x₃.set cur (x.regs cur + 1)) 1 := by
    simpa [hcur3, hone3, BinOp.eval] using ExecWithin.bin (w := w) (f := .add) (d := cur)
      (i := cur) (j := one) (x := x₃)
      (hI.fits_hi.of_le (by simp [hcur3, hone3, BinOp.eval]; omega))
  set y := x₃.set cur (x.regs cur + 1)
  have e_step : ExecWithin w partStep x y 9 :=
    (e_load.seq (ExecWithin.branch_pos hc_pos (eswap.seq (e_lt.seq e_cur)))).mono (by omega)
  have hymem : y.mem = swapMem x.mem (x.regs lt) (x.regs cur) := by simp [y, x₃, x₂, x₁]
  have hperm_y : (memSlice vlo vhi y.mem).Perm (memSlice vlo vhi mem₀) := by
    rw [hymem]
    exact (memSlice_swap_perm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x.mem).trans hI.perm
  have hmod_y : Modifies (Finset.Ico vlo vhi) mem₀ y.mem := by
    rw [hymem]
    simpa only [Finset.union_idempotent] using hI.modifies.trans
      (modifies_swapMem (lo := vlo) (hi := vhi) (p := x.regs lt) (q := x.regs cur)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x.mem)
  refine ⟨y, e_step, ?_, ?_⟩
  · refine ⟨by simp [y, x₃, hone2], by simp [y, x₃, x₂, x₁, hI.lo_eq],
      by simp [y, x₃, x₂, x₁, hI.hi_eq], by simp [y, x₃, x₂, x₁, hI.piv_eq], hI.fits_hi,
      by simp [y, x₃]; omega, by simp [y, x₃]; omega, by simp [y, x₃, x₂, x₁]; omega,
      by simp [y, x₃, x₂, x₁]; omega, hperm_y, hmod_y, ?_, ?_, ?_⟩
    · intro a ha1 ha2
      simp only [y, x₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ cur),
        Function.update_self] at ha2
      rw [hymem]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | halt
      · simpa using hlt_piv
      · rw [swapMem_of_ne (by omega) (by omega)]
        exact hI.lt_zone a ha1 halt
    · intro a ha1 ha2
      simp only [y, x₃, Data.set_regs, Function.update_of_ne (by decide : lt ≠ cur),
        Function.update_self] at ha1 ha2
      rw [hymem]
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | hacur
      · rw [swapMem_right]
        exact hI.eq_zone (x.regs lt) le_rfl (by omega)
      · rw [swapMem_of_ne (by omega) (by omega)]
        exact hI.eq_zone a (by omega) hacur
    · intro a ha1 ha2
      simp only [y, x₃, x₂, x₁, Data.set_regs, Function.update_of_ne (by decide : gt ≠ cur),
        Function.update_of_ne (by decide : gt ≠ lt), Function.update_of_ne (by decide : gt ≠ val2),
        Function.update_of_ne (by decide : gt ≠ val)] at ha1
      rw [hymem, swapMem_of_ne (by omega) (by omega)]
      exact hI.gt_zone a ha1 ha2
  · simp [y, x₃, x₂, x₁]; omega

private theorem partStep_gt {w vlo vhi vpiv : ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : PartInv w vlo vhi vpiv mem₀ x) (hcg : x.regs cur < x.regs gt)
    (hnlt : ¬x.mem (x.regs cur) < vpiv) (hgt_piv : vpiv < x.mem (x.regs cur)) :
    ∃ y, ExecWithin w partStep x y 9 ∧
      PartInv w vlo vhi vpiv mem₀ y ∧ y.regs gt - y.regs cur < x.regs gt - x.regs cur := by
  have h1 := hI.lo_le_lt; have h2 := hI.lt_le_cur; have h3 := hI.gt_le_hi
  have h1' : vlo ≤ x.regs 9 := h1
  have h2' : x.regs 9 ≤ x.regs 10 := h2
  have h3' : x.regs 11 ≤ vhi := h3
  have hcg' : x.regs 10 < x.regs 11 := hcg
  have hgt_eq : x.regs gt = x.regs 11 := rfl
  set x₁ := x.set val (x.mem (x.regs cur))
  have e_load : ExecWithin (B := .standard) w (.op (.load val cur)) x x₁ 1 := ExecWithin.load
  have hc_neg : ¬(Cond.lt val piv).Holds x₁ := by
    simp [Cond.holds_lt, x₁, hI.piv_eq, hnlt]
  have hc2_pos : (Cond.lt piv val).Holds x₁ := by
    simp [Cond.holds_lt, x₁, hI.piv_eq, hgt_piv]
  have hgt1 : x₁.regs gt = x.regs gt := by simp [x₁]
  have hone1 : x₁.regs one = 1 := by simp [x₁, hI.one_eq]
  have e_gt : ExecWithin w (.op (.bin .sub gt gt one)) x₁ (x₁.set gt (x.regs gt - 1)) 1 := by
    simpa [hgt1, hone1, BinOp.eval] using ExecWithin.bin (w := w) (f := .sub) (d := gt)
      (i := gt) (j := one) (x := x₁)
      (hI.fits_hi.of_le (by simp [hgt1, hone1, BinOp.eval]; omega))
  set x₂ := x₁.set gt (x.regs gt - 1)
  have eswap := (swapCells_exec (w := w) (a := cur) (b := gt) (v1 := val) (v2 := val2) (x := x₂)
    (by decide) (by decide) (by decide) (by decide) (by decide)).within
  set y : Data 16 :=
    ⟨Function.update (Function.update x₂.regs val (x₂.mem (x₂.regs cur))) val2
      (x₂.mem (x₂.regs gt)), swapMem x₂.mem (x₂.regs cur) (x₂.regs gt)⟩
  have e_step : ExecWithin w partStep x y 9 :=
    (e_load.seq (ExecWithin.branch_neg hc_neg
      (ExecWithin.branch_pos hc2_pos (e_gt.seq eswap)))).mono (by omega)
  have hymem : y.mem = swapMem x.mem (x.regs cur) (x.regs gt - 1) := by simp [y, x₂, x₁]
  have hperm_y : (memSlice vlo vhi y.mem).Perm (memSlice vlo vhi mem₀) := by
    rw [hymem]
    exact (memSlice_swap_perm ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x.mem).trans hI.perm
  have hmod_y : Modifies (Finset.Ico vlo vhi) mem₀ y.mem := by
    rw [hymem]
    simpa only [Finset.union_idempotent] using hI.modifies.trans
      (modifies_swapMem (lo := vlo) (hi := vhi) (p := x.regs cur) (q := x.regs gt - 1)
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ x.mem)
  refine ⟨y, e_step, ?_, ?_⟩
  · refine ⟨by simp [y, x₂, x₁, hI.one_eq], by simp [y, x₂, x₁, hI.lo_eq],
      by simp [y, x₂, x₁, hI.hi_eq], by simp [y, x₂, x₁, hI.piv_eq], hI.fits_hi,
      by simp [y, x₂, x₁]; omega, by simp [y, x₂, x₁]; omega, by simp [y, x₂, x₁]; omega,
      by simp [y, x₂, x₁]; omega, hperm_y, hmod_y, ?_, ?_, ?_⟩
    · intro a ha1 ha2
      simp only [y, x₂, x₁, Data.set_regs, Function.update_of_ne (by decide : lt ≠ val2),
        Function.update_of_ne (by decide : lt ≠ val),
        Function.update_of_ne (by decide : lt ≠ gt)] at ha2
      rw [hymem, swapMem_of_ne (by omega) (by omega)]
      exact hI.lt_zone a ha1 ha2
    · intro a ha1 ha2
      simp only [y, x₂, x₁, Data.set_regs, Function.update_of_ne (by decide : lt ≠ val2),
        Function.update_of_ne (by decide : lt ≠ val), Function.update_of_ne (by decide : lt ≠ gt),
        Function.update_of_ne (by decide : cur ≠ val2),
        Function.update_of_ne (by decide : cur ≠ val),
        Function.update_of_ne (by decide : cur ≠ gt)] at ha1 ha2
      rw [hymem, swapMem_of_ne (by omega) (by omega)]
      exact hI.eq_zone a ha1 ha2
    · intro a ha1 ha2
      simp only [y, x₂, x₁, Data.set_regs, Function.update_of_ne (by decide : gt ≠ val2),
        Function.update_of_ne (by decide : gt ≠ val), Function.update_self] at ha1
      rw [hymem]
      rcases eq_or_lt_of_le ha1 with h_eq | h_gt
      · subst h_eq
        simpa using hgt_piv
      · rw [swapMem_of_ne (by omega) (by omega)]
        exact hI.gt_zone a (by omega) ha2
  · simp [y, x₂, x₁]; omega

private theorem partStep_eq {w vlo vhi vpiv : ℕ} {mem₀ : ℕ → ℕ} {x : Data 16}
    (hI : PartInv w vlo vhi vpiv mem₀ x) (hcg : x.regs cur < x.regs gt)
    (hnlt : ¬x.mem (x.regs cur) < vpiv) (hngt : ¬vpiv < x.mem (x.regs cur)) :
    ∃ y, ExecWithin w partStep x y 9 ∧
      PartInv w vlo vhi vpiv mem₀ y ∧ y.regs gt - y.regs cur < x.regs gt - x.regs cur := by
  have h1 := hI.lo_le_lt; have h2 := hI.lt_le_cur; have h3 := hI.gt_le_hi
  simp only [lt, cur, gt] at h1 h2 h3 hcg
  set x₁ := x.set val (x.mem (x.regs cur))
  have e_load : ExecWithin (B := .standard) w (.op (.load val cur)) x x₁ 1 := ExecWithin.load
  have hc_neg : ¬(Cond.lt val piv).Holds x₁ := by simp [Cond.holds_lt, x₁, hI.piv_eq, hnlt]
  have hc2_neg : ¬(Cond.lt piv val).Holds x₁ := by simp [Cond.holds_lt, x₁, hI.piv_eq, hngt]
  have hcur1 : x₁.regs cur = x.regs cur := by simp [x₁]
  have hone1 : x₁.regs one = 1 := by simp [x₁, hI.one_eq]
  have e_cur : ExecWithin w (.op (.bin .add cur cur one)) x₁ (x₁.set cur (x.regs cur + 1)) 1 := by
    simpa [hcur1, hone1, BinOp.eval] using ExecWithin.bin (w := w) (f := .add) (d := cur)
      (i := cur) (j := one) (x := x₁)
      (hI.fits_hi.of_le (by simp [hcur1, hone1, BinOp.eval]; omega))
  set y := x₁.set cur (x.regs cur + 1)
  have e_step : ExecWithin w partStep x y 9 :=
    (e_load.seq (ExecWithin.branch_neg hc_neg
      (ExecWithin.branch_neg hc2_neg e_cur))).mono (by omega)
  refine ⟨y, e_step, ?_, ?_⟩
  · refine ⟨by simp [y, x₁, hI.one_eq], by simp [y, x₁, hI.lo_eq], by simp [y, x₁, hI.hi_eq],
      by simp [y, x₁, hI.piv_eq], hI.fits_hi, by simp [y, x₁]; omega, by simp [y, x₁]; omega,
      by simp [y, x₁]; omega, by simp [y, x₁]; omega, hI.perm, hI.modifies, hI.lt_zone, ?_,
      hI.gt_zone⟩
    intro a ha1 ha2
    simp only [y, x₁, Data.set_regs, Function.update_of_ne (by decide : lt ≠ cur),
      Function.update_of_ne (by decide : lt ≠ val), Function.update_self] at ha1 ha2
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ ha2) with rfl | hacur
    · simp only [y, x₁, Data.set_mem]; omega
    · exact hI.eq_zone a ha1 hacur
  · simp [y, x₁]; omega

/-- Full 3-way partition loop executes within `11 * (vhi - vlo) + 2` instructions and exits with
`cur = gt`. -/
theorem partLoop_spec {w vlo vhi vpiv : ℕ} {x : Data 16} (hI : PartInv w vlo vhi vpiv x.mem x)
    (_hlt_init : x.regs lt = vlo) (hcur_init : x.regs cur = vlo) (hgt_init : x.regs gt = vhi) :
    ∃ y, ExecWithin w (ram[ while cur < gt do [ ⟪partStep⟫ ] ]) x y (11 * (vhi - vlo) + 2) ∧
      PartInv w vlo vhi vpiv x.mem y ∧ y.regs cur = y.regs gt := by
  obtain ⟨y, hy, hIy, hnc⟩ := ExecWithin.loop_invariant
    (cond := Cond.lt cur gt) (body := partStep) (PartInv w vlo vhi vpiv x.mem)
    (fun z => z.regs gt - z.regs cur) (T := 9)
    (fun z hz hcz => by
      change z.regs cur < z.regs gt at hcz
      by_cases h1 : z.mem (z.regs cur) < vpiv
      · exact partStep_lt hz hcz h1
      · by_cases h2 : vpiv < z.mem (z.regs cur)
        · exact partStep_gt hz hcz h1 h2
        · exact partStep_eq hz hcz h1 h2) hI
  have hcg_eq : y.regs cur = y.regs gt := by
    change ¬y.regs cur < y.regs gt at hnc
    have := hIy.cur_le_gt
    omega
  refine ⟨y, hy.mono ?_, hIy, hcg_eq⟩
  rw [hgt_init, hcur_init]
  omega

/-! ## Work-stack representation and `pushIfNonTrivial` -/

/-- Read the active work-stack directly from `(x.regs sp, x.mem)` at base addresses `n + 1` and
`2 * n + 1`. -/
def readStack (n : ℕ) (x : Data 16) : List (ℕ × ℕ) :=
  (List.range (x.regs sp)).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))

@[simp]
theorem length_readStack (n : ℕ) (x : Data 16) : (readStack n x).length = x.regs sp := by
  simp [readStack]

theorem readStack_congr {n : ℕ} {x y : Data 16} (hsp : y.regs sp = x.regs sp)
    (hmem : ∀ a, n + 1 ≤ a → y.mem a = x.mem a) : readStack n y = readStack n x := by
  simp only [readStack, hsp]
  refine List.map_congr_left fun i _ => ?_
  rw [hmem (n + 1 + i) (by omega), hmem (2 * n + 1 + i) (by omega)]

/-- `pushIfNonTrivial a b` runs within `8` instructions, appending `(va, vb)` to `readStack n` iff
`va + 2 ≤ vb`, and modifying memory only inside `Finset.Ico (n + 1) (3 * n + 1)`. -/
theorem pushIfNonTrivial_spec {w n : ℕ} {a b : Fin 16} {x : Data 16}
    (ha_tmp : a ≠ tmp) (hb_tmp : b ≠ tmp)
    (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hsLo : x.regs stackLo = n + 1) (hsHi : x.regs stackHi = 2 * n + 1)
    (hfit_all : Fits w (3 * n + 3))
    (hvb : x.regs a ≤ n + 1 ∧ x.regs b ≤ n + 1)
    (hcap : x.regs a + 2 ≤ x.regs b → x.regs sp < n) :
    ∃ y, ExecWithin w (pushIfNonTrivial a b) x y 8 ∧
      readStack n y =
        (if x.regs a + 2 ≤ x.regs b then readStack n x ++ [(x.regs a, x.regs b)]
         else readStack n x) ∧
      Modifies (Finset.Ico (n + 1) (3 * n + 1)) x.mem y.mem := by
  set va := x.regs a
  set vb := x.regs b
  set k := x.regs sp
  set x₁ := x.set tmp (va + 2)
  have e₁ : ExecWithin w (.op (.bin .add tmp a two)) x x₁ 1 := by
    simpa [x₁, va, htwo, BinOp.eval] using ExecWithin.bin (w := w) (f := .add) (d := tmp)
      (i := a) (j := two) (x := x)
      (hfit_all.of_le (by simp [htwo, BinOp.eval]; omega))
  by_cases hcond : vb < va + 2
  · have hc_pos : (Cond.lt b tmp).Holds x₁ := by simp [Cond.holds_lt, x₁, hb_tmp, vb, hcond]
    have e_nop : ExecWithin (B := .standard) w (.op (.copy sp sp)) x₁ (x₁.set sp (x₁.regs sp)) 1 :=
      ExecWithin.copy
    set y := x₁.set sp (x₁.regs sp)
    refine ⟨y, (e₁.seq (ExecWithin.branch_pos hc_pos e_nop)).mono (by omega), ?_, ?_⟩
    · have hnot : ¬va + 2 ≤ vb := by omega
      simp only [hnot, ↓reduceIte]
      exact readStack_congr (by simp [y, x₁]) (fun _ _ => rfl)
    · exact Modifies.refl _ _
  · have hge : va + 2 ≤ vb := by omega
    have hk_lt : k < n := hcap hge
    have hk6 : x.regs 6 = k := rfl
    have hc_neg : ¬(Cond.lt b tmp).Holds x₁ := by simp [Cond.holds_lt, x₁, hb_tmp, vb, hcond]
    have ew₁ := (writeAt_exec (w := w) (tmp := tmp) (ptr := stackLo) (idx := sp) (src := a)
      (x := x₁) ha_tmp (hfit_all.of_le (by simp [x₁, hsLo, hk6]; omega))).within
    set x₂ := (x₁.set tmp (x₁.regs stackLo + x₁.regs sp)).write
      (x₁.regs stackLo + x₁.regs sp) (x₁.regs a)
    have ew₂ := (writeAt_exec (w := w) (tmp := tmp) (ptr := stackHi) (idx := sp) (src := b)
      (x := x₂) hb_tmp (hfit_all.of_le (by simp [x₂, x₁, hsHi, hk6]; omega))).within
    set x₃ := (x₂.set tmp (x₂.regs stackHi + x₂.regs sp)).write
      (x₂.regs stackHi + x₂.regs sp) (x₂.regs b)
    have hsp3 : x₃.regs sp = k := by simp [x₃, x₂, x₁, k]
    have hone3 : x₃.regs one = 1 := by simp [x₃, x₂, x₁, hone]
    have e_inc : ExecWithin w (.op (.bin .add sp sp one)) x₃ (x₃.set sp (k + 1)) 1 := by
      simpa [hsp3, hone3, BinOp.eval] using ExecWithin.bin (w := w) (f := .add) (d := sp)
        (i := sp) (j := one) (x := x₃)
        (hfit_all.of_le (by simp [hsp3, hone3, BinOp.eval]; omega))
    set y := x₃.set sp (k + 1)
    have hymem : y.mem = Function.update (Function.update x.mem (n + 1 + k) va)
        (2 * n + 1 + k) vb := by
      simp [y, x₃, x₂, x₁, hsLo, hsHi, ha_tmp, hb_tmp, va, vb, k]
    refine ⟨y, (e₁.seq (ExecWithin.branch_neg hc_neg (ew₁.seq (ew₂.seq e_inc)))).mono (by omega),
      ?_, ?_⟩
    · simp only [hge, ↓reduceIte]
      have hsp_y : y.regs sp = k + 1 := by simp [y]
      rw [readStack, hsp_y, List.range_succ, List.map_append, List.map_singleton]
      congr 1
      · simp only [readStack, k]
        refine List.map_congr_left fun i hi => ?_
        rw [List.mem_range] at hi
        rw [hymem, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · rw [hymem, Function.update_self, Function.update_of_ne (by omega), Function.update_self]
    · intro addr haddr
      rw [Finset.mem_Ico] at haddr
      rw [hymem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

/-! ## Global outer-loop invariant and preservation across 3-way partition -/

/-- Full outer-loop machine invariant for in-place randomized quicksort. -/
structure OuterInv (w : ℕ) (input : List ℕ) (x : Data 16) : Prop where
  /-- Word size meets `logWidth 3 input.length ≤ w`. -/
  hw : logWidth 3 input.length ≤ w
  /-- Register `zero` holds `0`. -/
  zero_eq : x.regs zero = 0
  /-- Register `one` holds `1`. -/
  one_eq : x.regs one = 1
  /-- Register `two` holds `2`. -/
  two_eq : x.regs two = 2
  /-- Register `len` holds `input.length`. -/
  len_eq : x.regs len = input.length
  /-- Register `stackLo` holds `input.length + 1`. -/
  stackLo_eq : x.regs stackLo = input.length + 1
  /-- Register `stackHi` holds `2 * input.length + 1`. -/
  stackHi_eq : x.regs stackHi = 2 * input.length + 1
  /-- Active work-stack intervals are valid and pairwise disjoint. -/
  valid_stack : ValidStack input.length (readStack input.length x)
  /-- All inversions lie strictly inside active work-stack intervals. -/
  no_ext_inv : NoExternalInversions input.length x.mem (readStack input.length x)
  /-- `mem[1 .. n + 1)` is a permutation of `input`. -/
  perm : (memSlice 1 (input.length + 1) x.mem).Perm input
  /-- Only `Finset.Ico 1 (3 * n + 1)` has been modified since `Data.init input`. -/
  modifies : Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem x.mem

private theorem validStack_push_children {n vlo vlt vgt vhi : ℕ} {S₀ : List (ℕ × ℕ)}
    (hS : ValidStack n (S₀ ++ [(vlo, vhi)]))
    (hb : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi) :
    let S₁ := if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀
    ValidStack n S₁ ∧ ValidStack n (if vgt + 2 ≤ vhi then S₁ ++ [(vgt, vhi)] else S₁) := by
  intro S₁
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  have hS₀_bnd : ∀ p ∈ S₀, 1 ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 ≤ n + 1 :=
    fun p hp => hS.1 p (List.mem_append_left _ hp)
  obtain ⟨hS₀_pwd, -, hdisj_hi⟩ := List.pairwise_append.mp hS.2
  have hdisj_S₀ : ∀ p ∈ S₀, IntervalDisjoint p (vlo, vhi) :=
    fun p hp => hdisj_hi p hp (vlo, vhi) (List.mem_singleton_self _)
  have hS₁ : ValidStack n S₁ := by
    dsimp only [S₁]
    split_ifs with hlt2
    · refine ⟨fun p hp => ?_, List.pairwise_append.mpr ⟨hS₀_pwd, List.pairwise_singleton _ _, ?_⟩⟩
      · rcases List.mem_append.mp hp with hp₀ | hp₁
        · exact hS₀_bnd p hp₀
        · rw [List.mem_singleton] at hp₁; subst hp₁; exact ⟨hp_hi.1, hlt2, by omega⟩
      · intro p hp q hq
        rw [List.mem_singleton] at hq; subst hq
        rcases hdisj_S₀ p hp with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (by omega)
    · exact ⟨hS₀_bnd, hS₀_pwd⟩
  refine ⟨hS₁, ?_⟩
  split_ifs with hgt2
  · refine ⟨fun p hp => ?_, List.pairwise_append.mpr ⟨hS₁.2, List.pairwise_singleton _ _, ?_⟩⟩
    · rcases List.mem_append.mp hp with hp₁ | hp₂
      · exact hS₁.1 p hp₁
      · rw [List.mem_singleton] at hp₂; subst hp₂; exact ⟨by omega, hgt2, hp_hi.2.2⟩
    · intro p hp q hq
      rw [List.mem_singleton] at hq; subst hq
      dsimp only [S₁] at hp
      split_ifs at hp with hlt2
      · rcases List.mem_append.mp hp with hp₀ | hp_lt
        · rcases hdisj_S₀ p hp₀ with h1 | h2
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        · rw [List.mem_singleton] at hp_lt; subst hp_lt
          exact Or.inl (by omega)
      · rcases hdisj_S₀ p hp with h1 | h2
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
  · exact hS₁

private theorem noExternalInversions_after_partition {n vlo vlt vgt vhi vpiv : ℕ}
    {S₀ : List (ℕ × ℕ)} {mem₀ mem₁ : ℕ → ℕ}
    (hS : ValidStack n (S₀ ++ [(vlo, vhi)]))
    (hinv₀ : NoExternalInversions n mem₀ (S₀ ++ [(vlo, vhi)]))
    (hb : vlo ≤ vlt ∧ vlt < vgt ∧ vgt ≤ vhi)
    (hperm : (memSlice vlo vhi mem₁).Perm (memSlice vlo vhi mem₀))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₀ mem₁)
    (hlt_z : ∀ a, vlo ≤ a → a < vlt → mem₁ a < vpiv)
    (heq_z : ∀ a, vlt ≤ a → a < vgt → mem₁ a = vpiv)
    (hgt_z : ∀ a, vgt ≤ a → a < vhi → vpiv < mem₁ a) :
    let S₁ := if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀
    let S₂ := if vgt + 2 ≤ vhi then S₁ ++ [(vgt, vhi)] else S₁
    NoExternalInversions n mem₁ S₂ := by
  intro S₁ S₂ i j hi1 hij hjn hno
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  obtain ⟨-, -, hdisj_hi⟩ := List.pairwise_append.mp hS.2
  have hS₀_sub : ∀ p ∈ S₀, p ∈ S₂ := by
    intro p hp
    dsimp only [S₂, S₁]
    split_ifs <;> simp [hp]
  have hex_orig : ∀ a, vlo ≤ a → a < vhi → ∃ a', vlo ≤ a' ∧ a' < vhi ∧ mem₁ a = mem₀ a' := by
    intro a ha1 ha2
    have hmem : mem₁ a ∈ memSlice vlo vhi mem₀ :=
      hperm.subset (mem_memSlice_iff.mpr ⟨a, ha1, ha2, rfl⟩)
    obtain ⟨a', ha'1, ha'2, heq⟩ := mem_memSlice_iff.mp hmem
    exact ⟨a', ha'1, ha'2, heq.symm⟩
  by_cases hij_in : vlo ≤ i ∧ j < vhi
  · rcases lt_or_ge i vlt with hi_lt | hi_ge_lt
    · rcases lt_or_ge j vlt with hj_lt | hj_ge_lt
      · have hlt2 : vlo + 2 ≤ vlt := by omega
        have hmem_lt : (vlo, vlt) ∈ S₂ := by
          dsimp only [S₂, S₁]; split_ifs <;> simp
        exact absurd ⟨hij_in.1, hj_lt⟩ (hno (vlo, vlt) hmem_lt)
      · rcases lt_or_ge j vgt with hj_eq | hj_gt
        · have := hlt_z i hij_in.1 hi_lt; have := heq_z j hj_ge_lt hj_eq; omega
        · have := hlt_z i hij_in.1 hi_lt; have := hgt_z j hj_gt hij_in.2; omega
    · rcases lt_or_ge i vgt with hi_eq | hi_gt
      · rcases lt_or_ge j vgt with hj_eq | hj_gt
        · have := heq_z i hi_ge_lt hi_eq; have := heq_z j (by omega) hj_eq; omega
        · have := heq_z i hi_ge_lt hi_eq; have := hgt_z j hj_gt hij_in.2; omega
      · have hgt2 : vgt + 2 ≤ vhi := by omega
        have hmem_gt : (vgt, vhi) ∈ S₂ := by dsimp only [S₂]; simp [hgt2]
        exact absurd ⟨hi_gt, hij_in.2⟩ (hno (vgt, vhi) hmem_gt)
  · by_cases hi_in : vlo ≤ i ∧ i < vhi
    · have hj_out : vhi ≤ j := by omega
      obtain ⟨i', hi'1, hi'2, hi_eq⟩ := hex_orig i hi_in.1 hi_in.2
      have hj_eq : mem₁ j = mem₀ j := hmod j (by simp [Finset.mem_Ico]; omega)
      rw [hi_eq, hj_eq]
      refine hinv₀ i' j (by omega) (by omega) hjn fun p hp => ?_
      rcases List.mem_append.mp hp with hp₀ | hp_last
      · rcases hdisj_hi p hp₀ (vlo, vhi) (List.mem_singleton_self _) with h1 | h2 <;> omega
      · rw [List.mem_singleton] at hp_last; subst hp_last; omega
    · by_cases hj_in : vlo ≤ j ∧ j < vhi
      · have hi_out : i < vlo := by omega
        obtain ⟨j', hj'1, hj'2, hj_eq⟩ := hex_orig j hj_in.1 hj_in.2
        have hi_eq : mem₁ i = mem₀ i := hmod i (by simp [Finset.mem_Ico]; omega)
        rw [hi_eq, hj_eq]
        refine hinv₀ i j' hi1 (by omega) (by omega) fun p hp => ?_
        rcases List.mem_append.mp hp with hp₀ | hp_last
        · rcases hdisj_hi p hp₀ (vlo, vhi) (List.mem_singleton_self _) with h1 | h2 <;> omega
        · rw [List.mem_singleton] at hp_last; subst hp_last; omega
      · have hi_eq : mem₁ i = mem₀ i := hmod i (by simp [Finset.mem_Ico]; omega)
        have hj_eq : mem₁ j = mem₀ j := hmod j (by simp [Finset.mem_Ico]; omega)
        rw [hi_eq, hj_eq]
        refine hinv₀ i j hi1 hij hjn fun p hp => ?_
        rcases List.mem_append.mp hp with hp₀ | hp_last
        · exact hno p (hS₀_sub p hp₀)
        · rw [List.mem_singleton] at hp_last; subst hp_last; omega

private theorem perm_full_of_subslice {n vlo vhi : ℕ} {mem₀ mem₁ : ℕ → ℕ}
    (hb : 1 ≤ vlo ∧ vlo ≤ vhi ∧ vhi ≤ n + 1)
    (hsub : (memSlice vlo vhi mem₁).Perm (memSlice vlo vhi mem₀))
    (hmod : Modifies (Finset.Ico vlo vhi) mem₀ mem₁) :
    (memSlice 1 (n + 1) mem₁).Perm (memSlice 1 (n + 1) mem₀) := by
  rw [memSlice_append hb.1 (by omega) mem₁, memSlice_append hb.2.1 hb.2.2 mem₁,
    memSlice_append hb.1 (by omega) mem₀, memSlice_append hb.2.1 hb.2.2 mem₀]
  have hleft : memSlice 1 vlo mem₁ = memSlice 1 vlo mem₀ :=
    memSlice_congr fun a ha1 ha2 => hmod a (by simp [Finset.mem_Ico]; omega)
  have hright : memSlice vhi (n + 1) mem₁ = memSlice vhi (n + 1) mem₀ :=
    memSlice_congr fun a ha1 ha2 => hmod a (by simp [Finset.mem_Ico]; omega)
  rw [hleft, hright]
  exact List.Perm.append_left _ (hsub.append_right _)

/-- Deterministic execution of `partitionAndPush` after `popAndSample` has popped `(vlo, vhi)`
leaving stack `S₀` and sampled offset `k < vhi - vlo` into `tmp`. -/
theorem partitionAndPush_spec {w : ℕ} {input : List ℕ} {vlo vhi : ℕ} {S₀ : List (ℕ × ℕ)}
    {x : Data 16} (k : Fin (vhi - vlo))
    (hktmp : x.regs tmp = k.val)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1) (htwo : x.regs two = 2)
    (hlen : x.regs len = input.length)
    (hsLo : x.regs stackLo = input.length + 1) (hsHi : x.regs stackHi = 2 * input.length + 1)
    (hlo : x.regs lo = vlo) (hhi : x.regs hi = vhi)
    (hw : logWidth 3 input.length ≤ w)
    (hread : readStack input.length x = S₀)
    (hS : ValidStack input.length (S₀ ++ [(vlo, vhi)]))
    (hinv₀ : NoExternalInversions input.length x.mem (S₀ ++ [(vlo, vhi)]))
    (hperm₀ : (memSlice 1 (input.length + 1) x.mem).Perm input)
    (hmod₀ : Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem x.mem) :
    let u := memSlice vlo vhi x.mem
    let m₁ := u.countP (· < u[k.val]'(by simp [u]))
    let m₂ := u.countP (u[k.val]'(by simp [u]) < ·)
    let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
    let S₂ := if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁
    ∃ y t, Exec w partitionAndPush x y t ∧ t ≤ 11 * (vhi - vlo) + 23 ∧
      OuterInv w input y ∧ readStack input.length y = S₂ := by
  intro u m₁ m₂ S₁ S₂
  set n := input.length
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hw
  have hp_hi := hS.1 (vlo, vhi) (by simp)
  set vpiv := x.mem (vlo + k.val)
  -- 1. `partInit` (`5` steps)
  set x₁ := x.set tmp (vlo + k.val)
  set x₂ := x₁.set piv vpiv
  set x₃ := x₂.set lt vlo
  set x₄ := x₃.set cur vlo
  set x₅ := x₄.set gt vhi
  have ei₁ : Exec w (.op (.bin .add tmp lo tmp)) x x₁ 1 := by
    have := k.isLt
    simpa [x₁, hlo, hktmp, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := tmp)
      (i := lo) (j := tmp) (x := x)
      (hfit_all.of_le (by simp [hlo, hktmp, BinOp.eval]; omega))
  have ei₂ : Exec (B := .standard) w (.op (.load piv tmp)) x₁ x₂ 1 := by
    simpa [x₂, x₁, vpiv] using Exec.load (w := w) (d := piv) (a := tmp) (x := x₁)
  have ei₃ : Exec (B := .standard) w (.op (.copy lt lo)) x₂ x₃ 1 := by
    have : x₂.regs lo = vlo := by simp [x₂, x₁, hlo]
    simpa [x₃, this] using Exec.copy (w := w) (d := lt) (s := lo) (x := x₂)
  have ei₄ : Exec (B := .standard) w (.op (.copy cur lo)) x₃ x₄ 1 := by
    have : x₃.regs lo = vlo := by simp [x₃, x₂, x₁, hlo]
    simpa [x₄, this] using Exec.copy (w := w) (d := cur) (s := lo) (x := x₃)
  have ei₅ : Exec (B := .standard) w (.op (.copy gt hi)) x₄ x₅ 1 := by
    have : x₄.regs hi = vhi := by simp [x₄, x₃, x₂, x₁, hhi]
    simpa [x₅, this] using Exec.copy (w := w) (d := gt) (s := hi) (x := x₄)
  have e_init : ExecWithin w partInit x x₅ 5 :=
    (ei₁.seq (ei₂.seq (ei₃.seq (ei₄.seq ei₅)))).within
  -- 2. `partLoop` (`≤ 11 * (vhi - vlo) + 2` steps)
  have hPart₀ : PartInv w vlo vhi vpiv x₅.mem x₅ :=
    ⟨by simp [x₅, x₄, x₃, x₂, x₁, hone], by simp [x₅, x₄, x₃, x₂, x₁, hlo],
     by simp [x₅, x₄, x₃, x₂, x₁, hhi], by simp [x₅, x₄, x₃, x₂],
     hfit_all.of_le (by omega), by simp [x₅, x₄, x₃], by simp [x₅, x₄, x₃],
     by simp [x₅, x₄]; omega, by simp [x₅], List.Perm.refl _, Modifies.refl _ _,
     fun a h1 h2 => by simp [x₅, x₄, x₃] at h2; omega,
     fun a h1 h2 => by simp [x₅, x₄, x₃] at h1 h2; omega,
     fun a h1 h2 => by simp [x₅] at h1; omega⟩
  obtain ⟨x₆, e_loop, hPart₆, hcg₆⟩ := partLoop_spec hPart₀
    (by simp [x₅, x₄, x₃]) (by simp [x₅, x₄]) (by simp [x₅])
  have hx₅_mem : x₅.mem = x.mem := rfl
  rw [hx₅_mem] at hPart₆
  set vlt := x₆.regs lt
  set vgt := x₆.regs gt
  have hpiv_u : vpiv = u[k.val]'(by simp [u]) := by
    rw [getElem_memSlice k.isLt]
  have hpiv_mem : vpiv ∈ u := mem_memSlice_iff.mpr ⟨vlo + k.val, by omega, by omega, rfl⟩
  have heq_gt : ∀ a, vlt ≤ a → a < vgt → x₆.mem a = vpiv := by
    intro a ha1 ha2; exact hPart₆.eq_zone a ha1 (hcg₆ ▸ ha2)
  obtain ⟨hlt_gt, hm₁_eq, hm₂_eq⟩ := partition_counts_and_lt
    ⟨(hPart₆.lo_le_lt : vlo ≤ vlt),
      by have : vlt ≤ x₆.regs cur := hPart₆.lt_le_cur; omega,
      (hPart₆.gt_le_hi : vgt ≤ vhi)⟩
    hPart₆.perm hPart₆.lt_zone heq_gt hPart₆.gt_zone hpiv_mem
  have hvlt_eq : vlt = vlo + m₁ := by
    have : m₁ = vlt - vlo := by dsimp only [m₁, u]; rw [← hpiv_u]; exact hm₁_eq.symm
    have := hPart₆.lo_le_lt; omega
  have hvgt_eq : vgt = vhi - m₂ := by
    have : m₂ = vhi - vgt := by dsimp only [m₂, u]; rw [← hpiv_u]; exact hm₂_eq.symm
    have := hPart₆.gt_le_hi; omega
  obtain ⟨hVS₁, hVS₂⟩ := validStack_push_children (vlt := vlt) (vgt := vgt) hS
    ⟨hPart₆.lo_le_lt, hlt_gt, hPart₆.gt_le_hi⟩
  have hread₆ : readStack n x₆ = S₀ := by
    rw [← hread]
    refine readStack_congr ?_ fun a ha => hPart₆.modifies a (by simp [Finset.mem_Ico]; omega)
    exact (e_loop.regs_eq (by decide)).trans (by simp [x₅, x₄, x₃, x₂, x₁])
  -- 3. `pushIfNonTrivial lo lt` (`≤ 8` steps)
  have hpres₆_one : x₆.regs one = 1 := hPart₆.one_eq
  have hpres₆_two : x₆.regs two = 2 :=
    (e_loop.regs_eq (by decide)).trans (by simp [x₅, x₄, x₃, x₂, x₁, htwo])
  have hpres₆_sLo : x₆.regs stackLo = n + 1 :=
    (e_loop.regs_eq (by decide)).trans (by simp [x₅, x₄, x₃, x₂, x₁, hsLo])
  have hpres₆_sHi : x₆.regs stackHi = 2 * n + 1 :=
    (e_loop.regs_eq (by decide)).trans (by simp [x₅, x₄, x₃, x₂, x₁, hsHi])
  obtain ⟨x₇, e_push₁, hread₇, hmod₇⟩ := pushIfNonTrivial_spec (w := w) (n := n)
    (a := lo) (b := lt) (x := x₆) (by decide) (by decide)
    hpres₆_one hpres₆_two hpres₆_sLo hpres₆_sHi hfit_all
    ⟨by rw [hPart₆.lo_eq]; omega, by change vlt ≤ n + 1; have := hPart₆.gt_le_hi; omega⟩
    (fun hge => by
      rw [hPart₆.lo_eq] at hge
      change vlo + 2 ≤ vlt at hge
      have hlen_S : 2 * (S₀ ++ [(vlo, vlt)]).length ≤ n := by
        have hVS₁' : ValidStack n (S₀ ++ [(vlo, vlt)]) := by simpa only [hge, ↓reduceIte] using hVS₁
        exact hVS₁'.two_mul_length_le
      have hsp₆ : x₆.regs sp = S₀.length := by rw [← length_readStack n x₆, hread₆]
      rw [List.length_append, List.length_singleton] at hlen_S
      omega)
  -- 4. `pushIfNonTrivial gt hi` (`≤ 8` steps)
  have hgt₇ : x₇.regs gt = vgt := e_push₁.regs_eq (by decide)
  have hhi₇ : x₇.regs hi = vhi := (e_push₁.regs_eq (by decide)).trans hPart₆.hi_eq
  obtain ⟨y, e_push₂, hread_y, hmod_y⟩ := pushIfNonTrivial_spec (w := w) (n := n)
    (a := gt) (b := hi) (x := x₇) (by decide) (by decide)
    ((e_push₁.regs_eq (by decide)).trans hpres₆_one)
    ((e_push₁.regs_eq (by decide)).trans hpres₆_two)
    ((e_push₁.regs_eq (by decide)).trans hpres₆_sLo)
    ((e_push₁.regs_eq (by decide)).trans hpres₆_sHi) hfit_all
    ⟨by rw [hgt₇]; have := hPart₆.gt_le_hi; omega, by rw [hhi₇]; omega⟩
    (fun hge => by
      rw [hgt₇, hhi₇] at hge
      have hVS₂' : ValidStack n ((if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) ++
          [(vgt, vhi)]) := by simpa only [hge, ↓reduceIte] using hVS₂
      have hlen_S := hVS₂'.two_mul_length_le
      have hsp₇ : x₇.regs sp = (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀).length := by
        rw [← length_readStack n x₇, hread₇, hread₆, hPart₆.lo_eq]
      rw [List.length_append, List.length_singleton] at hlen_S
      omega)
  have e_all : ExecWithin w partitionAndPush x y (11 * (vhi - vlo) + 23) :=
    (e_init.seq (e_loop.seq (e_push₁.seq e_push₂))).mono (by omega)
  obtain ⟨t, ht_le, he_all⟩ := e_all
  have hS₁_eq : (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) = S₁ := by
    dsimp only [S₁]
    simp only [hvlt_eq, show (vlo + 2 ≤ vlo + m₁) ↔ (2 ≤ m₁) by omega]
  have hS₂_eq : (if vgt + 2 ≤ vhi then
      (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀) ++ [(vgt, vhi)] else
      (if vlo + 2 ≤ vlt then S₀ ++ [(vlo, vlt)] else S₀)) = S₂ := by
    rw [hS₁_eq]
    dsimp only [S₂]
    have hgt_iff : (vgt + 2 ≤ vhi) ↔ (2 ≤ m₂) := by
      have : m₂ ≤ vhi - vlo := by rw [← length_memSlice vlo vhi x.mem]; exact List.countP_le_length
      omega
    simp only [hgt_iff]
    rw [hvgt_eq]
  have hread_final : readStack n y = S₂ := by
    rw [hread_y, hread₇, hread₆, hPart₆.lo_eq, hgt₇, hhi₇]
    exact hS₂_eq
  have hslice_unchanged : ∀ a, 1 ≤ a → a < n + 1 → y.mem a = x₆.mem a := fun a ha1 ha2 =>
    (hmod_y a (by simp [Finset.mem_Ico]; omega)).trans (hmod₇ a (by simp [Finset.mem_Ico]; omega))
  have hno_inv_x₆ := noExternalInversions_after_partition hS hinv₀
    ⟨hPart₆.lo_le_lt, hlt_gt, hPart₆.gt_le_hi⟩ hPart₆.perm hPart₆.modifies
    hPart₆.lt_zone heq_gt hPart₆.gt_zone
  have hno_inv_y : NoExternalInversions n y.mem S₂ := by
    rw [← hS₂_eq]
    intro i j hi1 hij hjn hno
    rw [hslice_unchanged i hi1 (by omega), hslice_unchanged j (by omega) hjn]
    exact hno_inv_x₆ i j hi1 hij hjn hno
  have hperm_y : (memSlice 1 (n + 1) y.mem).Perm input := by
    rw [memSlice_congr hslice_unchanged]
    exact (perm_full_of_subslice ⟨hp_hi.1, by omega, hp_hi.2.2⟩ hPart₆.perm hPart₆.modifies).trans
      hperm₀
  have hmod_final : Modifies (Finset.Ico 1 (3 * n + 1)) (Data.init (r := 16) input).mem y.mem := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    rw [hmod_y a (by simp [Finset.mem_Ico]; omega), hmod₇ a (by simp [Finset.mem_Ico]; omega),
      hPart₆.modifies a (by simp [Finset.mem_Ico]; omega),
      hmod₀ a (by simp [Finset.mem_Ico]; omega)]
  refine ⟨y, t, he_all, ht_le, ?_, hread_final⟩
  refine ⟨hw,
    (he_all.regs_eq (by decide)).trans hzero,
    (he_all.regs_eq (by decide)).trans hone,
    (he_all.regs_eq (by decide)).trans htwo,
    (he_all.regs_eq (by decide)).trans hlen,
    (he_all.regs_eq (by decide)).trans hsLo,
    (he_all.regs_eq (by decide)).trans hsHi,
    hread_final ▸ (hS₂_eq ▸ hVS₂),
    hread_final ▸ hno_inv_y,
    hperm_y,
    hmod_final⟩

/-! ## Randomized `popAndSample`, `outerBody`, `setup`, and headline bounds -/

private theorem readStack_eq_snoc {n k : ℕ} {x : Data 16} (hsp : x.regs sp = k + 1) :
    readStack n x =
      ((List.range k).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))) ++
        [(x.mem (n + 1 + k), x.mem (2 * n + 1 + k))] := by
  simp [readStack, hsp, List.range_succ]

/-- One iteration `outerBody` from an active state (`0 < sp`) pops `(vlo, vhi)`, samples a uniform
pivot `k ← unifFin (vhi - vlo - 1)` (`1` `rand` call), and runs `partitionAndPush` in at most
`11 * (vhi - vlo) + 31` total instructions. -/
theorem outerBody_spec {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ S₀ vlo vhi,
      readStack input.length x = S₀ ++ [(vlo, vhi)] ∧
      ∃ (_ : vlo + 2 ≤ vhi),
      ∃ y : Fin (vhi - vlo - 1 + 1) → Data 16,
      ∃ t : Fin (vhi - vlo - 1 + 1) → ℕ,
        ExecRand w outerBody x
          ((fun k => (y k, 8 + t k)) <$> ProbComp.unifFin (vhi - vlo - 1)) ∧
        ∀ k : Fin (vhi - vlo - 1 + 1),
          t k ≤ 11 * (vhi - vlo) + 23 ∧
          OuterInv w input (y k) ∧
          let u := memSlice vlo vhi x.mem
          let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
          let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
          let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
          readStack input.length (y k) =
            (if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁) := by
  set n := input.length
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hI.hw
  have hsp_pos : 0 < x.regs sp := by simpa [Cond.holds_lt, hI.zero_eq] using hc
  set k_sp := x.regs sp - 1
  have hsp_succ : x.regs sp = k_sp + 1 := by omega
  set S₀ := (List.range k_sp).map fun i => (x.mem (n + 1 + i), x.mem (2 * n + 1 + i))
  set vlo := x.mem (n + 1 + k_sp)
  set vhi := x.mem (2 * n + 1 + k_sp)
  have hstack_eq : readStack n x = S₀ ++ [(vlo, vhi)] := readStack_eq_snoc hsp_succ
  have hVS : ValidStack n (S₀ ++ [(vlo, vhi)]) := hstack_eq ▸ hI.valid_stack
  have hp_hi := hVS.1 (vlo, vhi) (by simp)
  have hk_lt_n : k_sp < n := by
    have h2 := hVS.two_mul_length_le
    have hS₀_len : S₀.length = k_sp := by simp [S₀]
    rw [List.length_append, List.length_singleton, hS₀_len] at h2
    omega
  -- Execute deterministic prefix `popPrefix` (`7` steps)
  have hsp6 : x.regs 6 = k_sp + 1 := hsp_succ
  set p₁ := x.set sp k_sp
  have ep₁ : Exec w (.op (.bin .sub sp sp one)) x p₁ 1 := by
    simpa [p₁, k_sp, hI.one_eq, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := sp)
      (i := sp) (j := one) (x := x)
      (hfit_all.of_le (by simp [hI.one_eq, hsp6, BinOp.eval]; omega))
  have er₁ := readAt_exec (w := w) (tmp := tmp) (dst := lo) (ptr := stackLo) (idx := sp)
    (x := p₁) (hfit_all.of_le (by simp [p₁, hI.stackLo_eq]; omega))
  set p₂ := (p₁.set tmp (p₁.regs stackLo + p₁.regs sp)).set lo
    (p₁.mem (p₁.regs stackLo + p₁.regs sp))
  have er₂ := readAt_exec (w := w) (tmp := tmp) (dst := hi) (ptr := stackHi) (idx := sp)
    (x := p₂) (hfit_all.of_le (by simp [p₂, p₁, hI.stackHi_eq]; omega))
  set p₃ := (p₂.set tmp (p₂.regs stackHi + p₂.regs sp)).set hi
    (p₂.mem (p₂.regs stackHi + p₂.regs sp))
  have hlo₃ : p₃.regs lo = vlo := by simp [p₃, p₂, p₁, hI.stackLo_eq, vlo, n]
  have hhi₃ : p₃.regs hi = vhi := by simp [p₃, p₂, p₁, hI.stackHi_eq, vhi, n]
  have ep₄ : Exec w (.op (.bin .sub tmp hi lo)) p₃ (p₃.set tmp (vhi - vlo)) 1 := by
    simpa [hhi₃, hlo₃, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := tmp) (i := hi)
      (j := lo) (x := p₃) (hfit_all.of_le (by simp [hhi₃, hlo₃, BinOp.eval]; omega))
  set p₄ := p₃.set tmp (vhi - vlo)
  have htmp₄ : p₄.regs tmp = vhi - vlo := by simp [p₄]
  have hone₄ : p₄.regs one = 1 := by simp [p₄, p₃, p₂, p₁, hI.one_eq]
  have ep₅ : Exec w (.op (.bin .sub tmp tmp one)) p₄ (p₄.set tmp (vhi - vlo - 1)) 1 := by
    simpa [htmp₄, hone₄, BinOp.eval] using Exec.bin (w := w) (f := .sub) (d := tmp) (i := tmp)
      (j := one) (x := p₄) (hfit_all.of_le (by simp [htmp₄, hone₄, BinOp.eval]; omega))
  set p₅ := p₄.set tmp (vhi - vlo - 1)
  have e_pre : Exec w popPrefix x p₅ 7 :=
    ep₁.seq (er₁.seq (er₂.seq (ep₄.seq ep₅)))
  have htmp₅ : p₅.regs tmp = vhi - vlo - 1 := by simp [p₅]
  have e_rand : ExecRand (B := .standard) w (.rand tmp tmp) p₅ (do
      let k ← ProbComp.unifFin (vhi - vlo - 1)
      pure (p₅.set tmp k.val, 1)) := by
    have hr := ExecRand.rand (B := .standard) (w := w) (dst := tmp) (src := tmp)
      (x := p₅) (by rw [htmp₅]; exact hfit_all.of_le (by omega))
    rwa [htmp₅] at hr
  have e_pop : ExecRand w popAndSample x
      ((fun k : Fin (vhi - vlo - 1 + 1) => (p₅.set tmp k.val, 8)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) := by
    have hs := e_pre.seqRand e_rand
    have heq : ((fun z : Data 16 × ℕ => (z.1, 7 + z.2)) <$> (do
        let k ← ProbComp.unifFin (vhi - vlo - 1)
        pure (p₅.set tmp k.val, 1))) =
      ((fun k : Fin (vhi - vlo - 1 + 1) => (p₅.set tmp k.val, 8)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) := by
      simp only [← bind_pure_comp, bind_assoc, pure_bind]
    simpa only [popAndSample, heq] using hs
  -- Apply `partitionAndPush_spec` for every sample `k`
  have hm_eq : vhi - vlo - 1 + 1 = vhi - vlo := by omega
  have hpart_all : ∀ k : Fin (vhi - vlo - 1 + 1),
      ∃ y t, Exec w partitionAndPush (p₅.set tmp k.val) y t ∧
        t ≤ 11 * (vhi - vlo) + 23 ∧
        OuterInv w input y ∧
        let u := memSlice vlo vhi x.mem
        let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
        let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
        let S₁ := if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀
        readStack n y = (if 2 ≤ m₂ then S₁ ++ [(vhi - m₂, vhi)] else S₁) := by
    intro k
    have hk_lt := k.isLt
    have hp₅_mem : (p₅.set tmp k.val).mem = x.mem := rfl
    have hp₅_stack : readStack n (p₅.set tmp k.val) = S₀ := by
      simp [readStack, p₅, p₄, p₃, p₂, p₁, S₀]
    exact partitionAndPush_spec ⟨k.val, by omega⟩
      (by simp)
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.zero_eq])
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.one_eq])
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.two_eq])
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.len_eq])
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.stackLo_eq])
      (by simp [p₅, p₄, p₃, p₂, p₁, hI.stackHi_eq])
      (by simp [p₅, p₄, hlo₃])
      (by simp [p₅, p₄, hhi₃])
      hI.hw hp₅_stack hVS (hstack_eq ▸ hI.no_ext_inv) hI.perm hI.modifies
  choose y t hspec using hpart_all
  refine ⟨S₀, vlo, vhi, hstack_eq, hp_hi.2.1, y, t, ?_, fun k => (hspec k).2⟩
  -- Note `p₅.set tmp k.val` determines `k.val` uniquely via `.regs tmp`!
  let m₂_fn : Data 16 → ProbComp (Data 16 × ℕ) := fun d =>
    if h : d.regs tmp < vhi - vlo - 1 + 1 then
      pure (y ⟨d.regs tmp, h⟩, t ⟨d.regs tmp, h⟩)
    else pure (d, 0)
  have hseq := ExecRand.seq e_pop (m₂ := m₂_fn)
    fun z hz => by
      obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
      have hreg : (p₅.set tmp k.val).regs tmp = k.val := by simp
      dsimp only [m₂_fn]
      simp only [hreg, k.isLt, ↓reduceDIte]
      exact (hspec k).1.execRand
  have hm_simpl : (do
      let z₁ ← (fun k : Fin (vhi - vlo - 1 + 1) => (p₅.set tmp k.val, 8)) <$>
        ProbComp.unifFin (vhi - vlo - 1)
      let z₂ ← m₂_fn z₁.1
      pure (z₂.1, z₁.2 + z₂.2)) =
      ((fun k : Fin (vhi - vlo - 1 + 1) => (y k, 8 + t k)) <$>
        ProbComp.unifFin (vhi - vlo - 1)) := by
    simp only [← bind_pure_comp, bind_assoc, pure_bind]
    refine congrArg (ProbComp.unifFin (vhi - vlo - 1) >>= ·) (funext fun k => ?_)
    have hreg : (p₅.set tmp k.val).regs tmp = k.val := by simp
    dsimp only [m₂_fn]
    simp only [hreg, k.isLt, ↓reduceDIte, pure_bind]
  rw [outerBody, ← hm_simpl]
  exact hseq

/-- Quadratic worst-case step potential `∑_{(a,b) ∈ S} 20 * (b - a) ^ 2`. -/
def stepPotential (n : ℕ) (x : Data 16) : ℕ :=
  ((readStack n x).map fun p => 20 * (p.2 - p.1) ^ 2).sum

/-- `rand`-call potential `∑_{(a,b) ∈ S} (b - a - 1)`. -/
def callPotential (n : ℕ) (x : Data 16) : ℕ :=
  ((readStack n x).map fun p => p.2 - p.1 - 1).sum

/-- Expected-time potential `ENNReal.ofReal (∑_{(a,b) ∈ S} subCost (b - a))`. -/
noncomputable def expPotential (n : ℕ) (x : Data 16) : ℝ≥0∞ :=
  ENNReal.ofReal (((readStack n x).map fun p => subCost (p.2 - p.1)).sum)

private theorem countP_lt_add_gt_le {u : List ℕ} {piv : ℕ} (hpiv : piv ∈ u) :
    u.countP (· < piv) + u.countP (piv < ·) + 1 ≤ u.length := by
  induction u with
  | nil => simp at hpiv
  | cons a tl ih =>
    simp only [List.length_cons, List.countP_cons]
    rcases List.mem_cons.mp hpiv with rfl | htl
    · simp only [Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hdisj : tl.countP (· < piv) + tl.countP (piv < ·) ≤ tl.length := by
        clear hpiv ih
        induction tl with
        | nil => simp
        | cons b rest ihr =>
          simp only [List.length_cons, List.countP_cons]
          by_cases h1 : b < piv
          · have h2 : ¬piv < b := by omega
            simp [h1, h2]; omega
          · by_cases h2 : piv < b
            · simp [h1, h2]; omega
            · simp [h1, h2]; omega
      omega
    · have hih := ih htl
      by_cases h1 : a < piv
      · have h2 : ¬piv < a := by omega
        simp [h1, h2]; omega
      · by_cases h2 : piv < a
        · simp [h1, h2]; omega
        · simp [h1, h2]; omega

private theorem outerBody_worstCase_step {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ T_b R_b, ExecRandWithin w outerBody x
      (fun y => OuterInv w input y ∧
        T_b + 2 + stepPotential input.length y ≤ stepPotential input.length x ∧
        R_b + callPotential input.length y ≤ callPotential input.length x) T_b R_b := by
  obtain ⟨S₀, vlo, vhi, hstack, hge2, y, t, hexec, hspec⟩ := outerBody_spec hI hc
  let m := vhi - vlo
  have hm_def : m = vhi - vlo := rfl
  have hm2 : 2 ≤ m := by omega
  refine ⟨11 * m + 31, 1, ⟨_, hexec, ?_, ?_⟩⟩
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbComp.isQueryBounded_unifFin (m - 1))
  · intro z hz
    obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨ht_le, hIy, hread_yk⟩ := hspec k
    let u := memSlice vlo vhi x.mem
    let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
    let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
    change readStack input.length (y k) =
      (if 2 ≤ m₂ then (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀) ++ [(vhi - m₂, vhi)]
       else (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀)) at hread_yk
    have hm12_le : m₁ + m₂ ≤ m - 1 := by
      have hpiv_in : u[k.val]'(by have := k.isLt; simp [u]; omega) ∈ u := List.getElem_mem _
      have hc_le := countP_lt_add_gt_le hpiv_in
      have hlen_u : u.length = m := length_memSlice vlo vhi x.mem
      omega
    have hstep_pot : (11 * m + 31) + 2 + stepPotential input.length (y k) ≤
        stepPotential input.length x := by
      have hquad : 11 * m + 33 + (20 * m₁ ^ 2 + 20 * m₂ ^ 2) ≤ 20 * m ^ 2 := by
        have hsum_sq : m₁ ^ 2 + m₂ ^ 2 ≤ (m - 1) ^ 2 := by
          have : (m₁ + m₂) ^ 2 ≤ (m - 1) ^ 2 := Nat.pow_le_pow_left hm12_le 2
          nlinarith
        have hbase : 11 * m + 33 + 20 * (m - 1) ^ 2 ≤ 20 * m ^ 2 := by
          obtain ⟨d, hd⟩ : ∃ d, m = d + 2 := ⟨m - 2, by omega⟩
          have hd1 : m - 1 = d + 1 := by omega
          rw [hd1, hd]
          nlinarith
        omega
      rw [stepPotential, hread_yk, stepPotential, hstack, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ← hm_def]
      split_ifs
      · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          Nat.add_sub_cancel_left, hsub2]; omega
      · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          hsub2]; omega
      · simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          Nat.add_sub_cancel_left]; omega
      · omega
    have hcall_pot : 1 + callPotential input.length (y k) ≤ callPotential input.length x := by
      rw [callPotential, hread_yk, callPotential, hstack]
      split_ifs <;> simp only [List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton] <;> omega
    exact ⟨⟨hIy, hstep_pot, hcall_pot⟩, by omega⟩

private theorem list_sum_subCost_nonneg (S : List (ℕ × ℕ)) :
    0 ≤ (S.map fun p => subCost (p.2 - p.1)).sum := by
  induction S with
  | nil => simp
  | cons p tl ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_nonneg (subCost_nonneg _) ih

private theorem outerBody_drift_step {w : ℕ} {input : List ℕ} {x : Data 16}
    (hI : OuterInv w input x) (hc : (Cond.lt zero sp).Holds x) :
    ∃ mb, ExecRand w outerBody x mb ∧
      (∀ z ∈ mb.support,
        OuterInv w input z.1 ∧ callPotential input.length z.1 < callPotential input.length x) ∧
      ProbComp.expect mb (fun z => (z.2 : ℝ≥0∞) + 2 + expPotential input.length z.1) ≤
        expPotential input.length x := by
  obtain ⟨S₀, vlo, vhi, hstack, hge2, y, t, hexec, hspec⟩ := outerBody_spec hI hc
  let m := vhi - vlo
  have hm_def : m = vhi - vlo := rfl
  have hm2 : 2 ≤ m := by omega
  have hm_eq : vhi - vlo - 1 + 1 = m := by omega
  refine ⟨_, hexec, ?_, ?_⟩
  · intro z hz
    obtain ⟨k, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨_, hIy, hread_yk⟩ := hspec k
    let u := memSlice vlo vhi x.mem
    let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
    let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
    change readStack input.length (y k) =
      (if 2 ≤ m₂ then (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀) ++ [(vhi - m₂, vhi)]
       else (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀)) at hread_yk
    have hm12_le : m₁ + m₂ ≤ m - 1 := by
      have hpiv_in : u[k.val]'(by have := k.isLt; simp [u]; omega) ∈ u := List.getElem_mem _
      have hc_le := countP_lt_add_gt_le hpiv_in
      have hlen_u : u.length = m := length_memSlice vlo vhi x.mem
      omega
    refine ⟨hIy, ?_⟩
    rw [callPotential, hread_yk, callPotential, hstack]
    split_ifs <;> simp only [List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton] <;> omega
  · rw [ProbComp.expect_map, ProbComp.expect_unifFin]
    set baseCost : ℝ := (S₀.map fun p => subCost (p.2 - p.1)).sum
    have hbase_nn : 0 ≤ baseCost := list_sum_subCost_nonneg S₀
    let u := memSlice vlo vhi x.mem
    have hlen_u : u.length = m := length_memSlice vlo vhi x.mem
    have hterm_le : ∀ k : Fin (vhi - vlo - 1 + 1),
        ((8 + t k : ℕ) : ℝ≥0∞) + 2 + expPotential input.length (y k) ≤
          ENNReal.ofReal (28 * (m : ℝ) + baseCost +
            (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
             subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)))) := by
      intro k
      obtain ⟨ht_le, -, hread_yk⟩ := hspec k
      let m₁ := u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))
      let m₂ := u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)
      change readStack input.length (y k) =
        (if 2 ≤ m₂ then (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀) ++ [(vhi - m₂, vhi)]
         else (if 2 ≤ m₁ then S₀ ++ [(vlo, vlo + m₁)] else S₀)) at hread_yk
      have hm12_le : m₁ + m₂ ≤ m - 1 := by
        have hpiv_in : u[k.val]'(by have := k.isLt; simp [u]; omega) ∈ u := List.getElem_mem _
        have hc_le := countP_lt_add_gt_le hpiv_in
        omega
      have hstep_real : ((8 + t k + 2 : ℕ) : ℝ) ≤ 28 * (m : ℝ) := by
        have hnat : 8 + t k + 2 ≤ 28 * m := by omega
        exact_mod_cast hnat
      have hyk_cost : ((readStack input.length (y k)).map fun p => subCost (p.2 - p.1)).sum =
          baseCost + (subCost m₁ + subCost m₂) := by
        rw [hread_yk]
        split_ifs
        · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
          simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            Nat.add_sub_cancel_left, hsub2, baseCost]; ring
        · have hsub2 : vhi - (vhi - m₂) = m₂ := by omega
          have hz1 : subCost m₁ = 0 := subCost_of_lt_two (by omega)
          simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            hsub2, hz1, baseCost]; ring
        · have hz2 : subCost m₂ = 0 := subCost_of_lt_two (by omega)
          simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
            Nat.add_sub_cancel_left, hz2, baseCost]; ring
        · have hz1 : subCost m₁ = 0 := subCost_of_lt_two (by omega)
          have hz2 : subCost m₂ = 0 := subCost_of_lt_two (by omega)
          simp only [hz1, hz2, baseCost]; ring
      have hcast_steps : ((8 + t k : ℕ) : ℝ≥0∞) + 2 =
          ENNReal.ofReal ((8 + t k + 2 : ℕ) : ℝ) := by
        rw [ENNReal.ofReal_natCast]; push_cast; rfl
      rw [hcast_steps, expPotential, hyk_cost, ← ENNReal.ofReal_add (by positivity)
        (add_nonneg hbase_nn (add_nonneg (subCost_nonneg _) (subCost_nonneg _)))]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hden : ((vhi - vlo - 1 : ℕ) : ℝ≥0∞) + 1 = ENNReal.ofReal (m : ℝ) := by
      rw [ENNReal.ofReal_natCast]
      norm_cast
    calc
      (∑ k : Fin (vhi - vlo - 1 + 1),
          (((8 + t k : ℕ) : ℝ≥0∞) + 2 + expPotential input.length (y k))) /
          (((vhi - vlo - 1 : ℕ) : ℝ≥0∞) + 1)
        ≤ (∑ k : Fin (vhi - vlo - 1 + 1),
            ENNReal.ofReal (28 * (m : ℝ) + baseCost +
              (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
               subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·))))) /
            (((vhi - vlo - 1 : ℕ) : ℝ≥0∞) + 1) := by
          gcongr with k
          exact hterm_le k
      _ = ENNReal.ofReal
            ((∑ k : Fin (vhi - vlo - 1 + 1),
              (28 * (m : ℝ) + baseCost +
                (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                 subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·))))) /
              (m : ℝ)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg fun k _ =>
            add_nonneg (add_nonneg (by positivity) hbase_nn)
              (add_nonneg (subCost_nonneg _) (subCost_nonneg _)),
            hden,
            ENNReal.ofReal_div_of_pos (by exact_mod_cast (show 0 < m by omega))]
      _ ≤ expPotential input.length x := by
          rw [expPotential, hstack, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton]
          refine ENNReal.ofReal_le_ofReal ?_
          have hfin_eq :
              ∑ k : Fin (vhi - vlo - 1 + 1),
                (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                 subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·))) =
              ∑ k : Fin u.length,
                (subCost (u.countP (· < u[k.val])) + subCost (u.countP (u[k.val] < ·))) :=
            Fintype.sum_equiv (finCongr (hm_eq.trans hlen_u.symm)) _ _ fun k => rfl
          have hpiv_sum :
              ∑ k : Fin (vhi - vlo - 1 + 1),
                (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                 subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·))) ≤
              ∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r)) := by
            rw [hfin_eq]
            simpa only [hlen_u] using sum_subCost_pivot_le u
          have hcard :
              (vhi - vlo - 1 + 1) • (28 * (m : ℝ) + baseCost) =
                (m : ℝ) * (28 * (m : ℝ) + baseCost) := by
            rw [nsmul_eq_mul]
            congr 1
            exact_mod_cast hm_eq
          have hsplit_sum :
              ∑ k : Fin (vhi - vlo - 1 + 1),
                (28 * (m : ℝ) + baseCost +
                  (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                   subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)))) =
              (m : ℝ) * (28 * (m : ℝ) + baseCost) +
                ∑ k : Fin (vhi - vlo - 1 + 1),
                  (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                   subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·))) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              hcard]
          have hm_pos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
          rw [hsplit_sum, add_div, mul_div_cancel_left₀ _ (ne_of_gt hm_pos)]
          have hrec := subCost_recurrence hm2
          have hdiv_le :
              (∑ k : Fin (vhi - vlo - 1 + 1),
                (subCost (u.countP (· < u[k.val]'(by have := k.isLt; simp [u]; omega))) +
                 subCost (u.countP (u[k.val]'(by have := k.isLt; simp [u]; omega) < ·)))) /
                (m : ℝ) ≤
              (∑ r ∈ Finset.range m, (subCost r + subCost (m - 1 - r))) / (m : ℝ) :=
            div_le_div_of_nonneg_right hpiv_sum (le_of_lt hm_pos)
          change 28 * (m : ℝ) + baseCost + _ ≤ baseCost + subCost m
          linarith

/-- `setup` executes deterministically from `Data.init input` within `8 * input.length + 29`
instructions, establishing `OuterInv` with initial stack `[(1, n + 1)]` (if `2 ≤ n`) or `[]`. -/
theorem setup_spec {w : ℕ} {input : List ℕ} (hw : logWidth 3 input.length ≤ w) :
    ∃ x_init t_s, Exec w setup (Data.init input) x_init t_s ∧
      t_s ≤ 8 * input.length + 29 ∧
      OuterInv w input x_init ∧
      readStack input.length x_init =
        (if 2 ≤ input.length then [(1, input.length + 1)] else []) := by
  set n := input.length
  set x₀ : Data 16 := Data.init input
  have hfit_all : Fits w (3 * n + 3) := fits_three_mul_add_three hw
  have hfit_1 : Fits w 1 := hfit_all.of_le (by omega)
  set s₁ := x₀.set len n
  set s₂ := s₁.set one 1
  set s₃ := s₂.set gt (n + 1)
  have e₁ : Exec (B := .standard) w (.op (.load len zero)) x₀ s₁ 1 := by
    simpa [s₁, x₀, n] using Exec.load (w := w) (d := len) (a := zero) (x := x₀)
  have e₂ : Exec (B := .standard) w (.op (.const one 1)) s₁ s₂ 1 := Exec.const hfit_1
  have e₃ : Exec w (.op (.bin .add gt len one)) s₂ s₃ 1 := by
    have hl : s₂.regs len = n := by simp [s₂, s₁, x₀]
    have ho : s₂.regs one = 1 := by simp [s₂]
    simpa [s₃, hl, ho, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := gt) (i := len)
      (j := one) (x := s₂) (hfit_all.of_le (by simp [hl, ho, BinOp.eval]; omega))
  have ea₁ := alloc_exec (w := w) (frontier := gt) (count := len) (result := stackLo)
    (cur := cur) (zero := zero) (one := one) (x := s₃) (by decide) hfit_1
    (hfit_all.of_le (by simp [s₃, s₂, s₁, x₀]; omega))
  set s₄ : Data 16 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
        s₃.regs zero 0) one 1) stackLo (s₃.regs gt)) gt (s₃.regs gt + s₃.regs len))
        cur (s₃.regs gt + s₃.regs len),
      clear s₃.mem (s₃.regs gt) (s₃.regs len)⟩
  have ea₂ := alloc_exec (w := w) (frontier := gt) (count := len) (result := stackHi)
    (cur := cur) (zero := zero) (one := one) (x := s₄) (by decide) hfit_1
    (hfit_all.of_le (by simp [s₄, s₃, s₂, s₁, x₀]; omega))
  set s₅ : Data 16 :=
    ⟨Function.update (Function.update (Function.update (Function.update (Function.update
        s₄.regs zero 0) one 1) stackHi (s₄.regs gt)) gt (s₄.regs gt + s₄.regs len))
        cur (s₄.regs gt + s₄.regs len),
      clear s₄.mem (s₄.regs gt) (s₄.regs len)⟩
  have hs₅_zero : s₅.regs zero = 0 := by simp [s₅]
  have hs₅_one : s₅.regs one = 1 := by simp [s₅]
  have hs₅_len : s₅.regs len = n := by simp [s₅, s₄, s₃, s₂, s₁, x₀]
  have hs₅_sLo : s₅.regs stackLo = n + 1 := by simp [s₅, s₄, s₃]
  have hs₅_sHi : s₅.regs stackHi = 2 * n + 1 := by simp [s₅, s₄, s₃, s₂, s₁, x₀]; omega
  set s₆ := s₅.set two 2
  set s₇ := s₆.set sp 0
  set s₈ := s₇.set lo 1
  set s₉ := s₈.set hi (n + 1)
  have e₆ : Exec w (.op (.bin .add two one one)) s₅ s₆ 1 := by
    simpa [s₆, hs₅_one, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := two) (i := one)
      (j := one) (x := s₅) (hfit_all.of_le (by simp [hs₅_one, BinOp.eval]))
  have e₇ : Exec (B := .standard) w (.op (.const sp 0)) s₆ s₇ 1 := Exec.const (fits_zero w)
  have e₈ : Exec (B := .standard) w (.op (.copy lo one)) s₇ s₈ 1 := by
    have : s₇.regs one = 1 := by simp [s₇, s₆, hs₅_one]
    simpa [s₈, this] using Exec.copy (w := w) (d := lo) (s := one) (x := s₇)
  have e₉ : Exec w (.op (.bin .add hi len one)) s₈ s₉ 1 := by
    have hl : s₈.regs len = n := by simp [s₈, s₇, s₆, hs₅_len]
    have ho : s₈.regs one = 1 := by simp [s₈, s₇, s₆, hs₅_one]
    simpa [s₉, hl, ho, BinOp.eval] using Exec.bin (w := w) (f := .add) (d := hi) (i := len)
      (j := one) (x := s₈) (hfit_all.of_le (by simp [hl, ho, BinOp.eval]; omega))
  obtain ⟨x_init, e_push, hread_init, hmod_push⟩ := pushIfNonTrivial_spec (w := w) (n := n)
    (a := lo) (b := hi) (x := s₉) (by decide) (by decide)
    (by simp [s₉, s₈, s₇, s₆, hs₅_one])
    (by simp [s₉, s₈, s₇, s₆])
    (by simp [s₉, s₈, s₇, s₆, hs₅_sLo])
    (by simp [s₉, s₈, s₇, s₆, hs₅_sHi])
    hfit_all
    ⟨by simp [s₉, s₈], by simp [s₉]⟩
    (fun hge => by simp [s₉, s₈, s₇] at hge ⊢; omega)
  have hlen_s₃ : s₃.regs len = n := by simp [s₃, s₂, s₁, x₀]
  have hlen_s₄ : s₄.regs len = n := by simp [s₄, hlen_s₃]
  have ew : ExecWithin w setup x₀ x_init (8 * n + 29) := by
    have epref : ExecWithin w setup x₀ x_init
        (1 + (1 + (1 + ((4 * s₃.regs len + 7) + ((4 * s₄.regs len + 7) +
          (1 + (1 + (1 + (1 + 8))))))))) :=
      e₁.within.seq (e₂.within.seq (e₃.within.seq (ea₁.within.seq (ea₂.within.seq
        (e₆.within.seq (e₇.within.seq (e₈.within.seq (e₉.within.seq e_push))))))))
    exact epref.mono (by rw [hlen_s₃, hlen_s₄]; omega)
  obtain ⟨t_s, hts_le, he_setup⟩ := ew
  have hread_s₉ : readStack n s₉ = [] := by simp [readStack, s₉, s₈, s₇]
  have hstack_final : readStack n x_init = (if 2 ≤ n then [(1, n + 1)] else []) := by
    rw [hread_init, hread_s₉]
    simp only [s₉, s₈, Data.set_regs, Function.update_of_ne (by decide : lo ≠ hi),
      Function.update_self, List.nil_append]
    have : (1 + 2 ≤ n + 1) ↔ (2 ≤ n) := by omega
    simp only [this]
  have hslice_init : memSlice 1 (n + 1) x_init.mem = input := by
    have hmem_eq : ∀ a, 1 ≤ a → a < n + 1 → x_init.mem a = x₀.mem a := by
      intro a ha1 ha2
      rw [hmod_push a (by simp [Finset.mem_Ico]; omega)]
      change clear (clear x₀.mem (s₃.regs gt) (s₃.regs len)) (s₄.regs gt) (s₄.regs len) a =
        x₀.mem a
      have hg₃ : s₃.regs gt = n + 1 := by simp [s₃]
      have hg₄ : s₄.regs gt = 2 * n + 1 := by simp [s₄, hg₃, hlen_s₃]; omega
      rw [clear_of_not_owns (by simp [Block.Owns, hg₄, hlen_s₄]; omega),
        clear_of_not_owns (by simp [Block.Owns, hg₃, hlen_s₃]; omega)]
    rw [memSlice_congr hmem_eq]
    refine List.ext_getElem (by simp [n]) fun i h1 h2 => ?_
    have hi : i < n := by simpa [n] using h2
    rw [getElem_memSlice (by omega), show 1 + i = i + 1 by omega]
    simp [x₀, Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hmod_init : Modifies (Finset.Ico 1 (3 * n + 1)) x₀.mem x_init.mem := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    rw [hmod_push a (by simp [Finset.mem_Ico]; omega)]
    change clear (clear x₀.mem (s₃.regs gt) (s₃.regs len)) (s₄.regs gt) (s₄.regs len) a = x₀.mem a
    have hg₃ : s₃.regs gt = n + 1 := by simp [s₃]
    have hg₄ : s₄.regs gt = 2 * n + 1 := by simp [s₄, hg₃, hlen_s₃]; omega
    rw [clear_of_not_owns (by simp [Block.Owns, hg₄, hlen_s₄]; omega),
      clear_of_not_owns (by simp [Block.Owns, hg₃, hlen_s₃]; omega)]
  have hVS_init : ValidStack n (readStack n x_init) := by
    rw [hstack_final]
    split_ifs with hn2
    · refine ⟨fun p hp => ?_, List.pairwise_singleton _ _⟩
      rw [List.mem_singleton] at hp; subst hp; exact ⟨le_rfl, by omega, le_rfl⟩
    · exact ⟨fun p hp => by simp at hp, List.Pairwise.nil⟩
  have hno_inv_init : NoExternalInversions n x_init.mem (readStack n x_init) := by
    rw [hstack_final]
    intro i j hi1 hij hjn hno
    have hn2 : 2 ≤ n := by omega
    simp only [hn2, ↓reduceIte] at hno
    exact absurd ⟨hi1, hjn⟩ (hno (1, n + 1) (List.mem_singleton_self _))
  refine ⟨x_init, t_s, he_setup, hts_le, ?_, hstack_final⟩
  exact ⟨hw,
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆, hs₅_zero]),
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆, hs₅_one]),
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆]),
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆, hs₅_len, n]),
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆, hs₅_sLo, n]),
    (e_push.regs_eq (by decide)).trans (by simp [s₉, s₈, s₇, s₆, hs₅_sHi, n]),
    hVS_init, hno_inv_init, by rw [hslice_init], hmod_init⟩

/-- **In-place randomized quicksort: correctness, worst-case bounds, `rand`-call bound, and
`O(n log n)` expected running time.**

For any `input : List ℕ` of length `n` and word size `w ≥ logWidth 3 n` with `InputFits w input`:
1. `program` halts without faulting within `worstCaseTime n = 20 * n ^ 2 + 8 * n + 32` instructions
   on every execution path (`RandHaltsWithin`);
2. Every execution path makes at most `n - 1` `rand` calls (`RandCallsBounded`);
3. On every supported halting configuration `.halted 0 y`, `y.Bounded w` holds,
   `memSlice 1 (n + 1) y.mem` is a sorted permutation of `input`, `Block.mk 1 n` realizes
   `input.mergeSort`, and memory outside `Finset.Ico 1 (3 * n + 1)` is untouched (`Modifies`);
4. The expected instruction count satisfies
   `expectedTime w program (.init input) ≤ expectedTimeBound n = 120 * n * (⌊log₂ n⌋ + 1) + 32`
   unconditionally (even when `input` contains duplicate elements). -/
theorem quicksort_correct_and_bounds {w : ℕ} {input : List ℕ}
    (hw : logWidth 3 input.length ≤ w) (hfit : InputFits w input) :
    RandHaltsWithin w program (.init input) (worstCaseTime input.length) ∧
    RandCallsBounded w program (.init input) (worstCaseTime input.length) (input.length - 1) ∧
    (∀ cfg ∈ (runRand w program (worstCaseTime input.length) (.running (.init input))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧
        y.Bounded w ∧
        (memSlice 1 (input.length + 1) y.mem).Perm input ∧
        (memSlice 1 (input.length + 1) y.mem).Pairwise (· ≤ ·) ∧
        (Block.mk 1 input.length).Realizes y.mem
          (fun i => input.mergeSort[i.val]'(by simpa only [List.length_mergeSort] using i.isLt)) ∧
        Modifies (Finset.Ico 1 (3 * input.length + 1)) (Data.init (r := 16) input).mem y.mem) ∧
    expectedTime w program (.init input) ≤ (expectedTimeBound input.length : ℝ≥0∞) := by
  set n := input.length
  obtain ⟨x_init, t_s, he_setup, hts_le, hI_init, hstack_init⟩ := setup_spec hw
  change t_s ≤ 8 * n + 29 at hts_le
  change readStack n x_init = if 2 ≤ n then [(1, n + 1)] else [] at hstack_init
  -- 1. Worst-case `ExecRandWithin` via `ExecRandWithin.loop_potential`
  have hloop_wc : ExecRandWithin w (ram[ while zero < sp do [ ⟪outerBody⟫ ] ]) x_init
      (fun y => OuterInv w input y ∧ ¬(Cond.lt zero sp).Holds y)
      (stepPotential n x_init + 2) (callPotential n x_init) :=
    ExecRandWithin.loop_potential (OuterInv w input) (stepPotential n) (callPotential n)
      (fun s hs hc => outerBody_worstCase_step hs hc) hI_init
  have hstep_init : stepPotential n x_init ≤ 20 * n ^ 2 := by
    rw [stepPotential, hstack_init]
    split_ifs <;> simp
  have hcall_init : callPotential n x_init ≤ n - 1 := by
    rw [callPotential, hstack_init]
    split_ifs <;> simp
  have hloop_wc' : ExecRandWithin w (ram[ while zero < sp do [ ⟪outerBody⟫ ] ]) x_init
      (fun y => OuterInv w input y ∧ ¬(Cond.lt zero sp).Holds y)
      (20 * n ^ 2 + 2) (n - 1) :=
    hloop_wc.mono (fun _ h => h) (by omega) hcall_init
  have hcode_wc : ExecRandWithin w code (Data.init input)
      (fun y => OuterInv w input y ∧ ¬(Cond.lt zero sp).Holds y)
      (20 * n ^ 2 + 8 * n + 31) (n - 1) := by
    have hs_wc : ExecRandWithin w setup (Data.init input) (· = x_init) (8 * n + 29) 0 :=
      (ExecWithin.mono he_setup.within hts_le).execRandWithin rfl
    exact (hs_wc.seq fun y hy => hy ▸ hloop_wc').mono (fun _ h => h) (by omega) (by omega)
  obtain ⟨hHalts, hCalls, hPost⟩ :=
    hcode_wc.program zero (T' := worstCaseTime n) (by simp only [worstCaseTime]; omega)
  -- 2. Expected running time via `expectedCodeTime_loop_le_of_drift`
  obtain ⟨⟨m_loop, hm_loop⟩, hloop_exp⟩ := expectedCodeTime_loop_le_of_drift
    (OuterInv w input) (callPotential n) (expPotential n) hI_init
    (fun s hs hc => outerBody_drift_step hs hc)
  have hexec_code : ExecRand w code (Data.init input)
      ((fun z => (z.1, t_s + z.2)) <$> m_loop) := he_setup.seqRand hm_loop
  have hexp_init :
      expPotential n x_init ≤ ENNReal.ofReal ((112 * n * (Nat.log 2 n + 1) : ℕ) : ℝ) := by
    rw [expPotential, hstack_init]
    split_ifs with hn2
    · simp only [List.map_singleton, List.sum_singleton, Nat.add_sub_cancel_right]
      refine ENNReal.ofReal_le_ofReal ?_
      have hsub : subCost n ≤ 56 * ((n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) := by
        calc
          subCost n ≤ 56 * ((n : ℝ) + 1) * (harmonic n : ℝ) := subCost_le_formula n
          _ ≤ 56 * ((n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left
              (by exact_mod_cast harmonic_le_log_add_one n) (by positivity)
      have hn_le : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
        have : n + 1 ≤ 2 * n := by omega
        exact_mod_cast this
      have hmul : 56 * ((n : ℝ) + 1) * ((Nat.log 2 n : ℝ) + 1) ≤
          ((112 * n * (Nat.log 2 n + 1) : ℕ) : ℝ) := by
        push_cast
        nlinarith [show (0 : ℝ) ≤ (Nat.log 2 n : ℝ) + 1 by positivity]
      exact hsub.trans hmul
    · simp
  have hexp_total : expectedTime w program (.init input) ≤ (expectedTimeBound n : ℝ≥0∞) := by
    rw [program, State.init, expectedCodeTime_program hexec_code zero, code,
      expectedCodeTime_seq_of_exec he_setup]
    rw [ENNReal.ofReal_natCast] at hexp_init
    have hts_cast : (t_s : ℝ≥0∞) ≤ (8 * n + 29 : ℕ) := by exact_mod_cast hts_le
    calc
      (t_s : ℝ≥0∞) + expectedCodeTime w (ram[ while zero < sp do [ ⟪outerBody⟫ ] ]) x_init + 1
        ≤ ((8 * n + 29 : ℕ) : ℝ≥0∞) +
            (((112 * n * (Nat.log 2 n + 1) : ℕ) : ℝ≥0∞) + 2) + 1 := by
          gcongr
          exact hloop_exp.trans (by gcongr)
      _ = (((8 * n + 29) + (112 * n * (Nat.log 2 n + 1) + 2) + 1 : ℕ) : ℝ≥0∞) := by
          norm_cast
      _ ≤ (expectedTimeBound n : ℝ≥0∞) := by
          norm_cast
          simp only [expectedTimeBound]
          have hlog1 : 1 ≤ Nat.log 2 n + 1 := by omega
          nlinarith
  -- 3. Assemble final postcondition on every supported halting configuration
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, hexp_total⟩
  obtain ⟨y, hcfg_eq, hIy, hnc⟩ := hPost cfg hcfg
  have hy_zero : y.regs zero = 0 := hIy.zero_eq
  rw [hy_zero] at hcfg_eq
  have hsp_zero : y.regs sp = 0 := by
    simp only [Cond.holds_lt, hy_zero] at hnc
    omega
  have hstack_empty : readStack n y = [] := by simp [readStack, hsp_zero]
  have hsorted : (memSlice 1 (n + 1) y.mem).Pairwise (· ≤ ·) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [length_memSlice, Nat.add_sub_cancel_right] at hi hj
    rw [getElem_memSlice (by omega), getElem_memSlice (by omega)]
    exact hIy.no_ext_inv (1 + i) (1 + j) (by omega) (by omega) (by omega) fun p hp => by
      rw [hstack_empty] at hp; simp at hp
  have hslice_eq_sort : memSlice 1 (n + 1) y.mem = input.mergeSort :=
    (hIy.perm.trans (List.mergeSort_perm input _).symm).eq_of_pairwise' hsorted
      (List.pairwise_mergeSort' (· ≤ ·) input)
  have hrealizes : (Block.mk 1 input.length).Realizes y.mem
      (fun i => input.mergeSort[i.val]'(by simpa only [List.length_mergeSort] using i.isLt)) := by
    intro i
    have hi_lt : i.val < n := i.isLt
    change y.mem (1 + i.val) = _
    have hget : (memSlice 1 (n + 1) y.mem)[i.val]'(by simp [hi_lt]) = y.mem (1 + i.val) :=
      getElem_memSlice (by omega)
    rw [← hget]
    simp [hslice_eq_sort]
  have hbounded : y.Bounded w := by
    have hb := runRand_bounded_init hfit hcfg
    rw [hcfg_eq] at hb
    exact hb.2
  exact ⟨y, hcfg_eq, hbounded, hIy.perm, hsorted, hrealizes, hIy.modifies⟩

end Cslib.Algorithms.WordRAM.Quicksort
