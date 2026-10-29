/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Quickselect

/-!
# Randomized quickselect tests

Concrete non-vacuity and behavioral tests for `Cslib.Algorithms.WordRAM.Quickselect`:

1. Six-element non-monotone input with multiple duplicate groups `[4, 2, 4, 0, 2, 1]` at `w = 6`
   across boundary and interior ranks (`k = 0`, `k = 2`, `k = 3`, `k = 5 = n - 1`): verifies
   `RandHaltsWithin` (`375` steps), `AlmostSurelyHalts`, `RandCallsBounded` (`≤ 5` calls), exact
   order-statistic return values (`0`, `2`, `2`, `4`), in-place partition inequalities around
   `2 + k`, zero-auxiliary-space frame preservation (`M[0] = 7`, `M[1] = k`, `M[8] = 0`), and
   `expectedTime ≤ 495`.
2. Singleton `[7]` at `k = 0`, `w = 3`: `0` `rand` calls (`RandCallsBounded ... 0`), returning `7`
   with `M[2] = 7`.
3. Out-of-range ranks `k ≥ n` (`k = 6` on `[4, 2, 4, 0, 2, 1]` at `w = 6`, and `k = 0` on `[]` at
   `w = 1`): deterministic `8`-step halting returning `0` with `0` `rand` calls, untouched memory,
   and `expectedTime = 8`.
4. Reusable structured subroutine `Quickselect.selectSlice` on a non-default slice `[10, 14)` at
   `w = 4`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMQuickselect

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM
open scoped ENNReal

/-! ## 1. Duplicate-heavy length-6 input `[4, 2, 4, 0, 2, 1]` across `k = 0, 2, 3, 5` -/

abbrev dup6 : List ℕ := [4, 2, 4, 0, 2, 1]

theorem dup6_mergeSort : dup6.mergeSort = [0, 1, 2, 2, 4, 4] := by
  have hp6 : dup6.Perm [0, 1, 2, 2, 4, 4] :=
    List.perm_iff_count.mpr fun a => by
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ 5 ≤ a) with
        rfl | rfl | rfl | rfl | rfl | ha
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rw [List.count_eq_zero.mpr
            (by simp only [dup6, List.mem_cons, List.not_mem_nil, or_false]; omega),
          List.count_eq_zero.mpr
            (by simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)]
  exact ((List.mergeSort_perm dup6 (· ≤ ·)).trans hp6).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) dup6) (by decide)

theorem quickselect_dup6_rank (k : ℕ) (hk : k < 6) (hk_fit : k < 64) :
    let expected := ([0, 1, 2, 2, 4, 4] : List ℕ)[k]'(by simpa using hk)
    RandHaltsWithin 6 Quickselect.program (.init (k :: dup6)) 375 ∧
    AlmostSurelyHalts 6 Quickselect.program (.init (k :: dup6)) ∧
    RandCallsBounded 6 Quickselect.program (.init (k :: dup6)) 375 5 ∧
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (k :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted expected y ∧
        y.Bounded 6 ∧
        (Quicksort.memSlice 2 8 y.mem).Perm dup6 ∧
        y.mem (2 + k) = expected ∧
        (∀ i < k, y.mem (2 + i) ≤ expected) ∧
        (∀ i, k < i → i < 6 → expected ≤ y.mem (2 + i)) ∧
        y.mem 0 = 7 ∧ y.mem 1 = k ∧ y.mem 8 = 0) ∧
    expectedTime 6 Quickselect.program (.init (k :: dup6)) ≤ 495 := by
  have hlen : dup6.length = 6 := rfl
  have hw : logWidth 2 dup6.length ≤ 6 := by decide
  have hfit : InputFits 6 (k :: dup6) := by
    refine ⟨by change Fits 6 7; decide, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hk_fit
    · simp only [dup6, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ :=
    Quickselect.quickselect_correct_and_bounds (by simpa only [hlen] using hk) hw hfit
  have hwc : Quickselect.worstCaseTime dup6.length = 375 := by decide
  have hcalls_n : dup6.length - 1 = 5 := rfl
  have hexpb : Quickselect.expectedTimeBound dup6.length = 495 := by decide
  rw [hwc] at hHalts hCalls hPost
  rw [hcalls_n] at hCalls
  rw [hexpb] at hExp
  have hexp_val : dup6.mergeSort[k]'(by rw [List.length_mergeSort, hlen]; exact hk) =
      ([0, 1, 2, 2, 4, 4] : List ℕ)[k]'(by simpa using hk) := by
    simp only [dup6_mergeSort]
  refine ⟨hHalts, hHalts.almostSurelyHalts, hCalls, fun cfg hcfg => ?_, by simpa using hExp⟩
  obtain ⟨y, hcfg_eq, hbnd, hperm, hy_k, hleft, hright, hmod⟩ := hPost cfg hcfg
  rw [hexp_val] at hcfg_eq hy_k
  have hm0 : y.mem 0 = 7 := hmod 0 (by simp)
  have hm1 : y.mem 1 = k := hmod 1 (by simp)
  have hm8 : y.mem 8 = 0 := hmod 8 (by simp)
  exact ⟨y, hcfg_eq, hbnd, hperm, hy_k,
    fun i hi => by rw [← hy_k]; exact hleft i hi,
    fun i hki hi6 => by rw [← hy_k]; exact hright i hki hi6,
    hm0, hm1, hm8⟩

/-- Minimum (`k = 0`) on `[4, 2, 4, 0, 2, 1]` returns `0`. -/
theorem quickselect_dup6_min :
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (0 :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.mem 2 = 0 ∧ y.mem 8 = 0) ∧
    expectedTime 6 Quickselect.program (.init (0 :: dup6)) ≤ 495 := by
  obtain ⟨-, -, -, hPost, hExp⟩ := quickselect_dup6_rank 0 (by omega) (by omega)
  refine ⟨fun cfg hcfg => ?_, hExp⟩
  obtain ⟨y, hcfg_eq, -, -, hy2, -, -, -, -, hm8⟩ := hPost cfg hcfg
  exact ⟨y, hcfg_eq, hy2, hm8⟩

/-- Interior duplicate ranks (`k = 2` and `k = 3`) on `[4, 2, 4, 0, 2, 1]` both return `2`. -/
theorem quickselect_dup6_mid :
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (2 :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted 2 y ∧ y.mem 4 = 2) ∧
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (3 :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted 2 y ∧ y.mem 5 = 2) := by
  obtain ⟨-, -, -, hPost2, -⟩ := quickselect_dup6_rank 2 (by omega) (by omega)
  obtain ⟨-, -, -, hPost3, -⟩ := quickselect_dup6_rank 3 (by omega) (by omega)
  refine ⟨fun cfg hcfg => ?_, fun cfg hcfg => ?_⟩
  · obtain ⟨y, hcfg_eq, -, -, hy, -⟩ := hPost2 cfg hcfg
    exact ⟨y, hcfg_eq, hy⟩
  · obtain ⟨y, hcfg_eq, -, -, hy, -⟩ := hPost3 cfg hcfg
    exact ⟨y, hcfg_eq, hy⟩

/-- Maximum (`k = 5 = n - 1`) on `[4, 2, 4, 0, 2, 1]` returns `4`. -/
theorem quickselect_dup6_max :
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (5 :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted 4 y ∧ y.mem 7 = 4 ∧ (∀ i < 5, y.mem (2 + i) ≤ 4)) ∧
    expectedTime 6 Quickselect.program (.init (5 :: dup6)) ≤ 495 := by
  obtain ⟨-, -, -, hPost, hExp⟩ := quickselect_dup6_rank 5 (by omega) (by omega)
  refine ⟨fun cfg hcfg => ?_, hExp⟩
  obtain ⟨y, hcfg_eq, -, -, hy7, hleft, -⟩ := hPost cfg hcfg
  exact ⟨y, hcfg_eq, hy7, hleft⟩

/-! ## 2. Singleton `[7]` at `k = 0`, `w = 3`: zero `rand` calls -/

theorem quickselect_singleton :
    RandHaltsWithin 3 Quickselect.program (.init [0, 7]) 25 ∧
    RandCallsBounded 3 Quickselect.program (.init [0, 7]) 25 0 ∧
    (∀ cfg ∈ (runRand 3 Quickselect.program 25 (.running (.init [0, 7]))).support,
      ∃ y : Data 16, cfg = .halted 7 y ∧ y.mem 2 = 7) ∧
    expectedTime 3 Quickselect.program (.init [0, 7]) ≤ 95 := by
  have hw : logWidth 2 ([7] : List ℕ).length ≤ 3 := by decide
  have hfit : InputFits 3 (0 :: [7]) := by decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ :=
    Quickselect.quickselect_correct_and_bounds (k := 0) (input := [7]) (by decide) hw hfit
  have hwc : Quickselect.worstCaseTime ([7] : List ℕ).length = 25 := rfl
  rw [hwc] at hHalts hCalls hPost
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, by simpa [Quickselect.expectedTimeBound] using hExp⟩
  obtain ⟨y, hcfg_eq, -, -, hy2, -⟩ := hPost cfg hcfg
  have hms1 : ([7] : List ℕ).mergeSort = [7] :=
    (List.mergeSort_perm [7] (· ≤ ·)).eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≤ ·) [7]) (by decide)
  simp only [hms1] at hcfg_eq hy2
  exact ⟨y, hcfg_eq, hy2⟩

/-! ## 3. Out-of-range `k ≥ n` (`k = 6` on `dup6`, and `k = 0` on `[]` at `w = 1`) -/

theorem quickselect_out_of_range_dup6 :
    Executes 6 Quickselect.program (.init (6 :: dup6)) 0 8 ∧
    RandCallsBounded 6 Quickselect.program (.init (6 :: dup6)) 375 0 ∧
    (∀ cfg ∈ (runRand 6 Quickselect.program 375 (.running (.init (6 :: dup6)))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded 6 ∧
        y.mem = (Data.init (r := 16) (6 :: dup6)).mem) ∧
    expectedTime 6 Quickselect.program (.init (6 :: dup6)) = 8 := by
  have hfit : InputFits 6 (6 :: dup6) := by decide
  obtain ⟨hExec, -, hCalls, hPost, hExp⟩ :=
    Quickselect.quickselect_out_of_range (w := 6) (k := 6) (input := dup6) (by decide) hfit
  exact ⟨hExec, hCalls, hPost, hExp⟩

theorem quickselect_out_of_range_empty :
    Executes 1 Quickselect.program (.init [0]) 0 8 ∧
    RandCallsBounded 1 Quickselect.program (.init [0]) 15 0 ∧
    (∀ cfg ∈ (runRand 1 Quickselect.program 15 (.running (.init [0]))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded 1 ∧
        y.mem = (Data.init (r := 16) [0]).mem) ∧
    expectedTime 1 Quickselect.program (.init [0]) = 8 := by
  have hfit : InputFits 1 (0 :: ([] : List ℕ)) := by decide
  obtain ⟨hExec, -, hCalls, hPost, hExp⟩ :=
    Quickselect.quickselect_out_of_range (w := 1) (k := 0) (input := []) (by decide) hfit
  exact ⟨hExec, hCalls, hPost, hExp⟩

/-! ## 4. Reusable `selectSlice` on a custom slice `[10, 14)` at `w = 4` -/

theorem selectSlice_offset_base :
    let m₀ : ℕ → ℕ := fun a =>
      if a = 10 then 5 else if a = 11 then 1 else if a = 12 then 5 else if a = 13 then 3 else 9
    let x₀ : Data 16 :=
      (((⟨fun _ => 0, m₀⟩ : Data 16).set Quickselect.Reg.base 10).set Quickselect.Reg.len 4).set
        Quickselect.Reg.rk 2
    ExecRandWithin 4 Quickselect.selectSlice x₀
      (fun y => y.regs Quickselect.Reg.ans = 5 ∧ y.mem 12 = 5 ∧ y.mem 0 = 9 ∧ y.mem 14 = 9)
      168 3 ∧
    expectedCodeTime 4 Quickselect.selectSlice x₀ ≤ 328 := by
  intro m₀ x₀
  obtain ⟨hWC, hExp⟩ := Quickselect.selectSlice_spec (w := 4) (x := x₀) (by decide) (by decide)
  have hslice_eq : Quicksort.memSlice 10 14 x₀.mem = [5, 1, 5, 3] := by decide
  have hsort : ([5, 1, 5, 3] : List ℕ).mergeSort = [1, 3, 5, 5] :=
    ((List.mergeSort_perm [5, 1, 5, 3] (· ≤ ·)).trans (by decide)).eq_of_pairwise'
      (List.pairwise_mergeSort' (· ≤ ·) [5, 1, 5, 3]) (by decide)
  refine ⟨hWC.mono (fun y hy => ?_) (by decide) (by decide), by simpa [x₀] using hExp⟩
  obtain ⟨hans, -, hm12, -, -, hmod⟩ := hy
  have hbase_r : x₀.regs Quickselect.Reg.base = 10 := rfl
  have hlen_r : x₀.regs Quickselect.Reg.len = 4 := rfl
  have hrk_r : x₀.regs Quickselect.Reg.rk = 2 := rfl
  simp only [hbase_r, hlen_r, hrk_r, hslice_eq, hsort] at hans hm12 hmod
  exact ⟨hans, hm12, hmod 0 (by simp), hmod 14 (by simp)⟩

end ComplexityTests.WordRAMQuickselect
