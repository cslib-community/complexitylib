/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Quicksort

/-!
# Randomized quicksort and expected-time tests

Concrete non-vacuity and behavioral tests for `Cslib.WordRAM.expectedTime` and
`Cslib.Algorithms.WordRAM.Quicksort`:

1. Non-monotone input with duplicates `[3, 1, 2, 1]` at `w = 9`: every supported halting path
   preserves `Bounded 9`, outputs `[1, 1, 2, 3]` in `mem[1..4]`, preserves memory outside `[1, 13)`,
   uses at most `3` `rand` calls, halts within `384` instructions, and satisfies
   `expectedTime ≤ 1472` and `AlmostSurelyHalts`.
2. Six-element non-monotone input with two duplicate groups `[4, 2, 4, 0, 2, 1]` at `w = 9`: every
   supported halting path outputs `[0, 1, 2, 2, 4, 4]` in `memSlice 1 7` within `5` `rand` calls.
3. Trivial edge cases `[]` and `[5]` at `w = 3`: `0` `rand` calls (`RandCallsBounded ... 0`).
4. Exact `expectedTime` evaluation on a randomized `Code.program` (`rand(1)` halting in `3` exact
   instructions on every branch, so `expectedTime = 3`).
-/

@[expose] public section

namespace ComplexityTests.WordRAMQuicksort

open Cslib Cslib.WordRAM Cslib.Algorithms.WordRAM
open scoped ENNReal

/-! ## 1. Non-monotone input with duplicates: `[3, 1, 2, 1]` at `w = 9` -/

theorem quicksort_dup4 :
    RandHaltsWithin 9 Quicksort.program (.init [3, 1, 2, 1]) 384 ∧
    AlmostSurelyHalts 9 Quicksort.program (.init [3, 1, 2, 1]) ∧
    RandCallsBounded 9 Quicksort.program (.init [3, 1, 2, 1]) 384 3 ∧
    (∀ cfg ∈ (runRand 9 Quicksort.program 384 (.running (.init [3, 1, 2, 1]))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.Bounded 9 ∧
        y.mem 1 = 1 ∧ y.mem 2 = 1 ∧ y.mem 3 = 2 ∧ y.mem 4 = 3 ∧
        (∀ a, a = 0 ∨ 13 ≤ a → y.mem a = (Data.init (r := 16) [3, 1, 2, 1]).mem a)) ∧
    expectedTime 9 Quicksort.program (.init [3, 1, 2, 1]) ≤ 1472 := by
  have hw : logWidth 3 ([3, 1, 2, 1] : List ℕ).length ≤ 9 := by decide
  have hfit : InputFits 9 [3, 1, 2, 1] := by decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := Quicksort.quicksort_correct_and_bounds hw hfit
  have hwc : Quicksort.worstCaseTime ([3, 1, 2, 1] : List ℕ).length = 384 := by decide
  have hcalls_n : ([3, 1, 2, 1] : List ℕ).length - 1 = 3 := rfl
  have hexpb : Quicksort.expectedTimeBound ([3, 1, 2, 1] : List ℕ).length = 1472 := by decide
  rw [hwc] at hHalts hCalls hPost
  rw [hcalls_n] at hCalls
  rw [hexpb] at hExp
  refine ⟨hHalts, hHalts.almostSurelyHalts, hCalls, fun cfg hcfg => ?_, by simpa using hExp⟩
  obtain ⟨y, hcfg_eq, hbnd, hperm, hsorted, -, hmod⟩ := hPost cfg hcfg
  have hslice : Quicksort.memSlice 1 5 y.mem = [1, 1, 2, 3] :=
    (hperm.trans (by decide : ([3, 1, 2, 1] : List ℕ).Perm [1, 1, 2, 3])).eq_of_pairwise'
      hsorted (by decide)
  have hlist : [y.mem 1, y.mem 2, y.mem 3, y.mem 4] = [1, 1, 2, 3] := by
    simpa [Quicksort.memSlice, List.range_succ] using hslice
  simp only [List.cons.injEq, and_true] at hlist
  rcases hlist with ⟨h1, h2, h3, h4⟩
  refine ⟨y, hcfg_eq, hbnd, h1, h2, h3, h4, fun a ha => hmod a ?_⟩
  rw [Finset.mem_Ico]
  simp only [List.length_cons, List.length_nil]
  omega

/-! ## 2. Six-element non-monotone input with multiple duplicate groups: `[4, 2, 4, 0, 2, 1]` -/

theorem quicksort_dup6 :
    RandHaltsWithin 9 Quicksort.program (.init [4, 2, 4, 0, 2, 1]) (Quicksort.worstCaseTime 6) ∧
    RandCallsBounded 9 Quicksort.program (.init [4, 2, 4, 0, 2, 1])
      (Quicksort.worstCaseTime 6) 5 ∧
    (∀ cfg ∈ (runRand 9 Quicksort.program (Quicksort.worstCaseTime 6)
        (.running (.init [4, 2, 4, 0, 2, 1]))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧
        Quicksort.memSlice 1 7 y.mem = [0, 1, 2, 2, 4, 4]) ∧
    expectedTime 9 Quicksort.program (.init [4, 2, 4, 0, 2, 1]) ≤
      (Quicksort.expectedTimeBound 6 : ℝ≥0∞) := by
  have hw : logWidth 3 ([4, 2, 4, 0, 2, 1] : List ℕ).length ≤ 9 := by decide
  have hfit : InputFits 9 [4, 2, 4, 0, 2, 1] := by decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := Quicksort.quicksort_correct_and_bounds hw hfit
  have hlen : ([4, 2, 4, 0, 2, 1] : List ℕ).length = 6 := rfl
  rw [hlen] at hHalts hCalls hExp
  have hcalls5 : (6 - 1 : ℕ) = 5 := rfl
  rw [hcalls5] at hCalls
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, hExp⟩
  rw [← hlen] at hcfg
  obtain ⟨y, hcfg_eq, -, hperm, hsorted, -, -⟩ := hPost cfg hcfg
  have hp6 : ([4, 2, 4, 0, 2, 1] : List ℕ).Perm [0, 1, 2, 2, 4, 4] :=
    List.perm_iff_count.mpr fun a => by
      rcases (by omega : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ 5 ≤ a) with
        rfl | rfl | rfl | rfl | rfl | ha
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
      · rw [List.count_eq_zero.mpr (by simp; omega), List.count_eq_zero.mpr (by simp; omega)]
  have hsort_eq : Quicksort.memSlice 1 7 y.mem = [0, 1, 2, 2, 4, 4] :=
    (hperm.trans hp6).eq_of_pairwise' hsorted (by decide)
  exact ⟨y, hcfg_eq, hsort_eq⟩

/-! ## 3. Edge cases `[]` and `[5]` at `w = 3`: zero `rand` calls -/

theorem quicksort_nil :
    RandHaltsWithin 3 Quicksort.program (.init []) 32 ∧
    RandCallsBounded 3 Quicksort.program (.init []) 32 0 ∧
    expectedTime 3 Quicksort.program (.init []) ≤ 32 := by
  have hw : logWidth 3 ([] : List ℕ).length ≤ 3 := by decide
  have hfit : InputFits 3 [] := by decide
  obtain ⟨hHalts, hCalls, -, hExp⟩ := Quicksort.quicksort_correct_and_bounds hw hfit
  have hwc : Quicksort.worstCaseTime ([] : List ℕ).length = 32 := rfl
  rw [hwc] at hHalts hCalls
  exact ⟨hHalts, hCalls, by simpa [Quicksort.expectedTimeBound] using hExp⟩

theorem quicksort_singleton :
    RandHaltsWithin 3 Quicksort.program (.init [5]) 60 ∧
    RandCallsBounded 3 Quicksort.program (.init [5]) 60 0 ∧
    (∀ cfg ∈ (runRand 3 Quicksort.program 60 (.running (.init [5]))).support,
      ∃ y : Data 16, cfg = .halted 0 y ∧ y.mem 1 = 5) ∧
    expectedTime 3 Quicksort.program (.init [5]) ≤ 152 := by
  have hw : logWidth 3 ([5] : List ℕ).length ≤ 3 := by decide
  have hfit : InputFits 3 [5] := by decide
  obtain ⟨hHalts, hCalls, hPost, hExp⟩ := Quicksort.quicksort_correct_and_bounds hw hfit
  have hwc : Quicksort.worstCaseTime ([5] : List ℕ).length = 60 := rfl
  rw [hwc] at hHalts hCalls hPost
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, by simpa [Quicksort.expectedTimeBound] using hExp⟩
  obtain ⟨y, hcfg_eq, -, hperm, -, -, -⟩ := hPost cfg hcfg
  have hslice : Quicksort.memSlice 1 2 y.mem = [5] := List.Perm.eq_singleton hperm
  have h1 : [y.mem 1] = [5] := by simpa [Quicksort.memSlice] using hslice
  exact ⟨y, hcfg_eq, List.head_eq_of_cons_eq h1⟩

/-! ## 4. Exact `expectedTime` on a small randomized `Code.program` -/

abbrev r0 : Fin 2 := 0

abbrev coinProg : Program .standard 2 :=
  (ram[ r0 ← #1; r0 ← rand r0 ]).program r0

theorem coinProg_expectedTime :
    expectedTime 2 coinProg (.init []) = 3 := by
  have e1 : Exec (B := .standard) 2 (.op (.const r0 1)) (.init [])
      ((Data.init [] : Data 2).set r0 1) 1 :=
    Exec.const (by decide)
  have e2 : ExecRand (B := .standard) 2 (.rand r0 r0) ((Data.init [] : Data 2).set r0 1)
      (do
        let k ← ProbComp.unifFin 1
        pure ((((Data.init [] : Data 2).set r0 1).set r0 k.val), 1)) :=
    ExecRand.rand (by decide)
  have hexec := e1.seqRand e2
  rw [coinProg, State.init, expectedCodeTime_program hexec r0,
    expectedCodeTime_seq_of_exec e1, expectedCodeTime_rand (by decide)]
  norm_num

/-! ## 5. `ProbComp.expect` and `harmonic` bounds -/

theorem uniform_fin4_expect :
    ProbComp.expect (ProbComp.uniform (Fin 4)) (fun k : Fin 4 => (k.val : ℝ≥0∞)) = 6 / 4 := by
  rw [ProbComp.expect_uniform]
  simp [Fin.sum_univ_four]
  norm_num

theorem harmonic_six_bound :
    harmonic 6 = 49 / 20 ∧ harmonic 6 ≤ (Nat.log 2 6 : ℚ) + 1 :=
  ⟨by norm_num [harmonic, Finset.sum_range_succ], harmonic_le_log_add_one 6⟩

end ComplexityTests.WordRAMQuicksort
