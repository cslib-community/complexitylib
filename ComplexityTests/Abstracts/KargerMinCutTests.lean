/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.KargerMinCutAbstract

/-!
# Regression tests for `KargerMinCutAbstract`

Concrete non-vacuity and behavioral checks on `KargerMinCutAbstract`:

1. Weighted 3-vertex triangle (`minCut = 5`): instantiates `kargerSingleTrial` at `w = 16`,
   checking `HaltsWithin`, `RandCallsBounded ... 1`, cut-weight lower bound and memory preservation
   outside `[2, 14)`, and `2 / 6 ≤ toOuterMeasure` of hitting `minCut = 5`.
2. Weighted 4-vertex barbell (`minCut = 2` achieved strictly by `{0, 1}`, whereas every singleton
   cut has weight `11`): instantiates `kargerAmplified` (`R = 6`) and `kargerHighProb` at `w = 16`,
   checking preservation of the input matrix in memory and failure bounds `(1 - 2 / 12) ^ 6` and
   `1 / 8`.
3. Empty 3-vertex multigraph (`minCut = 0`, `totalDoubledWeight = 0`): instantiates
   `kargerSingleTrial`, verifying fault-free halting with output `0` on every branch.
-/

namespace ComplexityTests.Abstracts.KargerMinCutTests

open ComplexityAbstracts.KargerMinCutAbstract

private theorem isNonTrivialCut_iff_card {n : ℕ} (C : Finset (Fin n)) :
    IsNonTrivialCut C ↔ 0 < C.card ∧ C.card < n := by
  constructor
  · rintro ⟨hne, hnu⟩
    refine ⟨Finset.card_pos.mpr hne, Nat.lt_of_le_of_ne ?_ fun hc => hnu ?_⟩
    · simpa using Finset.card_le_univ C
    · exact Finset.eq_univ_of_card C (by simpa using hc)
  · rintro ⟨hpos, hlt⟩
    refine ⟨Finset.card_pos.mp hpos, fun hu => ?_⟩
    simp [hu] at hlt

/-- Weighted 3-vertex triangle with edge weights `w(0, 1) = 3`, `w(1, 2) = 5`, `w(0, 2) = 2`. -/
def triangleW : Fin 3 → Fin 3 → ℕ
  | 0, 1 | 1, 0 => 3
  | 1, 2 | 2, 1 => 5
  | 0, 2 | 2, 0 => 2
  | _, _ => 0

theorem isMultigraph_triangleW : IsMultigraph triangleW := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · fin_cases u <;> fin_cases v <;> rfl
  · fin_cases u <;> rfl

theorem minCut_triangleW : minCut triangleW = 5 := by
  have hnt0 : IsNonTrivialCut ({(0 : Fin 3)} : Finset (Fin 3)) := by
    rw [isNonTrivialCut_iff_card]
    decide
  have hcw0 : cutWeight triangleW ({(0 : Fin 3)} : Finset (Fin 3)) = 5 := by decide
  unfold minCut
  apply le_antisymm
  · exact Nat.sInf_le ⟨{(0 : Fin 3)}, hnt0, hcw0⟩
  · obtain ⟨C, hC, hcw⟩ :=
      Nat.sInf_mem (s := {k | ∃ C : Finset (Fin 3), IsNonTrivialCut C ∧ cutWeight triangleW C = k})
        ⟨5, {(0 : Fin 3)}, hnt0, hcw0⟩
    rw [← hcw]
    clear hcw
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

/-- Non-vacuous instantiation of `kargerSingleTrial` on `triangleW` (`n = 3, minCut = 5, w = 16`):
halts within `435` steps and `1` `rand` call, preserves `M[0]` and `M[14]`, outputs a cut weight
`≥ 5` on every branch, and hits `5` with probability at least `2 / 6`. -/
theorem kargerSingleTrial_triangle :
    ∃ p : Program 16,
      let input := 3 :: flattenMatrix triangleW
      HaltsWithin 16 p (init input) 435 ∧
      RandCallsBounded 16 p (init input) 435 1 ∧
      (∀ cfg ∈ (evalRand 16 p 435 (init input)).support,
        ∃ (reg : Fin 16 → ℕ) (mem : ℕ → ℕ) (C : Finset (Fin 3)),
          cfg = .halted (cutWeight triangleW C) reg mem ∧
          5 ≤ cutWeight triangleW C ∧
          mem 0 = 10 ∧ mem 1 = 3 ∧ mem 14 = 0) ∧
      (2 : ENNReal) / 6 ≤
        (evalRand 16 p 435 (init input)).toOuterMeasure
          {cfg | ∃ reg mem, cfg = .halted 5 reg mem} := by
  obtain ⟨p, hp⟩ := kargerSingleTrial
  have hw : 3 * (Nat.log 2 3 + 1) ≤ 16 := by decide
  have htot : totalDoubledWeight triangleW < 2 ^ 16 := by decide
  obtain ⟨hHalts, hCalls, hPost, hProb⟩ := hp 3 16 triangleW (by decide) isMultigraph_triangleW
    hw htot
  rw [minCut_triangleW] at hPost hProb
  have hT : 42 * 3 ^ 2 + 12 * 3 + 21 = 435 := by decide
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · simpa [hT] using hHalts
  · simpa [hT] using hCalls
  · intro cfg hcfg
    rw [← hT] at hcfg
    obtain ⟨reg, mem, C, rfl, -, -, -, hge, hframe⟩ := hPost cfg hcfg
    have hm0 : mem 0 = 10 := (hframe 0 (Or.inl (by decide))).trans (by decide)
    have hm1 : mem 1 = 3 := (hframe 1 (Or.inl (by decide))).trans (by decide)
    have hm14 : mem 14 = 0 := (hframe 14 (Or.inr (by decide))).trans (by decide)
    exact ⟨reg, mem, C, rfl, hge, hm0, hm1, hm14⟩
  · simpa [hT] using hProb (by decide)

/-- Weighted 4-vertex barbell: heavy edges `{0, 1}` and `{2, 3}` of weight `10` connected by two
bridge edges `{1, 2}` and `{0, 3}` of weight `1` (`minCut = 2` achieved strictly by `{0, 1}`). -/
def barbellW : Fin 4 → Fin 4 → ℕ
  | 0, 1 | 1, 0 => 10
  | 2, 3 | 3, 2 => 10
  | 1, 2 | 2, 1 => 1
  | 0, 3 | 3, 0 => 1
  | _, _ => 0

theorem isMultigraph_barbellW : IsMultigraph barbellW := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · fin_cases u <;> fin_cases v <;> rfl
  · fin_cases u <;> rfl

theorem minCut_barbellW : minCut barbellW = 2 := by
  have hnt0 : IsNonTrivialCut ({(0 : Fin 4), 1} : Finset (Fin 4)) := by
    rw [isNonTrivialCut_iff_card]
    decide
  have hcw0 : cutWeight barbellW ({(0 : Fin 4), 1} : Finset (Fin 4)) = 2 := by decide
  unfold minCut
  apply le_antisymm
  · exact Nat.sInf_le ⟨{(0 : Fin 4), 1}, hnt0, hcw0⟩
  · obtain ⟨C, hC, hcw⟩ :=
      Nat.sInf_mem (s := {k | ∃ C : Finset (Fin 4), IsNonTrivialCut C ∧ cutWeight barbellW C = k})
        ⟨2, {(0 : Fin 4), 1}, hnt0, hcw0⟩
    rw [← hcw]
    clear hcw
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

/-- Non-vacuous instantiation of `kargerAmplified` (`R = 6`) and `kargerHighProb` on `barbellW`
(`n = 4, minCut = 2, w = 16`). -/
theorem kargerAmplified_and_highProb_barbell :
    (∃ p : Program 22,
      let input := 6 :: 4 :: flattenMatrix barbellW
      HaltsWithin 16 p (init input) 5284 ∧
      RandCallsBounded 16 p (init input) 5284 12 ∧
      (∀ cfg ∈ (evalRand 16 p 5284 (init input)).support,
        ∃ reg mem C, cfg = .halted (cutWeight barbellW C) reg mem ∧ mem 4 = 10) ∧
      (evalRand 16 p 5284 (init input)).toOuterMeasure
          {cfg | ∀ reg mem, cfg ≠ .halted 2 reg mem} ≤
        ((1 : ENNReal) - (2 : ENNReal) / 12) ^ 6) ∧
    (∃ q : Program 22,
      let input := 4 :: flattenMatrix barbellW
      HaltsWithin 16 q (init input) 33792 ∧
      RandCallsBounded 16 q (init input) 33792 48 ∧
      (evalRand 16 q 33792 (init input)).toOuterMeasure
          {cfg | ∀ reg mem, cfg ≠ .halted 2 reg mem} ≤
        (1 : ENNReal) / 8) := by
  have hw : 3 * (Nat.log 2 4 + 1) ≤ 16 := by decide
  have htot : totalDoubledWeight barbellW < 2 ^ 16 := by decide
  constructor
  · obtain ⟨p, hp⟩ := kargerAmplified
    obtain ⟨hH, hC, hP, hF⟩ := hp 6 4 16 barbellW (by decide) (by decide) isMultigraph_barbellW
      hw (by decide) htot
    rw [minCut_barbellW] at hF
    have hT : 6 * (50 * 4 ^ 2 + 12 * 4 + 30) + 16 = 5284 := by decide
    refine ⟨p, by simpa [hT] using hH, by simpa [hT] using hC, fun cfg hcfg => ?_,
      by simpa [hT] using hF (by decide)⟩
    rw [← hT] at hcfg
    obtain ⟨reg, mem, C, rfl, -, -, -, -, hframe⟩ := hP cfg hcfg
    have hm4 : mem 4 = 10 := (hframe 4 (Or.inl (by decide))).trans (by decide)
    exact ⟨reg, mem, C, rfl, hm4⟩
  · obtain ⟨q, hq⟩ := kargerHighProb
    obtain ⟨hH, hC, -, hF⟩ := hq 4 16 barbellW (by decide) isMultigraph_barbellW hw htot
    rw [minCut_barbellW] at hF
    have hF' := hF (by decide)
    have hT : 33 * 4 ^ 4 * (Nat.log 2 4 + 2) = 33792 := by decide
    have hR : (4 * (4 - 1) / 2) * (Nat.log 2 4 + 2) * (4 - 2) = 48 := by decide
    rw [hT] at hH hC hF'
    rw [hR] at hC
    rw [show ((2 * 4 : ℕ) : ENNReal) = 8 by norm_num] at hF'
    exact ⟨q, hH, hC, hF'⟩

/-- Boundary check on the zero-weight 3-vertex multigraph (`totalDoubledWeight = 0`): halts without
faulting and outputs `0` on every branch. -/
theorem kargerSingleTrial_zero :
    ∃ p : Program 16,
      let zeroW : Fin 3 → Fin 3 → ℕ := fun _ _ => 0
      let input := 3 :: flattenMatrix zeroW
      HaltsWithin 16 p (init input) 435 ∧
      (∀ cfg ∈ (evalRand 16 p 435 (init input)).support,
        ∃ reg mem, cfg = .halted 0 reg mem) := by
  obtain ⟨p, hp⟩ := kargerSingleTrial
  let zeroW : Fin 3 → Fin 3 → ℕ := fun _ _ => 0
  have hmg : IsMultigraph zeroW := ⟨fun _ _ => rfl, fun _ => rfl⟩
  obtain ⟨hH, -, hP, -⟩ := hp 3 16 zeroW (by decide) hmg (by decide) (by decide)
  have hT : 42 * 3 ^ 2 + 12 * 3 + 21 = 435 := by decide
  refine ⟨p, by simpa [hT] using hH, fun cfg hcfg => ?_⟩
  rw [← hT] at hcfg
  obtain ⟨reg, mem, C, rfl, -⟩ := hP cfg hcfg
  have hcw : cutWeight zeroW C = 0 := by simp [cutWeight, zeroW]
  exact ⟨reg, mem, by rw [hcw]⟩

end ComplexityTests.Abstracts.KargerMinCutTests
