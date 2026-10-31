/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.KargerMinCut

/-!
# Karger global minimum cut tests on the randomized word RAM

Concrete non-vacuity and behavioral tests for `Cslib.Algorithms.WordRAM.Karger`:

1. Weighted 3-vertex triangle (`W 0 1 = 3, W 1 2 = 5, W 0 2 = 2`, `minCut = 5`): exercises
   `singleProgram_spec` (`RandHaltsWithin`, `RandCallsBounded ... 1`, cut-validity on every branch,
   and success probability `≥ 2 / 6`).
2. Weighted 4-vertex imbalanced barbell (`W 0 1 = 10, W 2 3 = 10, W 1 2 = 1, W 0 3 = 1`,
   `minCut = 2` achieved strictly by the 2-vertex cut `{0, 1}` rather than any singleton degree
   `11`): exercises relocatable `contractDownTo_spec` at non-trivial workspace offset and row stride
   (`wb = 20, db = 50, str = 5, k = 4, t = 3`), `amplifiedProgram_spec` (`R = 6`), and
   `highProbProgram_spec` / `highProbProgram_failure_le_inv_n`.
3. Disconnected and zero-weight 3-vertex multigraphs (`minCut = 0`, `totalDoubledWeight = 0`):
   verifies fault-free halting along the deterministic `totS = 0` contraction branch.
-/

@[expose] public section

namespace ComplexityTests.WordRAMKargerMinCut

open Cslib Cslib.WordRAM Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger
open scoped ENNReal

/-! ## 1. Weighted 3-vertex triangle (`minCut = 5`) -/

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
  apply le_antisymm
  · have hnt : IsNonTrivialCut ({(0 : Fin 3)} : Finset (Fin 3)) :=
      isNonTrivialCut_singleton (by decide) 0
    have hcw : cutWeight triangleW ({(0 : Fin 3)} : Finset (Fin 3)) = 5 := by decide
    exact hcw ▸ minCut_le_cutWeight triangleW hnt
  · refine (le_minCut_iff (by decide) triangleW 5).mpr fun C hC => ?_
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

theorem singleProgram_triangle :
    let input := 3 :: flattenMatrix triangleW
    RandHaltsWithin 16 singleProgram (.init input) (singleTime 3) ∧
    RandCallsBounded 16 singleProgram (.init input) (singleTime 3) 1 ∧
    (∀ cfg ∈ (runRand 16 singleProgram (singleTime 3) (.running (.init input))).support,
      ∃ (y : Data 16) (C : Finset (Fin 3)),
        cfg = .halted (cutWeight triangleW C) y ∧
        y.Bounded 16 ∧
        IsNonTrivialCut C ∧
        5 ≤ cutWeight triangleW C) ∧
    (2 : ℝ≥0∞) / 6 ≤
      (evalRand 16 singleProgram (singleTime 3) (.init input)).toOuterMeasure
        {cfg | ∃ y, cfg = .halted 5 y} := by
  intro input
  have hw : logWidth 3 3 ≤ 16 := by decide
  have htot : Fits 16 (totalDoubledWeight triangleW) := by decide
  obtain ⟨hHalts, hCalls, hPost, hProb⟩ :=
    singleProgram_spec (by decide : 2 ≤ 3) isMultigraph_triangleW hw htot
  rw [minCut_triangleW] at hPost hProb
  refine ⟨hHalts, hCalls, fun cfg hcfg => ?_, ?_⟩
  · obtain ⟨y, C, hcfg_eq, hbnd, hC, hge, -⟩ := hPost cfg hcfg
    exact ⟨y, C, hcfg_eq, hbnd, hC, hge⟩
  · simpa using hProb (by decide)

/-! ## 2. Weighted 4-vertex barbell (`minCut = 2 < 11 = rowDeg`) and relocatable `contractDownTo` -/

/-- Weighted 4-vertex barbell: heavy edges `{0, 1}` and `{2, 3}` of weight `10` connected by two
light bridge edges `{1, 2}` and `{0, 3}` of weight `1`. Every singleton cut has weight `11`, whereas
the 2-vertex cut `{0, 1}` achieves `minCut = 2`. -/
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
  apply le_antisymm
  · have hnt : IsNonTrivialCut ({(0 : Fin 4), 1} : Finset (Fin 4)) := by
      rw [isNonTrivialCut_iff_card]
      decide
    have hcw : cutWeight barbellW ({(0 : Fin 4), 1} : Finset (Fin 4)) = 2 := by decide
    exact hcw ▸ minCut_le_cutWeight barbellW hnt
  · refine (le_minCut_iff (by decide) barbellW 2).mpr fun C hC => ?_
    rw [isNonTrivialCut_iff_card] at hC
    revert C hC
    decide

/-- Concrete machine state placing `barbellW` at relocated addresses `wb = 20`, `db = 50` with
non-unit-slack row stride `str = 5` (`k = 4, t = 3`), testing the workspace-relocatable interface
consumed by Karger–Stein (`FastCut`). -/
def barbellRelocState : Data 16 where
  regs r :=
    if r = Reg.wBase then 20
    else if r = Reg.dBase then 50
    else if r = Reg.stride then 5
    else if r = Reg.activeK then 4
    else if r = Reg.targetT then 3
    else if r = Reg.totS then totalDoubledWeight barbellW
    else 0
  mem a :=
    if h1 : 20 ≤ a ∧ a < 40 ∧ (a - 20) % 5 < 4 then
      barbellW ⟨(a - 20) / 5, by omega⟩ ⟨(a - 20) % 5, h1.2.2⟩
    else if h2 : 50 ≤ a ∧ a < 54 then
      rowDeg barbellW ⟨a - 50, by omega⟩
    else 0

theorem contractState_barbellReloc :
    ContractState 16 20 50 5 4 3 barbellW barbellRelocState := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, Or.inl (by decide),
    by decide, by decide, by decide, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> rfl

/-- Partial contraction (`k = 4 → t = 3`) on `barbellRelocState` uses at most `1` `rand` call,
modifies only `[20, 40) ∪ [50, 54)`, and preserves the unique minimum cut `{0, 1}` with probability
at least `(3 * 2) / (4 * 3) = 6 / 12`. -/
theorem contractDownTo_barbell_partial :
    ∃ m : ProbComp (Data 16 × ℕ),
      ExecRand 16 contractDownTo barbellRelocState m ∧
      m.IsQueryBounded 1 ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * (4 ^ 2 - 3 ^ 2) + 4 ∧
        Modifies (workspaceFootprint 20 50 5 4) barbellRelocState.mem z.1.mem) ∧
      (6 : ℝ≥0∞) / 12 ≤
        m.eval.toOuterMeasure
          {z | SurvivalPost barbellW 20 50 5 3 ({(0 : Fin 4), 1} : Finset (Fin 4)) z.1} := by
  obtain ⟨m, hm, hq, hsup, hsurv⟩ :=
    contractDownTo_spec (by decide : 2 ≤ 3) (by decide : 3 ≤ 4)
      (isContractionOf_id isMultigraph_barbellW) contractState_barbellReloc
  refine ⟨m, hm, hq, fun z hz => ⟨(hsup z hz).1, (hsup z hz).2.1⟩, ?_⟩
  let C_star : Finset (Fin 4) := {0, 1}
  have hpb : pullbackCut (id : Fin 4 → Fin 4) C_star = C_star := by
    ext u
    simp [pullbackCut]
  have hpos : 0 < minCut barbellW := by rw [minCut_barbellW]; decide
  have hnt : IsNonTrivialCut C_star := by
    rw [isNonTrivialCut_iff_card]
    decide
  have hcw : cutWeight barbellW C_star = minCut barbellW := by
    rw [minCut_barbellW]
    decide
  have hbound := hsurv C_star hpos hnt (by rw [hpb, hcw])
  rw [hpb] at hbound
  simpa using hbound

theorem amplifiedProgram_barbell :
    let input := 6 :: 4 :: flattenMatrix barbellW
    RandHaltsWithin 16 amplifiedProgram (.init input) (amplifiedTime 6 4) ∧
    RandCallsBounded 16 amplifiedProgram (.init input) (amplifiedTime 6 4) 12 ∧
    (evalRand 16 amplifiedProgram (amplifiedTime 6 4) (.init input)).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted 2 y} ≤
      ((1 : ℝ≥0∞) - (2 : ℝ≥0∞) / 12) ^ 6 := by
  intro input
  have hw : logWidth 3 4 ≤ 16 := by decide
  have hR_fit : Fits 16 6 := by decide
  have htot : Fits 16 (totalDoubledWeight barbellW) := by decide
  obtain ⟨hHalts, hCalls, -, hFail⟩ :=
    amplifiedProgram_spec (by decide : 1 ≤ 6) (by decide : 2 ≤ 4)
      isMultigraph_barbellW hw hR_fit htot
  rw [minCut_barbellW] at hFail
  exact ⟨hHalts, hCalls, by simpa using hFail (by decide)⟩

theorem highProbProgram_barbell :
    let input := 4 :: flattenMatrix barbellW
    RandHaltsWithin 16 highProbProgram (.init input) (highProbTime 4) ∧
    (evalRand 16 highProbProgram (highProbTime 4) (.init input)).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted 2 y} ≤
      (1 : ℝ≥0∞) / 8 ∧
    (evalRand 16 highProbProgram (highProbTime 4) (.init input)).toOuterMeasure
        {cfg | ∀ y, cfg ≠ .halted 2 y} ≤
      (1 : ℝ≥0∞) / 4 := by
  intro input
  have hw : logWidth 3 4 ≤ 16 := by decide
  have htot : Fits 16 (totalDoubledWeight barbellW) := by decide
  obtain ⟨hHalts, -, -, hFail⟩ :=
    highProbProgram_spec (by decide : 2 ≤ 4) isMultigraph_barbellW hw htot
  have hInv := highProbProgram_failure_le_inv_n (by decide : 2 ≤ 4) isMultigraph_barbellW hw htot
    (by rw [minCut_barbellW]; decide)
  rw [minCut_barbellW] at hFail hInv
  exact ⟨hHalts, by simpa using hFail (by decide), by simpa using hInv⟩

/-! ## 3. Disconnected and zero-weight multigraphs (`minCut = 0`, deterministic `totS = 0` path) -/

/-- Disconnected 3-vertex multigraph: edge `{0, 1}` of weight `4` and isolated vertex `2`. -/
def disconnectedW : Fin 3 → Fin 3 → ℕ
  | 0, 1 | 1, 0 => 4
  | _, _ => 0

/-- Empty 3-vertex multigraph (`totalDoubledWeight = 0`), exercising the `totS = 0` deterministic
contraction branch with `0` `rand` calls. -/
def zero3W : Fin 3 → Fin 3 → ℕ := fun _ _ => 0

theorem isMultigraph_disconnectedW : IsMultigraph disconnectedW := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · fin_cases u <;> fin_cases v <;> rfl
  · fin_cases u <;> rfl

theorem isMultigraph_zero3W : IsMultigraph zero3W :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem minCut_disconnectedW : minCut disconnectedW = 0 := by
  apply Nat.eq_zero_of_le_zero
  have hnt : IsNonTrivialCut ({(2 : Fin 3)} : Finset (Fin 3)) :=
    isNonTrivialCut_singleton (by decide) 2
  have hcw : cutWeight disconnectedW ({(2 : Fin 3)} : Finset (Fin 3)) = 0 := by decide
  exact hcw ▸ minCut_le_cutWeight disconnectedW hnt

theorem singleProgram_disconnected_and_zero :
    RandHaltsWithin 16 singleProgram (.init (3 :: flattenMatrix disconnectedW)) (singleTime 3) ∧
    RandHaltsWithin 16 singleProgram (.init (3 :: flattenMatrix zero3W)) (singleTime 3) ∧
    (∀ cfg ∈ (runRand 16 singleProgram (singleTime 3)
        (.running (.init (3 :: flattenMatrix zero3W)))).support,
      ∃ y : Data 16, cfg = .halted 0 y) := by
  have hw : logWidth 3 3 ≤ 16 := by decide
  obtain ⟨hH1, -, -, -⟩ :=
    singleProgram_spec (by decide : 2 ≤ 3) isMultigraph_disconnectedW hw (by decide)
  obtain ⟨hH0, -, hPost0, -⟩ :=
    singleProgram_spec (by decide : 2 ≤ 3) isMultigraph_zero3W hw (by decide)
  refine ⟨hH1, hH0, fun cfg hcfg => ?_⟩
  obtain ⟨y, C, hcfg_eq, -, -, -, -⟩ := hPost0 cfg hcfg
  have hcw0 : cutWeight zero3W C = 0 := by simp [cutWeight, zero3W]
  exact ⟨y, hcw0 ▸ hcfg_eq⟩

end ComplexityTests.WordRAMKargerMinCut
