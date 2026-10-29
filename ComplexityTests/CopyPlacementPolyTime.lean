/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.LinearAlgebra.CopyPlacement
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Concrete and polynomial-time composition tests for `CopyPlacement`

Exercises `fiberRanks`, `flatPlacement`, `varGroupList`, `pullbackMeasurementMatrix`,
`restrictGroupColumns`, and `pullbackReplacementRow` on concrete colliding-label and
repeated-variable instances, non-vacuous group-separation kernel witnesses, and `fun_prop`
polynomial-time pipelines.
-/

namespace ComplexityTests.CopyPlacementPolyTime

open Cslib.LinearAlgebra.CopyPlacement Turing.MultiTapeTM

/-! ### 1. Colliding block labels: `fiberRanks` and `flatPlacement` -/

example :
    fiberRanks [] = [] ∧
      flatPlacement 4 [] = [] ∧
      fiberRanks [2, 0, 2, 1, 2] = [0, 0, 1, 0, 2] ∧
      ((fiberRanks [2, 0, 2, 1, 2]).zip [2, 0, 2, 1, 2]).Nodup ∧
      (∀ c ∈ fiberRanks [2, 0, 2, 1, 2], c < 3) ∧
      flatPlacement 4 [2, 0, 2, 1, 2] = [2, 0, 6, 1, 10] ∧
      (flatPlacement 4 [2, 0, 2, 1, 2]).Nodup ∧
      (∀ e : Fin 5, (fiberRanks [2, 0, 2, 1, 2])[e.1] =
        Cslib.LinearAlgebra.fiberRank (fun i : Fin 5 => [2, 0, 2, 1, 2][i]) e) :=
  ⟨rfl, rfl, rfl, by decide, by decide, rfl, by decide,
    fun e => getElem_fiberRanks_eq_fiberRank [2, 0, 2, 1, 2] e⟩

/-! ### 2. Concrete 4-variable, 6-incidence instance (`D = 4, h = 2, R = 2, d_den = 2`) -/

private def testSchedules : List (List ℕ) := [[0, 1], [1, 0], [0, 0], [1, 1]]
private def testLabels : List ℕ := [0, 1, 2, 3, 0, 1]
private def testPlacements : List (ℕ × ℕ) := (fiberRanks testLabels).zip testLabels
private def testIncVars : List ℕ := [0, 0, 1, 3, 2, 0]
private def testBlockMeas : List (List ℤ) := [[1, 1, 1, -1]]
private def testBlockRepl : List (List (List ℤ)) :=
  [ [[2, 3], [0, 5], [0, 1], [0, -1]], [[0, 0], [2, 0], [0, 0], [0, 0]],
    [[0, 0], [0, 0], [2, -1], [0, 1]], [[0, 0], [0, 0], [0, 1], [2, -1]] ]

-- Variable-group partition at steps `t = 0` and `t = 1`.
example :
    varGroupList testSchedules 0 0 = [0, 2] ∧
      varGroupList testSchedules 0 1 = [1, 3] ∧
      varGroupList testSchedules 1 0 = [1, 2] ∧
      varGroupList testSchedules 1 1 = [0, 3] ∧
      (∀ (t g : Fin 2) (v : Fin 4), v.1 ∈ varGroupList testSchedules t.1 g.1 ↔
        v ∈ Cslib.LinearAlgebra.varGroup
          (fun (v : Fin 4) (t : Fin 2) =>
            ⟨(testSchedules.getD v.1 []).getD t.1 0, by revert v t; decide⟩) t g) :=
  ⟨rfl, rfl, rfl, rfl,
    fun t g v => mem_varGroupList_iff_mem_varGroup (n := 4) (Q := 2) (r := 2)
      (varSchedules := testSchedules) rfl (fun _ _ => rfl) t g v⟩

-- Copy 0 has variable 0 twice (`y = 0` and `y = 1`), giving entry `2` with row `ℓ₁ ≤ 4`.
example :
    testPlacements = [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1)] ∧
      pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas =
        [[2, 1, 0, -1], [1, 0, 1, 0]] ∧
      Cslib.IsTableShape 2 4
        (pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas) ∧
      (∀ row ∈ pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas,
        (row.map Int.natAbs).sum ≤ 4) ∧
      restrictGroupColumns (varGroupList testSchedules 0 1)
        (pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas) =
        [[1, -1], [0, 0]] :=
  ⟨rfl, rfl,
    isTableShape_pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas,
    by decide, rfl⟩

-- Exhaustive check of Boolean inner-product bound `[-4, 4]` across all `2^4 = 16` Boolean vectors,
-- dot-product pullback agreement with `copyEmbedExec`, and `T = 0` restoration (`Cslib.rowEntry`),
-- `IsTableShape`, and `Cslib.jetL1Norm` preservation.
private def sampleVec : ℕ → ℤ | 0 => 3 | 1 => -2 | 2 => 7 | 3 => 4 | _ => 0

example :
    (List.range 16).all (fun mask =>
        let x : ℕ → ℤ := fun v => if Nat.testBit mask v then 1 else 0
        (pullbackMeasurementMatrix 4 2 testPlacements testIncVars testBlockMeas).all fun row =>
          decide (|(List.zipWith (· * ·) row ((List.range 4).map x)).sum| ≤ 4)) = true ∧
      (List.zipWith (· * ·) (pullbackMeasurementRow 4 testPlacements testIncVars 0 [1, 1, 1, -1])
        ((List.range 4).map sampleVec)).sum =
      (List.zipWith (· * ·) [1, 1, 1, -1]
        ((List.range 4).map (copyEmbedExec testPlacements testIncVars sampleVec 0))).sum ∧
      pullbackReplacementRow 4 2 testPlacements testIncVars 0 testBlockRepl =
        [[2, 8], [0, 1], [0, 0], [0, -1]] ∧
      Cslib.IsTableShape 4 2
        (pullbackReplacementRow 4 2 testPlacements testIncVars 0 testBlockRepl) ∧
      Cslib.jetL1Norm (pullbackReplacementRow 4 2 testPlacements testIncVars 0 testBlockRepl) ≤
        Cslib.jetL1Norm (testBlockRepl.getD 0 []) ∧
      (List.range 6).all (fun e =>
        let row := pullbackReplacementRow 4 2 testPlacements testIncVars e testBlockRepl
        (List.range 4).all fun v =>
          decide (Cslib.rowEntry row v 0 = if v = testIncVars.getD e 0 then 2 else 0)) = true :=
  ⟨by decide, by decide, rfl,
    isTableShape_pullbackReplacementRow 4 2 testPlacements testIncVars 0 testBlockRepl,
    by decide, by decide⟩

-- Non-vacuous group-separation kernel transfer (`testKerVec 1 = 5 ≠ 0`, annihilated at `T = 1`).
private def testKerVec : ℕ → ℤ | 1 => 5 | 3 => 5 | _ => 0

example :
    (∃ v < 4, testKerVec v ≠ 0) ∧
      copyEmbedExec testPlacements testIncVars testKerVec 0 2 = 5 :=
  ⟨⟨1, by decide, by decide⟩, by decide⟩

example :
    (∑ v ∈ Finset.range 4, Polynomial.evalCoeffList (1 : ℤ)
        (((pullbackReplacementRow 4 2 testPlacements testIncVars 0 testBlockRepl).getD v []).map
          Int.cast) * testKerVec v) = 0 := by
  have hsupp : ∀ v < 4, v ∉ varGroupList testSchedules 0 1 → testKerVec v = 0 := fun v _ hnot => by
    rcases v with _ | _ | _ | _ | v <;> first | rfl | exact absurd (by decide) hnot
  apply sum_evalCoeffList_pullbackReplacementRow_eq_zero_of_kernel
    (h := 2) (D := 4) (groupVars := varGroupList testSchedules 0 1) (blockMeas := testBlockMeas)
    (badY := fun y => y < 2) (nodup_varGroupList testSchedules 0 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) hsupp (by decide)
  · intro y _ hy_lt
    apply copyEmbedExec_eq_zero_of_ne_group (varSchedules := testSchedules) (t := 0) (g := 1)
      (labelGroup := 0) (by decide) hsupp _ (by decide)
    intro e he hp; change e < 6 at he; have := hy_lt; revert hp
    rcases e with _ | _ | _ | _ | _ | _ | e <;> rcases y with _ | _ | y <;> first | decide | omega
  · intro η hmeas havoid
    have hrow := hmeas [1, 1, 1, -1] (List.mem_singleton.mpr rfl)
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Int.cast_id] at hrow ⊢
    change 0 + 1 * η 0 + 1 * η 1 + 1 * η 2 + (-1) * η 3 = 0 at hrow
    have h0 := havoid 0 (by decide) (by decide); have h1 := havoid 1 (by decide) (by decide)
    change 0 + 5 * η 0 + 5 * η 1 + 1 * η 2 + (-1) * η 3 = 0; omega

/-! ### 3. Compositional `ComputableInPolyTime` checks (`by fun_prop`) -/

section PolyTimeComposition

variable {Input : Type} (encIn : Input ↪ List Bool)
  (n h R : Input → ℕ) (labels incVars : Input → List ℕ)
  (scheds : Input → List (List ℕ)) (t g e : Input → ℕ)
  (blockMeas : Input → List (List ℤ)) (blockRepl : Input → List (List (List ℤ)))
  (hn : ComputableInPolyTime n encIn encUnary) (hh : ComputableInPolyTime h encIn encUnary)
  (hR : ComputableInPolyTime R encIn encUnary)
  (hlabels : ComputableInPolyTime labels encIn (encList encNat))
  (hinc : ComputableInPolyTime incVars encIn (encList encNat))
  (hscheds : ComputableInPolyTime scheds encIn (encList (encList encNat)))
  (ht : ComputableInPolyTime t encIn encNat) (hg : ComputableInPolyTime g encIn encNat)
  (he : ComputableInPolyTime e encIn encNat)
  (hmeas : ComputableInPolyTime blockMeas encIn (encList (encList encIntBin)))
  (hrepl : ComputableInPolyTime blockRepl encIn (encList (encList (encList encIntBin))))

-- End-to-end group-restricted measurement matrix `C_{t,g}` from raw labels, schedules, and `C^B`.
example : ComputableInPolyTime
    (fun x => restrictGroupColumns (varGroupList (scheds x) (t x) (g x))
      (pullbackMeasurementMatrix (n x) (h x) ((fiberRanks (labels x)).zip (labels x))
        (incVars x) (blockMeas x)))
    encIn (encList (encList encIntBin)) := by
  fail_if_success (clear hn; fun_prop)
  fail_if_success (clear hh; fun_prop)
  fail_if_success (clear hlabels; fun_prop)
  fun_prop

-- End-to-end pulled-back cleared replacement row from raw labels and `blockRepl`.
example : ComputableInPolyTime
    (fun x => pullbackReplacementRow (n x) (R x) ((fiberRanks (labels x)).zip (labels x))
      (incVars x) (e x) (blockRepl x))
    encIn (encList (encList encIntBin)) := by
  fail_if_success (clear hn; fun_prop)
  fail_if_success (clear hR; fun_prop)
  fail_if_success (clear hrepl; fun_prop)
  fun_prop

end PolyTimeComposition

end ComplexityTests.CopyPlacementPolyTime
