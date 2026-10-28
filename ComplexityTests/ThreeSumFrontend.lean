/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.ThreeSum.ThreeSets
import Complexity.Algorithms.ThreeSum.ArrayPacking

/-!
# Distinct-position preprocessing and three-array packing regressions

These examples check multiplicities, finite frontend enumeration and array tags. They assert no
machine running time for the frontend.
-/

namespace ComplexityTests.ThreeSumFrontend

open Cslib.Algorithms.ThreeSum
open Finset

private def repeated (i : Fin 3) : ℤ := if i = 0 then -2 else 1

/-- Three different positions may contain repeated values. -/
example : HasSolution repeated := by unfold HasSolution; decide

/-- Two zeros are insufficient, whereas three zeros solve distinct-position 3SUM. -/
example : ¬HasSolution (fun _ : Fin 2 => (0 : ℤ)) ∧
    HasSolution (fun _ : Fin 3 => (0 : ℤ)) := by simp only [HasSolution]; decide

/-- A single occurrence of 1 cannot be reused to manufacture the solution `1 + 1 - 2 = 0`. -/
example : ¬HasSolution (fun i : Fin 2 => if i = 0 then (-2 : ℤ) else 1) := by
  unfold HasSolution
  decide

/-- The repeated-value branch retains the multiplicity needed for two ones. -/
example : twiceSet repeated = {2} ∧ zeroSet repeated = ∅ := by decide

/-- The dedicated zero branch distinguishes two and three occurrences of zero. -/
example : zeroSet (fun _ : Fin 2 => (0 : ℤ)) = ∅ ∧
    zeroSet (fun _ : Fin 3 => (0 : ℤ)) = {0} := by decide

/-- On this input the frontend list has 34 entries, including the repeated-value instance. -/
example : (inputs 2 repeated).length = 34 ∧
    ({2}, {0}, {-2, 1}) ∈ inputs 2 repeated := by decide

/-- The public frontend theorem supplies a real bounded yes-instance for a repeated-value input. -/
example : ∃ T ∈ inputs 2 repeated, HasThreeSetSolution T.1 T.2.1 T.2.2 ∧
    #T.1 ≤ 3 ∧ #T.2.1 ≤ 3 ∧ #T.2.2 ≤ 3 ∧
      Bdd 4 T.1 ∧ Bdd 4 T.2.1 ∧ Bdd 4 T.2.2 := by
  have hx : ∀ i, |repeated i| ≤ (2 : ℤ) := by
    intro i
    unfold repeated
    split_ifs <;> decide
  obtain ⟨T, hT, hs⟩ := (threeSum_iff_exists_mem_inputs hx).mp
    (by unfold HasSolution; decide : HasSolution repeated)
  exact ⟨T, hT, hs, (mem_inputs_iff.mp hT).bounds (by decide) hx⟩

/-- The binary-digit branch separates three distinct values without manufacturing multiplicities. -/
example : ∃ T₁ T₂ T₃, IsInput 1 (fun i : Fin 3 => (i.val : ℤ) - 1) T₁ T₂ T₃ ∧
    HasThreeSetSolution T₁ T₂ T₃ := by
  apply (threeSum_iff_exists_input (U := 1) ?_).mp (by unfold HasSolution; decide)
  intro i
  have hi := i.isLt
  rw [abs_le]
  constructor <;> omega

/-- Tagging preserves an actual solution at positions `4i+1`, `4j+2`, `4(i+j)+3`. -/
example : oneArray 3 (fun _ => -2) (fun _ => 3) (fun _ => 1) 1 = 8 ∧
    oneArray 3 (fun _ => -2) (fun _ => 3) (fun _ => 1) 2 = 33 ∧
    oneArray 3 (fun _ => -2) (fun _ => 3) (fun _ => 1) 3 = 41 := by decide

/-- The packed array is a nonvacuous client of both correctness and magnitude bounds. -/
example : Convolution 4 (oneArray 3 (fun _ => -2) (fun _ => 3) (fun _ => 1)) ∧
    ∀ u < 4, |oneArray 3 (fun _ => -2) (fun _ => 3) (fun _ => 1) u| ≤ (100 : ℤ) := by
  constructor
  · exact oneArray_correct (N := 1) (by intros; decide) (by intros; decide)
      (by intros; decide) |>.mp ⟨0, 0, by decide, by decide⟩
  · intro u hu
    exact abs_oneArray_le (N := 1) (by intros; decide) (by intros; decide) (by intros; decide) hu

/-- When all three arrays are 1, the tags create no false solution; empty arrays also stay empty. -/
example : ¬Convolution 4 (oneArray 1 (fun _ => 1) (fun _ => 1) (fun _ => 1)) ∧
    ¬Convolution 0 (oneArray 0 (fun _ => 0) (fun _ => 0) (fun _ => 0)) := by
  constructor
  · intro h
    obtain ⟨i, j, _, he⟩ := (oneArray_correct (N := 1)
      (by intros; decide) (by intros; decide) (by intros; decide)).mpr h
    exact (by decide : (1 : ℤ) + 1 ≠ 1) he
  · rintro ⟨i, j, h, _⟩
    omega

end ComplexityTests.ThreeSumFrontend
