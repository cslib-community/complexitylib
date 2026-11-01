/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Hierarchy.WordRAM
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# Word-RAM time classes and their hierarchy

A two-instruction program puts `Set.univ` in constant word-RAM time. The two simulations and the
hierarchy are instantiated at the quadratic bound `(n + 1) ^ 2`: quadratic word-RAM time over
`Basis.additive` is strictly contained in word-RAM time `(n + 1) ^ 10`.
-/

namespace ComplexityTests.WordRAMTimeHierarchy

open Cslib Cslib.WordRAM Cslib.Complexity Turing.MultiTapeTM

/-! ## A member of a word-RAM time class -/

/-- Write `1` and return it. -/
def acceptProgram : Program .additive 1 := [.op (.const 0 1), .halt 0]

/-- **`Set.univ` is in constant word-RAM time**, by a two-instruction program. -/
example : (Set.univ : Set (List Bool)) ∈ RAMTIME .additive encBits fun _ => 1 := by
  refine ⟨2, 1, Nat.one_pos, 1, acceptProgram, fun l w hw _ => ?_⟩
  have hw1 : 1 ≤ w := le_trans (by simp [logWidth]) hw
  have h1 : Fits w 1 := fits_iff.mpr (Nat.one_lt_two_pow (by omega))
  refine ⟨1, 2, ?_, by norm_num, le_rfl, by simp⟩
  refine .of_run (fuel := 2) ?_
  simp [run, Cslib.WordRAM.step, WordSizeDependentProgram.const, acceptProgram, Op.eval,
    State.init, Data.put, h1]

/-! ## The two simulations at a quadratic bound -/

/-- Quadratic word-RAM time over `Basis.additive` is in deterministic time
`O((n + (n + 1) ^ 2 + 1) ^ 4 * (log n + 1) ^ 3)`. -/
example : RAMTIME .additive encBits (fun n => (n + 1) ^ 2) ⊆
    DTIME encBits fun n => (n + (n + 1) ^ 2 + 1) ^ 4 * (Nat.size n + 1) ^ 3 :=
  RAMTIME_additive_subset_DTIME timeConstructible_succ_sq

/-- Deterministic time `(n + 1) ^ 10` is in word-RAM time `(n + 1) ^ 10` over `Basis.additive`. -/
example : DTIME encBits (fun n => (n + 1) ^ 10) ⊆ RAMTIME .additive encBits fun n => (n + 1) ^ 10 :=
  DTIME_subset_RAMTIME_additive (by fun_prop)

/-! ## The hierarchy at a quadratic bound -/

/-- **Some problem is decided in word-RAM time `((n + 1) ^ 2) ^ 5` and not in quadratic word-RAM
time**, over `Basis.additive`. -/
example : ∃ A : Set (List Bool), A ∈ RAMTIME .additive encBits (fun n => ((n + 1) ^ 2) ^ 5) ∧
    A ∉ RAMTIME .additive encBits fun n => (n + 1) ^ 2 :=
  exists_mem_RAMTIME_pow_five_notMem_RAMTIME timeConstructible_succ_sq (fun n => by nlinarith)
    (by fun_prop)

/-- **Quadratic word-RAM time is strictly contained in word-RAM time `((n + 1) ^ 2) ^ 5`**, over
`Basis.additive`. -/
example : RAMTIME .additive encBits (fun n => (n + 1) ^ 2) ⊂
    RAMTIME .additive encBits fun n => ((n + 1) ^ 2) ^ 5 :=
  RAMTIME_ssubset_RAMTIME_pow_five timeConstructible_succ_sq (fun n => by nlinarith) (by fun_prop)

/-- The separating problem is decided over every basis containing `Basis.additive`, such as
`Basis.standard`. -/
example : ∃ A : Set (List Bool), A ∈ RAMTIME .standard encBits (fun n => ((n + 1) ^ 2) ^ 5) ∧
    A ∉ RAMTIME .additive encBits fun n => (n + 1) ^ 2 := by
  obtain ⟨A, hA, hA'⟩ := exists_mem_RAMTIME_pow_five_notMem_RAMTIME timeConstructible_succ_sq
    (fun n => by nlinarith) (by fun_prop)
  exact ⟨A, RAMTIME_subset_of_hom Basis.additiveHomStandard hA, hA'⟩

end ComplexityTests.WordRAMTimeHierarchy
