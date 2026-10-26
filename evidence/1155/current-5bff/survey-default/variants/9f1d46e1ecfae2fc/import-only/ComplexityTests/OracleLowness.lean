/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.Oracle.Lowness


import Diag1155.Measure
/-!
# Regression tests for `NP ∩ coNP` and `UP ∩ coUP` oracle lowness

Verifies concrete instantiations of `PWithOracle` Boolean closure, `UP ∩ coUP` lowness for `P`,
`NP ∩ coNP` lowness for `P` and `NP`, and the `Low₁ = NP ∩ coNP` characterization.
-/

@[expose] public section

namespace ComplexityTests.OracleLowness

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- Non-trivial oracle language: non-empty words whose first bit is `true`. -/
def headTrue : Set (List Bool) := {w | w.headD false = true}

theorem headTrue_mem_P : headTrue ∈ P encBits :=
  ⟨fun w => w.headD false, .of_tidy (by fun_prop), fun _ => Iff.rfl⟩

theorem headTrue_mem_UP : headTrue ∈ UP encBits :=
  P_subset_UP headTrue_mem_P

theorem headTrue_mem_coUP : headTrue ∈ coUP encBits :=
  P_subset_coUP headTrue_mem_P

theorem headTrue_mem_NP : headTrue ∈ NP encBits :=
  P_subset_NP headTrue_mem_P

theorem headTrue_mem_coNP : headTrue ∈ coNP encBits :=
  P_subset_coNP headTrue_mem_P

/-- Non-vacuity: `headTrue` distinguishes `[true]` from `[false]`. -/
example : [true] ∈ headTrue ∧ [false] ∉ headTrue := by
  simp [headTrue]

/-- Concrete instantiation: `headTrueᶜ ∈ PWithOracle headTrue encBits` via complement closure. -/
example : headTrueᶜ ∈ PWithOracle headTrue encBits :=
  mem_PWithOracle_compl_self headTrue

/-- Concrete instantiation: `NPWithOracle headTrue encBits = NP encBits`. -/
example : NPWithOracle headTrue encBits = NP encBits :=
  NPWithOracle_eq_NP_of_mem_NP_of_mem_coNP headTrue_mem_NP headTrue_mem_coNP encBits

/-- Concrete instantiation of the `Low₁` iff on `headTrue`. -/
example : NPWithOracle headTrue encBits = NP encBits :=
  NPWithOracle_eq_NP_iff.mpr ⟨headTrue_mem_NP, headTrue_mem_coNP⟩

/-- Concrete instantiation: `PWithOracle headTrue encBits ⊆ UP encBits ∩ coUP encBits`. -/
example : PWithOracle headTrue encBits ⊆ UP encBits ∩ coUP encBits :=
  PWithOracle_subset_UP_inter_coUP headTrue_mem_UP headTrue_mem_coUP

/-- Concrete instantiation: `PWithOracle headTrue encBits ⊆ NP encBits ∩ coNP encBits`. -/
example : PWithOracle headTrue encBits ⊆ NP encBits ∩ coNP encBits :=
  PWithOracle_subset_NP_inter_coNP headTrue_mem_NP headTrue_mem_coNP

end ComplexityTests.OracleLowness
