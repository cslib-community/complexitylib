/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.AWPP.Lowness
public import Complexity.Computability.Complexity.Classes.AWPP.OracleWeights

/-! # Concrete AWPP oracles and boundary cases for PP lowness -/

@[expose] public section

namespace ComplexityTests.AWPPLowness

open Cslib.Complexity Turing.MultiTapeTM

/-- The empty language has the zero GapP witness and denominator one. -/
theorem empty_mem : (∅ : Set (List Bool)) ∈ AWPP encBits := by
  refine ⟨0, GapP.zero_mem, 0, fun w => ?_⟩
  norm_num

/-- The universal language has the constant-one GapP witness and denominator one. -/
theorem univ_mem : (Set.univ : Set (List Bool)) ∈ AWPP encBits := by
  refine ⟨1, GapP.one_mem, 0, fun w => ?_⟩
  norm_num

/-- Both endpoint witnesses have actual instances. -/
example : ([] : List Bool) ∉ (∅ : Set (List Bool)) ∧
    ([] : List Bool) ∈ (Set.univ : Set (List Bool)) := by simp

example : PPWithOracle (∅ : Set (List Bool)) encBits = PP encBits :=
  PPWithOracle_eq_PP_of_mem_AWPP empty_mem encBits

example : PPWithOracle (Set.univ : Set (List Bool)) encBits = PP encBits :=
  PPWithOracle_eq_PP_of_mem_AWPP univ_mem encBits

/-- Lowness is uniform over the instance type and its injective encoding. -/
example : PPWithOracle (Set.univ : Set (List Bool)) encBool = PP encBool :=
  PPWithOracle_eq_PP_of_mem_AWPP univ_mem encBool

/-- A nonempty AWPP oracle admits weights even when every query is truncated to the empty word
and the requested error exponent is zero. Bounds still cover arbitrary replay words. -/
example : ∃ H ∈ GapP (encPair encBits encBits), ∃ R : List Bool → ℕ,
    ComputableInPolyTime R encBits encUnary ∧ ∀ a w,
      let D := (2 : ℤ) ^ R a
      (0 ≤ H (a, w) ∧ H (a, w) ≤ D) ∧ D - H (a, w) ≤ D := by
  obtain ⟨H, hH, R, hR, hb⟩ := exists_AWPP_queryWeights univ_mem
    (T := fun _ : List Bool => 0) (e := fun _ : List Bool => 0)
    (.const 0) (.const 0)
  refine ⟨H, hH, R, hR, fun a w => ⟨(hb a w).1, ?_⟩⟩
  simpa only [pow_zero, one_mul] using (hb a w).2.1 (Set.mem_univ _)

end ComplexityTests.AWPPLowness
