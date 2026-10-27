/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Init
public import Complexity.Foundations.LinearAlgebra.VariableCopyPlacement

/-!
# Tests for variable copy placement and coefficient norm bounds

Concrete nonvacuity tests for `Complexity.Foundations.LinearAlgebra.VariableCopyPlacement`
on a multi-incidence system where `Q = 2, r = 2, A₀ = 0, R = 2, h = 2, n = 2`, a label repeats
with multiplicity `2`, and the same variable appears at multiple incidences within the same copy.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.VariableCopyPlacementTests

open Cslib.LinearAlgebra Finset Matrix Polynomial

/-- Auxiliary label `(0, 0)` in `AuxLabel 2 2`. -/
def u00 : AuxLabel 2 2 := (fun _ => 0, fun _ => 0)

/-- Auxiliary label `(1, 1)` in `AuxLabel 2 2`. -/
def u11 : AuxLabel 2 2 := (fun _ => 1, fun _ => 1)

/-- Concrete 3-incidence label map `Fin 3 → AuxLabel 2 2` where `u00` has fiber size `2 ≤ h = 2`
and `u11` has fiber size `1 ≤ h = 2`. -/
def testLabel : Fin 3 → AuxLabel 2 2
  | ⟨0, _⟩ => u00
  | ⟨1, _⟩ => u00
  | ⟨2, _⟩ => u11

/-- Variable projection `Fin 3 → Fin 2` where incidences `0` and `2` share variable `0`. -/
def testVarOf : Fin 3 → Fin 2
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Variable assignment `a : Fin 2 → Fin 2 → Fin 2` compatible with `testLabel`:
`(testLabel e).1 = testVarA (testVarOf e)` would hold if `u00.1 = u11.1`; here we also define a
label map with matching `a`-part for testing `evalVarReplacementRow_nodePoint_eq_zero_of_kernel`. -/
def u01 : AuxLabel 2 2 := (fun _ => 0, fun _ => 1)

def compatLabel : Fin 3 → AuxLabel 2 2
  | ⟨0, _⟩ => u00
  | ⟨1, _⟩ => u00
  | ⟨2, _⟩ => u01

def compatVarA : Fin 2 → Fin 2 → Fin 2 := fun _ _ => 0

theorem testLabel_fiber_le (y : AuxLabel 2 2) :
    #{e : Fin 3 | testLabel e = y} ≤ 2 := by
  by_cases hy0 : u00 = y
  · subst hy0
    decide
  · by_cases hy1 : u11 = y
    · subst hy1
      decide
    · have hEmpty : (univ.filter fun e : Fin 3 => testLabel e = y) = ∅ := by
        ext e
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        fin_cases e
        · exact hy0
        · exact hy0
        · exact hy1
      simp [hEmpty]

theorem compatLabel_fiber_le (y : AuxLabel 2 2) :
    #{e : Fin 3 | compatLabel e = y} ≤ 2 := by
  by_cases hy0 : u00 = y
  · subst hy0
    decide
  · by_cases hy1 : u01 = y
    · subst hy1
      decide
    · have hEmpty : (univ.filter fun e : Fin 3 => compatLabel e = y) = ∅ := by
        ext e
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        fin_cases e
        · exact hy0
        · exact hy0
        · exact hy1
      simp [hEmpty]

/-- Deterministic placement into `Fin 2 × AuxLabel 2 2` via `fiberRankCopy`. -/
def testPlace (e : Fin 3) : Fin 2 × AuxLabel 2 2 :=
  (fiberRankCopy testLabel testLabel_fiber_le e, testLabel e)

def compatPlace (e : Fin 3) : Fin 2 × AuxLabel 2 2 :=
  (fiberRankCopy compatLabel compatLabel_fiber_le e, compatLabel e)

theorem injective_testPlace : Function.Injective testPlace :=
  injective_fiberRankCopy_prod testLabel testLabel_fiber_le

theorem injective_compatPlace : Function.Injective compatPlace :=
  injective_fiberRankCopy_prod compatLabel compatLabel_fiber_le

/-- Incidences `0` and `1` share the same label `u00` and are placed into distinct copies `0` and
`1`. -/
example : (testPlace 0).1 = 0 ∧ (testPlace 1).1 = 1 ∧ (testPlace 2).1 = 0 := by
  decide

/-- Compatibility `(compatPlace e).2.1 = compatVarA (testVarOf e)` for all `e : Fin 3`. -/
theorem compatPlace_fst_snd (e : Fin 3) :
    (compatPlace e).2.1 = compatVarA (testVarOf e) := by
  fin_cases e <;> rfl

/-- Degree bound and `T = 0` evaluation on `testPlace` (where incidences `0` and `2` both lie in
copy `0` and map to variable `0`). -/
example (e : Fin 3) (v : Fin 2) :
    (varReplacementRow 2 2 0 2 testPlace testVarOf e v).natDegree ≤ 1 ∧
      (varReplacementRow 2 2 0 2 testPlace testVarOf e v).eval 0 =
        if testVarOf e = v then 1 else 0 :=
  ⟨natDegree_varReplacementRow_le 2 2 0 2 testPlace testVarOf e v,
    eval_varReplacementRow_zero 2 2 0 2 injective_testPlace testVarOf e v⟩

/-- Row `ℓ₁`-norm bound `≤ 2 ^ 4 = 16` on `varMeasurementMatrix` even when multiple incidences in
copy `0` share variable `0`. -/
example (p : Fin 2 × measurementIndices 2 2 0 2) :
    (∑ v : Fin 2, |varMeasurementMatrix 2 2 0 2 ℤ testPlace testVarOf p v|) ≤ 16 :=
  sum_abs_varMeasurementMatrix_le 2 2 0 2 injective_testPlace testVarOf p

/-- Definition 3.1 kernel separation on `compatPlace`: for `e = 0` (`d_e(0) = 0`) and `g = 1 ≠ 0`,
any `ξ` supported on `varGroup compatVarA 0 1` in `ker Ĉ` is annihilated by
`evalVarReplacementRow` at `nodePoint 0`. -/
example (ξ : Fin 2 → ℚ)
    (hsupp : ∀ v, v ∉ varGroup compatVarA (0 : Fin 2) (1 : Fin 2) → ξ v = 0)
    (hker : (varMeasurementMatrix 2 2 0 2 ℚ compatPlace testVarOf).mulVec ξ = 0) :
    evalVarReplacementRow 2 2 0 2 compatPlace testVarOf 0 (nodePoint (0 : Fin 2)) ξ = 0 :=
  evalVarReplacementRow_nodePoint_eq_zero_of_kernel 2 2 0 2 compatPlace testVarOf compatVarA
    compatPlace_fst_snd 0 (0 : Fin 2) (1 : Fin 2) (by decide) ξ hsupp hker

/-- Lemma 4.6 explicit `ℓ₁`-coefficient norm bounds for `Q = 2, r = 2, A₀ = 0, R = 2`:
`commonDenom 2 2 = 2`, `1 + (1 + 2 ^ 2) * 2 * (4 * 2) ^ 1 = 81`, so the cleared row coefficient
`ℓ₁`-sum is at most `2 * 81 = 162`. -/
example (e : Fin 3) :
    polyNorm1 (mismatchAnnihilatorScaledInt u00 u11) ≤ 8 ∧
      rowNorm1 (M0ScaledInt 2 2 0 2) u00 ≤ 16 ∧
      (∑ v : Fin 2, polyNorm1 (varReplacementRowScaledInt 2 2 0 2 testPlace testVarOf e v)) ≤
        162 := by
  have hI : ∀ a < 2 - 1, 0 + a ≤ 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa using polyNorm1_mismatchAnnihilatorScaledInt_le u00 u11
  · simpa using rowNorm1_M0ScaledInt_le (by decide : 0 < 2) hI u00
  · simpa [commonDenom] using
      sum_polyNorm1_varReplacementRowScaledInt_le (by decide : 0 < 2) injective_testPlace
        testVarOf hI e

end Cslib.LinearAlgebra.VariableCopyPlacementTests
