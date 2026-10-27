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
with multiplicity `2`, the same variable appears at multiple incidences within the same copy
(producing an accumulated measurement entry equal to `2`), and a nonzero off-group kernel vector
with a nonzero polynomial replacement entry is annihilated at `nodePoint 0`.
-/

@[expose] public section

namespace Cslib.LinearAlgebra.VariableCopyPlacementTests

open Cslib.LinearAlgebra Finset Matrix Polynomial

/-- Auxiliary label `((0, 0), (0, 0))` in `AuxLabel 2 2`. -/
def u00 : AuxLabel 2 2 := (fun _ => 0, fun _ => 0)

/-- Auxiliary label `((0, 0), (1, 1))` in `AuxLabel 2 2`. -/
def u01 : AuxLabel 2 2 := (fun _ => 0, fun _ => 1)

/-- Auxiliary label `((1, 1), (0, 0))` in `AuxLabel 2 2`. -/
def u10 : AuxLabel 2 2 := (fun _ => 1, fun _ => 0)

/-- Auxiliary label `((1, 1), (1, 1))` in `AuxLabel 2 2`. -/
def u11 : AuxLabel 2 2 := (fun _ => 1, fun _ => 1)

/-- Auxiliary label `((1, 0), (0, 0))` in `AuxLabel 2 2`, disagreeing with `d_{u00} = (0, 0)` at
slot `0` and agreeing at slot `1`. -/
def u10_00 : AuxLabel 2 2 :=
  (fun s => if s = 0 then 1 else 0, fun _ => 0)

/-- Concrete 3-incidence label map `Fin 3 → AuxLabel 2 2` where `u01` has fiber size `2 ≤ h = 2`
and `u10` has fiber size `1 ≤ h = 2`. -/
def testLabel : Fin 3 → AuxLabel 2 2
  | ⟨0, _⟩ => u01
  | ⟨1, _⟩ => u01
  | ⟨2, _⟩ => u10

/-- Variable projection `Fin 3 → Fin 2` where incidences `0` and `2` share variable `0`. -/
def testVarOf : Fin 3 → Fin 2
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0

/-- Variable schedule `Fin 2 → Fin 2 → Fin 2` with variable `0` in group `0` at both steps and
variable `1` in group `1` at step `0` and group `0` at step `1`. -/
def sepVarA : Fin 2 → Fin 2 → Fin 2
  | ⟨0, _⟩ => fun _ => 0
  | ⟨1, _⟩ => fun s => if s = 0 then 1 else 0

/-- Label map compatible with `sepVarA` and `testVarOf`:
`sepLabel 0 = u00`, `sepLabel 1 = u10_00`, `sepLabel 2 = u01`. -/
def sepLabel : Fin 3 → AuxLabel 2 2
  | ⟨0, _⟩ => u00
  | ⟨1, _⟩ => u10_00
  | ⟨2, _⟩ => u01

theorem testLabel_fiber_le (y : AuxLabel 2 2) :
    #{e : Fin 3 | testLabel e = y} ≤ 2 := by
  by_cases hy0 : u01 = y
  · subst hy0
    decide
  · by_cases hy1 : u10 = y
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

theorem sepLabel_fiber_le (y : AuxLabel 2 2) :
    #{e : Fin 3 | sepLabel e = y} ≤ 2 := by
  by_cases hy0 : u00 = y
  · subst hy0
    decide
  · by_cases hy1 : u10_00 = y
    · subst hy1
      decide
    · by_cases hy2 : u01 = y
      · subst hy2
        decide
      · have hEmpty : (univ.filter fun e : Fin 3 => sepLabel e = y) = ∅ := by
          ext e
          simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          fin_cases e
          · exact hy0
          · exact hy1
          · exact hy2
        simp [hEmpty]

/-- Deterministic placement into `Fin 2 × AuxLabel 2 2` via `fiberRankCopy`. -/
def testPlace (e : Fin 3) : Fin 2 × AuxLabel 2 2 :=
  (fiberRankCopy testLabel testLabel_fiber_le e, testLabel e)

def sepPlace (e : Fin 3) : Fin 2 × AuxLabel 2 2 :=
  (fiberRankCopy sepLabel sepLabel_fiber_le e, sepLabel e)

theorem injective_testPlace : Function.Injective testPlace :=
  injective_fiberRankCopy_prod testLabel testLabel_fiber_le

theorem injective_sepPlace : Function.Injective sepPlace :=
  injective_fiberRankCopy_prod sepLabel sepLabel_fiber_le

/-- Incidences `0` and `1` share the same label `u01` and are placed into distinct copies `0` and
`1`, while incidence `2` (`u10`) is placed in copy `0`. -/
example : (testPlace 0).1 = 0 ∧ (testPlace 1).1 = 1 ∧ (testPlace 2).1 = 0 := by
  decide

/-- Compatibility `(sepPlace e).2.1 = sepVarA (testVarOf e)` for all `e : Fin 3`. -/
theorem sepPlace_fst_snd (e : Fin 3) :
    (sepPlace e).2.1 = sepVarA (testVarOf e) := by
  fin_cases e <;> rfl

/-- Degree bound and `T = 0` evaluation on `testPlace` (where incidences `0` and `2` both lie in
copy `0` and map to variable `0`). -/
example (e : Fin 3) (v : Fin 2) :
    (varReplacementRow 2 2 0 2 testPlace testVarOf e v).natDegree ≤ 1 ∧
      (varReplacementRow 2 2 0 2 testPlace testVarOf e v).eval 0 =
        if testVarOf e = v then 1 else 0 :=
  ⟨natDegree_varReplacementRow_le 2 2 0 2 testPlace testVarOf e v,
    eval_varReplacementRow_zero 2 2 0 2 injective_testPlace testVarOf e v⟩

/-- The unique antisymmetric basis index `u10 = ((1, 1), (0, 0))` for `Q = 2, r = 2`
lies in `measurementIndices 2 2 0 2` (`antisymCount u10 = 2 ∉ [0, 2)`). -/
theorem u10_mem_measurementIndices : u10 ∈ measurementIndices 2 2 0 2 := by
  decide

/-- Nonzero aliased measurement-row control: in copy `0`, incidences `0` (`u01`) and `2` (`u10`)
both map to variable `0` and both have value `+1` under `eigenvecInt u10`, so their coefficients
accumulate to `2` in `varMeasurementMatrix`, while the row `ℓ₁`-norm is `2 ≤ 16`. -/
example :
    varMeasurementMatrix 2 2 0 2 ℤ testPlace testVarOf
        (0, ⟨u10, u10_mem_measurementIndices⟩) 0 = 2 ∧
      (∑ v : Fin 2,
        |varMeasurementMatrix 2 2 0 2 ℤ testPlace testVarOf
          (0, ⟨u10, u10_mem_measurementIndices⟩) v|) ≤ 16 :=
  ⟨by decide,
    sum_abs_varMeasurementMatrix_le 2 2 0 2 injective_testPlace testVarOf
      (0, ⟨u10, u10_mem_measurementIndices⟩)⟩

/-- Nonzero vector `sepVec = ![0, 1]` supported on the nonempty off-group
`varGroup sepVarA 0 1 = {1}`. -/
def sepVec : Fin 2 → ℚ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1

theorem sepVec_supp (v : Fin 2) (hv : v ∉ varGroup sepVarA (0 : Fin 2) (1 : Fin 2)) :
    sepVec v = 0 := by
  fin_cases v
  · rfl
  · exfalso
    apply hv
    decide

theorem varMeasurementMatrix_sepPlace_one_int (p : Fin 2 × measurementIndices 2 2 0 2) :
    varMeasurementMatrix 2 2 0 2 ℤ sepPlace testVarOf p 1 = 0 := by
  rcases p with ⟨c, b, hb⟩
  fin_cases c <;> revert b hb <;> decide

theorem sepVec_ker :
    (varMeasurementMatrix 2 2 0 2 ℚ sepPlace testVarOf).mulVec sepVec = 0 := by
  ext p
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h0 : sepVec 0 = 0 := rfl
  have h1 :
      varMeasurementMatrix 2 2 0 2 ℚ sepPlace testVarOf p 1 =
        (varMeasurementMatrix 2 2 0 2 ℤ sepPlace testVarOf p 1 : ℚ) := by
    simp [varMeasurementMatrix, measurementMatrix, eigenvec]
  rw [h0, mul_zero, zero_add, h1, varMeasurementMatrix_sepPlace_one_int p, Int.cast_zero,
     zero_mul]
  rfl

/-- Nonvacuous Definition 3.1 kernel separation on `sepPlace` for incidence `1`
(`testVarOf 1 = 1`, assigned factor group `(sepPlace 1).2.2 0 = 0`):
`sepVec` is nonzero (`sepVec 1 = 1`), supported on the nonempty off-group
`varGroup sepVarA 0 1 = {1}` (`1 ≠ 0`), and in `ker Ĉ`; at `T = 0`, `evalVarReplacementRow`
for incidence `1` evaluates on `sepVec` to `1` (`evalVarReplacementRow_zero`), whereas at
`nodePoint 0 = 1` it annihilates `sepVec` (`= 0`) by
`evalVarReplacementRow_nodePoint_eq_zero_of_kernel`. -/
example :
    sepVec 1 = 1 ∧
      (1 : Fin 2) ∈ varGroup sepVarA (0 : Fin 2) (1 : Fin 2) ∧
      evalVarReplacementRow 2 2 0 2 sepPlace testVarOf 1 0 sepVec = 1 ∧
      evalVarReplacementRow 2 2 0 2 sepPlace testVarOf 1 (nodePoint (0 : Fin 2)) sepVec = 0 :=
  ⟨rfl, by decide,
    evalVarReplacementRow_zero 2 2 0 2 injective_sepPlace testVarOf 1 sepVec,
    evalVarReplacementRow_nodePoint_eq_zero_of_kernel 2 2 0 2 sepPlace testVarOf sepVarA
      sepPlace_fst_snd 1 (0 : Fin 2) (1 : Fin 2) (by decide) sepVec sepVec_supp sepVec_ker⟩

/-- Lemma 4.6 explicit `ℓ₁`-coefficient norm bounds for `Q = 2, r = 2, A₀ = 0, R = 2`:
`commonDenom 2 2 = 2`, `1 + (1 + 2 ^ 2) * 2 * (4 * 2) ^ 1 = 81`, so the cleared row coefficient
`ℓ₁`-sum is at most `2 * 81 = 162`. -/
example (e : Fin 3) :
    (mismatchAnnihilatorScaledInt u00 u11).coeffNorm1 ≤ 8 ∧
      rowNorm1 (M0ScaledInt 2 2 0 2) u00 ≤ 16 ∧
      (∑ v : Fin 2,
        ((varReplacementRowScaledInt 2 2 0 2 testPlace testVarOf e v).coeffNorm1 : ℤ)) ≤ 162 := by
  have hI : ∀ a < 2 - 1, 0 + a ≤ 2 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa using coeffNorm1_mismatchAnnihilatorScaledInt_le u00 u11
  · simpa using rowNorm1_M0ScaledInt_le (by decide : 0 < 2) hI u00
  · simpa [commonDenom] using
      sum_coeffNorm1_varReplacementRowScaledInt_le (by decide : 0 < 2) injective_testPlace
        testVarOf hI e

end Cslib.LinearAlgebra.VariableCopyPlacementTests
