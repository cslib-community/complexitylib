/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.MvPolynomial.FactorCounting
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Concrete tests for factor-counting synthesis and subset-pair costs

Nonvacuous checks exercising `Cslib.AffineTaylor` (`FactorCounting.lean`) across:
- `targetSum`, `eval_zero_replacedSum_eq_targetSum`, and univariate degree bounds on `replacedSum`
  for a 2-variable, 2-factor polynomial system with nontrivial degree-1 replacement rows;
- variable group partitioning (`groupSplitEquiv`, `groupReassemble_add_single_eq`),
  `prod_groupFactorProduct_eq_map_eval_factorProduct`,
  `sum_filter_cube_eq_sum_piFinset_localAllowed`,
  `sum_restricted_factorProduct_eq_sum_measurement_fibers`,
  `coeff_taylor_replacedSum_eq_sum_measurement_fibers`,
  `groupFactorProduct_locality_of_kernel_shifts` (with a nonzero off-group kernel vector),
  `card_intMeasurementBox`, and `mulVec_bitVal_mem_intMeasurementBox`;
- end-to-end `targetSum_eq_of_taylorJet` recovery over `ℚ` from Hermite jet coefficients at
  distinct nonzero nodes `nodes = ![1, 2]`;
- `subsetPairCount` exact enumeration (`sum_card_powerset_filter_card_le_eq_subsetPairCount`),
  boundary values (`subsetPairCount_zero_left`, `subsetPairCount_of_le`), and the equation (3.15)
  cost bound (`pow_mul_subsetPairCount_le`).
-/

open scoped BigOperators
open Finset Polynomial Cslib Cslib.BitString Cslib.AffineTaylor Cslib.SharedSummaries

namespace FactorCountingTests

private theorem cube_two_sum {M : Type*} [AddCommMonoid M]
    (s : Finset (Fin 2 → Bool)) (f : (Fin 2 → Bool) → M) (hs : ∀ x, x ∈ s) :
    (∑ x ∈ s, f x) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  have hsuniv : s = univ := Finset.eq_univ_iff_forall.mpr hs
  rw [hsuniv, ← (finTwoArrowEquiv Bool).symm.sum_comp f]
  change (∑ b : Bool × Bool, f ![b.1, b.2]) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ac_rfl

/-! ### 1. Target sum, `T = 0` specialization, and `replacedSum` degree bounds -/

private abbrev sysVars : Bool → Type
  | true => Fin 2
  | false => Fin 1

private def sysVarIdx : (b : Bool) → sysVars b → Fin 2
  | true => ![0, 1]
  | false => ![1]

private noncomputable def sysFactors : (b : Bool) → MvPolynomial (sysVars b) ℚ
  | true => MvPolynomial.X 0 + MvPolynomial.X 1
  | false => 1 + MvPolynomial.X 0

-- Degree-1 replacement rows reducing to the identity selection at T = 0:
-- P true 0 = ![1 + X, X], P true 1 = ![-X, 1 + 2X], P false 0 = ![X, 1 - X].
private noncomputable def sysRows : (b : Bool) → sysVars b → Fin 2 → Polynomial ℚ
  | true => ![![1 + Polynomial.X, Polynomial.X], ![-Polynomial.X, 1 + 2 * Polynomial.X]]
  | false => ![![Polynomial.X, 1 - Polynomial.X]]

private theorem sysRows_eval_zero (f : Bool) (_hfs : f ∈ ({true, false} : Finset Bool))
    (v : sysVars f) (i : Fin 2) :
    (sysRows f v i).eval 0 = if i = sysVarIdx f v then 1 else 0 := by
  rcases f with _ | _ <;> fin_cases v <;> fin_cases i <;>
    simp [sysRows, sysVarIdx]

private theorem sysRows_natDegree_le (f : Bool) (_hfs : f ∈ ({true, false} : Finset Bool))
    (v : sysVars f) (i : Fin 2) :
    (sysRows f v i).natDegree ≤ 1 := by
  rcases f with _ | _ <;> fin_cases v <;> fin_cases i <;>
    dsimp [sysRows] <;> compute_degree!

-- Exact value of targetSum on the 2-variable system:
-- x = (0,0): (0 + 0)*(1 + 0) = 0
-- x = (0,1): (0 + 1)*(1 + 1) = 2
-- x = (1,0): (1 + 0)*(1 + 0) = 1
-- x = (1,1): (1 + 1)*(1 + 1) = 4
-- Total = 7.
private theorem targetSum_sys :
    targetSum ({true, false} : Finset Bool) sysFactors sysVarIdx = 7 := by
  unfold targetSum
  rw [cube_two_sum _ _ (fun x => by simp)]
  simp only [Finset.prod_pair (by decide : true ≠ false)]
  dsimp only [sysFactors, sysVarIdx]
  simp [bitVal]
  norm_num

-- Equation (3.1): evaluating replacedSum at T = 0 recovers targetSum = 7.
example : (replacedSum ({true, false} : Finset Bool) sysFactors sysRows).eval 0 = 7 := by
  rw [eval_zero_replacedSum_eq_targetSum _ _ _ _ sysRows_eval_zero, targetSum_sys]

-- Empty factor set on Fin 2 gives targetSum = 2^2 = 4.
example : targetSum (∅ : Finset Bool) sysFactors sysVarIdx = 4 := by
  rw [targetSum_empty]
  norm_num

-- Degree bound on replacedSum: natDegree ≤ (∑ totalDegree) * 1.
example :
    (replacedSum ({true, false} : Finset Bool) sysFactors sysRows).natDegree ≤
      (∑ f ∈ ({true, false} : Finset Bool), (sysFactors f).totalDegree) * 1 :=
  natDegree_replacedSum_le ({true, false} : Finset Bool) sysFactors sysRows sysRows_natDegree_le

private theorem sum_totalDegree_sys_le :
    ∑ f ∈ ({true, false} : Finset Bool), (sysFactors f).totalDegree ≤ 2 := by
  rw [Finset.sum_pair (by decide : true ≠ false)]
  have htrue : (sysFactors true).totalDegree ≤ 1 := by
    dsimp only [sysFactors]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_) <;>
      simp [MvPolynomial.totalDegree_X]
  have hfalse : (sysFactors false).totalDegree ≤ 1 := by
    dsimp only [sysFactors]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_) <;>
      simp [MvPolynomial.totalDegree_X]
  omega

-- Equations (3.2)–(3.3) & (3.5): natDegree ≤ 2 and degree < 4 = 2 * 2.
example : (replacedSum ({true, false} : Finset Bool) sysFactors sysRows).natDegree ≤ 2 * 1 :=
  natDegree_replacedSum_le_of_sum_totalDegree_le _ _ _ sum_totalDegree_sys_le sysRows_natDegree_le

example : (replacedSum ({true, false} : Finset Bool) sysFactors sysRows).degree < ↑(2 * 2) :=
  degree_replacedSum_lt_of_sum_totalDegree_le _ _ _ sum_totalDegree_sys_le sysRows_natDegree_le
    (by decide : 2 * 1 < 2 * 2)

/-! ### 2. End-to-end Proposition 3.4 recovery (`targetSum_eq_of_taylorJet`) -/

-- Recovering targetSum = 7 from the Q = 2, J = 2 Taylor jet at distinct integer nodes ![1, 2].
example :
    targetSum ({true, false} : Finset Bool) sysFactors sysVarIdx =
      ((hermiteMatrix (![1, 2] : Fin 2 → ℤ) 2).det : ℚ)⁻¹ •
        (((hermiteMatrix (![1, 2] : Fin 2 → ℤ) 2).map (Int.cast : ℤ → ℚ)).updateCol
          (⟨0, by decide⟩, ⟨0, by decide⟩)
          (taylorJet (fun i => ((![1, 2] : Fin 2 → ℤ) i : ℚ)) 2
            (replacedSum ({true, false} : Finset Bool) sysFactors sysRows))).det := by
  refine targetSum_eq_of_taylorJet ({true, false} : Finset Bool) sysFactors sysRows sysVarIdx
    ?_ (by decide : 0 < 2) (by decide : 0 < 2) sysRows_eval_zero sum_totalDegree_sys_le
    sysRows_natDegree_le (by decide : 2 * 1 < 2 * 2)
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp at hab ⊢

/-! ### 3. Group partition, `SharedSummaries` bridge, and off-group kernel locality -/

-- Partitioning 3 variables Fin 3 into two groups (false : {0}, true : {1, 2}).
private def varGrp3 : Fin 3 → Bool
  | 0 => false
  | 1 => true
  | 2 => true

example (x : Fin 3 → Bool) : groupSplitEquiv varGrp3 Bool (groupRestrict varGrp3 x) = x :=
  groupReassemble_groupRestrict varGrp3 x

-- Equation (3.11) product of groupFactorProducts across groups equals mapped factorProduct.
example (t : ℚ) (U : Finset (Fin 2)) (x : Fin 2 → Bool) :
    ∏ g : Bool, groupFactorProduct ({true, false} : Finset Bool) sysFactors sysRows id t U g x =
      (factorProduct ({true, false} : Finset Bool) sysFactors sysRows t x).map
        (MvPolynomial.eval fun i => bitVal ℚ (decide (i ∈ U))) :=
  prod_groupFactorProduct_eq_map_eval_factorProduct _ _ _ id t U x

-- Nonvacuous off-group kernel shift invariance test on Fin 3:
-- Group `false` has 1 variable {0}; group `true` has 2 variables {1, 2}.
-- On group `true`, the linear measurement `measure true u = u ⟨1, rfl⟩ + u ⟨2, rfl⟩` sums the two
-- coordinates. A factor assigned to group `false` whose row has equal off-group weights on
-- coordinates 1 and 2 (`rowQ () () = ![5, 3, 3]`) is invariant under shifting between the two
-- off-group assignments `x true = ![true, false]` and `x' true = ![false, true]` (which have the
-- same sum `1 + 0 = 0 + 1` on group `true` and differ by the nonzero kernel vector `![1, -1]`).
private def kerMeasure : ∀ g : Bool, (GroupCoord varGrp3 g → ℚ) →ₗ[ℚ] ℚ
  | false =>
    { toFun := fun u => u ⟨0, rfl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  | true =>
    { toFun := fun u => u ⟨1, rfl⟩ + u ⟨2, rfl⟩
      map_add' := fun u v => by simp [Pi.add_apply]; ring
      map_smul' := fun c u => by simp [Pi.smul_apply]; ring }

private noncomputable def kerFactor : Unit → MvPolynomial Unit ℚ :=
  fun _ => MvPolynomial.X ()

private def kerRowQ : Unit → Unit → Fin 3 → ℚ :=
  fun _ _ => ![5, 3, 3]

private noncomputable def kerRowP : Unit → Unit → Fin 3 → Polynomial ℚ :=
  fun f v i => Polynomial.C (kerRowQ f v i)

private def assignA : ∀ g : Bool, GroupCoord varGrp3 g → Bool
  | false => fun _ => true
  | true => fun i => if i.1 = 1 then true else false

private def assignB : ∀ g : Bool, GroupCoord varGrp3 g → Bool
  | false => fun _ => true
  | true => fun i => if i.1 = 2 then true else false

private theorem ker_locality (U : Finset (Fin 3)) (g : Bool)
    (x x' : ∀ h : Bool, GroupCoord varGrp3 h → Bool)
    (sameMeasurements : ∀ h,
      kerMeasure h (fun i => bitVal ℚ (x h i)) = kerMeasure h (fun i => bitVal ℚ (x' h i)))
    (sameCoordinate : x g = x' g) :
    groupFactorProduct ({()} : Finset Unit) kerFactor kerRowP (fun _ => false) 0 U g
      (groupReassemble varGrp3 x) =
    groupFactorProduct ({()} : Finset Unit) kerFactor kerRowP (fun _ => false) 0 U g
      (groupReassemble varGrp3 x') := by
  refine groupFactorProduct_locality_of_kernel_shifts varGrp3 (fun _ => false) kerMeasure
    ({()} : Finset Unit) kerFactor kerRowP 0 U kerRowQ ?_ ?_ g x x' sameMeasurements sameCoordinate
  · intro _ _ _ i
    simp [kerRowP]
  · intro _ _ _ h hne δ hδ
    rcases h with _ | _
    · exact (hne rfl).elim
    · have hδsum : δ ⟨1, rfl⟩ + δ ⟨2, rfl⟩ = 0 := hδ
      rw [Fin.sum_univ_three]
      have h0 : extendGroupVec varGrp3 true δ 0 = 0 :=
        extendGroupVec_of_ne varGrp3 δ (by decide : varGrp3 0 ≠ true)
      have h1 : extendGroupVec varGrp3 true δ 1 = δ ⟨1, rfl⟩ :=
        extendGroupVec_of_eq varGrp3 δ rfl
      have h2 : extendGroupVec varGrp3 true δ 2 = δ ⟨2, rfl⟩ :=
        extendGroupVec_of_eq varGrp3 δ rfl
      rw [h0, h1, h2]
      change 5 * 0 + 3 * δ ⟨1, rfl⟩ + 3 * δ ⟨2, rfl⟩ = 0
      linarith

-- The two assignments differ on group `true`, yet have identical measurements and agree on `false`,
-- so `groupFactorProduct_locality_of_kernel_shifts` proves their groupFactorProducts at `false`
-- are equal.
example (U : Finset (Fin 3)) :
    groupFactorProduct ({()} : Finset Unit) kerFactor kerRowP (fun _ => false) 0 U false
      (groupReassemble varGrp3 assignA) =
    groupFactorProduct ({()} : Finset Unit) kerFactor kerRowP (fun _ => false) 0 U false
      (groupReassemble varGrp3 assignB) := by
  refine ker_locality U false assignA assignB ?_ rfl
  intro h
  rcases h with _ | _ <;>
    simp [kerMeasure, assignA, assignB, bitVal]

-- Chaining `ker_locality` into `coeff_taylor_replacedSum_eq_sum_measurement_fibers`:
private def kerBox : Bool → Finset ℚ
  | false => {0, 1}
  | true => {0, 1, 2}

private theorem kerCovers (g : Bool) (u : GroupCoord varGrp3 g → Bool) :
    kerMeasure g (fun i => bitVal ℚ (u i)) ∈ kerBox g := by
  rcases g with _ | _
  · simp only [kerMeasure, kerBox, LinearMap.coe_mk, AddHom.coe_mk, mem_insert, mem_singleton]
    cases u ⟨0, rfl⟩ <;> simp [bitVal]
  · simp only [kerMeasure, kerBox, LinearMap.coe_mk, AddHom.coe_mk, mem_insert, mem_singleton]
    cases u ⟨1, rfl⟩ <;> cases u ⟨2, rfl⟩ <;> norm_num [bitVal]

open Classical in
private noncomputable def kerRep (y : Bool → ℚ)
    (hy : ∀ g, ∃ u : GroupCoord varGrp3 g → Bool,
      kerMeasure g (fun i => bitVal ℚ (u i)) = y g) :
    ∀ g, GroupCoord varGrp3 g → Bool :=
  fun g => (hy g).choose

private theorem kerRep_valid (y : Bool → ℚ)
    (hy : ∀ g, ∃ u : GroupCoord varGrp3 g → Bool,
      kerMeasure g (fun i => bitVal ℚ (u i)) = y g) (g : Bool) :
    kerMeasure g (fun i => bitVal ℚ (kerRep y hy g i)) = y g :=
  (hy g).choose_spec

example :
    (Polynomial.taylor 0 (replacedSum ({()} : Finset Unit) kerFactor kerRowP)).coeff 1 =
      ∑ E ∈ (univ : Finset (Fin 3)).powerset.filter (fun E => #E ≤ 1),
        ∑ U ∈ E.powerset, (-1 : ℚ) ^ (#E - #U) *
          (∑ y ∈ Fintype.piFinset kerBox,
            fiberContribution (fun g u => kerMeasure g (fun i => bitVal ℚ (u i)))
              (localAllowed varGrp3 E)
              (fun g x => groupFactorProduct ({()} : Finset Unit) kerFactor kerRowP
                (fun _ => false) 0 U g (groupReassemble varGrp3 x))
              kerRep y).coeff 1 :=
  coeff_taylor_replacedSum_eq_sum_measurement_fibers varGrp3 (fun _ => false)
    (fun g u => kerMeasure g (fun i => bitVal ℚ (u i))) kerBox kerCovers
    ({()} : Finset Unit) kerFactor kerRowP 0 (le_refl 1)
    (fun U _ => ker_locality U) kerRep kerRep_valid

-- Integer measurement box cardinality and coverage on `Fin 2` with bound `D = 3`:
-- `#[-3, 3]^2 = (2 * 3 + 1)^2 = 49`.
example : #(intMeasurementBox (Fin 2) 3) = 49 := by
  rw [card_intMeasurementBox]
  norm_num

example (u : Fin 2 → Bool) :
    Matrix.mulVec ![![(1 : ℤ), -2], ![0, 3]] (fun j => bitVal ℤ (u j)) ∈
      intMeasurementBox (Fin 2) 3 := by
  refine mulVec_bitVal_mem_intMeasurementBox _ ?_ u
  intro i
  fin_cases i <;>
    simp [Fin.sum_univ_two]

/-! ### 4. Subset-pair count identity and equation (3.15) bound -/

-- Exact count of pairs (E, U) with E ⊆ Fin 3, #E ≤ 2, and U ⊆ E:
-- k = 0: C(3,0)*2^0 = 1
-- k = 1: C(3,1)*2^1 = 6
-- k = 2: C(3,2)*2^2 = 12
-- Total = 19.
example :
    ∑ E ∈ (univ : Finset (Fin 3)).powerset.filter (fun E => #E ≤ 2), #(E.powerset) = 19 := by
  rw [sum_card_powerset_filter_card_le_eq_subsetPairCount]
  decide

example : subsetPairCount 0 5 = 1 :=
  subsetPairCount_zero_left 5

example : subsetPairCount 3 2 = 9 := by
  rw [subsetPairCount_of_le (by decide : 2 ≤ 3)]
  norm_num

-- Equation (3.15) at η = 1/2, q = 2, n = 4:
-- (1/2)^2 * subsetPairCount 2 4 ≤ (1 + 2 * (1/2))^4 = 16.
example :
    ((1 / 2 : ℚ) ^ 2) * (subsetPairCount 2 4 : ℚ) ≤ (1 + 2 * (1 / 2 : ℚ)) ^ 4 :=
  pow_mul_subsetPairCount_le 2 4 (by norm_num) (by norm_num)

end FactorCountingTests
