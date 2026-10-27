/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CNF.SparseDesignCounter

/-!
# Tests for `Complexity.Logics.Propositional.CNF.SparseDesignCounter`
-/

@[expose] public noncomputable section

namespace ComplexityTests.SparseDesignCounter

open Finset Polynomial Cslib.BitString Cslib.BalancedSchedules Cslib.LinearAlgebra Cslib.Logic.PL

/-- Concrete 2-variable 2-CNF formula `(x₀ ∨ ¬x₁) ∧ (x₁)` on `Fin 2`, with unique satisfying
assignment `x₀ = true, x₁ = true`. -/
def testCNF : CNF (Fin 2) :=
  [[(0, true), (1, false)], [(1, true)]]

/-- Concrete two-row unit parity check matrix selecting clause `0` and clause `1` of `testCNF`. -/
def testRows : List (Fin testCNF.length → Bool) :=
  [Pi.single ⟨0, by decide⟩ true, Pi.single ⟨1, by decide⟩ true]

/-- Concrete 3-variable 2-CNF formula `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ ¬x₂)` on `Fin 3`, with `4` satisfying
assignments (`(false, false, false)`, `(true, false, false)`, `(true, true, false)`, and
`(true, true, true)`). -/
def testCNF3 : CNF (Fin 3) :=
  [[(0, true), (1, false)], [(1, true), (2, false)]]

/-- Unit parity check rows for `testCNF3`. -/
def testRows3 : List (Fin testCNF3.length → Bool) :=
  [Pi.single ⟨0, by decide⟩ true, Pi.single ⟨1, by decide⟩ true]

/-- Explicit equivalence between the unbranched variables `{1, 2}` (`univ \ {0}` in `Fin 3`) and
`Fin 2`. -/
def freeVarEquiv3 : ↥((univ : Finset (Fin 3)) \ ({0} : Finset (Fin 3))) ≃ Fin 2 where
  toFun v := if v.1 = 1 then 0 else 1
  invFun i := if i = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- Expected-value and sparsity controls on `testCNF3.branchParityRowSystem`,
`branchParityRowScope`, and `branchParityRowNeutralScope` for branch `b = fun _ => false` on
`S = {0}`:
- Clause `0` (`x₀ ∨ ¬x₁`) has violation monomial `(1 + x₀) x₁ = x₁ + x₀ x₁`, which under
  `x₀ = false` restricts to `x₁` (free variable `0 : Fin 2`, scope `{0}`).
- Clause `1` (`x₁ ∨ ¬x₂`) has violation monomial `(1 + x₁) x₂ = x₂ + x₁ x₂`, which restricts to
  `{1}, {0, 1}` on `Fin 2` (scope `{0, 1}`).
- Neutral singleton factors add `{0}` and `{1}`, so total neutral-augmented incidence is
  `(1 + 2) + 2 = 5 ≥ 2`. -/
example (j : Fin testRows3.length) (f : Fin testRows3.length ⊕ Fin 2) :
    #(testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
      (fun _ => false) j) ≤ 1 * 2 ^ 2 ∧
    #(testCNF3.branchParityRowScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
      (fun _ => false) j) ≤ 2 * (1 * 2 ^ 2) ∧
    #(testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
      (fun _ => false) f) ≤ max 1 (2 * (1 * 2 ^ 2)) ∧
    totalIncidence (univ : Finset (Fin testRows3.length ⊕ Fin 2))
      (testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false)) = 5 ∧
    2 ≤ totalIncidence (univ : Finset (Fin testRows3.length ⊕ Fin 2))
      (testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false)) := by
  refine ⟨?_, ?_, ?_, by decide, ?_⟩
  · exact testCNF3.card_branchParityRowSystem_le (k := 2) (W := 1) (by decide) (by decide)
      ({0} : Finset (Fin 3)) freeVarEquiv3 (fun _ => false) j
  · exact testCNF3.card_branchParityRowScope_le (k := 2) (W := 1) (by decide) (by decide)
      ({0} : Finset (Fin 3)) freeVarEquiv3 (fun _ => false) j
  · exact testCNF3.card_branchParityRowNeutralScope_le (k := 2) (W := 1) (by decide) (by decide)
      ({0} : Finset (Fin 3)) freeVarEquiv3 (fun _ => false) f
  · exact testCNF3.le_totalIncidence_branchParityRowNeutralScope testRows3
      ({0} : Finset (Fin 3)) freeVarEquiv3 (fun _ => false)

/-- Canonical `Q = 1, r = 1, A₀ = 0, R = 1, τ = 0` replacement design for any scope family on
`Fin n`. -/
def unitReplacementDesign {F : Type*} [Fintype F] {n : ℕ}
    (scope : F → Finset (Fin n)) : ReplacementDesign scope 1 1 0 1 0 :=
  let h := Fintype.card (ScopeIncidence scope)
  let eFin := Fintype.equivFin (ScopeIncidence scope)
  let place : ScopeIncidence scope → Fin h × AuxLabel 1 1 :=
    fun e => (eFin e, (fun _ => 0, fun _ => 0))
  have hinj : Function.Injective place := fun _ _ hEq =>
    eFin.injective (congrArg Prod.fst hEq)
  { varAssign := fun _ _ => 0
    factorAssign := fun _ _ => 0
    h := h
    place := place
    card_varGroup_le := fun t g => by
      have hsub : #(varGroup (fun (_ : Fin n) (_ : Fin 1) => (0 : Fin 1)) t g) ≤ n := by
        simpa only [card_univ, Fintype.card_fin] using
          card_le_univ (varGroup (fun (_ : Fin n) (_ : Fin 1) => (0 : Fin 1)) t g)
      omega
    factorAssign_of_empty := fun _ _ _ => rfl
    injective_place := hinj
    place_snd := fun _ => rfl
    h_mul_D_le := by
      change Fintype.card (ScopeIncidence scope) * 1 ^ (2 * 1) ≤ 2 * ∑ f : F, #(scope f)
      rw [card_scopeIncidence]
      omega
    total_measurement_rows_le := by
      have hmeas : #(measurementIndices 1 1 0 1) = 0 := by decide
      simp [hmeas]
    sum_abs_measurement_row_le :=
      sum_abs_varMeasurementMatrix_le 1 1 0 1 hinj (scopeVarOf scope)
    natDegree_replacementRow_le :=
      natDegree_varReplacementRow_le 1 1 0 1 place (scopeVarOf scope)
    eval_replacementRow_zero :=
      eval_varReplacementRow_zero 1 1 0 1 hinj (scopeVarOf scope)
    evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
      evalVarReplacementRow_nodePoint_eq_zero_of_kernel 1 1 0 1 place (scopeVarOf scope)
        (fun _ _ => 0) (fun _ => rfl) e t g hg ξ hsupp hker
    map_replacementRowScaledInt :=
      map_varReplacementRowScaledInt 1 1 0 1 place (scopeVarOf scope)
    sum_coeffNorm1_replacementRowScaledInt_le :=
      sum_coeffNorm1_varReplacementRowScaledInt_le (by decide) hinj (scopeVarOf scope)
        (by intro a ha; omega) }

/-- Scope family on `Fin testRows3.length ⊕ Fin 2` for branch `b = fun _ => false` of `testCNF3`. -/
abbrev sampleBranchNeutralScope : Fin testRows3.length ⊕ Fin 2 → Finset (Fin 2) :=
  testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
    (fun _ => false)

/-- Variable group schedule for `nonconstBranchDesign`: free variable `0` in group `0`, free
variable `1` in group `1`. -/
def nonconstBranchVarAssign : Fin 2 → Fin 1 → Fin 2 :=
  fun v _ => v

/-- Factor group schedule for `nonconstBranchDesign`: equation factors in group `0`, neutral
factors in group `1`. -/
def nonconstBranchFactorAssign : Fin testRows3.length ⊕ Fin 2 → Fin 1 → Fin 2
  | Sum.inl _, _ => 0
  | Sum.inr _, _ => 1

/-- Copy index in `Fin 2` separating the `5` incidences of `sampleBranchNeutralScope`. -/
def nonconstBranchCopy (e : ScopeIncidence sampleBranchNeutralScope) : Fin 2 :=
  match e.1 with
  | Sum.inl ⟨0, _⟩ => 0
  | Sum.inl ⟨1, _⟩ => if e.2.1 = 0 then 1 else 0
  | Sum.inr _ => 0

/-- Injective placement for `nonconstBranchDesign`. -/
def nonconstBranchPlace (e : ScopeIncidence sampleBranchNeutralScope) :
    Fin 2 × AuxLabel 1 2 :=
  (nonconstBranchCopy e,
    (nonconstBranchVarAssign (scopeVarOf sampleBranchNeutralScope e),
     nonconstBranchFactorAssign (scopeFactorOf sampleBranchNeutralScope e)))

theorem injective_nonconstBranchPlace : Function.Injective nonconstBranchPlace := by
  decide

/-- Concrete `Q = 1, r = 2, A₀ = 0, R = 2, τ = 0` replacement design on `sampleBranchNeutralScope`
with nonconstant degree-`1` replacement rows. -/
def nonconstBranchDesign :
    ReplacementDesign sampleBranchNeutralScope 1 2 0 2 0 where
  varAssign := nonconstBranchVarAssign
  factorAssign := nonconstBranchFactorAssign
  h := 2
  place := nonconstBranchPlace
  card_varGroup_le := by decide
  factorAssign_of_empty := by decide
  injective_place := injective_nonconstBranchPlace
  place_snd := fun _ => rfl
  h_mul_D_le := by decide
  total_measurement_rows_le := by
    have hmeas : #(measurementIndices 1 2 0 2) = 0 := by decide
    simp [hmeas]
  sum_abs_measurement_row_le :=
    sum_abs_varMeasurementMatrix_le 1 2 0 2 injective_nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope)
  natDegree_replacementRow_le :=
    natDegree_varReplacementRow_le 1 2 0 2 nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope)
  eval_replacementRow_zero :=
    eval_varReplacementRow_zero 1 2 0 2 injective_nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope)
  evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
    evalVarReplacementRow_nodePoint_eq_zero_of_kernel 1 2 0 2 nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope) nonconstBranchVarAssign (fun _ => rfl) e t g hg ξ
      hsupp hker
  map_replacementRowScaledInt :=
    map_varReplacementRowScaledInt 1 2 0 2 nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope)
  sum_coeffNorm1_replacementRowScaledInt_le :=
    sum_coeffNorm1_varReplacementRowScaledInt_le (by decide) injective_nonconstBranchPlace
      (scopeVarOf sampleBranchNeutralScope) (by intro a ha; omega)

/-- Assignment `x₁ = (false, true)` on `Fin 2` placing `true` on free variable `1 : Fin 2` in
group `1`. -/
def branchAssign₁ : Fin 2 → Bool := fun v => decide (v = 1)

/-- All-false assignment `x₂ = (false, false)` on `Fin 2` agreeing with `branchAssign₁` on group
`0 = {0}`. -/
def branchAssign₂ : Fin 2 → Bool := fun _ => false

/-- Checked client of `CNF.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq`,
`CNF.natDegree_univariateClearedParityCoord_branchParityRowSystem_le`,
`CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le`, and
`CNF.coeffNorm1_univariateClearedParityCoord_branchParityRowSystem_le` on `nonconstBranchDesign`:
1. The replacement polynomial for equation `1` and free variable `1 : Fin 2` on `branchAssign₁` has
   exact nonconstant degree `1` (`eval 0 = 1`, `eval (nodePoint 0) = 0`).
2. `CNF.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq` proves that the
   substituted equation-`1` factors for `branchAssign₁` and `branchAssign₂` coincide at
   `nodePoint (0 : Fin 1)`.
3. The cleared coordinate and truncated-sum polynomials at `k = 2, ℓ = 4` have `natDegree ≤ 16`
   and satisfy the Appendix B.2 `coeffNorm1` bound. -/
example {E_ℓ : ℕ} (hE : ∀ j < 4, (Polynomial.parityBaseDigit 4 j).coeffNorm1 ≤ E_ℓ) :
    (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₁ ⟨1, by decide⟩ 1).eval 0 = 1 ∧
    (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₁ ⟨1, by decide⟩ 1).eval
      (nodePoint (0 : Fin 1)) = 0 ∧
    (univariateMonomialSumPoly ℚ
      (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₁ ⟨1, by decide⟩)
      (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false) ⟨1, by decide⟩)).eval (nodePoint (0 : Fin 1)) =
    (univariateMonomialSumPoly ℚ
      (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₂ ⟨1, by decide⟩)
      (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false) ⟨1, by decide⟩)).eval (nodePoint (0 : Fin 1)) ∧
    (univariateClearedParityCoord (univ : Finset (Fin testRows3.length))
      (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false))
      (commonDenom 1 2 : ℤ) 2 4 (designReplacementScaledIntMap nonconstBranchDesign Sum.inl)
        0).natDegree ≤ 16 ∧
    (univariateClearedParityTruncatedSum (univ : Finset (Fin testRows3.length))
      (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false))
      (commonDenom 1 2 : ℤ) 2 4
      (designReplacementScaledIntMap nonconstBranchDesign Sum.inl)).natDegree ≤ 16 ∧
    (univariateClearedParityCoord (univ : Finset (Fin testRows3.length))
      (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false))
      (commonDenom 1 2 : ℤ) 2 4 (designReplacementScaledIntMap nonconstBranchDesign Sum.inl)
        0).coeffNorm1 ≤
      2 ^ 2 *
        (4 * E_ℓ *
          ((1 * 2 ^ 2) * designRowNormBound 1 2 ^ 2 + commonDenom 1 2 ^ 2) ^ (2 * 4 - 1)) ^ 2 := by
  have hgrp : ∀ u ∈ varGroup nonconstBranchDesign.varAssign (0 : Fin 1)
      (nonconstBranchDesign.factorAssign (Sum.inl ⟨1, by decide⟩) (0 : Fin 1)),
      branchAssign₁ u = branchAssign₂ u := by
    decide
  have hmeas :
      (varMeasurementMatrix 1 2 0 2 ℚ nonconstBranchDesign.place
        (scopeVarOf sampleBranchNeutralScope)).mulVec (fun u => bitVal ℚ (branchAssign₁ u)) =
      (varMeasurementMatrix 1 2 0 2 ℚ nonconstBranchDesign.place
        (scopeVarOf sampleBranchNeutralScope)).mulVec (fun u => bitVal ℚ (branchAssign₂ u)) := by
    funext p
    exact absurd p.2.2 (by decide +revert)
  have heval0 :
      (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₁ ⟨1, by decide⟩ 1).eval 0 =
        1 := by
    rw [eval_zero_designReplacementMap]
    rfl
  have heval1 :
      (designReplacementMap nonconstBranchDesign Sum.inl branchAssign₁ ⟨1, by decide⟩ 1).eval
        (nodePoint (0 : Fin 1)) = 0 := by
    have hloc := eval_nodePoint_designReplacementMap_eq_of_eq_on_varGroup
      nonconstBranchDesign Sum.inl (i := (⟨1, by decide⟩ : Fin testRows3.length))
      (v := (1 : Fin 2)) (by decide) (0 : Fin 1) branchAssign₁ branchAssign₂ hgrp hmeas
    have hzero :
        designReplacementMap nonconstBranchDesign Sum.inl branchAssign₂ ⟨1, by decide⟩ 1 = 0 := by
      simp [branchAssign₂, designReplacementMap, evalVarReplacementRowPoly]
    rw [hloc, hzero, Polynomial.eval_zero]
  refine ⟨heval0, heval1, ?_, ?_, ?_, ?_⟩
  · exact testCNF3.eval_univariateMonomialSumPoly_branchParityRowSystem_nodePoint_eq
      testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3 (fun _ => false) nonconstBranchDesign
      ⟨1, by decide⟩ (0 : Fin 1) branchAssign₁ branchAssign₂ hgrp hmeas
  · simpa [testRows3] using testCNF3.natDegree_univariateClearedParityCoord_branchParityRowSystem_le
      (k := 2) (ℓ := 4) (s := 0) (by decide) testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
      (fun _ => false) nonconstBranchDesign Sum.inl (by decide)
  · simpa [testRows3] using
      testCNF3.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le
        (k := 2) (by decide) testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false) nonconstBranchDesign Sum.inl 4
  · simpa [testRows3] using
      testCNF3.coeffNorm1_univariateClearedParityCoord_branchParityRowSystem_le
        (k := 2) (W := 1) (ℓ := 4) (by decide) (by decide) ({0} : Finset (Fin 3)) freeVarEquiv3
        (fun _ => false) nonconstBranchDesign Sum.inl hE 0

/-- Checked client of `CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design` and
`CNF.numPassing_eq_sum_branch_emod_ediv_design` on `testCNF3` and `testRows3` (`S = {0}`):
the branch-summed `ReplacementDesign` recovery equals `4`. -/
example :
    ∑ b ∈ branchAssignments ({0} : Finset (Fin 3)),
      ((univariateClearedParityTruncatedSum (univ : Finset (Fin testRows3.length))
        (testCNF3.branchParityRowSystem testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3 b)
        (commonDenom 1 1 : ℤ) 2 (branchPrecision (Fintype.card (Fin 3)))
        (designReplacementScaledIntMap
          (unitReplacementDesign
            (testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3 b))
          Sum.inl)).eval 0 /
            clearedProductDenom (commonDenom 1 1 : ℤ) 2 (branchPrecision (Fintype.card (Fin 3)))
              #(univ : Finset (Fin testRows3.length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin 3))) = 4 := by
  have hrec := testCNF3.numPassing_eq_sum_branch_emod_ediv_design (k := 2) (by decide) testRows3
    ({0} : Finset (Fin 3)) freeVarEquiv3
    (fun b => testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3 b)
    (fun b => unitReplacementDesign
      (testCNF3.branchParityRowNeutralScope testRows3 ({0} : Finset (Fin 3)) freeVarEquiv3 b))
    (fun _ => Sum.inl)
  have hpass : numPassing testCNF3.violations testRows3 = 4 := by decide
  rw [← hrec, hpass]
  rfl

/-- Explicit equivalence between `{1}` (`univ \ {0}` in `Fin 2`) and `Fin 1`. -/
def freeVarEquiv2 : ↥((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨1, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- Concrete candidate tuple of length `P = 2` for `testCNF`. -/
def testCand : Fin 2 → Fin testCNF.length × Bool :=
  fun _ => (⟨0, by decide⟩, false)

/-- Concrete `3 * n`-step greedy row sequence starting from `testRows`. -/
def testGreedySeq : ℕ → List (Fin testCNF.length → Bool)
  | 0 => testRows
  | i + 1 => testGreedySeq i ++ [testRow testCand]

private theorem passesTests_testGreedySeq_imp_passesTests_testRows :
    ∀ (i : ℕ) (σ : Fin 2 → Bool),
      PassesTests testCNF.violations (testGreedySeq i) σ →
        PassesTests testCNF.violations testRows σ
  | 0, _, h => h
  | i + 1, σ, h =>
    passesTests_testGreedySeq_imp_passesTests_testRows i σ
      ((passesTests_append_singleton _ _ _ _).mp h).1

private theorem violations_eq_zero_of_passesTests_testRows :
    ∀ σ : Fin 2 → Bool, PassesTests testCNF.violations testRows σ → testCNF.violations σ = 0 := by
  decide

private theorem commonZeroCount_testGreedySeq_step_le (i : ℕ)
    (γ' : Fin 2 → Fin testCNF.length × Bool) :
    commonZeroCount univ (testCNF.parityRowSystem (testGreedySeq i ++ [testRow testCand])) ≤
      commonZeroCount univ (testCNF.parityRowSystem (testGreedySeq i ++ [testRow γ'])) := by
  rw [testCNF.commonZeroCount_parityRowSystem, testCNF.commonZeroCount_parityRowSystem]
  apply card_le_card
  intro σ hσ
  rw [mem_filter] at hσ ⊢
  refine ⟨mem_univ σ, ?_⟩
  have hpasses_i := ((passesTests_append_singleton _ _ _ _).mp hσ.2).1
  have hzero := violations_eq_zero_of_passesTests_testRows σ
    (passesTests_testGreedySeq_imp_passesTests_testRows i σ hpasses_i)
  rw [passesTests_append_singleton]
  refine ⟨hpasses_i, ?_⟩
  rw [hzero, dotProduct_zero]
  rfl

/-- Checked client of `CNF.modelCountOn_eq_sum_branch_emod_ediv_design_greedy`: recovers
`testCNF.modelCountOn Finset.univ = 1` via `unitReplacementDesign` without any auxiliary `θ` or
`hθ` hypotheses. -/
example :
    ∑ b ∈ branchAssignments ({0} : Finset (Fin 2)),
      ((univariateClearedParityTruncatedSum
        (univ : Finset (Fin (testGreedySeq (3 * Fintype.card (Fin 2))).length))
        (testCNF.branchParityRowSystem (testGreedySeq (3 * Fintype.card (Fin 2)))
          ({0} : Finset (Fin 2)) freeVarEquiv2 b)
        (commonDenom 1 1 : ℤ) 2 (branchPrecision (Fintype.card (Fin 2)))
        (designReplacementScaledIntMap
          (unitReplacementDesign
            (testCNF.branchParityRowNeutralScope (testGreedySeq (3 * Fintype.card (Fin 2)))
              ({0} : Finset (Fin 2)) freeVarEquiv2 b))
          Sum.inl)).eval 0 /
            clearedProductDenom (commonDenom 1 1 : ℤ) 2 (branchPrecision (Fintype.card (Fin 2)))
              #(univ : Finset (Fin (testGreedySeq (3 * Fintype.card (Fin 2))).length))) %
                ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin 2))) = 1 := by
  have hrec := testCNF.modelCountOn_eq_sum_branch_emod_ediv_design_greedy
    (k := 2) (P := 2) (by decide) (by decide) (by decide) testGreedySeq (by decide)
    (fun _ => testCand) (fun _ => rfl) commonZeroCount_testGreedySeq_step_le
    ({0} : Finset (Fin 2)) freeVarEquiv2
    (fun b => testCNF.branchParityRowNeutralScope (testGreedySeq (3 * Fintype.card (Fin 2)))
      ({0} : Finset (Fin 2)) freeVarEquiv2 b)
    (fun b => unitReplacementDesign
      (testCNF.branchParityRowNeutralScope (testGreedySeq (3 * Fintype.card (Fin 2)))
        ({0} : Finset (Fin 2)) freeVarEquiv2 b))
    (fun _ => Sum.inl)
  have hcount : testCNF.modelCountOn Finset.univ = 1 := by decide
  rw [← hrec, hcount]
  rfl

/-- Concrete check of `CNF.max_initialRowWeightBound_greedyRowListLength` at `B = 2, m = 8`. -/
example :
    max (initialRowWeightBound 2 8) (greedyRowListLength 2 8) =
      320000 * 2 ^ 2 * (3 + 1) ^ 3 := by
  rw [CNF.max_initialRowWeightBound_greedyRowListLength]
  decide

/-- Empty CNF on `Fin 16384` used to witness
`CNF.exists_replacementDesign_branchParityRowNeutralScope` at `b₀ = 0`, `Q = 3`, `r = 2`,
`A₀ = 0`, `R = 2`, `τ = 1 / 2`. -/
def emptyCNF16384 : CNF (Fin 16384) := []

/-- Equivalence between `↥(univ \ heavyVars univ univ ... 0)` and `Fin 16384` for `emptyCNF16384`
with `rows = []`. -/
def emptyFreeVarEquiv16384 :
    ↥((univ : Finset (Fin 16384)) \
      heavyVars univ (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
        (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0) ≃ Fin 16384 where
  toFun v := v.1
  invFun v := ⟨v, by
    rw [mem_sdiff]
    refine ⟨mem_univ v, ?_⟩
    simp [heavyVars, varIncidence]⟩
  left_inv v := by ext; rfl
  right_inv _ := rfl

/-- Nonvacuous witness of `CNF.exists_replacementDesign_branchParityRowNeutralScope` and
single-branch recovery `CNF.emod_ediv_eval_zero_branchParityRowSystem_design_eq_commonZeroCount` on
`emptyCNF16384` (`commonZeroCount = 2 ^ 16384` at `ℓ = 16385`). -/
theorem exists_design_and_recover_emptyCNF16384 :
    ∃ D : ReplacementDesign
        (emptyCNF16384.branchParityRowNeutralScope []
          (heavyVars univ (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
            (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0)
          emptyFreeVarEquiv16384 (fun _ => false)) 3 2 0 2 (1 / 2),
      ((univariateClearedParityTruncatedSum
          (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
          (emptyCNF16384.branchParityRowSystem []
            (heavyVars univ
              (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
              (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0)
            emptyFreeVarEquiv16384 (fun _ => false))
          (commonDenom 3 2 : ℤ) 3 16385 (designReplacementScaledIntMap D Sum.inl)).eval 0 /
        clearedProductDenom (commonDenom 3 2 : ℤ) 3 16385
          #(univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))) %
            ((2 : ℤ) ^ 16385) = (2 : ℤ) ^ 16384 := by
  have hcard : #(measurementIndices 3 2 0 2) = 10 := by
    rw [card_measurementIndices_eq]
    decide
  have htail : binomTailProb 3 2 0 2 ≤ (1 / 2 : ℚ) / ((2 : ℚ) * ((0 + 1 : ℕ) : ℚ)) := by
    rw [binomTailProb_eq_div 3 2 0 2 (by decide), hcard]
    norm_num
  have hI : ∀ a < 2 - 1, 0 + a ≤ 3 := by decide
  have hbal₁_arith : 2 * (0 + 1 + max 1 (3 * (0 * 2 ^ 3))) * (2 ^ (2 * 3)) ^ 2 ≤ 0 + 16384 := by
    decide
  have hbal₂ : 2 * 3 * 2 ^ 2 ≤ 16384 := by decide
  have hne := emptyCNF16384.exists_replacementDesign_branchParityRowNeutralScope
    (k := 3) (W := 0) (b₀ := 0) (Q := 3) (r := 2) (A₀ := 0) (R := 2) (τ := 1 / 2)
    (rows := []) (fun _ hc => nomatch hc) (fun _ hr => nomatch hr)
    emptyFreeVarEquiv16384 (fun _ => false)
    (by decide) (by decide) (by decide) (by decide) (by norm_num)
    hI hbal₁_arith hbal₂ htail
  obtain ⟨D⟩ := hne
  refine ⟨D, ?_⟩
  have hrec := emptyCNF16384.emod_ediv_eval_zero_branchParityRowSystem_design_eq_commonZeroCount
    (k := 3) (ℓ := 16385) (fun _ hc => nomatch hc) []
    (heavyVars univ (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
      (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0)
    emptyFreeVarEquiv16384 (fun _ => false) D Sum.inl (by decide)
  have hcount :
      (commonZeroCount
        (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
        (emptyCNF16384.branchParityRowSystem []
          (heavyVars univ (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
            (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0)
          emptyFreeVarEquiv16384 (fun _ => false)) : ℤ) = (2 : ℤ) ^ 16384 := by
    change
      (commonZeroCount (∅ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
        (emptyCNF16384.branchParityRowSystem []
          (heavyVars univ (univ : Finset (Fin ([] : List (Fin emptyCNF16384.length → Bool)).length))
            (fun j => equationScope (emptyCNF16384.parityRowSystem [] j)) 0)
          emptyFreeVarEquiv16384 (fun _ => false)) : ℤ) = (2 : ℤ) ^ 16384
    rw [commonZeroCount_empty, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact hrec.trans hcount

end ComplexityTests.SparseDesignCounter
