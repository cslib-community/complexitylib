/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.BooleanAnalysis.SparseHermiteRecovery
import Mathlib.Tactic.NormNum

/-!
# Tests for `Complexity.Foundations.BooleanAnalysis.SparseHermiteRecovery`

Concrete nonvacuous checks and witnesses for:
1. §3.4 affine-Taylor to measurement-fiber jet identities (`targetPolynomial_eq_replacedSum`,
   `Design.map_eval_affineFactor_indicator`,
   `Design.coeff_taylor_targetPoly_eq_measurementFiberJet`,
   `Design.targetSum_eq_of_measurementFiberJet_jetOrder`),
2. §5.4 and Appendix B.2 Taylor-shift commutation and `JetTable.ofPolyVPolyZ` /
   `clearedParityJetTable_apply`,
3. §5.4–5.5 and Appendix B.3 unconditional Hermite–Cramer determinant recovery
   (`hermiteCramerNumerator_intPoly_eq_mul`, `hermiteCramerNumerator_intPoly_ediv_eq`,
   `emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount`,
   `emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount`, and
   `commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design`) on concrete equation systems and
   nonconstant `ReplacementDesign`s.
-/

@[expose] public noncomputable section

namespace Cslib.BitString.SparseHermiteRecoveryTests

open Finset Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules Cslib.LinearAlgebra Cslib.ReplacementCounting

/-! ### 1. §3.4 Concrete `ReplacementCounting.Design` and measurement-fiber jet recovery -/

/-- Scope of the single factor `0 : Fin 1` on `Fin 2`, selecting variable `0 : Fin 2`. -/
def toyDesignScope (_f : Fin 1) (_v : Fin 1) : Fin 2 := 0

/-- Concrete `Design (Fin 2) univ (fun _ => Fin 1) toyDesignScope 2 2 1 1 (1 / 2)` with `r = 2`,
`Q = 2`, `R = 1`, `D = 1`, `τ = 1 / 2`, nodes `nodeInt : Fin 2 → ℤ` (`1, 2`), and zero measurement
rows (`c_{t,g} = 0`), where replacement row `row f v i` is the constant Kronecker delta
`δ_{i, 0}`. -/
def toyCountingDesign :
    Design (Fin 2) (univ : Finset (Fin 1)) (fun _ => Fin 1) toyDesignScope 2 2 1 1 (1 / 2) where
  two_le_r := by decide
  one_le_D := by decide
  one_le_R := by decide
  R_lt_Q := by decide
  τ_pos := by norm_num
  τ_le_half := by norm_num
  nodes := nodeInt
  nodes_injective := nodeInt_injective 2
  nodes_ne_zero := nodeInt_ne_zero
  varGroup _t i := i
  card_varGroup_le t g := by
    have hcard : #{i : Fin 2 | i = g} = 1 := by
      fin_cases g <;> decide
    rw [hcard, Fintype.card_fin]
    decide
  factorGroup _f _t := 0
  numRows _t _g := 0
  sum_numRows_le _t := by norm_num
  matrix _t _g k := Fin.elim0 k
  matrix_support _t _g k := Fin.elim0 k
  row_l1_le _t _g k := Fin.elim0 k
  row _f _v i := if i = 0 then 1 else 0
  row_eval_zero _f _hf _v i := by
    unfold toyDesignScope
    split_ifs <;> simp
  row_natDegree_le _f _hf _v i := by
    split_ifs <;> simp
  kernel_zero _t _f _hf _v g hg _ξ hsupp _hker := by
    have h0 : g ≠ (0 : Fin 2) := hg
    have hsum :
        (∑ i : Fin 2,
          (if i = (0 : Fin 2) then (1 : Polynomial ℚ) else 0).eval (nodeInt _t : ℚ) * _ξ i) =
          _ξ 0 := by
      simp [Fin.sum_univ_two]
    rw [hsum]
    exact hsupp 0 h0.symm

/-- Factor family `Φ 0 = X 0` on `toyCountingDesign`, counting assignments `x : Fin 2 → Bool` with
`x 0 = true` (`targetSum = 2`). -/
def toyFactor (_f : Fin 1) : MvPolynomial (Fin 1) ℚ :=
  MvPolynomial.X 0

/-- Concrete verification of `targetPolynomial_eq_replacedSum`,
`Design.coeff_taylor_targetPoly_eq_measurementFiberJet`,
`Design.taylorJet_targetPoly_eq_measurementFiberJet`, and
`Design.targetSum_eq_of_measurementFiberJet_jetOrder` on `toyCountingDesign` (with explicit
expected value `targetSum = 2`). -/
example :
    targetSum (univ : Finset (Fin 1)) toyDesignScope toyFactor = 2 ∧
    toyCountingDesign.targetPoly toyFactor =
      Cslib.AffineTaylor.replacedSum (univ : Finset (Fin 1)) toyFactor
        (toyCountingDesign.rowIn ℚ) ∧
    (∀ (t : Fin 2) (j : ℕ), j ≤ 1 →
      (Polynomial.taylor (toyCountingDesign.nodes t : ℚ)
          (toyCountingDesign.targetPoly toyFactor)).coeff j =
        toyCountingDesign.measurementFiberJet toyFactor 1 t
          (toyCountingDesign.classicalRepresentative t) j) ∧
    targetSum (univ : Finset (Fin 1)) toyDesignScope toyFactor =
      ((Polynomial.hermiteMatrix toyCountingDesign.nodes (jetOrder (1 * 1) 2)).det : ℚ)⁻¹ •
        (((Polynomial.hermiteMatrix toyCountingDesign.nodes (jetOrder (1 * 1) 2)).map
          (Int.cast : ℤ → ℚ)).updateCol (⟨0, toyCountingDesign.Q_pos⟩, ⟨0, jetOrder_pos _ _⟩)
          (fun p => toyCountingDesign.measurementFiberJet toyFactor ((1 * 1) / 2) p.1
            (toyCountingDesign.classicalRepresentative p.1) p.2.1)).det := by
  have hsum : targetSum (univ : Finset (Fin 1)) toyDesignScope toyFactor = 2 := by
    have hbij : (univ : Finset (Fin 2 → Bool)) =
        {![false, false], ![false, true], ![true, false], ![true, true]} := by
      decide
    simp [targetSum, toyFactor, toyDesignScope, hbij]
    norm_num
  have hd : (liftedFactorProduct (univ : Finset (Fin 1)) toyFactor).totalDegree ≤ 1 := by
    refine (totalDegree_liftedFactorProduct_le (univ : Finset (Fin 1)) toyFactor).trans ?_
    simp [toyFactor]
  refine ⟨hsum, toyCountingDesign.targetPoly_eq_replacedSum toyFactor, ?_, ?_⟩
  · intro t j hj
    exact toyCountingDesign.coeff_taylor_targetPoly_eq_measurementFiberJet toyFactor t hj
      (toyCountingDesign.classicalRepresentative t)
      (toyCountingDesign.classicalRepresentative_valid t)
  · exact toyCountingDesign.targetSum_eq_of_measurementFiberJet_jetOrder ℚ toyFactor hd
      toyCountingDesign.classicalRepresentative toyCountingDesign.classicalRepresentative_valid

/-! ### 2. §5.4 & Appendix B.2–B.3 `JetTable` bridge and unconditional Hermite–Cramer recovery -/

/-- Concrete equation family on `Fin 3` with two equations:
- equation `0`: `x₀ + x₀ x₁ = 0` (monomials `{0}`, `{0, 1}`; scope `{0, 1}`),
- equation `1`: `x₁ x₂ + 1 = 0` (monomials `{1, 2}`, `∅`; scope `{1, 2}`).
Its satisfying assignments are `(false, true, true)` and `(true, true, true)` (`2` common zeros). -/
def sampleEqs : Fin 2 → Finset (Finset (Fin 3))
  | ⟨0, _⟩ => {{0}, {0, 1}}
  | ⟨1, _⟩ => {{1, 2}, ∅}

/-- Scope family of `sampleEqs`. -/
def sampleScope (i : Fin 2) : Finset (Fin 3) :=
  equationScope (sampleEqs i)

/-- Canonical `Q = 1, r = 1, A₀ = 0, R = 1, τ = 0` replacement design for any scope family on
`Fin n`. -/
def unitReplacementDesign {F : Type*} [Fintype F] {n : ℕ}
    (scope : F → Finset (Fin n)) : ReplacementDesign scope 1 1 0 1 0 :=
  let h := Fintype.card (ScopeIncidence scope)
  let eFin := Fintype.equivFin (ScopeIncidence scope)
  let place : ScopeIncidence scope → Fin h × AuxLabel 1 1 :=
    fun e => (eFin e, (fun _ => 0, fun _ => 0))
  have hinj : Function.Injective place := fun e₁ e₂ hEq =>
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

/-- Explicit `Q = 1, r = 2, A₀ = 0, R = 2, τ = 0` replacement design on
`withNeutralScope sampleScope` with nonconstant degree-`1` replacement rows. -/
def nonconstSampleVarAssign : Fin 3 → Fin 1 → Fin 2 :=
  fun v _ => if v.1 < 2 then 0 else 1

/-- Factor group schedule for `nonconstSampleDesign`. -/
def nonconstSampleFactorAssign : Fin 2 ⊕ Fin 3 → Fin 1 → Fin 2
  | Sum.inl _, _ => 0
  | Sum.inr _, _ => 1

/-- Copy index in `Fin 3` separating the `7` incidences of `withNeutralScope sampleScope`. -/
def nonconstSampleCopy (e : ScopeIncidence (withNeutralScope sampleScope)) : Fin 3 :=
  match e.1 with
  | Sum.inl 0 => if e.2.1 = 0 then 0 else 1
  | Sum.inl 1 => if e.2.1 = 1 then 2 else 0
  | Sum.inr 0 => 0
  | Sum.inr 1 => 1
  | Sum.inr 2 => 0

/-- Injective placement for `nonconstSampleDesign`. -/
def nonconstSamplePlace (e : ScopeIncidence (withNeutralScope sampleScope)) :
    Fin 3 × AuxLabel 1 2 :=
  (nonconstSampleCopy e,
    (nonconstSampleVarAssign (scopeVarOf (withNeutralScope sampleScope) e),
     nonconstSampleFactorAssign (scopeFactorOf (withNeutralScope sampleScope) e)))

theorem injective_nonconstSamplePlace : Function.Injective nonconstSamplePlace := by
  decide

/-- Concrete `Q = 1, r = 2, A₀ = 0, R = 2, τ = 0` replacement design on
`withNeutralScope sampleScope` with nonconstant degree-`1` replacement rows. -/
def nonconstSampleDesign :
    ReplacementDesign (withNeutralScope sampleScope) 1 2 0 2 0 where
  varAssign := nonconstSampleVarAssign
  factorAssign := nonconstSampleFactorAssign
  h := 3
  place := nonconstSamplePlace
  card_varGroup_le := by decide
  factorAssign_of_empty := by decide
  injective_place := injective_nonconstSamplePlace
  place_snd := fun _ => rfl
  h_mul_D_le := by decide
  total_measurement_rows_le := by
    have hmeas : #(measurementIndices 1 2 0 2) = 0 := by decide
    simp [hmeas]
  sum_abs_measurement_row_le :=
    sum_abs_varMeasurementMatrix_le 1 2 0 2 injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  natDegree_replacementRow_le :=
    natDegree_varReplacementRow_le 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  eval_replacementRow_zero :=
    eval_varReplacementRow_zero 1 2 0 2 injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  evalReplacementRow_nodePoint_eq_zero_of_kernel := fun e t g hg ξ hsupp hker =>
    evalVarReplacementRow_nodePoint_eq_zero_of_kernel 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope)) nonconstSampleVarAssign (fun _ => rfl) e t g hg
      ξ hsupp hker
  map_replacementRowScaledInt :=
    map_varReplacementRowScaledInt 1 2 0 2 nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope))
  sum_coeffNorm1_replacementRowScaledInt_le :=
    sum_coeffNorm1_varReplacementRowScaledInt_le (by decide) injective_nonconstSamplePlace
      (scopeVarOf (withNeutralScope sampleScope)) (by intro a ha; omega)

/-- Concrete verification of `clearedParityJetTable_apply` and
`taylor_univariateClearedParityTruncatedSum` on `sampleEqs` with `nonconstSampleDesign` (`R = 2`) at
evaluation point `t = nodeInt (0 : Fin 1) = 1`. -/
example (j : Fin 17) (s : Fin 4) :
    clearedParityJetTable (univ : Finset (Fin 2)) sampleEqs (commonDenom 1 2 : ℤ) 2 4 17
        (designReplacementScaledIntMap nonconstSampleDesign Sum.inl)
        (nodeInt (0 : Fin 1)) j s =
      (Polynomial.taylor (nodeInt (0 : Fin 1))
        (univariateClearedParityCoord (univ : Finset (Fin 2)) sampleEqs (commonDenom 1 2 : ℤ) 2 4
          (designReplacementScaledIntMap nonconstSampleDesign Sum.inl) s)).coeff j ∧
    Polynomial.taylor (nodeInt (0 : Fin 1))
        (univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) sampleEqs
          (commonDenom 1 2 : ℤ) 2 4
          (designReplacementScaledIntMap nonconstSampleDesign Sum.inl)) =
      univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) sampleEqs
        (commonDenom 1 2 : ℤ) 2 4
        (fun x i v =>
          Polynomial.taylor (nodeInt (0 : Fin 1))
            (designReplacementScaledIntMap nonconstSampleDesign Sum.inl x i v)) := by
  exact ⟨clearedParityJetTable_apply (univ : Finset (Fin 2)) sampleEqs (commonDenom 1 2 : ℤ) 2 4 17
      (designReplacementScaledIntMap nonconstSampleDesign Sum.inl) (nodeInt (0 : Fin 1)) j s,
    taylor_univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) sampleEqs
      (nodeInt (0 : Fin 1)) (commonDenom 1 2 : ℤ) 2 4
      (designReplacementScaledIntMap nonconstSampleDesign Sum.inl)⟩

/-- Concrete verification of `hermiteCramerNumerator_intPoly_eq_mul` and
`hermiteCramerNumerator_intPoly_ediv_eq` on `p = 3 + 5 * X : Polynomial ℤ` at
`nodeInt : Fin 2 → ℤ` with `J = 2` (`Q * J = 4 > 1`), recovering `p.eval 0 = 3`. -/
example :
    let p : Polynomial ℤ := C 3 + C 5 * X
    hermiteCramerNumerator (nodeInt (Q := 2)) (by decide) (by decide : 0 < 2)
        (fun i j => (Polynomial.taylor (nodeInt i) p).coeff j) =
      (Polynomial.hermiteMatrix (nodeInt (Q := 2)) 2).det * 3 ∧
    hermiteCramerNumerator (nodeInt (Q := 2)) (by decide) (by decide : 0 < 2)
        (fun i j => (Polynomial.taylor (nodeInt i) p).coeff j) /
          (Polynomial.hermiteMatrix (nodeInt (Q := 2)) 2).det = 3 := by
  intro p
  have hdeg : p.natDegree < 2 * 2 := by
    have hle : p.natDegree ≤ max (C (3 : ℤ)).natDegree (C (5 : ℤ) * X).natDegree :=
      Polynomial.natDegree_add_le _ _
    have h1 : (C (3 : ℤ)).natDegree = 0 := Polynomial.natDegree_C 3
    have h2 : (C (5 : ℤ) * X).natDegree ≤ 1 :=
      (Polynomial.natDegree_C_mul_le 5 X).trans Polynomial.natDegree_X_le
    omega
  have heval : p.eval 0 = 3 := by
    simp [p]
  refine ⟨?_, ?_⟩
  · rw [← heval]
    exact hermiteCramerNumerator_intPoly_eq_mul (nodeInt (Q := 2)) (by decide) (by decide) hdeg
  · rw [← heval]
    exact hermiteCramerNumerator_intPoly_ediv_eq (nodeInt_injective 2) (by decide) (by decide) hdeg

/-- Concrete values of `sparseParityJetOrder`:
for `k = 2, R = 2, Q = 1, m_eq = 2, ℓ = 4`, `(2 * 1) * (2 + 2 * 3) = 16`, so
`sparseParityJetOrder 2 2 1 2 4 = 16 / 1 + 1 = 17 > 16`. -/
example :
    sparseParityJetOrder 2 2 1 2 4 = 17 ∧
    0 < sparseParityJetOrder 2 2 1 2 4 ∧
    (2 * (2 - 1)) * (2 + 2 * (4 - 1)) < 1 * sparseParityJetOrder 2 2 1 2 4 := by
  refine ⟨by decide, sparseParityJetOrder_pos 2 2 1 2 4,
    lt_mul_sparseParityJetOrder 2 2 2 4 (by decide)⟩

/-- Unconditional Hermite–Cramer coordinate and truncated-sum recovery of `commonZeroCount` on
`sampleEqs` using `nonconstSampleDesign` (`Q = 1, r = 2, R = 2`, nonconstant degree-`1` replacement
rows) at precision `ℓ = 4` and canonical jet order `J = sparseParityJetOrder 2 2 1 2 4 = 17`:
both the coordinate sum and the single truncated-sum Cramer ratio modulo `2 ^ 4` equal `2`. -/
example :
    let J := sparseParityJetOrder 2 2 1 #(univ : Finset (Fin 2)) 4
    (∑ s ∈ range 4,
      hermiteCramerNumerator (nodeInt (Q := 1)) (by decide)
        (sparseParityJetOrder_pos 2 2 1 #(univ : Finset (Fin 2)) 4)
        (fun t j =>
          (Polynomial.taylor (nodeInt t)
            (univariateClearedParityCoord (univ : Finset (Fin 2)) sampleEqs
              (commonDenom 1 2 : ℤ) 2 4
              (designReplacementScaledIntMap nonconstSampleDesign Sum.inl) s)).coeff j) /
        (clearedProductDenom (commonDenom 1 2 : ℤ) 2 4 #(univ : Finset (Fin 2)) *
          (Polynomial.hermiteMatrix (nodeInt (Q := 1)) J).det)) % ((2 : ℤ) ^ 4) = 2 ∧
    (hermiteCramerNumerator (nodeInt (Q := 1)) (by decide)
        (sparseParityJetOrder_pos 2 2 1 #(univ : Finset (Fin 2)) 4)
        (fun t j =>
          (Polynomial.taylor (nodeInt t)
            (univariateClearedParityTruncatedSum (univ : Finset (Fin 2)) sampleEqs
              (commonDenom 1 2 : ℤ) 2 4
              (designReplacementScaledIntMap nonconstSampleDesign Sum.inl))).coeff j) /
      (clearedProductDenom (commonDenom 1 2 : ℤ) 2 4 #(univ : Finset (Fin 2)) *
        (Polynomial.hermiteMatrix (nodeInt (Q := 1)) J).det)) % ((2 : ℤ) ^ 4) = 2 := by
  intro J
  have hcount : (commonZeroCount (univ : Finset (Fin 2)) sampleEqs : ℤ) = 2 := by decide
  refine ⟨?_, ?_⟩
  · rw [emod_sum_hermiteCramerNumerator_design_eq_commonZeroCount nonconstSampleDesign Sum.inl
      (univ : Finset (Fin 2)) sampleEqs (by decide)
      (sparseParityJetOrder_pos 2 2 1 #(univ : Finset (Fin 2)) 4)
      (by decide) (by decide)
      (lt_mul_sparseParityJetOrder 2 2 #(univ : Finset (Fin 2)) 4 (by decide))]
    exact hcount
  · rw [emod_hermiteCramerNumerator_truncatedSum_design_eq_commonZeroCount nonconstSampleDesign
      Sum.inl (univ : Finset (Fin 2)) sampleEqs (by decide)
      (sparseParityJetOrder_pos 2 2 1 #(univ : Finset (Fin 2)) 4)
      (by decide) (by decide)
      (lt_mul_sparseParityJetOrder 2 2 #(univ : Finset (Fin 2)) 4 (by decide))]
    exact hcount

/-- Explicit equivalence between the unbranched variables `{0, 2}` (`univ \ {1}` in `Fin 3`) and
`Fin 2`. -/
def sampleFreeVarEquiv : ↥((univ : Finset (Fin 3)) \ ({1} : Finset (Fin 3))) ≃ Fin 2 where
  toFun v := if v.1 = 0 then 0 else 1
  invFun i := if i = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- Checked client of `commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design` on `sampleEqs`
with branching set `S = {1}` (`branchPrecision 3 = 4`): summing the per-branch Hermite–Cramer
determinant quotients modulo `2 ^ 4` across `b ∈ branchAssignments {1}` recovers the exact count
`2`. -/
example :
    let ℓ := branchPrecision 3
    let J := sparseParityJetOrder 2 1 1 #(univ : Finset (Fin 2)) ℓ
    ∑ b ∈ branchAssignments ({1} : Finset (Fin 3)),
      (hermiteCramerNumerator (nodeInt (Q := 1)) (by decide)
        (sparseParityJetOrder_pos 2 1 1 #(univ : Finset (Fin 2)) ℓ)
        (fun t j =>
          (Polynomial.taylor (nodeInt t)
            (univariateClearedParityTruncatedSum (univ : Finset (Fin 2))
              (fun i => relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b
                (sampleEqs i))
              (commonDenom 1 1 : ℤ) 2 ℓ
              (designReplacementScaledIntMap
                (unitReplacementDesign
                  (withNeutralScope fun i =>
                    equationScope
                      (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b
                        (sampleEqs i))))
                Sum.inl))).coeff j) /
        (clearedProductDenom (commonDenom 1 1 : ℤ) 2 ℓ #(univ : Finset (Fin 2)) *
          (Polynomial.hermiteMatrix (nodeInt (Q := 1)) J).det)) % ((2 : ℤ) ^ ℓ) = 2 := by
  intro ℓ J
  have hrec := commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design
    ({1} : Finset (Fin 3)) sampleFreeVarEquiv (univ : Finset (Fin 2)) sampleEqs (k := 2)
    (fun b => withNeutralScope fun i =>
      equationScope
        (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i)))
    (fun b => unitReplacementDesign
      (withNeutralScope fun i =>
        equationScope
          (relabelRestrictedMonomials ({1} : Finset (Fin 3)) sampleFreeVarEquiv b (sampleEqs i))))
    (fun _ => Sum.inl)
    (by decide) (by decide)
  have hcount : (commonZeroCount (univ : Finset (Fin 2)) sampleEqs : ℤ) = 2 := by decide
  exact hrec.symm.trans hcount

end Cslib.BitString.SparseHermiteRecoveryTests
