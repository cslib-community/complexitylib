/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.CommonCountingAccum
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Regression tests for `Complexity.Computability.PolyTime.CommonCountingAccum`. -/

namespace ComplexityTests.CommonCountingAccum

open Cslib Cslib.BitString Cslib.CommonCountingAccum Polynomial Turing.MultiTapeTM

example : ofJetTable (toJetTable 2 3 [[1, -2, 3], [0, 4, -5]]) = [[1, -2, 3], [0, 4, -5]] ∧
    ofJetTable (0 : JetTable 0 3 ℤ) = [] ∧ ofJetTable (0 : JetTable 2 0 ℤ) = [[], []] :=
  ⟨ofJetTable_toJetTable ⟨rfl, by decide +kernel⟩, rfl, ofJetTable_zero_cols 0⟩

example (j u : ℕ) : (encList (encList encIntBin) [[1, -2, 3], [0, 4, -5]]).length ≤
      2 * (2 * (3 * (2 * (15 : ℕ).size + 3)) + 1) ∧
    (rowEntry (prodJet 2 3 [[[1, 2, -1], [3, 0, 4]], [[2, -3, 1], [-1, 5, 2]]]) j u).natAbs.size ≤
      1 + 2 * (3 + (2 * 3).size) :=
  ⟨length_encJetRows_le_of_l1Norm_le (J := 2) (ℓ := 3) ⟨rfl, by decide +kernel⟩
    (by rw [l1Norm_toJetTable_eq (J := 2) (ℓ := 3) ⟨rfl, by decide +kernel⟩]; decide +kernel),
   size_natAbs_rowEntry_prodJet_le (b := 3) (by decide +kernel) j u⟩

example : let F₁ : JetRows := [[1, 2, -1], [3, 0, 4]]; let F₂ : JetRows := [[2, -3, 1], [-1, 5, 2]]
    prodJet 2 3 [F₁, F₂, [[1, 1, 0], [0, -1, 2]]] = [[2, 3, -6], [5, -3, 21]] ∧
      prodJet 2 3 [] = [[1, 0, 0], [0, 0, 0]] ∧
      weightedProdJet 2 3 (-2) [F₁, F₂] = [[-4, -2, 14], [-10, 12, -48]] ∧
      weightedProdJet 2 3 0 [F₁, F₂] = [[0, 0, 0], [0, 0, 0]] := by decide +kernel

private def testGroupEval (p : ℤ × (ℕ × List Bool)) : JetRows :=
  let b (k : ℕ) : ℤ := if p.2.2.getD k false then 1 else 0
  [[p.1 + b 0 + 2 * b 1, b 0 - b 1], [1 + b 1, b 0 * b 1]]

example : streamGroupJetSum testGroupEval 2 2 0 3 = [[3, 0], [1, 0]] ∧
    streamGroupJetSumPrefix testGroupEval 2 2 2 2 3 = [[7, 1], [2, 0]] ∧
    streamGroupJetSum testGroupEval 2 2 2 3 = [[18, 0], [6, 1]] := by decide +kernel

example : ofJetTable (∑ x : ∀ g : Fin 2, BitString (![1, 2] g),
      ∏ g : Fin 2, toJetTable 2 2 (testGroupEval (3 + g.1, (![1, 2] g, List.ofFn (x g))))) =
    [[154, 22], [86, 13]] := by
  rw [← toJetTable_prodJet_streamGroupJetSum ![1, 2] (fun g p => testGroupEval (p.1 + g.1, p.2)) 3,
    ofJetTable_toJetTable (isTableShape_prodJet 2 2 _)]
  decide +kernel

private def testRoundJet (t : ℤ) (idx : ℕ) (g : Fin 2) : JetRows :=
  if idx = 0 then if g.1 = 0 then [[-2 + t, 4], [1, 0]] else [[4 - t, t], [-1, 1]]
  else if g.1 = 0 then [[2 + t, 0], [1, 0]] else [[2, 6 - t], [0, -1]]

private def testRoundEval (p : ℤ × ℕ) : ℤ × List JetRows :=
  (if p.2 = 0 then 3 else -3, List.ofFn (testRoundJet p.1 p.2))

example : let j₁ := streamOuterJetAccum testRoundEval 2 2 2 1
    let j₂ := streamOuterJetAccum testRoundEval 2 2 2 2
    streamOuterJetAccum testRoundEval 2 2 0 1 = [[0, 0], [0, 0]] ∧
      j₁ = [[-27, -12], [6, -18]] ∧ j₂ = [[-24, -24], [0, -6]] ∧
      extractAllCoordNodeJets 2 2 [j₁, j₂] = [[[-27, 6], [-24, 0]], [[-12, -18], [-24, -6]]] ∧
      Cslib.Circuits.Rational.hermiteRecoverZero [1, 2] 2 4 [[-27, 6], [-24, 0]] = -9 ∧
      Cslib.Circuits.Rational.hermiteRecoverZero [1, 2] 2 4 [[-12, -18], [-24, -6]] = 3 ∧
      recoverOuterJetSumModPowTwo [1, 2] 2 2 4 [j₁, j₂] = 2 ∧
      recoverOuterJetSumModPowTwo [1, 2] 2 2 0 [j₁, j₂] = 0 := by decide +kernel

private noncomputable def testRoundPoly (idx : ℕ) (g : Fin 2) : Polynomial (Polynomial ℚ) :=
  if idx = 0 then
    if g.1 = 0 then C (C (-1) + C (1 / 2) * X) + C (C 2) * X
    else C (C 2 - C (1 / 2) * X) + C (C (1 / 2) * X) * X
  else if g.1 = 0 then C (C 1 + C (1 / 2) * X) + C 0 * X
  else C (C 1) + C (C 3 - C (1 / 2) * X) * X

private theorem coeff_linear_mul (a₁ b₁ a₂ b₂ : Polynomial ℚ) (u : Fin 2) :
    ((C a₁ + C b₁ * X) * (C a₂ + C b₂ * X)).coeff u =
      if u.1 = 0 then a₁ * a₂ else a₁ * b₂ + b₁ * a₂ := by
  fin_cases u
  · simp only [↓reduceIte, Nat.one_ne_zero, mul_add, add_mul, mul_assoc, X_mul_C, coeff_add,
      coeff_C_mul, coeff_X_mul_zero, coeff_X, coeff_C]; ring
  · change ((C a₁ + C b₁ * X) * (C a₂ + C b₂ * X)).coeff (0 + 1) = a₁ * b₂ + b₁ * a₂
    simp only [↓reduceIte, Nat.one_ne_zero, mul_add, add_mul, mul_assoc, X_mul_C, coeff_add,
      coeff_C_mul, coeff_X_mul, coeff_C_succ, zero_add, coeff_X]; ring
private theorem coeff_sum_testRoundPoly (u : Fin 2) :
    (∑ idx ∈ Finset.range 2, (if idx = 0 then (3 : ℤ) else -3) •
      ∏ g : Fin 2, testRoundPoly idx g).coeff u =
    (3 : ℤ) • ((testRoundPoly 0 0 * testRoundPoly 0 1).coeff u) +
      (-3 : ℤ) • ((testRoundPoly 1 0 * testRoundPoly 1 1).coeff u) := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    Fin.prod_univ_two, ↓reduceIte, Nat.one_ne_zero, coeff_add, coeff_smul]

theorem recover_outer_stream_mod4 : recoverOuterJetSumModPowTwo [1, 2] 2 2 ((2 : ℤ) ^ 2)
    (List.ofFn fun i : Fin ([1, 2] : List ℤ).length =>
      streamOuterJetAccum testRoundEval 2 2 2 ([1, 2][i])) = 2 := by
  refine recoverOuterJetSumModPowTwo_streamOuterJetAccum_eq (r := 2) (m := 2) (T_rounds := 2)
    (by decide) (by decide) testRoundEval (fun i => [1, 2][i]) (fun i => if i = 0 then 3 else -3)
    (fun _ => ![1, 1]) testRoundPoly (fun i idx g => testRoundJet [1, 2][i] idx g) ![-9, 3]
    (fun _ _ _ => rfl) (fun _ _ => by decide) (fun i idx hidx g => ?_) (fun u => ?_) (fun u => ?_)
    (by decide) (by decide) ⟨-2, by decide⟩
  · ext j u; fin_cases i <;> rcases (by omega : idx = 0 ∨ idx = 1) with rfl | rfl <;>
      fin_cases g <;> fin_cases j <;> fin_cases u
    all_goals
      simp only [testRoundPoly, testRoundJet, JetTable.coe_zsmul, zsmul_eq_mul,
        taylorOuterVJet_apply, JetTable.castRingHom_apply, toJetTable_apply, ↓reduceIte,
        Nat.one_ne_zero, coeff_add, coeff_C_mul, coeff_X, coeff_C, taylor_apply, add_comp,
        sub_comp, mul_comp, C_comp, X_comp, rowEntry, List.getD, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some]
      ring_nf; norm_num [coeff_add, coeff_sub, coeff_C_mul, coeff_X, coeff_C, coeff_one]
  · rw [coeff_sum_testRoundPoly]
    simp only [testRoundPoly, Fin.val_zero, Fin.val_one, ↓reduceIte, Nat.one_ne_zero]
    rw [coeff_linear_mul, coeff_linear_mul]; fin_cases u <;> (
      simp only [↓reduceIte, Nat.one_ne_zero, zsmul_eq_mul, Int.cast_neg, Int.cast_ofNat]
      change _ < 4; compute_degree!)
  · rw [coeff_sum_testRoundPoly]
    simp only [testRoundPoly, Fin.val_zero, Fin.val_one, ↓reduceIte, Nat.one_ne_zero]
    rw [coeff_linear_mul, coeff_linear_mul]; fin_cases u <;> norm_num [Matrix.cons_val_zero,
      Matrix.cons_val_one, zsmul_eq_mul, eval_add, eval_sub, eval_neg, eval_mul, eval_C, eval_X]

example : IsComputable
    (fun d : ℕ => streamGroupJetSum (fun q : ℤ × (ℕ × List Bool) => constJet q.2.1 2 q.1) 2 2 d 5)
    encUnary (encList (encList encIntBin)) ∧
    IsComputable (fun T : ℕ => streamOuterJetAccum (fun q : ℤ × ℕ => (q.1, [])) 2 2 T 1)
      encNat (encList (encList encIntBin)) := by
  have hc₅ : ComputableInPolyTime (fun _ : ℕ => (5 : ℤ)) encUnary encIntBin := by fun_prop
  have hc₁ : ComputableInPolyTime (fun _ : ℕ => (1 : ℤ)) encNat encIntBin := by fun_prop
  exact ⟨(groupJetSumCertificate (.ofPolyTime (by fun_prop)) (.ofPolyTime (by fun_prop))
      (.ofPolyTime (by fun_prop)) (.ofPolyTime hc₅) (.ofPolyTime (by fun_prop))).isComputable,
    (outerJetAccumCertificate (.ofPolyTime (by fun_prop)) (.ofPolyTime (by fun_prop))
      (.ofPolyTime (by fun_prop)) (.ofPolyTime hc₁) (.ofPolyTime (by fun_prop))).isComputable⟩

example : ComputableInPolySpace (fun p : ((ℕ × ℕ) × ℕ) × JetRows =>
      streamGroupJetSum (fun q : JetRows × (ℕ × List Bool) => q.1) p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encUnary) encUnary) (encList (encList encIntBin)))
    (encList (encList encIntBin)) ∧
    ComputableInPolySpace (fun p : ((ℕ × ℕ) × ℕ) × (ℤ × List JetRows) =>
      streamOuterJetAccum (fun q : (ℤ × List JetRows) × ℕ => q.1) p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encUnary) encNat)
      (encPair encIntBin (encList (encList (encList encIntBin))))) (encList (encList encIntBin)) ∧
    ComputableInPolyTime (fun q : ((List ℤ × (ℕ × ℕ)) × ℤ) × List JetRows =>
      recoverOuterJetSumModPowTwo q.1.1.1 q.1.1.2.1 q.1.1.2.2 q.1.2
        [prodJet q.1.1.2.1 q.1.1.2.2 q.2, weightedProdJet q.1.1.2.1 q.1.1.2.2 q.1.2
          (extractAllCoordNodeJets q.1.1.2.2 q.1.1.2.1 q.2)])
    (encPair (encPair (encPair (encList encIntBin) (encPair encUnary encUnary)) encIntBin)
      (encList (encList (encList encIntBin)))) encIntBin := ⟨by fun_prop, by fun_prop, by fun_prop⟩

example (factors : ℕ → List JetRows)
    (_hf : ComputableInPolyTime factors encNat (encList (encList (encList encIntBin)))) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun J : ℕ => prodJet J 1 (factors J))
      encNat (encList (encList encIntBin)) := by fun_prop (config := { maxTransitionDepth := 1 })
  trivial

end ComplexityTests.CommonCountingAccum
