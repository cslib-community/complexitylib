/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.PolyTime.CNF.ClauseJetEval
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Concrete tests for `SatisfactionPolynomial`, `IntJet`, and `ClauseJetEval`

Kernel-checked witnesses exercising:
- the manuscript §2.2 example `x₀ ∨ ¬x₁ ∨ x₂`, empty clause `[]`, empty formula `[]`, duplicate
  and tautological clauses, and undeclared variable extensions;
- `replacementCountPoly` with a nontrivial degree-`1` replacement verifying `H(0) = #F` and degree
  bound `deg H ≤ M · R_deg`;
- `Cslib.IntJet` and `evalClauseClearedJet` / `evalGroupClauseProductJet` with short/overlong input
  lists, nontrivial `z ^ 4` truncation, `δ = 0` sanity check, rational `clauseSatPoly`/`cnfSatPoly`
  congruence, bit-length bounds, and `by fun_prop` polytime composition.
-/

open scoped BigOperators
open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM

namespace SatisfactionPolynomialTests

private def exClause : Clause (Fin 3) := [(0, true), (1, false), (2, true)]

example : clauseSatPoly ℤ exClause =
    1 - (1 - MvPolynomial.X 0) * MvPolynomial.X 1 * (1 - MvPolynomial.X 2) := by
  unfold clauseSatPoly exClause
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, literalPoly_pos,
    literalPoly_neg]
  ring

example : MvPolynomial.eval (bitPoint ![false, true, false]) (clauseSatPoly ℤ exClause) = 0 ∧
    MvPolynomial.eval (bitPoint ![true, true, false]) (clauseSatPoly ℤ exClause) = 1 := by
  rw [eval_clauseSatPoly_bitPoint, eval_clauseSatPoly_bitPoint]; decide

private abbrev extOn {V : Type*} [DecidableEq V] (S : Finset V) (σ : S → Bool) (v : V) : Bool :=
  if h : v ∈ S then σ ⟨v, h⟩ else false

private abbrev univFin (n : ℕ) : Finset (Fin n) := Finset.univ

example : (∑ σ : univFin 3 → Bool,
    MvPolynomial.eval (bitPoint (extOn (univFin 3) σ))
      (cnfSatPoly ℤ ([exClause] : CNF (Fin 3)))) = 7 := by
  rw [sum_eval_cnfSatPoly_eq_modelCountOn]
  exact congrArg Nat.cast (by decide : CNF.modelCountOn ([exClause] : CNF (Fin 3)) (univFin 3) = 7)

-- Empty clause `[]` gives count `0`; empty formula `[]` on `3` declared variables gives `2^3 = 8`.
example : (∑ σ : Finset.range 2 → Bool, MvPolynomial.eval (bitPoint (extOn (Finset.range 2) σ))
      (cnfSatPoly ℤ ([[]] : CNF ℕ))) = 0 ∧
    (∑ σ : Finset.range 3 → Bool, MvPolynomial.eval (bitPoint (extOn (Finset.range 3) σ))
      (cnfSatPoly ℤ ([] : CNF ℕ))) = 8 := by
  rw [sum_eval_cnfSatPoly_eq_modelCountOn, sum_eval_cnfSatPoly_eq_modelCountOn]
  exact ⟨congrArg Nat.cast (by decide : CNF.modelCountOn ([[]] : CNF ℕ) (Finset.range 2) = 0),
    congrArg Nat.cast (by decide : CNF.modelCountOn ([] : CNF ℕ) (Finset.range 3) = 8)⟩

-- Duplicate literal `x₀ ∨ x₀` (`2 X₀ - X₀²`) and tautological clause `x₀ ∨ ¬x₀`.
example : clauseSatPoly ℤ ([(0, true), (0, true)] : Clause (Fin 2)) =
      2 * MvPolynomial.X 0 - MvPolynomial.X 0 ^ 2 ∧
    clauseSatPoly ℤ ([(0, true), (0, false)] : Clause (Fin 2)) =
      1 - (1 - MvPolynomial.X 0) * MvPolynomial.X 0 := by
  unfold clauseSatPoly
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, literalPoly_pos,
    literalPoly_neg]
  exact ⟨by ring, by ring⟩

example : (∑ σ : univFin 2 → Bool, MvPolynomial.eval (bitPoint (extOn (univFin 2) σ))
      (cnfSatPoly ℤ ([[(0, true), (0, true)]] : CNF (Fin 2)))) = 2 ∧
    (∑ σ : univFin 2 → Bool, MvPolynomial.eval (bitPoint (extOn (univFin 2) σ))
      (cnfSatPoly ℤ ([[(0, true), (0, false)]] : CNF (Fin 2)))) = 4 ∧
    (∑ σ : Finset.range 2 → Bool, MvPolynomial.eval (bitPoint (extOn (Finset.range 2) σ))
      (cnfSatPoly ℤ ([[(2, false)]] : CNF ℕ))) = 4 := by
  rw [sum_eval_cnfSatPoly_eq_modelCountOn, sum_eval_cnfSatPoly_eq_modelCountOn,
    sum_eval_cnfSatPoly_eq_modelCountOn]
  exact ⟨congrArg Nat.cast
      (by decide : CNF.modelCountOn ([[(0, true), (0, true)]] : CNF (Fin 2)) (univFin 2) = 2),
    congrArg Nat.cast
      (by decide : CNF.modelCountOn ([[(0, true), (0, false)]] : CNF (Fin 2)) (univFin 2) = 4),
    congrArg Nat.cast (by decide : CNF.modelCountOn ([[(2, false)]] : CNF ℕ) (Finset.range 2) = 4)⟩

private def repPhi : CNF (Fin 2) := [[(0, true), (1, false)]]

private noncomputable def linRep (e : Fin repPhi.length) (j : Fin repPhi[e].length)
    (i : Fin 2) : Polynomial ℤ :=
  if i = repPhi[e][j].1 then 1 + Polynomial.X else Polynomial.X

example : (replacementCountPoly repPhi Finset.univ linRep).eval 0 = 3 ∧
    (replacementCountPoly repPhi Finset.univ linRep).natDegree ≤ 2 := by
  refine ⟨?_, (natDegree_replacementCountPoly_le repPhi Finset.univ linRep 1
    fun e j i _ => ?_).trans (by decide)⟩
  · rw [eval_zero_replacementCountPoly repPhi Finset.univ linRep]
    · exact congrArg Nat.cast (by decide : CNF.modelCountOn repPhi Finset.univ = 3)
    · intro e j i _; dsimp only [linRep]; split_ifs <;> simp
  · dsimp only [linRep]; split_ifs
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) Polynomial.natDegree_X_le)
    · exact Polynomial.natDegree_X_le

private def testVarJet : Fin 2 → List ℤ
  | 0 => [2, 1]
  | 1 => [3, -1, 1, 0]

private def testPhi : CNF (Fin 2) := [[(0, true), (1, false)], [(0, false)]]

private def testClauses : List (List (Bool × List ℤ)) :=
  testPhi.map fun C => C.map fun l => (l.2, testVarJet l.1)

example : evalClauseClearedJet 4 6 (testPhi[0].map fun l => (l.2, testVarJet l.1)) =
      [24, 7, -5, 1] ∧
    evalGroupClauseProductJet 4 6 testClauses = [96, 4, -27, 9] ∧
    evalClauseClearedJet 2 0 [(true, [3, 1, 9])] = [3, 1] := by decide

example :
    ((Polynomial.X : Polynomial ℚ) ^ 4 ∣
      (Polynomial.ofCoeffList
          (evalClauseClearedJet 4 6 (testPhi[0].map fun l => (l.2, testVarJet l.1)))).map
          (Int.castRingHom ℚ) -
        Polynomial.C (6 : ℚ) ^ testPhi[0].length * MvPolynomial.aeval
          (fun v => (Polynomial.ofCoeffList (testVarJet v)).map (Int.castRingHom ℚ) *
            Polynomial.C ((6 : ℚ)⁻¹)) (clauseSatPoly ℚ testPhi[0])) ∧
    ((Polynomial.X : Polynomial ℚ) ^ 4 ∣
      (Polynomial.ofCoeffList (evalGroupClauseProductJet 4 6
          (testPhi.map fun C => C.map fun l => (l.2, testVarJet l.1)))).map (Int.castRingHom ℚ) -
        Polynomial.C (6 : ℚ) ^ testPhi.totalLiterals * MvPolynomial.aeval
          (fun v => (Polynomial.ofCoeffList (testVarJet v)).map (Int.castRingHom ℚ) *
            Polynomial.C ((6 : ℚ)⁻¹)) (cnfSatPoly ℚ testPhi)) ∧
    (encIntBin ((evalGroupClauseProductJet 4 6 testClauses).getD 2 0)).length ≤ 20 := by
  refine ⟨X_pow_dvd_evalClauseClearedJet_clauseSatPoly 4 (by decide) testVarJet testPhi[0],
    X_pow_dvd_evalGroupClauseProductJet_cnfSatPoly 4 (by decide) testVarJet testPhi, ?_⟩
  have hB : ∀ C ∈ testClauses, ∀ lit ∈ C, (Polynomial.ofCoeffList lit.2).coeffNorm1 ≤ 5 := by
    simpa only [Polynomial.coeffNorm1_ofCoeffList] using
      (by decide : ∀ C ∈ testClauses, ∀ lit ∈ C, (lit.2.map Int.natAbs).sum ≤ 5)
  have h1 := length_encIntBin_getD_evalGroupClauseProductJet_le 4 6 testClauses 5 hB 2
  have hlen : testClauses.length = 2 := rfl
  have hsum : (testClauses.map List.length).sum = 3 := rfl
  have hsz : ((6 : ℤ).natAbs + 5).size ≤ 4 := Nat.size_le.mpr (by decide)
  exact h1.trans (by rw [hlen, hsum]; omega)

-- Plain `ComputableInPolyTime` composition across `ParityFactorEval`, `IntJet`, and `ClauseJetEval`
-- via `fun_prop`.
example : ComputableInPolyTime
    (fun p : (ℕ × ℤ) × (List (Bool × List ℤ) × List (List (Bool × List ℤ))) =>
      Cslib.mulZJet p.1.1 (IntJet.add p.1.1 (evalClauseClearedJet p.1.1 p.1.2 p.2.1)
        (IntJet.sub p.1.1 (Cslib.truncZJet p.1.1 [p.1.2]) (IntJet.subConst p.1.1 p.1.2 [1, -1])))
        (evalGroupClauseProductJet p.1.1 p.1.2 p.2.2))
    (encPair (encPair encUnary encIntBin)
      (encPair (encList (encPair encBool (encList encIntBin)))
        (encList (encList (encPair encBool (encList encIntBin))))))
    (encList encIntBin) := by fun_prop

end SatisfactionPolynomialTests
