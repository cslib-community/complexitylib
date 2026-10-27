/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

import Complexity.Computability.PolyTime.SparseMonomialJet
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Concrete tests for Stage-1 sparse monomial $z$-jet substitution and Taylor shift

Nonvacuous computational, specification, and `fun_prop` synthesis tests for
`Cslib.taylorShiftZJet`, `Cslib.evalBaselineAt`, `Cslib.evalTaylorCorrectionZJet`,
`Cslib.evalAffineInputZJet`, `Cslib.evalAffineInputZJetTable`, `Cslib.evalClearedMonomialJet`,
`Cslib.evalClearedEquationJet`, and `Cslib.evalEquationParityFactorJet`.
-/

namespace Cslib.SparseMonomialJetTests

open Turing.MultiTapeTM

/-! ### 1. `taylorShiftZJet` across boundary (`J = 0`, `[]`), truncation, padding, and `t < 0` -/

example :
    taylorShiftZJet 0 4 [2, -3, 1] = [] ∧
      taylorShiftZJet 2 4 [2, -3, 1] = [6, 5] ∧
      taylorShiftZJet 4 4 [2, -3, 1] = [6, 5, 1, 0] ∧
      taylorShiftZJet 3 (-2) [2, -3, 1] = [12, -7, 1] ∧
      taylorShiftZJet 3 5 [] = [0, 0, 0] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

example : (Polynomial.taylor 4 (Polynomial.ofCoeffList [2, -3, 1])).coeff 1 = 5 :=
  (getD_taylorShiftZJet_of_lt (J := 3) (by decide) 4 [2, -3, 1]).symm

/-! ### 2. Affine-Taylor input `z`-jet (`evalAffineInputZJet` & `AffineTaylor.affineInput`) -/

example :
    let rowCoeffs : List (List ℤ) := [[1, 2], [-3, 0, 1], [4, -1]]
    let idRow0 : List (List ℤ) := [[6], [], []]
    let U := [false, true, true]; let x := [true, false, true]
    evalBaselineAt 2 rowCoeffs x = 7 ∧ evalTaylorCorrectionZJet 3 2 rowCoeffs U = [0, 3, 1] ∧
      evalAffineInputZJet 3 2 rowCoeffs U x = [7, 3, 1] ∧
      evalAffineInputZJet 0 2 rowCoeffs U x = [] ∧
      evalAffineInputZJet 3 0 idRow0 [false, false, false] [true, false, true] = [6, 0, 0] ∧
      evalAffineInputZJetTable 3 2 [rowCoeffs, idRow0] U x = [[7, 3, 1], [6, 0, 0]] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    let row : List (List ℤ) := [[1, 2], [-3, 0, 1], [4, -1]]
    let U := [false, true, true]; let x := [true, false, true]
    let p := (Cslib.AffineTaylor.affineInput (fun i : Fin row.length =>
        Polynomial.ofCoeffList (row.getD i [])) 2 (fun i : Fin row.length => x.getD i false)).map
      (MvPolynomial.eval fun i : Fin row.length => Cslib.BitString.bitVal ℤ (U.getD i false))
    p.coeff 0 = 7 ∧ p.coeff 1 = 3 ∧ p.coeff 2 = 1 :=
  ⟨(getD_evalAffineInputZJet_eq_coeff_affineInput (J := 3) (by decide) 2 _ _ _).symm,
    (getD_evalAffineInputZJet_eq_coeff_affineInput (J := 3) (by decide) 2 _ _ _).symm,
    (getD_evalAffineInputZJet_eq_coeff_affineInput (J := 3) (by decide) 2 _ _ _).symm⟩

/-! ### 3. Stage-1 cleared monomial/equation jets and composite Stage-2 factor table -/

example :
    let varJets : List (List ℤ) := [[2, 1, 0], [0, 3, 0], [2, -1, 0]]
    let eq : List (List ℕ) := [[], [0, 2], [1]]
    evalClearedMonomialJet 3 2 2 varJets [] = [4, 0, 0] ∧
      evalClearedMonomialJet 3 2 2 varJets [0, 2] = [4, 0, -1] ∧
      evalClearedMonomialJet 3 2 2 varJets [1] = [0, 6, 0] ∧
      evalClearedEquationJet 3 2 2 varJets eq = [8, 6, -1] ∧
      Cslib.Complexity.evalMonomialList eq (fun v => decide (v = 0 ∨ v = 2)) = false ∧
      evalEquationParityFactorJet 3 2 2 2 varJets eq = [[-64, 384], [-96, 1248], [16, 1088]] ∧
      ((evalEquationParityFactorJet 3 2 2 2 varJets eq).getD 0 []).sum =
        (2 ^ 2) ^ 3 * evalParityAmplifier 2 2 ∧
      Int.emod (evalParityAmplifier 2 2) 4 = 1 ∧
      jetL1Norm (evalEquationParityFactorJet 3 2 2 2 varJets eq) = 2896 ∧
      evalEquationParityFactorJet 1 1 1 0 [[1]] [[0]] = [[-1]] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

example :
    IsTableShape 3 2
      (evalEquationParityFactorJet 3 2 2 2 [[2, 1, 0], [0, 3, 0], [2, -1, 0]] [[], [0, 2], [1]]) :=
  isTableShape_evalEquationParityFactorJet 3 2 2 2 _ _

example :
    let rawCoeffs : List (List ℤ) := [[1, 1], [-3, 3], [3, -1]]
    let θ₀ : ℕ → Polynomial ℤ := fun v => Polynomial.ofCoeffList (rawCoeffs.getD v [])
    let eq : List (List ℕ) := [[], [0, 2], [1]]
    let P := Cslib.BitString.parityFactorCleared 2 (Polynomial.C ((2 : ℤ) ^ 2))
      (Cslib.BitString.clearedMonomialSumPoly 2 2 θ₀ (eq.map List.toFinset).toFinset)
    (Polynomial.taylor 1 (P.coeff 1)).coeff 1 = 1248 := by
  let rawCoeffs : List (List ℤ) := [[1, 1], [-3, 3], [3, -1]]
  let varJets := rawCoeffs.map (taylorShiftZJet 3 1)
  have heq : Cslib.Complexity.IsCanonicalEquation [[], [0, 2], [1]] :=
    ⟨by decide, fun m hm => by unfold Cslib.Complexity.IsCanonicalMonomial; decide +revert⟩
  have hdeg : ∀ mon ∈ ([[], [0, 2], [1]] : List (List ℕ)), mon.length ≤ 2 := by decide
  have hθ : ∀ mon ∈ ([[], [0, 2], [1]] : List (List ℕ)), ∀ v ∈ mon, ∀ i < 3,
      rowEntry varJets v i =
        (Polynomial.taylor 1 (Polynomial.ofCoeffList (rawCoeffs.getD v []))).coeff i := by
    intro mon hmon v hv i hi
    have hmap : varJets.getD v [] = taylorShiftZJet 3 1 (rawCoeffs.getD v []) := by decide +revert
    rw [rowEntry, hmap, getD_taylorShiftZJet_of_lt hi]
  exact (evalEquationParityFactorJet_entry_eq_taylor_parityFactorCleared
    (J := 3) (k := 2) (j := 1) (by decide) 2 1 1 2 heq hdeg hθ).symm.trans rfl

/-! ### 4. Compositional `fun_prop` synthesis (both `encBits` and `encList encBool`) -/

example :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × ℕ) × (ℤ × ℤ)) ×
          ((List Bool × List Bool) × (List (List (List ℤ)) × List (List ℕ))) =>
        let J := p.1.1.1.1 + 1; let ℓ := p.1.1.1.2 + 1; let k := p.1.1.2
        let varJets := evalAffineInputZJetTable J p.1.2.1 p.2.2.1 p.2.1.1 p.2.1.2
        evalEquationParityFactorJet J ℓ k p.1.2.2 varJets p.2.2.2)
      (encPair
        (encPair (encPair (encPair encUnary encUnary) encUnary) (encPair encIntBin encIntBin))
        (encPair (encPair encBits encBits)
          (encPair (encList (encList (encList encIntBin))) (encList (encList encNat)))))
      (encList (encList encIntBin)) := by fun_prop

example :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (ℤ × ℤ) ×
          ((List Bool × List Bool) × (List (List (List ℤ)) × List (List ℕ))) =>
        evalClearedEquationJet p.1.1 p.1.2 p.2.1.2
          (evalAffineInputZJetTable p.1.1 p.2.1.1 p.2.2.2.1 p.2.2.1.1 p.2.2.1.2) p.2.2.2.2)
      (encPair (encPair encUnary encUnary) (encPair (encPair encIntBin encIntBin)
        (encPair (encPair (encList encBool) (encList encBool))
          (encPair (encList (encList (encList encIntBin))) (encList (encList encNat))))))
      (encList encIntBin) := by fun_prop

example : True := by
  fail_if_success
    have : ComputableInPolyTime
        (fun p : ℕ × (ℤ × List ℤ) => taylorShiftZJet p.1 p.2.1 p.2.2)
        (encPair encNat (encPair encIntBin (encList encIntBin)))
        (encList encIntBin) := by fun_prop
  trivial

end Cslib.SparseMonomialJetTests
