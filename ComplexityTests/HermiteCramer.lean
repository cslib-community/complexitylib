/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.Circuit.Rational.Runtime.HermiteCramer
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Regression tests for signed binary integer division and Hermite Cramer recovery

Concrete `#eval` / kernel checks, nonvacuous theorem instantiations, bit-length bound checks, and
plain `ComputableInPolyTime` composition tests for:
* `Complexity.Computability.PolyTime.Int.ExactDiv` (`tdiv`, `tmod`, `ediv`, `emod`, `modPowTwo`,
  exact division, and `encIntBin` code-length bounds across signed and zero-divisor edge cases);
* `Complexity.Computability.Circuit.Rational.Runtime.HermiteCramer` (recovering `H(0)` for a
  concrete degree-5 polynomial `H ∈ ℚ[X]` with non-integer rational coefficients from `r = 2,
  J = 3` scaled Taylor jets with `Ω = 6 > 1`, modular count recovery mod `2 ^ ℓ`, and `intBits`
  bit-length bounds).
-/

namespace ComplexityTests.HermiteCramer

open Polynomial
open Turing MultiTapeTM
open Cslib.Circuits.Rational

/-! ### Signed division, remainder, and `modPowTwo` edge cases -/

-- Truncated vs Euclidean division and remainder across all sign quadrants and zero divisor.
example :
    (7 : ℤ).tdiv 3 = 2 ∧ (7 : ℤ).tmod 3 = 1 ∧
    (7 : ℤ).ediv 3 = 2 ∧ (7 : ℤ).emod 3 = 1 ∧
    (7 : ℤ).tdiv (-3) = -2 ∧ (7 : ℤ).tmod (-3) = 1 ∧
    (7 : ℤ).ediv (-3) = -2 ∧ (7 : ℤ).emod (-3) = 1 ∧
    (-7 : ℤ).tdiv 3 = -2 ∧ (-7 : ℤ).tmod 3 = -1 ∧
    (-7 : ℤ).ediv 3 = -3 ∧ (-7 : ℤ).emod 3 = 2 ∧
    (-7 : ℤ).tdiv (-3) = 2 ∧ (-7 : ℤ).tmod (-3) = -1 ∧
    (-7 : ℤ).ediv (-3) = 3 ∧ (-7 : ℤ).emod (-3) = 2 ∧
    (-7 : ℤ).tdiv 0 = 0 ∧ (-7 : ℤ).tmod 0 = -7 ∧
    (-7 : ℤ).ediv 0 = 0 ∧ (-7 : ℤ).emod 0 = -7 := by
  decide +kernel

-- Exact signed multiples and `modPowTwo` wraparound.
example :
    Int.ediv_mul_left_exact (-17) (d := -12) (by decide) = rfl ∧
    (-17 : ℤ).modPowTwo 5 = 15 ∧
    (-32 : ℤ).modPowTwo 5 = 0 ∧
    (0 : ℤ).modPowTwo 0 = 0 := by
  refine ⟨rfl, ?_⟩
  decide +kernel

-- Concrete `encIntBin` code-length and `intBits` bounds on negative division and modular reduction.
example :
    (encIntBin ((-1 : ℤ).ediv 100)).length ≤ (encIntBin (-1)).length ∧
    (encIntBin ((-7 : ℤ).emod (-3))).length ≤ (encIntBin (-3)).length ∧
    (encIntBin ((-17 : ℤ).modPowTwo 5)).length ≤ 5 + 1 ∧
    intBits ((-1 : ℤ).ediv 100) ≤ intBits (-1) ∧
    intBits ((-7 : ℤ).ediv 3) ≤ intBits (-7) ∧
    intBits ((-7 : ℤ).emod (-3)) ≤ intBits (-3) + 1 ∧
    intBits ((-17 : ℤ).modPowTwo 5) ≤ 5 + 1 :=
  ⟨length_encIntBin_ediv_le (-1) 100, length_encIntBin_emod_le_of_ne_zero (-7) (by decide),
    length_encIntBin_modPowTwo_le (-17) 5, intBits_ediv_le (-1) 100, intBits_ediv_le (-7) 3,
    intBits_emod_le_add_one_of_ne_zero (-7) (by decide), intBits_modPowTwo_le (-17) 5⟩

/-! ### Concrete degree-5 Hermite Cramer recovery (`r = 2, J = 3, Ω = 6 > 1`) -/

/-- Concrete degree-5 polynomial with non-integer rational coefficients and integer `H(0) = -17`:
`H(T) = -17 + (1/2) T - (1/3) T^2 + (5/6) T^3 - (1/2) T^4 + (1/6) T^5`. -/
noncomputable def testPoly : ℚ[X] :=
  C (-17) + C (1 / 2) * X - C (1 / 3) * X ^ 2 + C (5 / 6) * X ^ 3 -
    C (1 / 2) * X ^ 4 + C (1 / 6) * X ^ 5

/-- Scaled order-3 Taylor jets `6 · [z ^ j] testPoly(t + z)` at nodes `[1, 2]`. -/
def testJetsPos : List (List ℤ) :=
  [[-98, 7, 5], [-80, 39, 36]]

/-- Scaled order-3 Taylor jets `6 · [z ^ j] testPoly(t + z)` at signed nodes `[-1, 2]`. -/
def testJetsSigned : List (List ℤ) :=
  [[-116, 39, -45], [-80, 39, 36]]

/-- info: (-17, -17, 15, 1, -102, 19683, -2007666, 1, []) -/
#guard_msgs in
#eval (hermiteRecoverZero [1, 2] 3 6 testJetsPos,
  hermiteRecoverZero [-1, 2] 3 6 testJetsSigned,
  hermiteRecoverModPowTwo [1, 2] 3 5 6 testJetsPos,
  detRows (hermiteRows [1, 2] 3),
  detRows (cramerColZeroRows (hermiteRows [1, 2] 3) testJetsPos.flatten),
  detRows (hermiteRows [-1, 2] 3),
  detRows (cramerColZeroRows (hermiteRows [-1, 2] 3) testJetsSigned.flatten),
  detRows (hermiteRows [1, 2] 0),
  hermiteRows [] 3)

example :
    hermiteRecoverZero [1, 2] 3 6 testJetsPos = -17 ∧
    hermiteRecoverZero [-1, 2] 3 6 testJetsSigned = -17 ∧
    hermiteRecoverModPowTwo [1, 2] 3 5 6 testJetsPos = 15 := by
  decide +kernel

-- Nonvacuous propositional instantiation of `hermiteRecoverZero_eq` and
-- `hermiteRecoverModPowTwo_eq` on `testPoly` (`r = 2, J = 3, Ω = 6`).
private lemma testPoly_natDegree_eq : testPoly.natDegree = 5 := by
  unfold testPoly
  compute_degree!

private lemma testPoly_natDegree_lt (nodes : List ℤ) (h : nodes.length = 2) :
    testPoly.natDegree < nodes.length * 3 := by
  rw [testPoly_natDegree_eq, h]
  omega

private lemma testPoly_eval_zero : testPoly.eval 0 = ((-17 : ℤ) : ℚ) := by
  unfold testPoly
  norm_num

private lemma testPoly_jets_pos (i : Fin ([1, 2] : List ℤ).length) (j : Fin 3) :
    (rowEntry testJetsPos i j : ℚ) =
      (6 : ℚ) * (Polynomial.taylor (([1, 2] : List ℤ)[i] : ℚ) testPoly).coeff j := by
  have hp : testPoly.degree < ↑(([1, 2] : List ℤ).length * 3) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    exact fun m hm => Polynomial.coeff_eq_zero_of_natDegree_lt
      ((testPoly_natDegree_lt [1, 2] rfl).trans_le hm)
  have hm := congrFun
    (Polynomial.hermiteMatrix_mulVec (J := 3) (fun k : Fin 2 => ([1, 2] : List ℤ)[k]) hp) (i, j)
  rw [Polynomial.taylorJet_apply] at hm
  rw [← hm]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.map_apply, hermiteMatrix_apply,
      testJetsPos, testPoly, rowEntry, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_pow, coeff_X, coeff_C] <;>
    norm_num
  all_goals
    rw [show Nat.choose 4 2 = 6 by decide, show Nat.choose 5 2 = 10 by decide]
    norm_num

private lemma testPoly_jets_signed (i : Fin ([-1, 2] : List ℤ).length) (j : Fin 3) :
    (rowEntry testJetsSigned i j : ℚ) =
      (6 : ℚ) * (Polynomial.taylor (([-1, 2] : List ℤ)[i] : ℚ) testPoly).coeff j := by
  have hp : testPoly.degree < ↑(([-1, 2] : List ℤ).length * 3) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    exact fun m hm => Polynomial.coeff_eq_zero_of_natDegree_lt
      ((testPoly_natDegree_lt [-1, 2] rfl).trans_le hm)
  have hm := congrFun
    (Polynomial.hermiteMatrix_mulVec (J := 3) (fun k : Fin 2 => ([-1, 2] : List ℤ)[k]) hp) (i, j)
  rw [Polynomial.taylorJet_apply] at hm
  rw [← hm]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three, Matrix.map_apply, hermiteMatrix_apply,
      testJetsSigned, testPoly, rowEntry, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, coeff_add, coeff_sub, coeff_C_mul,
      coeff_X_pow, coeff_X, coeff_C] <;>
    norm_num
  all_goals
    rw [show Nat.choose 4 2 = 6 by decide, show Nat.choose 5 2 = 10 by decide]
    norm_num

theorem recover_testPoly_zero : hermiteRecoverZero [1, 2] 3 6 testJetsPos = -17 :=
  hermiteRecoverZero_eq (H := testPoly) (by decide) (by decide) (testPoly_natDegree_lt [1, 2] rfl)
    testPoly_eval_zero rfl (by decide) fun i j => by
      have h := testPoly_jets_pos i j
      fin_cases i <;> fin_cases j <;> simpa [testJetsPos, rowEntry] using h

theorem recover_testPoly_signed : hermiteRecoverZero [-1, 2] 3 6 testJetsSigned = -17 :=
  hermiteRecoverZero_eq (H := testPoly) (by decide) (by decide) (testPoly_natDegree_lt [-1, 2] rfl)
    testPoly_eval_zero rfl (by decide) fun i j => by
      have h := testPoly_jets_signed i j
      fin_cases i <;> fin_cases j <;> simpa [testJetsSigned, rowEntry] using h

theorem recover_testPoly_mod32 : hermiteRecoverModPowTwo [1, 2] 3 5 6 testJetsPos = 15 :=
  hermiteRecoverModPowTwo_eq (H := testPoly) (H_zero := -17) (by decide) (by decide)
    (testPoly_natDegree_lt [1, 2] rfl) testPoly_eval_zero rfl (by decide) testPoly_jets_pos
    (by decide) (by decide) ⟨-1, by decide⟩

-- Concrete entry bit-length bounds on the `6 × 6` Hermite and Cramer tables, and plain
-- `ComputableInPolyTime` composition checks (zero `Tidy` annotations).
example {row₁ row₂ : List ℤ} (hrow₁ : row₁ ∈ hermiteRows [-1, 2] 3) {z₁ : ℤ} (hz₁ : z₁ ∈ row₁)
    (hrow₂ : row₂ ∈ cramerColZeroRows (hermiteRows [-1, 2] 3) testJetsSigned.flatten)
    {z₂ : ℤ} (hz₂ : z₂ ∈ row₂) :
    intBits z₁ ≤ 6 * (2 + 1) + 1 ∧
    intBits z₂ ≤ 18 + 1 ∧
    ComputableInPolyTime
      (fun p : (ℤ × ℤ) × ℕ => ((p.1.1.ediv p.1.2) + (p.1.1.tdiv p.1.2)).modPowTwo p.2)
      (encPair (encPair encIntBin encIntBin) encUnary) encIntBin ∧
    ComputableInPolyTime
      (fun p : ℤ × ℤ => (p.1 / p.2) * (p.1 % p.2) + p.1.tmod p.2)
      (encPair encIntBin encIntBin) encIntBin ∧
    ComputableInPolyTime
      (fun q : (((List ℤ × ℕ) × ℕ) × ℤ) × List (List (List ℤ)) =>
        ((q.2.map (hermiteRecoverZero q.1.1.1.1 q.1.1.1.2 q.1.2)).sum).modPowTwo q.1.1.2)
      (encPair (encPair (encPair (encPair (encList encIntBin) encUnary) encUnary) encIntBin)
        (encList (encList (encList encIntBin))))
      encIntBin :=
  ⟨intBits_le_of_mem_hermiteRows (b := 2) (by decide +kernel) hrow₁ hz₁,
    intBits_le_of_mem_cramerColZeroRows (B := 18)
      (fun _ hr _ hz' => intBits_le_of_mem_hermiteRows (b := 2) (by decide +kernel) hr hz')
      (by decide +kernel) hrow₂ hz₂,
    by fun_prop, by fun_prop, by fun_prop⟩

end ComplexityTests.HermiteCramer
