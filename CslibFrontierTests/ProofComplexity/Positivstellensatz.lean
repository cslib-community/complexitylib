/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.Pigeonhole

/-!
# Tests: Positivstellensatz refutations and the pigeonhole principle

`PHP³₂` has a Positivstellensatz refutation of degree `2` over `ℤ` and over `ℚ`, and none of degree
`1` over `ℚ`. Its degree-`1` pseudo-expectation, evaluation at `xᵢⱼ = 1 / 2`, is a fractional
point, so `SOS.Psatz.PseudoExpectation` is inhabited for an unsatisfiable system without a
`0/1` solution. For `n = 1` the bound `2 ≤ d` fails: `PHP²₁` has an explicit refutation of degree
`1`. For `n = 0` the empty pigeon clause is `0 ≥ 1`, a refutation of degree `0`. The satisfiable
`PHP²₂` has no refutation of any degree. Sum-of-squares refutations of equations embed as the
refutations without inequality factors.
-/

namespace CslibFrontierTests.ProofComplexity.Positivstellensatz

open Cslib Cslib.Logic.PL Cslib.Logic.PL.CNF Cslib.Logic.PL.SOS.Psatz MvPolynomial Finset

/-! ### `PHP³₂`: degree `2` exactly -/

example : RefutableInDegree (cnfIneqs (pigeonhole 3 2) : Set (MvPolynomial (Fin 3 × Fin 2) ℤ))
    (booleanAxioms (Fin 3 × Fin 2) ℤ) 2 :=
  refutableInDegree_two_pigeonhole (by norm_num)

example : ¬ RefutableInDegree
    (cnfIneqs (pigeonhole 3 2) : Set (MvPolynomial (Fin 3 × Fin 2) ℚ))
    (booleanAxioms (Fin 3 × Fin 2) ℚ) 1 :=
  not_refutableInDegree_one_pigeonhole le_rfl

example (d : ℕ) : RefutableInDegree
    (cnfIneqs (pigeonhole 3 2) : Set (MvPolynomial (Fin 3 × Fin 2) ℚ))
    (booleanAxioms (Fin 3 × Fin 2) ℚ) d ↔ 2 ≤ d := by
  rw [refutableInDegree_pigeonhole_iff le_rfl]
  omega

/-- The degree-`1` pseudo-expectation of `PHP³₂`: evaluation at `xᵢⱼ = 1 / 2`. -/
noncomputable def php32PseudoExpectation :
    PseudoExpectation (cnfIneqs (pigeonhole 3 2) : Set (MvPolynomial (Fin 3 × Fin 2) ℚ))
      (booleanAxioms (Fin 3 × Fin 2) ℚ) 1 :=
  degreeOnePseudoExpectation _ (eval_inv_nonneg_of_mem_cnfIneqs_pigeonhole le_rfl)

/-- It is fractional: it gives `xᵢⱼ` the value `1 / 2`, so it is not a `0/1` point. -/
example : php32PseudoExpectation.toLinearMap (X (0, 0)) = 1 / 2 := by
  simp [php32PseudoExpectation]

/-- It does not satisfy the Boolean axioms beyond degree `1`: `Ẽ (x² - x) = -1/4`. -/
example : php32PseudoExpectation.toLinearMap (X (0, 0) ^ 2 - X (0, 0)) = -1 / 4 := by
  simp [php32PseudoExpectation]
  norm_num

/-! ### `PHP²₁`: degree `1` suffices for one hole -/

private theorem totalDegree_pigeonPoly_le (i : Fin 2) :
    (∑ j : Fin 1, X (i, j) - 1 : MvPolynomial (Fin 2 × Fin 1) ℤ).totalDegree ≤ 1 := by
  rw [← toPoly_toIneq_pigeonClause]
  exact Ineq.totalDegree_toPoly_le _

/-- `P₀ + P₁ + H₀₁₀ = (x₀₀ - 1) + (x₁₀ - 1) + (1 - x₀₀ - x₁₀) = -1`. -/
example : RefutableInDegree (cnfIneqs (pigeonhole 2 1) : Set (MvPolynomial (Fin 2 × Fin 1) ℤ))
    (booleanAxioms (Fin 2 × Fin 1) ℤ) 1 := by
  refine RefutableInDegree.of_sum (ι := Empty) (κ := Fin 3) (fun _ => 0) (fun _ => 0)
    ![⟨{∑ j, X (0, j) - 1}, 1, 1⟩, ⟨{∑ j, X (1, j) - 1}, 1, 1⟩,
      ⟨{1 - X (0, 0) - X (1, 0)}, 1, 1⟩] (fun i => i.elim) (fun i => i.elim) ?_ ?_ ?_ ?_
  · intro k
    fin_cases k
    · simpa using pigeonPoly_mem_cnfIneqs (R := ℤ) (n := 1) (0 : Fin 2)
    · simpa using pigeonPoly_mem_cnfIneqs (R := ℤ) (n := 1) (1 : Fin 2)
    · simpa using holePoly_mem_cnfIneqs (R := ℤ) (show (0 : Fin 2) ≠ 1 by decide) (0 : Fin 1)
  · intro k
    fin_cases k <;> simp
  · intro k
    fin_cases k
    · simpa [Summand.degree_def] using totalDegree_pigeonPoly_le 0
    · simpa [Summand.degree_def] using totalDegree_pigeonPoly_le 1
    · simp only [Summand.degree_def]
      rw [← toPoly_toIneq_holeClause (show (0 : Fin 2) ≠ 1 by decide)]
      simpa using Ineq.totalDegree_toPoly_le (R := ℤ) (holeClause (0 : Fin 2) 1 0).toIneq
  · simp [Summand.toPoly_def, Fin.sum_univ_three]
    ring

/-! ### `PHP¹₀`: degree `0` -/

/-- With no holes, the pigeon clause is empty and its polynomial is the constant `-1`. -/
example : RefutableInDegree (cnfIneqs (pigeonhole 1 0) : Set (MvPolynomial (Fin 1 × Fin 0) ℤ))
    (booleanAxioms (Fin 1 × Fin 0) ℤ) 0 := by
  refine RefutableInDegree.of_sum (ι := Empty) (κ := Unit) (fun _ => 0) (fun _ => 0)
    (fun _ => ⟨{∑ j, X (0, j) - 1}, 1, 1⟩) (fun i => i.elim) (fun i => i.elim) ?_ ?_ ?_ ?_
  · intro _
    simpa using pigeonPoly_mem_cnfIneqs (R := ℤ) (n := 0) (0 : Fin 1)
  · intro _
    simp
  · intro _
    simp [Summand.degree_def]
  · simp [Summand.toPoly_def]

/-! ### `PHP²₂` is satisfiable: no refutation of any degree -/

example (d : ℕ) : ¬ RefutableInDegree
    (cnfIneqs (pigeonhole 2 2) : Set (MvPolynomial (Fin 2 × Fin 2) ℚ))
    (booleanAxioms (Fin 2 × Fin 2) ℚ) d := fun h =>
  not_satisfiable_of_refutableInDegree h (satisfiable_pigeonhole_iff.2 le_rfl)

/-! ### Sum-of-squares refutations of equations -/

/-- The equation `1 = 0` has the sum-of-squares refutation `(-1) · 1 = -1`, which is a
Positivstellensatz refutation for any set of inequality constraints. -/
example : RefutableInDegree (∅ : Set (MvPolynomial (Fin 1) ℤ)) {g | g ∈ [1]} 0 := by
  rw [refutableInDegree_empty_iff]
  exact SOS.RefutableInDegree.of_list [(-1, 1)] (by simp) [] (by simp) (by simp) (by simp)

end CslibFrontierTests.ProofComplexity.Positivstellensatz
