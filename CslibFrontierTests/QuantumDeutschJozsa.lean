/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.Quantum.DeutschJozsa

/-! The Deutsch–Jozsa algorithm on concrete inputs: `n = 1` (Deutsch's problem, `N = 2`) and
`n = 2` (`N = 4`), with positions identified with `{0,1}^n`. -/

namespace ComplexityTests.QuantumDeutschJozsa

open Cslib Cslib.Quantum Cslib.QueryComplexity Cslib.BitString

/-- The positions `Fin 2` identified with `{0,1}^1`. -/
noncomputable def e2 : Fin 2 ≃ (Fin 1 → Bool) := Fintype.equivOfCardEq (by simp)

/-- The positions `Fin 4` identified with `{0,1}^2`. -/
noncomputable def e4 : Fin 4 ≃ (Fin 2 → Bool) := Fintype.equivOfCardEq (by simp)

/-! ### `n = 1`: Deutsch's problem -/

-- The balanced input `01` (identity function): the algorithm never measures `0`.
example : regProb (run (bernsteinVazirani e2) (bernsteinVaziraniInit e2) ![false, true] 1)
    (e2.symm 0) = 0 :=
  regProb_run_bernsteinVazirani_zero_of_isBalanced e2 (by decide)

-- The balanced input `10` (negation).
example : regProb (run (bernsteinVazirani e2) (bernsteinVaziraniInit e2) ![true, false] 1)
    (e2.symm 0) = 0 :=
  regProb_run_bernsteinVazirani_zero_of_isBalanced e2 (by decide)

-- The constant inputs `00` and `11`: the algorithm measures `0` with certainty.
example (c : Bool) : regProb (run (bernsteinVazirani e2) (bernsteinVaziraniInit e2)
    (fun _ => c) 1) (e2.symm 0) = 1 :=
  regProb_run_bernsteinVazirani_zero_of_const e2 c

-- One quantum query against two deterministic queries.
example : ‖bernsteinVaziraniInit e2‖ = 1 ∧
    (∀ F : (Fin 2 → Bool) → Bool, SolvesDeutschJozsa F → ∀ x, (∃ c, x = fun _ => c) ∨
      IsBalanced x → regProb (run (bernsteinVazirani e2) (bernsteinVaziraniInit e2) x 1)
        (e2.symm 0) = bitVal ℝ (F x)) ∧
    ∀ F : (Fin 2 → Bool) → Bool, SolvesDeutschJozsa F → 2 ≤ DecisionTree.complexity F := by
  simpa using deutschJozsa_separation e2 (by simp)

/-! ### `n = 2` -/

-- The balanced input `0110`.
example : regProb (run (bernsteinVazirani e4) (bernsteinVaziraniInit e4) ![false, true, true, false]
    1) (e4.symm 0) = 0 :=
  regProb_run_bernsteinVazirani_zero_of_isBalanced e4 (by decide)

-- The unbalanced, non-constant input `1000` is outside the promise: the probability of `00` is
-- `((1 + 1 + 1 - 1) / 4)² = 1/4`, strictly between `0` and `1`.
example : regProb (run (bernsteinVazirani e4) (bernsteinVaziraniInit e4)
    ![true, false, false, false] 1) (e4.symm 0) = 1 / 4 := by
  rw [regProb_run_bernsteinVazirani_zero]
  norm_num [Fin.sum_univ_four]

-- One quantum query against three deterministic queries.
example (F : (Fin 4 → Bool) → Bool) (hF : SolvesDeutschJozsa F) :
    regProb (run (bernsteinVazirani e4) (bernsteinVaziraniInit e4) ![false, true, true, false] 1)
      (e4.symm 0) = bitVal ℝ (F ![false, true, true, false]) ∧
    3 ≤ DecisionTree.complexity F := by
  obtain ⟨-, hq, hd⟩ := deutschJozsa_separation e4 (by simp)
  exact ⟨hq F hF _ (Or.inr (by decide)), by simpa using hd F hF⟩

end ComplexityTests.QuantumDeutschJozsa
