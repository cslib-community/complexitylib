/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Logics.Propositional.CNF.SparseParityCounter

/-!
# Tests for `Complexity.Logics.Propositional.CNF.SparseParityCounter`
-/

@[expose] public noncomputable section

namespace ComplexityTests.SparseParityCounter

open Finset Cslib.BitString Cslib.Logic.PL

/-- Concrete 2-variable 2-CNF formula `(x₀ ∨ ¬x₁) ∧ (x₁)` on `Fin 2`, with unique satisfying
assignment `x₀ = true, x₁ = true`. -/
def testCNF : CNF (Fin 2) :=
  [[(0, true), (1, false)], [(1, true)]]

/-- Concrete two-row unit parity check matrix selecting clause `0` and clause `1` of `testCNF`. -/
def testRows : List (Fin testCNF.length → Bool) :=
  [Pi.single ⟨0, by decide⟩ true, Pi.single ⟨1, by decide⟩ true]

/-- Concrete check of `CNF.commonZeroCount_parityRowSystem` and
`CNF.commonZeroCount_parityRowSystem_eq_modelCountOn_add` on `testCNF` and `testRows`. -/
example :
    commonZeroCount univ (testCNF.parityRowSystem testRows) =
      numPassing testCNF.violations testRows ∧
    commonZeroCount univ (testCNF.parityRowSystem testRows) =
      testCNF.modelCountOn Finset.univ +
        #{σ : Fin 2 → Bool | testCNF.eval σ = false ∧ PassesTests testCNF.violations testRows σ} :=
  ⟨testCNF.commonZeroCount_parityRowSystem testRows,
    testCNF.commonZeroCount_parityRowSystem_eq_modelCountOn_add testRows⟩

/-- Concrete check of `CNF.exists_initialTests_commonZeroCount_greedy` on `testCNF` (`k = 2`,
`B = 1`, `n = 2`, `m = 2 ≤ 1 * 2`). -/
example :
    let D₀ := CNF.initialRowWeightBound 1 testCNF.length
    let P := CNF.greedyRowListLength 1 testCNF.length
    ∃ A₀ : List (Fin testCNF.length → Bool), A₀.length ≤ 3 * Fintype.card (Fin 2) ∧
      (∀ r ∈ A₀, weight r ≤ D₀) ∧
      ∀ (A : ℕ → List (Fin testCNF.length → Bool))
        (γ : ℕ → Fin P → Fin testCNF.length × Bool),
        A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
        (∀ i (γ' : Fin P → Fin testCNF.length × Bool),
          commonZeroCount univ (testCNF.parityRowSystem (A i ++ [testRow (γ i)])) ≤
            commonZeroCount univ (testCNF.parityRowSystem (A i ++ [testRow γ']))) →
        commonZeroCount univ (testCNF.parityRowSystem (A (3 * Fintype.card (Fin 2)))) =
          testCNF.modelCountOn Finset.univ ∧
        ∀ i ≤ 3 * Fintype.card (Fin 2),
          (A i).length ≤ 6 * Fintype.card (Fin 2) ∧
          ∀ j : Fin (A i).length,
            (∀ M ∈ testCNF.parityRowSystem (A i) j, M ⊆ testCNF.vars.toFinset ∧ #M ≤ 2) ∧
            #(testCNF.parityRowSystem (A i) j) ≤ max D₀ P * 2 ^ 2 ∧
            #(equationScope (testCNF.parityRowSystem (A i) j)) ≤ 2 * (max D₀ P * 2 ^ 2) := by
  exact testCNF.exists_initialTests_commonZeroCount_greedy (by decide) (by decide) (by decide)
    (by decide)

end ComplexityTests.SparseParityCounter
