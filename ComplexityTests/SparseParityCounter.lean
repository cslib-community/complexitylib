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

/-- Concrete 3-variable 2-CNF formula with the same clauses as `testCNF` and an unused third
declared variable `2 : Fin 3`. -/
def testCNFUnusedVar : CNF (Fin 3) :=
  [[(0, true), (1, false)], [(1, true)]]

/-- Unit parity check rows for `testCNFUnusedVar`. -/
def testRowsUnusedVar : List (Fin testCNFUnusedVar.length → Bool) :=
  [Pi.single ⟨0, by decide⟩ true, Pi.single ⟨1, by decide⟩ true]

/-- Expected-value control: `testCNF` has a unique satisfying assignment (`modelCountOn univ = 1`),
and the full two-row parity system `testRows` has `commonZeroCount = 1` with `0` false positives. -/
example :
    testCNF.modelCountOn Finset.univ = 1 ∧
    commonZeroCount univ (testCNF.parityRowSystem testRows) = 1 ∧
    #{σ : Fin 2 → Bool |
      testCNF.eval σ = false ∧ PassesTests testCNF.violations testRows σ} = 0 := by
  rw [testCNF.commonZeroCount_parityRowSystem testRows]
  decide

/-- Edge control (no parity rows): with `rows = []`, all `2 ^ 2 = 4` assignments are common zeros of
`testCNF.parityRowSystem []`, decomposing into `1` satisfying assignment plus `3` falsifying
assignments that vacuously pass `[]`. -/
example :
    commonZeroCount univ (testCNF.parityRowSystem []) = 4 ∧
    #{σ : Fin 2 → Bool | testCNF.eval σ = false ∧ PassesTests testCNF.violations [] σ} = 3 := by
  rw [testCNF.commonZeroCount_parityRowSystem []]
  decide

/-- Edge control (single clause-0 parity row): checking only clause `0` (`x₀ ∨ ¬x₁`) yields
`commonZeroCount = 3` (`1` satisfying assignment plus the `2` falsifying assignments with
`x₁ = false`). -/
example :
    commonZeroCount univ (testCNF.parityRowSystem [Pi.single ⟨0, by decide⟩ true]) = 3 ∧
    #{σ : Fin 2 → Bool | testCNF.eval σ = false ∧
      PassesTests testCNF.violations [Pi.single ⟨0, by decide⟩ true] σ} = 2 := by
  rw [testCNF.commonZeroCount_parityRowSystem [Pi.single ⟨0, by decide⟩ true]]
  decide

/-- Edge control (unused declared variable): adding the unused variable `2 : Fin 3` in
`testCNFUnusedVar` doubles both `modelCountOn Finset.univ` and `commonZeroCount` from `1` to `2`. -/
example :
    testCNFUnusedVar.modelCountOn Finset.univ = 2 ∧
    commonZeroCount univ (testCNFUnusedVar.parityRowSystem testRowsUnusedVar) = 2 := by
  rw [testCNFUnusedVar.commonZeroCount_parityRowSystem testRowsUnusedVar]
  decide

/-- Concrete heavy-variable branching and post-branching incidence check on `testCNF` and
`testRows` (`k = 2`, `W = 1`, `b₀ = 1`): every clause has width `≤ 2`, every row in `testRows`
has weight `≤ 1`, branching on `heavyVars` with threshold `b₀ = 1` yields at most `2 ^ 16`
branches, and every variable has post-branching incidence at most `1`. -/
example (b : Fin 2 → Bool) (v : Fin 2) :
    #(branchAssignments
        (heavyVars univ (univ : Finset (Fin testRows.length))
          (fun i => equationScope (testCNF.parityRowSystem testRows i)) 1)) ≤ 2 ^ 16 ∧
    varIncidence (univ : Finset (Fin testRows.length))
      (fun i => equationScope
        (restrictMonomials
          (heavyVars univ (univ : Finset (Fin testRows.length))
            (fun j => equationScope (testCNF.parityRowSystem testRows j)) 1)
          b (testCNF.parityRowSystem testRows i))) v ≤ 1 := by
  refine ⟨?_, testCNF.varIncidence_restrictMonomials_heavyVars_parityRowSystem_le testRows 1 b v⟩
  exact testCNF.card_branchAssignments_heavyVars_parityRowSystem_le (k := 2) (W := 1) (b₀ := 1)
    (by decide) (by decide) (by decide)

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

/-- Explicit equivalence between the unbranched variable `{1}` (`univ \ {0}` in `Fin 2`) and
`Fin 1`. -/
def freeVarEquiv : ↥((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ⟨1, by decide⟩
  left_inv := by decide
  right_inv := by decide

/-- Concrete degree-1 cleared-denominator replacement family `θ b x j v = 2 * x_v + X`, evaluating
at `T = 0` to `2 * bitVal ℤ (x v)` with nonzero denominator `d_den = 2`. -/
def testTheta :
    (Fin 2 → Bool) → (Fin 1 → Bool) →
      Fin (testGreedySeq (3 * Fintype.card (Fin 2))).length → Fin 1 → Polynomial ℤ :=
  fun _ x _ v => Polynomial.C (2 * bitVal ℤ (x v)) + Polynomial.X

/-- Checked client of `CNF.modelCountOn_eq_sum_branch_emod_ediv_cleared_greedy`: discharging all
width, initial-residual, greedy-minimality, free-variable relabeling, nonzero-denominator
(`d_den = 2`), and `T = 0` Boolean-restoration premises on `testCNF` with partial branch set
`S = {0}` proves that the cleared branch-recovery sum equals `1`. -/
example :
    ∑ b ∈ branchAssignments ({0} : Finset (Fin 2)),
      ((univariateClearedParityTruncatedSum
        (univ : Finset (Fin (testGreedySeq (3 * Fintype.card (Fin 2))).length))
        (fun j => relabelRestrictedMonomials ({0} : Finset (Fin 2)) freeVarEquiv b
          (testCNF.parityRowSystem (testGreedySeq (3 * Fintype.card (Fin 2))) j))
        2 2 (branchPrecision (Fintype.card (Fin 2))) (testTheta b)).eval 0 /
          clearedProductDenom 2 2 (branchPrecision (Fintype.card (Fin 2)))
            #(univ : Finset (Fin (testGreedySeq (3 * Fintype.card (Fin 2))).length))) %
              ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin 2))) = 1 := by
  have hrec := testCNF.modelCountOn_eq_sum_branch_emod_ediv_cleared_greedy
    (k := 2) (P := 2) (by decide) (by decide) (by decide) testGreedySeq (by decide)
    (fun _ => testCand) (fun _ => rfl) commonZeroCount_testGreedySeq_step_le
    ({0} : Finset (Fin 2)) freeVarEquiv (d_den := 2) (by decide) testTheta
    (fun _ _ x _ _ _ _ v _ => by simp [testTheta])
  have hcount : testCNF.modelCountOn Finset.univ = 1 := by decide
  rw [← hrec, hcount]
  rfl

end ComplexityTests.SparseParityCounter
