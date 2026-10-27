/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFCountingAsymptotics
public import Complexity.Foundations.BooleanAnalysis.SparseHermiteJetRecovery

/-!
# Stage-1/Stage-2 `clearedParityJetTable` and Hermite–Cramer recovery across Section 6.3/6.4

This module connects the Stage-1/Stage-2 `JetTable` bridge and unconditional Hermite–Cramer
determinant recovery (`Complexity.Foundations.BooleanAnalysis.SparseHermiteJetRecovery`) with the
Section 6.3 compiled CNF parity-row schedule
(`Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule`) and the Section 6.4
Proposition 6.4 tree-wide candidate-indexed recovery and examination bounds
(`Complexity.Computability.Complexity.FineGrained.GeneralCNFCountingAsymptotics`) of
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH] (Sections 5.4–5.5, 6.1–6.4,
and Appendices A–B, printed pp. 37–50):

1. **Shared parity-system recovery (Appendix B.2–B.3, printed pp. 48–50):**
   `Complexity.Foundations.BooleanAnalysis.SparseHermiteJetRecovery` supplies the generic
   `Cslib.BitString` coordinate and arbitrary-finite-type branch recovery lemmas. This module
   publicly imports that API and specializes it to CNF parity-row systems below.

2. **Section 6.3 compiled CNF parity-row schedule Hermite–Cramer and `clearedParityJetTable`
   recovery with `interpolationScale` examination bounds (`Cslib.Logic.PL.CNF`, pp. 38–43, 48–50):**
   - `CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design`,
     `CNF.numPassing_eq_sum_branch_hermiteCramerNumerator_design`,
     `CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design`, and
     `CNF.numPassing_eq_sum_branch_clearedParityJetTable_design`: specialize both Hermite–Cramer
     recovery forms to `φ.branchParityRowSystem rows S e b` across `b ∈ branchAssignments S`.
   - `CNF.exists_branch_schedule_hermiteCramer_and_examBound_parityRowSystem_of_le_clog_pow`,
     `CNF.exists_greedy_parityRowSystem_hermiteCramer_recovery_and_examBound_of_le_clog_pow`, and
     `CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow`:
     certify that the Lemma 4.8 per-branch `ReplacementDesign` family `D b` at
     `b₀ = CNF.parityBranchThreshold k W (Fintype.card V)` and `β = 2 * β_B + 5` has positive node
     count `0 < numNodes n'` and simultaneously recovers
     `commonZeroCount univ (φ.parityRowSystem rows)` (and `φ.modelCountOn Finset.univ` after
     `3 * n` greedy rounds) via **both** explicit Hermite–Cramer truncated-sum determinants and
     Stage-1/Stage-2 `clearedParityJetTable` coordinate sums at `nodeInt` and canonical jet order
     `J = sparseParityJetOrder k (rowBound (2 * β_B + 5) n') (numNodes n') rows.length ℓ`, while
     satisfying the univariate degree bound and the per-branch / branch-summed
     `2 ^ (A * interpolationScale (Fintype.card V))` domain-examination bounds.

3. **Proposition 6.4 tree-wide candidate-indexed Hermite–Cramer & `clearedParityJetTable` recovery
   and total examination bounds (`Cslib.Logic.PL.CNF`, §6.4 & Appendices A–B, pp. 43–50):**
   - `CNF.exists_prop64NormalizedLeaves_greedy_total_hermiteCramer_recovery_and_examBound` and
     `CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound`: for any
     `k ≥ 2`, there exists `N₃ ≥ 2 ^ 640000` such that for any finite variable type `V` with
     `N₃ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V`, on every normalized leaf
     `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`) and every candidate query
     `q : CNF.LeafCandidateQueryIndex V B ψ` (covering all `3 * n` greedy stages and all ordered
     candidate lists `γ'` with list multiplicity, including discarded candidates, plus the final
     query `Sum.inr ()`), the certified per-branch `ReplacementDesign` family `D q b` recovers
     `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A q))` via **both** explicit
     Hermite–Cramer truncated-sum determinants and Stage-1/Stage-2 `clearedParityJetTable`
     coordinate sums at `nodeInt` and canonical jet order `sparseParityJetOrder`, while satisfying
     the per-query (`≤ 2 ^ ((CNF.prop64BranchExamScaleCoeff k + 32) * interpolationScale n)`),
     per-leaf candidate-summed
     (`≤ 2 ^ (CNF.prop64LeafQueryExamScaleCoeff k * interpolationScale n)`),
     and tree-wide candidate-summed
     (`≤ 2 ^ (CNF.prop64TotalExamScaleCoeff k * interpolationScale n)`)
     domain-examination bounds.

## Main results

* `Cslib.Logic.PL.CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design`,
  `Cslib.Logic.PL.CNF.numPassing_eq_sum_branch_hermiteCramerNumerator_design`,
  `Cslib.Logic.PL.CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design`,
  `Cslib.Logic.PL.CNF.numPassing_eq_sum_branch_clearedParityJetTable_design`
* `CNF.exists_branch_schedule_hermiteCramer_and_examBound_parityRowSystem_of_le_clog_pow`,
  `CNF.exists_greedy_parityRowSystem_hermiteCramer_recovery_and_examBound_of_le_clog_pow`,
  `CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow`
* `CNF.exists_prop64NormalizedLeaves_greedy_total_hermiteCramer_recovery_and_examBound`,
  `CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.4–5.5, pp. 38–39; Sections 6.1–6.4, pp. 39–44; Appendices A–B, pp. 44–50)
-/

@[expose] public noncomputable section

open Finset Polynomial
open scoped BigOperators

/-! ### 2. Section 6.3 CNF parity-row schedule Hermite–Cramer & `clearedParityJetTable` recovery -/

namespace Cslib.Logic.PL

open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {V : Type*}

section CNFDeterminantRecovery

variable [Fintype V] [DecidableEq V] {n' Q r A₀ R : ℕ} {τ : ℚ}

/-- **§5.4–5.5 & §6.3 branch-summed Hermite–Cramer truncated-sum recovery of `commonZeroCount` on
`φ.parityRowSystem rows`**: when every clause of `φ` has width at most `k` and `0 < Q`, summing the
per-branch `hermiteCramerNumerator` quotients of `univariateClearedParityTruncatedSum` at `nodeInt`
and canonical jet order `J = sparseParityJetOrder k R Q #(univ : Finset (Fin rows.length)) ℓ`
across `b ∈ branchAssignments S` recovers `commonZeroCount univ (φ.parityRowSystem rows)`. -/
theorem CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) (hQ : 0 < Q) :
    let ℓ := branchPrecision (Fintype.card V)
    let J := sparseParityJetOrder k R Q #(univ : Finset (Fin rows.length)) ℓ
    (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
      ∑ b ∈ branchAssignments S,
        (hermiteCramerNumerator (nodeInt (Q := Q)) hQ
          (sparseParityJetOrder_pos k R Q #(univ : Finset (Fin rows.length)) ℓ)
          (fun t j =>
            (Polynomial.taylor (nodeInt t)
              (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
                (designReplacementScaledIntMap (D b) (emb b)))).coeff j) /
          (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #(univ : Finset (Fin rows.length)) *
            (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) :=
  commonZeroCount_eq_sum_branch_hermiteCramerNumerator_design_of_fintype S e
    (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) scope D emb hQ
    (fun j _ _M hM => CNF.card_mem_parityRowSystem_le hk rows j hM)

/-- **§5.4–5.5 & §6.3 branch-summed Hermite–Cramer truncated-sum recovery of `numPassing`**:
under the same hypotheses, the branch-summed `hermiteCramerNumerator` quotients recover
`numPassing φ.violations rows`. -/
theorem CNF.numPassing_eq_sum_branch_hermiteCramerNumerator_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) (hQ : 0 < Q) :
    let ℓ := branchPrecision (Fintype.card V)
    let J := sparseParityJetOrder k R Q #(univ : Finset (Fin rows.length)) ℓ
    (numPassing φ.violations rows : ℤ) =
      ∑ b ∈ branchAssignments S,
        (hermiteCramerNumerator (nodeInt (Q := Q)) hQ
          (sparseParityJetOrder_pos k R Q #(univ : Finset (Fin rows.length)) ℓ)
          (fun t j =>
            (Polynomial.taylor (nodeInt t)
              (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ
                (designReplacementScaledIntMap (D b) (emb b)))).coeff j) /
          (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #(univ : Finset (Fin rows.length)) *
            (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) := by
  rw [← CNF.commonZeroCount_parityRowSystem]
  exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk rows S e
    scope D emb hQ

/-- **§5.4–5.5, §6.3 & Appendix B.2–B.3 branch-summed Stage-1/Stage-2 `clearedParityJetTable`
Hermite–Cramer coordinate recovery of `commonZeroCount` on `φ.parityRowSystem rows`**: under the
same hypotheses, summing the coordinate Cramer quotients of `clearedParityJetTable` over
`s : Fin ℓ` modulo `2 ^ ℓ` on each branch and summing across `b ∈ branchAssignments S` recovers
`commonZeroCount univ (φ.parityRowSystem rows)`. -/
theorem CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) (hQ : 0 < Q) :
    let ℓ := branchPrecision (Fintype.card V)
    let J := sparseParityJetOrder k R Q #(univ : Finset (Fin rows.length)) ℓ
    (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
      ∑ b ∈ branchAssignments S,
        (∑ s : Fin ℓ,
          hermiteCramerNumerator (nodeInt (Q := Q)) hQ
            (sparseParityJetOrder_pos k R Q #(univ : Finset (Fin rows.length)) ℓ)
            (fun t j =>
              clearedParityJetTable (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ J
                (designReplacementScaledIntMap (D b) (emb b)) (nodeInt t) j s) /
            (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #(univ : Finset (Fin rows.length)) *
              (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) :=
  commonZeroCount_eq_sum_branch_clearedParityJetTable_design S e
    (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) scope D emb hQ
    (fun j _ _M hM => CNF.card_mem_parityRowSystem_le hk rows j hM)

/-- **§5.4–5.5, §6.3 & Appendix B.2–B.3 branch-summed Stage-1/Stage-2 `clearedParityJetTable`
Hermite–Cramer coordinate recovery of `numPassing`**: under the same hypotheses, the branch-summed
coordinate Cramer quotients of `clearedParityJetTable` recover `numPassing φ.violations rows`. -/
theorem CNF.numPassing_eq_sum_branch_clearedParityJetTable_design
    {F : (V → Bool) → Type*} [∀ b, Fintype (F b)] {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) (rows : List (Fin φ.length → Bool))
    (S : Finset V) (e : ↥(univ \ S) ≃ Fin n')
    (scope : (b : V → Bool) → F b → Finset (Fin n'))
    (D : (b : V → Bool) → ReplacementDesign (scope b) Q r A₀ R τ)
    (emb : (b : V → Bool) → Fin rows.length → F b) (hQ : 0 < Q) :
    let ℓ := branchPrecision (Fintype.card V)
    let J := sparseParityJetOrder k R Q #(univ : Finset (Fin rows.length)) ℓ
    (numPassing φ.violations rows : ℤ) =
      ∑ b ∈ branchAssignments S,
        (∑ s : Fin ℓ,
          hermiteCramerNumerator (nodeInt (Q := Q)) hQ
            (sparseParityJetOrder_pos k R Q #(univ : Finset (Fin rows.length)) ℓ)
            (fun t j =>
              clearedParityJetTable (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b) (commonDenom Q R : ℤ) k ℓ J
                (designReplacementScaledIntMap (D b) (emb b)) (nodeInt t) j s) /
            (clearedProductDenom (commonDenom Q R : ℤ) k ℓ #(univ : Finset (Fin rows.length)) *
              (Polynomial.hermiteMatrix (nodeInt (Q := Q)) J).det)) % ((2 : ℤ) ^ ℓ) := by
  rw [← CNF.commonZeroCount_parityRowSystem]
  exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk rows S e
    scope D emb hQ

end CNFDeterminantRecovery

/-- Helper: any `Feasible β n b w M` instance implies `0 < numNodes n`. -/
theorem _root_.Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible.numNodes_pos
    {β n b w M : ℕ} (hF : Feasible β n b w M) :
    0 < numNodes n := by
  have hR := hF.thirtyTwo_le_rowBound
  have hQ := hF.six_mul_rowBound_le_numNodes
  omega

/-- **Unified Section 6.3 schedule feasibility, Hermite–Cramer & `clearedParityJetTable` recovery,
degree bound, and `2 ^ (A * interpolationScale n)` examination bound for `CNF.parityRowSystem`
([OpenAI2026ETH], §§5.4–5.5, 6.3, and Appendix B.2–B.3, printed pp. 38–43, 48–50):**
For any `k C_B β_B : ℕ`, at the threshold `N₁ ≥ 16384` of
`CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow k C_B β_B`,
whenever `∀ c ∈ φ, c.length ≤ k`, `N₁ ≤ Fintype.card V`, `φ.length ≤ B * Fintype.card V`,
`B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, `W ≤ BitString.initialRowWeightBound B φ.length`,
`∀ r ∈ rows, weight r ≤ W`, and `rows.length ≤ 6 * Fintype.card V`, at
`b₀ = CNF.parityBranchThreshold k W (Fintype.card V)` and `β = 2 * β_B + 5`, for any
free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`, there exist `hQ : 0 < numNodes n'`,
per-branch feasibility proofs `hF b`, and concrete `ReplacementDesign`s `D b` such that at shared
precision `ℓ = branchPrecision (Fintype.card V)` and canonical jet order
`J = sparseParityJetOrder k (rowBound (2 * β_B + 5) n') (numNodes n')`
`#(univ : Finset (Fin rows.length)) ℓ`:
1. `(commonZeroCount univ (φ.parityRowSystem rows) : ℤ)` equals the branch-summed Hermite–Cramer
   truncated-sum determinant residue at `nodeInt` and jet order `J`.
2. `(commonZeroCount univ (φ.parityRowSystem rows) : ℤ)` ALSO equals the branch-summed
   Stage-1/Stage-2 `clearedParityJetTable` coordinate Hermite–Cramer residue over `s : Fin ℓ` at
   `nodeInt` and jet order `J` (Appendix B.2–B.3, eq. `(B.1)`).
3. Every branch polynomial has
   `natDegree ≤ (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)`.
4. Every branch `b : V → Bool` has domain-examination count at most
   `(2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) * interpolationScale (Fintype.card V))`,
   and any per-branch examination family bounded by that quantity sums across `branchAssignments S`
   to at most `(2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *`
   `interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_branch_schedule_hermiteCramer_and_examBound_parityRowSystem_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ BitString.initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r ∈ rows, weight r ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
            (∃ (hQ : 0 < numNodes n')
                (hF : ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                    (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                      #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
                (D : ∀ b : V → Bool,
                  ReplacementDesign
                    (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                    (rowBound (2 * β_B + 5) n') (tauRat n')),
                let ℓ := branchPrecision (Fintype.card V)
                let J := sparseParityJetOrder k (rowBound (2 * β_B + 5) n') (numNodes n')
                  #(univ : Finset (Fin rows.length)) ℓ
                (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                      (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                        #(univ : Finset (Fin rows.length)) ℓ)
                      (fun t j =>
                        (Polynomial.taylor (nodeInt t)
                          (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                            (φ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                      (clearedProductDenom
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                        #(univ : Finset (Fin rows.length)) *
                        (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                          ((2 : ℤ) ^ ℓ)) ∧
                (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (∑ s : Fin ℓ,
                      hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                        (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                          #(univ : Finset (Fin rows.length)) ℓ)
                        (fun t j =>
                          clearedParityJetTable (univ : Finset (Fin rows.length))
                            (φ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ J
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                        (clearedProductDenom
                          (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                          #(univ : Finset (Fin rows.length)) *
                          (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                            ((2 : ℤ) ^ ℓ)) ∧
                (∀ b : V → Bool,
                  (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                    (designReplacementScaledIntMap (D b)
                      (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                    (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                ∀ (b : V → Bool)
                    (s_active : Finset
                      ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                  let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                  let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                  let C := (hF b).toCountingDesign (D b) s_active
                  (∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                    (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (examSum : (V → Bool) → ℝ),
              (∀ b ∈ branchAssignments S,
                examSum b ≤
                  (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ b ∈ branchAssignments S, examSum b) ≤
                (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V)) := by
  obtain ⟨N₁, hN₁, hrec⟩ :=
    CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow k C_B β_B
  refine ⟨N₁, hN₁, fun {V _ _ φ n' B W} hk hcard hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ S e
  obtain ⟨hn_bounds, ⟨hF, D, _, hdeg, hexam⟩, hsum⟩ :=
    hrec hk hcard hm hB hW_bound hW hlen e
  have hQ : 0 < numNodes n' := (hF (fun _ => false)).numNodes_pos
  refine ⟨hn_bounds, ⟨hQ, hF, D, ?_, ?_, hdeg, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk rows
      S e (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk rows
      S e (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ

/-- **Unified Lemma 6.1 + Lemma 6.2 + Section 6.3 greedy parity-test schedule with
Hermite–Cramer & `clearedParityJetTable` recovery and `2 ^ (A * interpolationScale n)` bounds:**
At every stage `i ≤ 3 * Fintype.card V`, the greedy trajectory `A i` admits per-branch `hF b` and
`D b` recovering `commonZeroCount univ (φ.parityRowSystem (A i))` (and `φ.modelCountOn Finset.univ`
at stage `3 * Fintype.card V`) via **both** explicit Hermite–Cramer truncated-sum determinants and
Stage-1/Stage-2 `clearedParityJetTable` coordinate sums at `nodeInt` and canonical jet order
`sparseParityJetOrder`, with single-branch and branch-summed `interpolationScale` examination
bounds. -/
theorem CNF.exists_greedy_parityRowSystem_hermiteCramer_recovery_and_examBound_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := BitString.initialRowWeightBound B φ.length
        let P := BitString.greedyRowListLength B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
          (∀ r ∈ A₀, weight r ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
              φ.modelCountOn Finset.univ ∧
            ∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              let S := heavyVars univ (univ : Finset (Fin (A i).length))
                (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀
              ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                (∃ (hQ : 0 < numNodes n')
                    (hF : ∀ b : V → Bool,
                      Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                        (∑ f : {j : Fin (A i).length //
                            j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                          #(branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b f)))
                    (D : ∀ b : V → Bool,
                      ReplacementDesign
                        (branchAugmentedScope S e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                        (rowBound (2 * β_B + 5) n') (tauRat n')),
                    let ℓ := branchPrecision (Fintype.card V)
                    let J := sparseParityJetOrder k (rowBound (2 * β_B + 5) n') (numNodes n')
                      #(univ : Finset (Fin (A i).length)) ℓ
                    (commonZeroCount (univ : Finset (Fin (A i).length))
                        (φ.parityRowSystem (A i)) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                          (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                            #(univ : Finset (Fin (A i).length)) ℓ)
                          (fun t j =>
                            (Polynomial.taylor (nodeInt t)
                              (univariateClearedParityTruncatedSum
                                (univ : Finset (Fin (A i).length))
                                (φ.branchParityRowSystem (A i) S e b)
                                (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                                (designReplacementScaledIntMap (D b)
                                  (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                          (clearedProductDenom
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                            #(univ : Finset (Fin (A i).length)) *
                            (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                              ((2 : ℤ) ^ ℓ)) ∧
                    (commonZeroCount (univ : Finset (Fin (A i).length))
                        (φ.parityRowSystem (A i)) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        (∑ s : Fin ℓ,
                          hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                            (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                              #(univ : Finset (Fin (A i).length)) ℓ)
                            (fun t j =>
                              clearedParityJetTable (univ : Finset (Fin (A i).length))
                                (φ.branchParityRowSystem (A i) S e b)
                                (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ J
                                (designReplacementScaledIntMap (D b)
                                  (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                            (clearedProductDenom
                              (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                              #(univ : Finset (Fin (A i).length)) *
                              (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                                ((2 : ℤ) ^ ℓ)) ∧
                    (∀ b : V → Bool,
                      (univariateClearedParityTruncatedSum (univ : Finset (Fin (A i).length))
                        (φ.branchParityRowSystem (A i) S e b)
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                        (designReplacementScaledIntMap (D b)
                          (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                        (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                    ∀ (b : V → Bool)
                        (s_active : Finset
                          ({j : Fin (A i).length //
                              j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n')),
                      let d := k * ((A i).length + 2 * (branchPrecision (Fintype.card V) - 1))
                      let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                      let C := (hF b).toCountingDesign (D b) s_active
                      (∑ t : Fin (numNodes n'),
                          (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                            (2 * (#(C.measurementBox t) : ℝ) *
                              ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                        (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                          interpolationScale (Fintype.card V))) ∧
                ∀ (examSum : (V → Bool) → ℝ),
                  (∀ b ∈ branchAssignments S,
                    examSum b ≤
                      (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                        interpolationScale (Fintype.card V))) →
                  (∑ b ∈ branchAssignments S, examSum b) ≤
                    (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V)) := by
  obtain ⟨N₁, hN₁, hgreedy⟩ :=
    CNF.exists_greedy_parityRowSystem_recovery_and_examBound_of_le_clog_pow k C_B β_B
  refine ⟨N₁, hN₁, fun {V _ _} φ {B} hk hcard hB1 hB_le hm => ?_⟩
  intro D₀ P b₀
  obtain ⟨A₀, hlen0, hw0, htraj⟩ := hgreedy φ hk hcard hB1 hB_le hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := htraj A γ h0 hA hγ
  refine ⟨hcount, fun i hi => ?_⟩
  obtain ⟨hlen_i, hstage_e⟩ := hstage i hi
  refine ⟨hlen_i, fun ⦃n'⦄ e => ?_⟩
  obtain ⟨hn_bounds, ⟨hF, D, _, hdeg, hexam⟩, hsum⟩ := hstage_e e
  have hQ : 0 < numNodes n' := (hF (fun _ => false)).numNodes_pos
  refine ⟨hn_bounds, ⟨hQ, hF, D, ?_, ?_, hdeg, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk (A i)
      _ e (fun b => branchAugmentedScope _ e univ (φ.parityRowSystem (A i)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk (A i)
      _ e (fun b => branchAugmentedScope _ e univ (φ.parityRowSystem (A i)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ

/-- **Unconditional Section 6.3 parity-row system existence, Hermite–Cramer &
`clearedParityJetTable` recovery of `φ.modelCountOn Finset.univ`, degree bound, and
`2 ^ (A * interpolationScale n)` examination bound:**
For any `k C_B β_B : ℕ`, at `N₁ ≥ 16384`, for any width-`≤ k` CNF `φ : CNF V` with
`N₁ ≤ Fintype.card V`, `1 ≤ B`, `B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B`, and
`φ.length ≤ B * Fintype.card V` (including `φ = []`), there exists a parity-row list
`rows : List (Fin φ.length → Bool)` (`rows.length ≤ 6 * Fintype.card V`) such that
`commonZeroCount univ (φ.parityRowSystem rows) = φ.modelCountOn Finset.univ`, and for any
free-variable equivalence `e : ↥(univ \ S) ≃ Fin n'`, there exist `hQ : 0 < numNodes n'`,
per-branch `hF b`, and concrete `ReplacementDesign`s `D b` recovering
`(φ.modelCountOn Finset.univ : ℤ)` via **both** explicit Hermite–Cramer truncated-sum determinants
and Stage-1/Stage-2 `clearedParityJetTable` coordinate sums at `nodeInt` and canonical jet order
`sparseParityJetOrder`, with single-branch and branch-summed `interpolationScale` examination
bounds. -/
theorem CNF.exists_parityRowSystem_modelCountOn_hermiteCramer_recovery_and_examBound_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₁ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := BitString.initialRowWeightBound B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ rows : List (Fin φ.length → Bool),
          rows.length ≤ 6 * Fintype.card V ∧
          commonZeroCount univ (φ.parityRowSystem rows) = φ.modelCountOn Finset.univ ∧
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
            (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
            (∃ (hQ : 0 < numNodes n')
                (hF : ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                    (∑ f : {j : Fin rows.length //
                        j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                      #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f)))
                (D : ∀ b : V → Bool,
                  ReplacementDesign
                    (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                    (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                    (rowBound (2 * β_B + 5) n') (tauRat n')),
                let ℓ := branchPrecision (Fintype.card V)
                let J := sparseParityJetOrder k (rowBound (2 * β_B + 5) n') (numNodes n')
                  #(univ : Finset (Fin rows.length)) ℓ
                (φ.modelCountOn Finset.univ : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                      (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                        #(univ : Finset (Fin rows.length)) ℓ)
                      (fun t j =>
                        (Polynomial.taylor (nodeInt t)
                          (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                            (φ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                      (clearedProductDenom
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                        #(univ : Finset (Fin rows.length)) *
                        (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                          ((2 : ℤ) ^ ℓ)) ∧
                (φ.modelCountOn Finset.univ : ℤ) =
                  (∑ b ∈ branchAssignments S,
                    (∑ s : Fin ℓ,
                      hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                        (sparseParityJetOrder_pos k (rowBound (2 * β_B + 5) n') (numNodes n')
                          #(univ : Finset (Fin rows.length)) ℓ)
                        (fun t j =>
                          clearedParityJetTable (univ : Finset (Fin rows.length))
                            (φ.branchParityRowSystem rows S e b)
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ J
                            (designReplacementScaledIntMap (D b)
                              (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                        (clearedProductDenom
                          (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                          #(univ : Finset (Fin rows.length)) *
                          (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                            ((2 : ℤ) ^ ℓ)) ∧
                (∀ b : V → Bool,
                  (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k ℓ
                    (designReplacementScaledIntMap (D b)
                      (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                    (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V)) ∧
                ∀ (b : V → Bool)
                    (s_active : Finset
                      ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                  let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                  let q := (d * rowBound (2 * β_B + 5) n') / numNodes n'
                  let C := (hF b).toCountingDesign (D b) s_active
                  (∑ t : Fin (numNodes n'),
                      (#{p : Finset (Fin n') × Finset (Fin n') | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                        (2 * (#(C.measurementBox t) : ℝ) *
                          ∑ g : Fin (numGroups n'), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                    (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (examSum : (V → Bool) → ℝ),
              (∀ b ∈ branchAssignments S,
                examSum b ≤
                  (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff k β_B : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ b ∈ branchAssignments S, examSum b) ≤
                (2 : ℝ) ^ (((CNF.parityBranchExamScaleCoeff k β_B + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V)) := by
  obtain ⟨N₁, hN₁, hmodel⟩ :=
    CNF.exists_parityRowSystem_modelCountOn_recovery_and_examBound_of_le_clog_pow k C_B β_B
  refine ⟨N₁, hN₁, fun {V _ _} φ {B} hk hcard hB1 hB_le hm => ?_⟩
  intro D₀ b₀
  obtain ⟨rows, hlen, hcount, hstage⟩ := hmodel φ hk hcard hB1 hB_le hm
  refine ⟨rows, hlen, hcount, fun ⦃n'⦄ e => ?_⟩
  obtain ⟨hn_bounds, ⟨hF, D, _, hdeg, hexam⟩, hsum⟩ := hstage e
  have hQ : 0 < numNodes n' := (hF (fun _ => false)).numNodes_pos
  refine ⟨hn_bounds, ⟨hQ, hF, D, ?_, ?_, hdeg, hexam⟩, hsum⟩
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk rows
      _ e (fun b => branchAugmentedScope _ e univ (φ.parityRowSystem rows) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk rows
      _ e (fun b => branchAugmentedScope _ e univ (φ.parityRowSystem rows) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ

/-! ### 3. Proposition 6.4 tree-wide Hermite–Cramer & `clearedParityJetTable` recovery -/

/-- **Proposition 6.4 tree-wide candidate-indexed Hermite–Cramer & `clearedParityJetTable`
recovery and total `2 ^ (O_k(interpolationScale n))` examination bounds ([OpenAI2026ETH],
§§5.4–5.5, 6.1–6.4, and Appendices A–B, printed pp. 38–50):**
For any `k ≥ 2`, there exists `N₃ ≥ 2 ^ 640000` such that for any finite variable type `V` with
`N₃ ≤ Fintype.card V` and any width-`≤ k` CNF `φ : CNF V`:
1. **Exact leaf-summed model-count conservation and `2 ^ (17 * interpolationScale n)` leaf-count
   bound:**
   `((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =`
   `φ.modelCountOn Finset.univ`, `2 ≤ numGroups (Fintype.card V)`,
   `(φ.prop64NormalizedLeaves k).length ≤ 2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1)`,
   and `((φ.prop64NormalizedLeaves k).length : ℝ) ≤`
   `(2 : ℝ) ^ (17 * interpolationScale (Fintype.card V))`.
2. **Per-leaf candidate-query cardinality and overhead bound:**
   For every leaf `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`),
   `Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) = 3 * Fintype.card V * (2 * ψ.length) ^ P + 1`
   `≤ CNF.leafCandidateQueryBound B ψ`, and
   `(CNF.leafCandidateQueryBound B ψ : ℝ) ≤ (2 : ℝ) ^ interpolationScale (Fintype.card V)`.
3. **Every candidate query and final query certified via explicit Hermite–Cramer determinants,
   Stage-1/Stage-2 `clearedParityJetTable` coordinate sums, and `interpolationScale` examination
   bounds:**
   There exist Lemma 6.1 initial rows `A₀` such that for any Lemma 6.2 greedy trajectory `A`:
   - `commonZeroCount univ (ψ.parityRowSystem (A (3 * Fintype.card V))) = ψ.modelCountOn univ`,
   - for **every** query `q : CNF.LeafCandidateQueryIndex V B ψ` (every candidate `(i, γ')` across
     `i < 3 * n` and ordered candidate list `γ'` with list multiplicity, including discarded
     candidates, plus the final query `Sum.inr ()`), and any free-variable equivalence
     `e : ↥(univ \ S_q) ≃ Fin n'`, there exist `hQ : 0 < numNodes n'`, per-branch `hF b`, and
     concrete `ReplacementDesign`s `D b` at schedule exponent `β = CNF.prop64ScheduleExponent k`
     recovering `commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows A q))` via **both**
     explicit Hermite–Cramer truncated-sum determinants and Stage-1/Stage-2 `clearedParityJetTable`
     coordinate sums at `nodeInt` and canonical jet order `sparseParityJetOrder`, with single-query
     branch-summed examination count at most
     `(2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) * interpolationScale n)` and
     candidate-summed leaf examination count `∑ q, queryExam q` at most
     `(2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) * interpolationScale n)`.
4. **Tree-wide single-query and total candidate-indexed examination bounds:**
   Summing across `φ.prop64NormalizedLeaves k` bounds the tree-wide single-query examination count
   by `(2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) * interpolationScale (Fintype.card V))` and
   the total candidate-indexed examination count across the entire sparsification tree by
   `(2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) * interpolationScale (Fintype.card V))`. -/
theorem CNF.exists_prop64NormalizedLeaves_greedy_total_hermiteCramer_recovery_and_examBound
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₃ : ℕ, 2 ^ 640000 ≤ N₃ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₃ ≤ Fintype.card V →
        let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
        ((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        2 ≤ numGroups (Fintype.card V) ∧
        (φ.prop64NormalizedLeaves k).length ≤
          2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) ∧
        ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
          (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) ∧
        (∀ L ∈ φ.prop64NormalizedLeaves k,
          let ψ := L.toCNF
          let D₀ := BitString.initialRowWeightBound B ψ.length
          let P := BitString.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) =
            3 * Fintype.card V * (2 * ψ.length) ^ P + 1 ∧
          Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) ≤
            CNF.leafCandidateQueryBound B ψ ∧
          (CNF.leafCandidateQueryBound B ψ : ℝ) ≤
            (2 : ℝ) ^ interpolationScale (Fintype.card V) ∧
          ∃ A₀ : List (Fin ψ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
            (∀ r ∈ A₀, weight r ≤ D₀) ∧
            ∀ (A : ℕ → List (Fin ψ.length → Bool))
              (γ : ℕ → Fin P → Fin ψ.length × Bool),
              A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
              (∀ i (γ' : Fin P → Fin ψ.length × Bool),
                commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                  commonZeroCount univ (ψ.parityRowSystem (A i ++ [testRow γ']))) →
              commonZeroCount univ (ψ.parityRowSystem (A (3 * Fintype.card V))) =
                ψ.modelCountOn Finset.univ ∧
              (∀ (q : CNF.LeafCandidateQueryIndex V B ψ),
                let rows := CNF.candidateQueryRows A q
                rows.length ≤ 6 * Fintype.card V ∧
                (∀ r ∈ rows, weight r ≤ D₀) ∧
                let S := heavyVars univ (univ : Finset (Fin rows.length))
                  (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
                ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                  (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                  (∃ (hQ : 0 < numNodes n')
                      (hF : ∀ b : V → Bool,
                        Feasible (CNF.prop64ScheduleExponent k) n' (b₀ + 1)
                          (max (k * (D₀ * 2 ^ k)) 1)
                          (∑ f : {j : Fin rows.length //
                              j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                            #(branchAugmentedScope S e univ (ψ.parityRowSystem rows) b f)))
                      (D : ∀ b : V → Bool,
                        ReplacementDesign
                          (branchAugmentedScope S e univ (ψ.parityRowSystem rows) b)
                          (numNodes n') (numGroups n')
                          (intervalStart (CNF.prop64ScheduleExponent k) n')
                          (rowBound (CNF.prop64ScheduleExponent k) n') (tauRat n')),
                      let ℓ := branchPrecision (Fintype.card V)
                      let J := sparseParityJetOrder k (rowBound (CNF.prop64ScheduleExponent k) n')
                        (numNodes n') #(univ : Finset (Fin rows.length)) ℓ
                      (commonZeroCount (univ : Finset (Fin rows.length))
                          (ψ.parityRowSystem rows) : ℤ) =
                        (∑ b ∈ branchAssignments S,
                          (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                            (sparseParityJetOrder_pos k
                              (rowBound (CNF.prop64ScheduleExponent k) n') (numNodes n')
                              #(univ : Finset (Fin rows.length)) ℓ)
                            (fun t j =>
                              (Polynomial.taylor (nodeInt t)
                                (univariateClearedParityTruncatedSum
                                  (univ : Finset (Fin rows.length))
                                  (ψ.branchParityRowSystem rows S e b)
                                  (commonDenom (numNodes n')
                                    (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                                  (designReplacementScaledIntMap (D b)
                                    (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                            (clearedProductDenom
                              (commonDenom (numNodes n')
                                (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                              #(univ : Finset (Fin rows.length)) *
                              (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                                ((2 : ℤ) ^ ℓ)) ∧
                      (commonZeroCount (univ : Finset (Fin rows.length))
                          (ψ.parityRowSystem rows) : ℤ) =
                        (∑ b ∈ branchAssignments S,
                          (∑ s : Fin ℓ,
                            hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                              (sparseParityJetOrder_pos k
                                (rowBound (CNF.prop64ScheduleExponent k) n') (numNodes n')
                                #(univ : Finset (Fin rows.length)) ℓ)
                              (fun t j =>
                                clearedParityJetTable (univ : Finset (Fin rows.length))
                                  (ψ.branchParityRowSystem rows S e b)
                                  (commonDenom (numNodes n')
                                    (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ J
                                  (designReplacementScaledIntMap (D b)
                                    (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                              (clearedProductDenom
                                (commonDenom (numNodes n')
                                  (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                                #(univ : Finset (Fin rows.length)) *
                                (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                                  ((2 : ℤ) ^ ℓ)) ∧
                      (∀ b : V → Bool,
                        (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                          (ψ.branchParityRowSystem rows S e b)
                          (commonDenom (numNodes n')
                            (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                          (designReplacementScaledIntMap (D b)
                            (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                          (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) *
                            (8 * Fintype.card V)) ∧
                      ∀ (b : V → Bool)
                          (s_active : Finset
                            ({j : Fin rows.length //
                                j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                        let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                        let q_jet := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                        let C := (hF b).toCountingDesign (D b) s_active
                        (∑ t : Fin (numNodes n'),
                            (#{p : Finset (Fin n') × Finset (Fin n') |
                                #p.1 ≤ q_jet ∧ p.2 ⊆ p.1} : ℝ) *
                              (2 * (#(C.measurementBox t) : ℝ) *
                                ∑ g : Fin (numGroups n'),
                                  (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                          (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                            interpolationScale (Fintype.card V))) ∧
                  ∀ (examSum : (V → Bool) → ℝ),
                    (∀ b ∈ branchAssignments S,
                      examSum b ≤
                        (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                          interpolationScale (Fintype.card V))) →
                    (∑ b ∈ branchAssignments S, examSum b) ≤
                      (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                        interpolationScale (Fintype.card V))) ∧
              ∀ (queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ),
                (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
                  queryExam q ≤
                    (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V))) →
                (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q) ≤
                  (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
                    interpolationScale (Fintype.card V))) ∧
        (∀ (leafExam : ClauseSet V → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            leafExam L ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          (((φ.prop64NormalizedLeaves k).map leafExam).sum) ≤
            (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) ∧
        (∀ (treeQueryExam : (L : ClauseSet V) →
              CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            ∀ q : CNF.LeafCandidateQueryIndex V B L.toCNF,
              treeQueryExam L q ≤
                (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V))) →
          (((φ.prop64NormalizedLeaves k).map fun (L : ClauseSet V) =>
              ∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum) ≤
            (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) := by
  obtain ⟨N₃, hN₃, hprop64⟩ :=
    CNF.exists_prop64NormalizedLeaves_greedy_total_recovery_and_examBound hk
  refine ⟨N₃, hN₃, fun {V _ _} φ hk_φ hcard => ?_⟩
  intro B
  obtain ⟨hsum_mc, hs2, hlen_pow, hlen_scale, hleaf, htree_branch, htree_total⟩ :=
    hprop64 φ hk_φ hcard
  refine ⟨hsum_mc, hs2, hlen_pow, hlen_scale, fun L hL => ?_, htree_branch, htree_total⟩
  intro ψ D₀ P b₀
  obtain ⟨hk_ψ, hm_ψ, hcand_scale, A₀, hlen0, hw0, htraj⟩ := hleaf L hL
  refine ⟨hk_ψ, hm_ψ, CNF.card_leafCandidateQueryIndex_eq B ψ,
    CNF.card_leafCandidateQueryIndex_le B ψ, hcand_scale, A₀, hlen0, hw0,
    fun A γ h0 hA hmin => ?_⟩
  obtain ⟨hcount, hquery, hleaf_sum⟩ := htraj A γ h0 hA hmin
  refine ⟨hcount, fun q => ?_, hleaf_sum⟩
  obtain ⟨hlen_q, hw_q, hstage_q⟩ := hquery q
  refine ⟨hlen_q, hw_q, fun ⦃n'⦄ e => ?_⟩
  obtain ⟨hn_bounds, ⟨hF, D, _, hdeg, hexam⟩, hsum⟩ := hstage_q e
  have hQ : 0 < numNodes n' := (hF (fun _ => false)).numNodes_pos
  refine ⟨hn_bounds, ⟨hQ, hF, D, ?_, ?_, hdeg, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk_ψ
      (CNF.candidateQueryRows A q) _ e
      (fun b => branchAugmentedScope _ e univ (ψ.parityRowSystem (CNF.candidateQueryRows A q)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk_ψ
      (CNF.candidateQueryRows A q) _ e
      (fun b => branchAugmentedScope _ e univ (ψ.parityRowSystem (CNF.candidateQueryRows A q)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ

/-- **Proposition 6.4 unconditional trajectory-instantiated tree-wide Hermite–Cramer &
`clearedParityJetTable` recovery and total candidate-indexed `2 ^ (O_k(interpolationScale n))`
examination bounds ([OpenAI2026ETH], §6.4 & Appendices A–B, printed pp. 43–50):**
For any `k ≥ 2`, at `N₃ ≥ 2 ^ 640000`, for any finite variable type `V` with `N₃ ≤ Fintype.card V`
and any width-`≤ k` CNF `φ : CNF V`, every leaf `L ∈ φ.prop64NormalizedLeaves k` (`ψ := L.toCNF`)
unconditionally admits a concrete Lemma 6.2 greedy trajectory `A : ℕ → List (Fin ψ.length → Bool)`
such that
`commonZeroCount univ (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =`
`ψ.modelCountOn Finset.univ`, every round satisfies the Lemma 6.2 minimality inequality, and
every candidate query `q : CNF.LeafCandidateQueryIndex V B ψ` (including discarded candidates with
list multiplicity and the final query `Sum.inr ()`) is recovered via **both** explicit
Hermite–Cramer truncated-sum determinants and Stage-1/Stage-2 `clearedParityJetTable` coordinate
sums at `nodeInt` and canonical jet order `sparseParityJetOrder`, with per-query, per-leaf
candidate-summed, and tree-wide candidate-summed `interpolationScale` examination bounds. -/
theorem CNF.exists_prop64NormalizedLeaves_total_hermiteCramer_recovery_and_examBound
    {k : ℕ} (hk : 2 ≤ k) :
    ∃ N₃ : ℕ, 2 ^ 640000 ≤ N₃ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V),
        (∀ c ∈ φ, c.length ≤ k) →
        N₃ ≤ Fintype.card V →
        let B := CNF.prop64LeafClauseRatio k (Fintype.card V)
        ((φ.prop64NormalizedLeaves k).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
          φ.modelCountOn Finset.univ ∧
        2 ≤ numGroups (Fintype.card V) ∧
        (φ.prop64NormalizedLeaves k).length ≤
          2 ^ (Fintype.card V / numGroups (Fintype.card V) + 1) ∧
        ((φ.prop64NormalizedLeaves k).length : ℝ) ≤
          (2 : ℝ) ^ (17 * interpolationScale (Fintype.card V)) ∧
        (∀ L ∈ φ.prop64NormalizedLeaves k,
          let ψ := L.toCNF
          let D₀ := BitString.initialRowWeightBound B ψ.length
          let P := BitString.greedyRowListLength B ψ.length
          let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
          (∀ c ∈ ψ, c.length ≤ k) ∧
          ψ.length ≤ B * Fintype.card V ∧
          Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) =
            3 * Fintype.card V * (2 * ψ.length) ^ P + 1 ∧
          Fintype.card (CNF.LeafCandidateQueryIndex V B ψ) ≤
            CNF.leafCandidateQueryBound B ψ ∧
          (CNF.leafCandidateQueryBound B ψ : ℝ) ≤
            (2 : ℝ) ^ interpolationScale (Fintype.card V) ∧
          ∃ A : ℕ → List (Fin ψ.length → Bool),
            commonZeroCount univ
              (ψ.parityRowSystem (CNF.candidateQueryRows (B := B) A (Sum.inr ()))) =
              ψ.modelCountOn Finset.univ ∧
            (∀ (i : Fin (3 * Fintype.card V)) (γ' : Fin P → Fin ψ.length × Bool),
              commonZeroCount univ (ψ.parityRowSystem (A (i.1 + 1))) ≤
                commonZeroCount univ
                  (ψ.parityRowSystem (CNF.candidateQueryRows A (Sum.inl (i, γ'))))) ∧
            (∀ (q : CNF.LeafCandidateQueryIndex V B ψ),
              let rows := CNF.candidateQueryRows A q
              rows.length ≤ 6 * Fintype.card V ∧
              (∀ r ∈ rows, weight r ≤ D₀) ∧
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (ψ.parityRowSystem rows j)) b₀
              ∀ ⦃n' : ℕ⦄ (e : ↥(univ \ S) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ n' ≤ Fintype.card V) ∧
                (∃ (hQ : 0 < numNodes n')
                    (hF : ∀ b : V → Bool,
                      Feasible (CNF.prop64ScheduleExponent k) n' (b₀ + 1)
                        (max (k * (D₀ * 2 ^ k)) 1)
                        (∑ f : {j : Fin rows.length //
                            j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                          #(branchAugmentedScope S e univ (ψ.parityRowSystem rows) b f)))
                    (D : ∀ b : V → Bool,
                      ReplacementDesign
                        (branchAugmentedScope S e univ (ψ.parityRowSystem rows) b)
                        (numNodes n') (numGroups n')
                        (intervalStart (CNF.prop64ScheduleExponent k) n')
                        (rowBound (CNF.prop64ScheduleExponent k) n') (tauRat n')),
                    let ℓ := branchPrecision (Fintype.card V)
                    let J := sparseParityJetOrder k (rowBound (CNF.prop64ScheduleExponent k) n')
                      (numNodes n') #(univ : Finset (Fin rows.length)) ℓ
                    (commonZeroCount (univ : Finset (Fin rows.length))
                        (ψ.parityRowSystem rows) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        (hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                          (sparseParityJetOrder_pos k
                            (rowBound (CNF.prop64ScheduleExponent k) n') (numNodes n')
                            #(univ : Finset (Fin rows.length)) ℓ)
                          (fun t j =>
                            (Polynomial.taylor (nodeInt t)
                              (univariateClearedParityTruncatedSum
                                (univ : Finset (Fin rows.length))
                                (ψ.branchParityRowSystem rows S e b)
                                (commonDenom (numNodes n')
                                  (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                                (designReplacementScaledIntMap (D b)
                                  (fun j => Sum.inl ⟨j, mem_univ j⟩)))).coeff j) /
                          (clearedProductDenom
                            (commonDenom (numNodes n')
                              (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                            #(univ : Finset (Fin rows.length)) *
                            (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                              ((2 : ℤ) ^ ℓ)) ∧
                    (commonZeroCount (univ : Finset (Fin rows.length))
                        (ψ.parityRowSystem rows) : ℤ) =
                      (∑ b ∈ branchAssignments S,
                        (∑ s : Fin ℓ,
                          hermiteCramerNumerator (nodeInt (Q := numNodes n')) hQ
                            (sparseParityJetOrder_pos k
                              (rowBound (CNF.prop64ScheduleExponent k) n') (numNodes n')
                              #(univ : Finset (Fin rows.length)) ℓ)
                            (fun t j =>
                              clearedParityJetTable (univ : Finset (Fin rows.length))
                                (ψ.branchParityRowSystem rows S e b)
                                (commonDenom (numNodes n')
                                  (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ J
                                (designReplacementScaledIntMap (D b)
                                  (fun j => Sum.inl ⟨j, mem_univ j⟩)) (nodeInt t) j s) /
                            (clearedProductDenom
                              (commonDenom (numNodes n')
                                (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                              #(univ : Finset (Fin rows.length)) *
                              (Polynomial.hermiteMatrix (nodeInt (Q := numNodes n')) J).det)) %
                                ((2 : ℤ) ^ ℓ)) ∧
                    (∀ b : V → Bool,
                      (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                        (ψ.branchParityRowSystem rows S e b)
                        (commonDenom (numNodes n')
                          (rowBound (CNF.prop64ScheduleExponent k) n') : ℤ) k ℓ
                        (designReplacementScaledIntMap (D b)
                          (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                        (k * (rowBound (CNF.prop64ScheduleExponent k) n' - 1)) *
                          (8 * Fintype.card V)) ∧
                    ∀ (b : V → Bool)
                        (s_active : Finset
                          ({j : Fin rows.length //
                              j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n')),
                      let d := k * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))
                      let q_jet := (d * rowBound (CNF.prop64ScheduleExponent k) n') / numNodes n'
                      let C := (hF b).toCountingDesign (D b) s_active
                      (∑ t : Fin (numNodes n'),
                          (#{p : Finset (Fin n') × Finset (Fin n') |
                              #p.1 ≤ q_jet ∧ p.2 ⊆ p.1} : ℝ) *
                            (2 * (#(C.measurementBox t) : ℝ) *
                              ∑ g : Fin (numGroups n'),
                                (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                        (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                          interpolationScale (Fintype.card V))) ∧
                ∀ (examSum : (V → Bool) → ℝ),
                  (∀ b ∈ branchAssignments S,
                    examSum b ≤
                      (2 : ℝ) ^ ((CNF.prop64BranchExamScaleCoeff k : ℝ) *
                        interpolationScale (Fintype.card V))) →
                  (∑ b ∈ branchAssignments S, examSum b) ≤
                    (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                      interpolationScale (Fintype.card V))) ∧
            ∀ (queryExam : CNF.LeafCandidateQueryIndex V B ψ → ℝ),
              (∀ q : CNF.LeafCandidateQueryIndex V B ψ,
                queryExam q ≤
                  (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                    interpolationScale (Fintype.card V))) →
              (∑ q : CNF.LeafCandidateQueryIndex V B ψ, queryExam q) ≤
                (2 : ℝ) ^ ((CNF.prop64LeafQueryExamScaleCoeff k : ℝ) *
                  interpolationScale (Fintype.card V))) ∧
        (∀ (leafExam : ClauseSet V → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            leafExam L ≤
              (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                interpolationScale (Fintype.card V))) →
          (((φ.prop64NormalizedLeaves k).map leafExam).sum) ≤
            (2 : ℝ) ^ ((CNF.prop64TreeExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) ∧
        (∀ (treeQueryExam : (L : ClauseSet V) →
              CNF.LeafCandidateQueryIndex V B L.toCNF → ℝ),
          (∀ L ∈ φ.prop64NormalizedLeaves k,
            ∀ q : CNF.LeafCandidateQueryIndex V B L.toCNF,
              treeQueryExam L q ≤
                (2 : ℝ) ^ (((CNF.prop64BranchExamScaleCoeff k + 32 : ℕ) : ℝ) *
                  interpolationScale (Fintype.card V))) →
          (((φ.prop64NormalizedLeaves k).map fun (L : ClauseSet V) =>
              ∑ q : CNF.LeafCandidateQueryIndex V B L.toCNF, treeQueryExam L q).sum) ≤
            (2 : ℝ) ^ ((CNF.prop64TotalExamScaleCoeff k : ℝ) *
              interpolationScale (Fintype.card V))) := by
  obtain ⟨N₃, hN₃, htotal⟩ :=
    CNF.exists_prop64NormalizedLeaves_total_recovery_and_examBound hk
  refine ⟨N₃, hN₃, fun {V _ _} φ hk_φ hcard => ?_⟩
  intro B
  obtain ⟨hsum_mc, hs2, hlen_pow, hlen_scale, hleaf, htree_branch, htree_total⟩ :=
    htotal φ hk_φ hcard
  refine ⟨hsum_mc, hs2, hlen_pow, hlen_scale, fun L hL => ?_, htree_branch, htree_total⟩
  intro ψ D₀ P b₀
  obtain ⟨hk_ψ, hm_ψ, hcand_scale, A, hcount, hmin, hquery, hleaf_sum⟩ := hleaf L hL
  refine ⟨hk_ψ, hm_ψ, CNF.card_leafCandidateQueryIndex_eq B ψ,
    CNF.card_leafCandidateQueryIndex_le B ψ, hcand_scale, A, hcount, hmin,
    fun q => ?_, hleaf_sum⟩
  obtain ⟨hlen_q, hw_q, hstage_q⟩ := hquery q
  refine ⟨hlen_q, hw_q, fun ⦃n'⦄ e => ?_⟩
  obtain ⟨hn_bounds, ⟨hF, D, _, hdeg, hexam⟩, hsum⟩ := hstage_q e
  have hQ : 0 < numNodes n' := (hF (fun _ => false)).numNodes_pos
  refine ⟨hn_bounds, ⟨hQ, hF, D, ?_, ?_, hdeg, hexam⟩, hsum⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_hermiteCramerNumerator_design hk_ψ
      (CNF.candidateQueryRows A q) _ e
      (fun b => branchAugmentedScope _ e univ (ψ.parityRowSystem (CNF.candidateQueryRows A q)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_clearedParityJetTable_design hk_ψ
      (CNF.candidateQueryRows A q) _ e
      (fun b => branchAugmentedScope _ e univ (ψ.parityRowSystem (CNF.candidateQueryRows A q)) b) D
      (fun _ j => Sum.inl ⟨j, mem_univ j⟩) hQ

end Cslib.Logic.PL
