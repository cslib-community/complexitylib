/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseParitySchedule
public import Complexity.Logics.Propositional.CNF.SparseDesignCounter

/-!
# Schedule-Instantiated Exact Recovery for the CNF Sparse Parity-Design Counter

This module composes the Section 6.3 compiled parity-row schedule supplier of
`Complexity.Computability.Complexity.FineGrained.SparseParitySchedule` with the `ReplacementDesign`
constant-term recovery and univariate numerator degree bounds of
`Complexity.Logics.Propositional.CNF.SparseDesignCounter`, following Sections 5.4–5.5 and 6.1–6.3
(printed pp. 38–43) of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]:

1. **Index-equivalence bridge between `Fin m ⊕ Fin n'` and `{j : Fin m // j ∈ univ} ⊕ Fin n'`**:
   - `CNF.parityRowAugmentedIndexEquiv`: canonical equivalence
     `Fin m ⊕ Fin n' ≃ {j : Fin m // j ∈ (univ : Finset (Fin m))} ⊕ Fin n'`.
   - `CNF.parityRowAugmentedInl`: active-equation factor embedding into `{j // j ∈ univ} ⊕ Fin n'`.
   - `CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inl` and
     `CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inr`: evaluate
     `branchAugmentedScope S e univ (φ.parityRowSystem rows) b` along
     `CNF.parityRowAugmentedIndexEquiv`.
2. **Schedule-instantiated exact recovery of `commonZeroCount` and `numPassing` (§5.4–5.5 & §6.3)**:
   - `CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq` and
     `CNF.exists_schedule_design_numPassing_eq`: combine
     `CNF.exists_branch_schedule_parityRowSystem` with
     `CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design` and
     `CNF.numPassing_eq_sum_branch_emod_ediv_design` under polylogarithmic schedule bounds.
   - `CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow` and
     `CNF.exists_schedule_design_numPassing_of_le_clog_pow`: combine the unconditional
     polylogarithmic schedule supplier `CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow`
     (`B ≤ C_B * (Nat.clog 2 n) ^ β_B`, `b₀ = CNF.parityBranchThreshold k W n`,
     `β = 2 * β_B + 5`) with exact branch-summed constant-term recovery and numerator degree bounds.
3. **End-to-end greedy `modelCountOn` schedule-design recovery (§6.1–6.3)**:
   - `CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_eq`: combines
     `CNF.exists_greedy_parityRowSystem_branch_schedule` with exact branch-summed constant-term
     recovery of `φ.modelCountOn Finset.univ` and the `(k * (rowBound β n' - 1)) * (8 * n)`
     numerator degree bound after `3 * n` greedy rounds.
   - `CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow`: combines
     `CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow` with exact branch-summed
     constant-term recovery of `φ.modelCountOn Finset.univ` unconditionally for any width-`≤ k` CNF
     with `φ.length ≤ B * n` and `B ≤ C_B * (Nat.clog 2 n) ^ β_B`.

## Main definitions

* `Cslib.Logic.PL.CNF.parityRowAugmentedIndexEquiv`
* `Cslib.Logic.PL.CNF.parityRowAugmentedInl`

## Main results

* `Cslib.Logic.PL.CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inl`
* `Cslib.Logic.PL.CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inr`
* `Cslib.Logic.PL.CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq`
* `Cslib.Logic.PL.CNF.exists_schedule_design_numPassing_eq`
* `Cslib.Logic.PL.CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow`
* `Cslib.Logic.PL.CNF.exists_schedule_design_numPassing_of_le_clog_pow`
* `Cslib.Logic.PL.CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_eq`
* `Cslib.Logic.PL.CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow`

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
  (Sections 5.4–5.5, pp. 38–39; Sections 6.1–6.3, pp. 39–43)
-/

public section

namespace Cslib.Logic.PL

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

variable {V : Type*} {n' : ℕ}

/-! ### 1. Index-equivalence bridge between `Fin m ⊕ Fin n'` and `{j // j ∈ univ} ⊕ Fin n'` -/

/-- Canonical equivalence between the flat factor index `Fin m ⊕ Fin n'` of
`CNF.branchParityRowNeutralScope` and the active-subtype factor index
`{j : Fin m // j ∈ (univ : Finset (Fin m))} ⊕ Fin n'` of `branchAugmentedScope`. -/
@[expose]
def CNF.parityRowAugmentedIndexEquiv (m n' : ℕ) :
    Fin m ⊕ Fin n' ≃ {j : Fin m // j ∈ (univ : Finset (Fin m))} ⊕ Fin n' :=
  Equiv.sumCongr (Equiv.subtypeUnivEquiv mem_univ).symm (Equiv.refl (Fin n'))

/-- Active-equation factor embedding `Fin m → {j : Fin m // j ∈ univ} ⊕ Fin n'` into the left
summand of `branchAugmentedScope`. -/
@[expose]
def CNF.parityRowAugmentedInl {m n' : ℕ} (j : Fin m) :
    {j : Fin m // j ∈ (univ : Finset (Fin m))} ⊕ Fin n' :=
  Sum.inl ⟨j, mem_univ j⟩

@[simp]
theorem CNF.parityRowAugmentedIndexEquiv_inl {m n' : ℕ} (j : Fin m) :
    CNF.parityRowAugmentedIndexEquiv m n' (Sum.inl j) = CNF.parityRowAugmentedInl j :=
  rfl

@[simp]
theorem CNF.parityRowAugmentedIndexEquiv_inr {m n' : ℕ} (v : Fin n') :
    CNF.parityRowAugmentedIndexEquiv m n' (Sum.inr v) = Sum.inr v :=
  rfl

/-- Evaluating `branchAugmentedScope S e univ (φ.parityRowSystem rows) b` at
`CNF.parityRowAugmentedInl j` yields `branchEquationScope S e (φ.parityRowSystem rows) b j`. -/
@[simp]
theorem CNF.branchAugmentedScope_parityRowAugmentedInl [Fintype V] [DecidableEq V]
    (φ : CNF V) (rows : List (Fin φ.length → Bool)) (S : Finset V)
    (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool) (j : Fin rows.length) :
    branchAugmentedScope S e univ (φ.parityRowSystem rows) b (CNF.parityRowAugmentedInl j) =
      branchEquationScope S e (φ.parityRowSystem rows) b j :=
  branchAugmentedScope_inl S e univ (φ.parityRowSystem rows) b ⟨j, mem_univ j⟩

/-- Evaluating `branchAugmentedScope S e univ (φ.parityRowSystem rows) b` at
`CNF.parityRowAugmentedIndexEquiv rows.length n' (Sum.inl j)` yields
`branchEquationScope S e (φ.parityRowSystem rows) b j`. -/
theorem CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inl [Fintype V] [DecidableEq V]
    (φ : CNF V) (rows : List (Fin φ.length → Bool)) (S : Finset V)
    (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool) (j : Fin rows.length) :
    branchAugmentedScope S e univ (φ.parityRowSystem rows) b
        (CNF.parityRowAugmentedIndexEquiv rows.length n' (Sum.inl j)) =
      branchEquationScope S e (φ.parityRowSystem rows) b j :=
  branchAugmentedScope_inl S e univ (φ.parityRowSystem rows) b ⟨j, mem_univ j⟩

/-- Evaluating `branchAugmentedScope S e univ (φ.parityRowSystem rows) b` at
`CNF.parityRowAugmentedIndexEquiv rows.length n' (Sum.inr v)` yields the neutral singleton scope
`{v}`. -/
theorem CNF.branchAugmentedScope_parityRowSystem_comp_equiv_inr [Fintype V] [DecidableEq V]
    (φ : CNF V) (rows : List (Fin φ.length → Bool)) (S : Finset V)
    (e : ↥(univ \ S) ≃ Fin n') (b : V → Bool) (v : Fin n') :
    branchAugmentedScope S e univ (φ.parityRowSystem rows) b
        (CNF.parityRowAugmentedIndexEquiv rows.length n' (Sum.inr v)) = {v} :=
  branchAugmentedScope_inr S e univ (φ.parityRowSystem rows) b v

/-! ### 2. Schedule-instantiated exact recovery of `commonZeroCount` and `numPassing` -/

/-- **§5.4–5.5 & §6.3 (schedule-instantiated `ReplacementDesign` recovery of `commonZeroCount` on
`φ.parityRowSystem rows`)**: for every `1 ≤ β`, the threshold `n₀ ≥ 20` of
`CNF.exists_branch_schedule_parityRowSystem` guarantees that whenever `n₀ ≤ n'`,
`b₀ + 1 ≤ (Nat.clog 2 n') ^ β`, `max (k * (W * 2 ^ k)) 1 ≤ (Nat.clog 2 n') ^ β`,
`∀ c ∈ φ, c.length ≤ k`, and `∀ r_row ∈ rows, weight r_row ≤ W`, there exists a family `D` of
concrete Lemma 4.8 schedule `ReplacementDesign`s across all branches `b : V → Bool` (with every
branch satisfying `Feasible`) such that the branch-summed modular evaluation of
`univariateClearedParityTruncatedSum` at `T = 0` equals
`(commonZeroCount univ (φ.parityRowSystem rows) : ℤ)` and every branch numerator has degree at most
`(k * (rowBound β n' - 1)) * (rows.length + 2 * (branchPrecision (Fintype.card V) - 1))`. -/
theorem CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' k W b₀ : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r_row ∈ rows, weight r_row ≤ W) →
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            n₀ ≤ n' →
            b₀ + 1 ≤ Nat.clog 2 n' ^ β →
            max (k * (W * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
            (∀ b : V → Bool,
              Feasible β n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))) ∧
            ∃ D : (b : V → Bool) →
                ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
              (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                (∑ b ∈ branchAssignments S,
                  ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                      clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        #(univ : Finset (Fin rows.length))) %
                          ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
              ∀ b : V → Bool,
                (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S e b)
                  (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                  (branchPrecision (Fintype.card V))
                  (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                (k * (rowBound β n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := CNF.exists_branch_schedule_parityRowSystem hβ
  refine ⟨n₀, hn₀20, fun {V _ _ φ n' k W b₀} hk {rows} hW => ?_⟩
  intro S e hn' hb₀ hw
  have h_all := hsched hk hW e hn' hb₀ hw
  let D : (b : V → Bool) →
      ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n') :=
    fun b => Classical.choice (h_all b).2
  refine ⟨fun b => (h_all b).1, D, ?_, fun b => ?_⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ => CNF.parityRowAugmentedInl)
  · exact CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
      (D b) CNF.parityRowAugmentedInl (branchPrecision (Fintype.card V))

/-- **§5.4–5.5 & §6.3 (schedule-instantiated `ReplacementDesign` recovery of
`numPassing φ.violations rows`)**: under the hypotheses of
`CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq`, the branch-summed constant-term
evaluation from the schedule `ReplacementDesign` family `D` recovers
`(numPassing φ.violations rows : ℤ)`. -/
theorem CNF.exists_schedule_design_numPassing_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' k W b₀ : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r_row ∈ rows, weight r_row ≤ W) →
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            n₀ ≤ n' →
            b₀ + 1 ≤ Nat.clog 2 n' ^ β →
            max (k * (W * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
            (∀ b : V → Bool,
              Feasible β n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))) ∧
            ∃ D : (b : V → Bool) →
                ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
              (numPassing φ.violations rows : ℤ) =
                (∑ b ∈ branchAssignments S,
                  ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                      clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        #(univ : Finset (Fin rows.length))) %
                          ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
              ∀ b : V → Bool,
                (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S e b)
                  (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                  (branchPrecision (Fintype.card V))
                  (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                (k * (rowBound β n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨n₀, hn₀20, hsched⟩ := CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq hβ
  refine ⟨n₀, hn₀20, fun {V _ _ φ n' k W b₀} hk {rows} hW => ?_⟩
  intro S e hn' hb₀ hw
  rw [← CNF.commonZeroCount_parityRowSystem]
  exact hsched hk hW e hn' hb₀ hw

/-- **Unconditional Section 6.3 schedule-design recovery of `commonZeroCount` for
`B ≤ C_B * (Nat.clog 2 n) ^ β_B`**: combines
`CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow` with
`CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design` and
`CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le`. -/
theorem CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₀ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ CNF.initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r_row ∈ rows, weight r_row ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt ∧
            (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
            #(branchAssignments S) ≤
              2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) ∧
            (∀ b : V → Bool,
              Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))) ∧
            ∃ D : (b : V → Bool) →
                ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                  (rowBound (2 * β_B + 5) n') (tauRat n'),
              (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                (∑ b ∈ branchAssignments S,
                  ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                      clearedProductDenom
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        #(univ : Finset (Fin rows.length))) %
                          ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
              ∀ b : V → Bool,
                (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S e b)
                  (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                  (branchPrecision (Fintype.card V))
                  (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                (k * (rowBound (2 * β_B + 5) n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨N₀, hN₀20, hsched⟩ := CNF.exists_branch_schedule_parityRowSystem_of_le_clog_pow k C_B β_B
  refine ⟨N₀, hN₀20, fun {V _ _ φ n' B W} hk hN₀ hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ S e
  obtain ⟨hsqrt, hcard, hbr, h_all⟩ := hsched hk hN₀ hm hB hW_bound hW hlen e
  let D : (b : V → Bool) →
      ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
        (rowBound (2 * β_B + 5) n') (tauRat n') :=
    fun b => Classical.choice (h_all b).2
  refine ⟨hsqrt, hcard, hbr, fun b => (h_all b).1, D, ?_, fun b => ?_⟩
  · exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ => CNF.parityRowAugmentedInl)
  · exact CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
      (D b) CNF.parityRowAugmentedInl (branchPrecision (Fintype.card V))

/-- **Unconditional Section 6.3 schedule-design recovery of `numPassing φ.violations rows` for
`B ≤ C_B * (Nat.clog 2 n) ^ β_B`**. -/
theorem CNF.exists_schedule_design_numPassing_of_le_clog_pow (k C_B β_B : ℕ) :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' B W : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        N₀ ≤ Fintype.card V →
        φ.length ≤ B * Fintype.card V →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        W ≤ CNF.initialRowWeightBound B φ.length →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r_row ∈ rows, weight r_row ≤ W) →
          rows.length ≤ 6 * Fintype.card V →
          let b₀ := CNF.parityBranchThreshold k W (Fintype.card V)
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            2 ≤ (Nat.clog 2 (Fintype.card V)).sqrt ∧
            (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
            #(branchAssignments S) ≤
              2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) ∧
            (∀ b : V → Bool,
              Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))) ∧
            ∃ D : (b : V → Bool) →
                ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                  (rowBound (2 * β_B + 5) n') (tauRat n'),
              (numPassing φ.violations rows : ℤ) =
                (∑ b ∈ branchAssignments S,
                  ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                      clearedProductDenom
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        #(univ : Finset (Fin rows.length))) %
                          ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
              ∀ b : V → Bool,
                (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S e b)
                  (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                  (branchPrecision (Fintype.card V))
                  (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                (k * (rowBound (2 * β_B + 5) n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) := by
  obtain ⟨N₀, hN₀20, hsched⟩ :=
    CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow k C_B β_B
  refine ⟨N₀, hN₀20, fun {V _ _ φ n' B W} hk hN₀ hm hB hW_bound {rows} hW hlen => ?_⟩
  intro b₀ S e
  rw [← CNF.commonZeroCount_parityRowSystem]
  exact hsched hk hN₀ hm hB hW_bound hW hlen e

/-! ### 3. End-to-end greedy `modelCountOn` schedule-design recovery -/

/-- **Lemmas 6.1–6.2 & §§5.4–5.5, 6.3 (conditional greedy parity-test schedule-design recovery of
`φ.modelCountOn Finset.univ`)**: combines `CNF.exists_greedy_parityRowSystem_branch_schedule` with
`CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design` so that at every stage
`i ≤ 3 * n`, concrete Lemma 4.8 schedule `ReplacementDesign`s exist across all heavy-variable
branches, and at the final stage `i = 3 * n`, they recover `(φ.modelCountOn Finset.univ : ℤ)` with
univariate numerator degree at most `(k * (rowBound β n' - 1)) * (8 * Fintype.card V)`. -/
theorem CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_eq {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {k B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        1 ≤ Fintype.card V →
        1 ≤ B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := CNF.initialRowWeightBound B φ.length
        let P := CNF.greedyRowListLength B φ.length
        ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
          (∀ r_row ∈ A₀, weight r_row ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
              φ.modelCountOn Finset.univ ∧
            (∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              ∀ ⦃n' b₀ : ℕ⦄
                (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A i).length))
                  (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀) ≃ Fin n'),
                n₀ ≤ n' →
                b₀ + 1 ≤ Nat.clog 2 n' ^ β →
                max (k * (max D₀ P * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
                ∀ b : V → Bool,
                  Feasible β n' (b₀ + 1) (max (k * (max D₀ P * 2 ^ k)) 1)
                    (∑ f : {j : Fin (A i).length //
                        j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                      #(branchAugmentedScope
                        (heavyVars univ (univ : Finset (Fin (A i).length))
                          (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                        e univ (φ.parityRowSystem (A i)) b f)) ∧
                    Nonempty
                      (ReplacementDesign
                        (branchAugmentedScope
                          (heavyVars univ (univ : Finset (Fin (A i).length))
                            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                          e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart β n')
                        (rowBound β n') (tauRat n'))) ∧
            ∀ ⦃n' b₀ : ℕ⦄,
              let rows := A (3 * Fintype.card V)
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (φ.parityRowSystem rows j)) b₀
              ∀ (e : ↥(univ \ S) ≃ Fin n'),
                n₀ ≤ n' →
                b₀ + 1 ≤ Nat.clog 2 n' ^ β →
                max (k * (max D₀ P * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ β →
                ∃ D : (b : V → Bool) →
                    ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                      (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n'),
                  (φ.modelCountOn Finset.univ : ℤ) =
                    (∑ b ∈ branchAssignments S,
                      ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                        (φ.branchParityRowSystem rows S e b)
                        (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                          clearedProductDenom (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                            (branchPrecision (Fintype.card V))
                            #(univ : Finset (Fin rows.length))) %
                              ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                  ∀ b : V → Bool,
                    (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound β n') : ℤ) k
                      (branchPrecision (Fintype.card V))
                      (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                    (k * (rowBound β n' - 1)) * (8 * Fintype.card V) := by
  obtain ⟨n₀, hn₀20, hgreedy_sched⟩ := CNF.exists_greedy_parityRowSystem_branch_schedule hβ
  refine ⟨n₀, hn₀20, fun {V _ _} φ {k B} hk hn hB hm => ?_⟩
  intro D₀ P
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := hgreedy_sched φ hk hn hB hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, hstage, fun {n' b₀} => ?_⟩
  intro rows S e hn' hb₀ hw
  obtain ⟨hlen_final, h_all⟩ := hstage (3 * Fintype.card V) le_rfl
  let D : (b : V → Bool) →
      ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
        (numNodes n') (numGroups n') (intervalStart β n') (rowBound β n') (tauRat n') :=
    fun b => Classical.choice (h_all e hn' hb₀ hw b).2
  refine ⟨D, ?_, fun b => ?_⟩
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ => CNF.parityRowAugmentedInl)
  · have hdeg :=
      CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
        (D b) CNF.parityRowAugmentedInl (branchPrecision (Fintype.card V))
    have hrows : rows.length ≤ 6 * Fintype.card V := hlen_final
    refine hdeg.trans (Nat.mul_le_mul_left _ ?_)
    unfold branchPrecision
    omega

/-- **Unconditional Section 6.3 greedy parity-test schedule-design recovery of
`φ.modelCountOn Finset.univ` for `B ≤ C_B * (Nat.clog 2 n) ^ β_B`**: combines
`CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow` with exact branch-summed
constant-term recovery and univariate numerator degree bounds. -/
theorem CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow
    (k C_B β_B : ℕ) :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (φ : CNF V) {B : ℕ},
        (∀ c ∈ φ, c.length ≤ k) →
        N₀ ≤ Fintype.card V →
        1 ≤ B →
        B ≤ C_B * Nat.clog 2 (Fintype.card V) ^ β_B →
        φ.length ≤ B * Fintype.card V →
        let D₀ := CNF.initialRowWeightBound B φ.length
        let P := CNF.greedyRowListLength B φ.length
        let b₀ := CNF.parityBranchThreshold k D₀ (Fintype.card V)
        ∃ A₀ : List (Fin φ.length → Bool), A₀.length ≤ 3 * Fintype.card V ∧
          (∀ r_row ∈ A₀, weight r_row ≤ D₀) ∧
          ∀ (A : ℕ → List (Fin φ.length → Bool))
            (γ : ℕ → Fin P → Fin φ.length × Bool),
            A 0 = A₀ → (∀ i, A (i + 1) = A i ++ [testRow (γ i)]) →
            (∀ i (γ' : Fin P → Fin φ.length × Bool),
              commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow (γ i)])) ≤
                commonZeroCount univ (φ.parityRowSystem (A i ++ [testRow γ']))) →
            commonZeroCount univ (φ.parityRowSystem (A (3 * Fintype.card V))) =
              φ.modelCountOn Finset.univ ∧
            (∀ i ≤ 3 * Fintype.card V,
              (A i).length ≤ 6 * Fintype.card V ∧
              ∀ ⦃n' : ℕ⦄
                (e : ↥(univ \ heavyVars univ (univ : Finset (Fin (A i).length))
                  (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀) ≃ Fin n'),
                (Fintype.card V ≤ 2 * n' ∧ Fintype.card V / 2 ≤ n') ∧
                #(branchAssignments
                    (heavyVars univ (univ : Finset (Fin (A i).length))
                      (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)) ≤
                  2 ^ (Fintype.card V / (Nat.clog 2 (Fintype.card V)).sqrt) ∧
                ∀ b : V → Bool,
                  Feasible (2 * β_B + 5) n' (b₀ + 1) (max (k * (D₀ * 2 ^ k)) 1)
                    (∑ f : {j : Fin (A i).length //
                        j ∈ (univ : Finset (Fin (A i).length))} ⊕ Fin n',
                      #(branchAugmentedScope
                        (heavyVars univ (univ : Finset (Fin (A i).length))
                          (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                        e univ (φ.parityRowSystem (A i)) b f)) ∧
                    Nonempty
                      (ReplacementDesign
                        (branchAugmentedScope
                          (heavyVars univ (univ : Finset (Fin (A i).length))
                            (fun j => equationScope (φ.parityRowSystem (A i) j)) b₀)
                          e univ (φ.parityRowSystem (A i)) b)
                        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                        (rowBound (2 * β_B + 5) n') (tauRat n'))) ∧
            ∀ ⦃n' : ℕ⦄,
              let rows := A (3 * Fintype.card V)
              let S := heavyVars univ (univ : Finset (Fin rows.length))
                (fun j => equationScope (φ.parityRowSystem rows j)) b₀
              ∀ (e : ↥(univ \ S) ≃ Fin n'),
                ∃ D : (b : V → Bool) →
                    ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                      (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
                      (rowBound (2 * β_B + 5) n') (tauRat n'),
                  (φ.modelCountOn Finset.univ : ℤ) =
                    (∑ b ∈ branchAssignments S,
                      ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                        (φ.branchParityRowSystem rows S e b)
                        (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                          clearedProductDenom
                            (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                            (branchPrecision (Fintype.card V))
                            #(univ : Finset (Fin rows.length))) %
                              ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
                  ∀ b : V → Bool,
                    (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                      (φ.branchParityRowSystem rows S e b)
                      (commonDenom (numNodes n') (rowBound (2 * β_B + 5) n') : ℤ) k
                      (branchPrecision (Fintype.card V))
                      (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                    (k * (rowBound (2 * β_B + 5) n' - 1)) * (8 * Fintype.card V) := by
  obtain ⟨N₀, hN₀20, hgreedy_sched⟩ :=
    CNF.exists_greedy_parityRowSystem_branch_schedule_of_le_clog_pow k C_B β_B
  refine ⟨N₀, hN₀20, fun {V _ _} φ {B} hk hN₀ hB1 hB_le hm => ?_⟩
  intro D₀ P b₀
  obtain ⟨A₀, hlen0, hw0, hgreedy⟩ := hgreedy_sched φ hk hN₀ hB1 hB_le hm
  refine ⟨A₀, hlen0, hw0, fun A γ h0 hA hγ => ?_⟩
  obtain ⟨hcount, hstage⟩ := hgreedy A γ h0 hA hγ
  refine ⟨hcount, hstage, fun {n'} => ?_⟩
  intro rows S e
  obtain ⟨hlen_final, h_all⟩ := hstage (3 * Fintype.card V) le_rfl
  let D : (b : V → Bool) →
      ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
        (numNodes n') (numGroups n') (intervalStart (2 * β_B + 5) n')
        (rowBound (2 * β_B + 5) n') (tauRat n') :=
    fun b => Classical.choice ((h_all e).2.2 b).2
  refine ⟨D, ?_, fun b => ?_⟩
  · rw [← hcount]
    exact CNF.commonZeroCount_parityRowSystem_eq_sum_branch_emod_ediv_design hk rows S e
      (fun b => branchAugmentedScope S e univ (φ.parityRowSystem rows) b) D
      (fun _ => CNF.parityRowAugmentedInl)
  · have hdeg :=
      CNF.natDegree_univariateClearedParityTruncatedSum_branchParityRowSystem_le hk rows S e b
        (D b) CNF.parityRowAugmentedInl (branchPrecision (Fintype.card V))
    have hrows : rows.length ≤ 6 * Fintype.card V := hlen_final
    refine hdeg.trans (Nat.mul_le_mul_left _ ?_)
    unfold branchPrecision
    omega

end Cslib.Logic.PL
