/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseCNFDesignSchedule

/-!
# Tests for `SparseCNFDesignSchedule`

Concrete tests and nonvacuity witnesses for the index-equivalence bridge and schedule-instantiated
exact recovery theorems in
`Complexity.Computability.Complexity.FineGrained.SparseCNFDesignSchedule`.
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementParams.SparseCNFDesignScheduleTests

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

/-! ### 1. Index-equivalence bridge between `Fin m ⊕ Fin n'` and `{j // j ∈ univ} ⊕ Fin n'` -/

/-- A 2-CNF over `Fin 3` with two clauses `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ x₂)` and one single-clause row. -/
def sampleCNF3 : CNF (Fin 3) :=
  [[⟨0, true⟩, ⟨1, false⟩], [⟨1, true⟩, ⟨2, true⟩]]

def sampleRow3 : Fin sampleCNF3.length → Bool :=
  fun i => decide (i = ⟨0, by decide⟩)

def sampleRows3 : List (Fin sampleCNF3.length → Bool) := [sampleRow3]

example (j : Fin 1) :
    CNF.parityRowAugmentedIndexEquiv 1 3 (Sum.inl j) = CNF.parityRowAugmentedInl j := by
  simp only [CNF.parityRowAugmentedIndexEquiv_inl]

example (v : Fin 3) :
    CNF.parityRowAugmentedIndexEquiv 1 3 (Sum.inr v) = Sum.inr v := by
  simp only [CNF.parityRowAugmentedIndexEquiv_inr]

example (e : ↥(univ \ (∅ : Finset (Fin 3))) ≃ Fin 3) (b : Fin 3 → Bool)
    (j : Fin sampleRows3.length) :
    branchAugmentedScope ∅ e univ (sampleCNF3.parityRowSystem sampleRows3) b
        (CNF.parityRowAugmentedIndexEquiv sampleRows3.length 3 (Sum.inl j)) =
      branchEquationScope ∅ e (sampleCNF3.parityRowSystem sampleRows3) b j :=
  sampleCNF3.branchAugmentedScope_parityRowSystem_comp_equiv_inl sampleRows3 ∅ e b j

example (e : ↥(univ \ (∅ : Finset (Fin 3))) ≃ Fin 3) (b : Fin 3 → Bool) (v : Fin 3) :
    branchAugmentedScope ∅ e univ (sampleCNF3.parityRowSystem sampleRows3) b
        (CNF.parityRowAugmentedIndexEquiv sampleRows3.length 3 (Sum.inr v)) = {v} :=
  sampleCNF3.branchAugmentedScope_parityRowSystem_comp_equiv_inr sampleRows3 ∅ e b v

/-! ### 2. Schedule-instantiated exact recovery of `commonZeroCount`, `numPassing`, and `#F` -/

example :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V]
        {φ : CNF V} ⦃n' k W b₀ : ℕ⦄,
        (∀ c ∈ φ, c.length ≤ k) →
        ∀ {rows : List (Fin φ.length → Bool)},
          (∀ r_row ∈ rows, weight r_row ≤ W) →
          let S := heavyVars univ (univ : Finset (Fin rows.length))
            (fun j => equationScope (φ.parityRowSystem rows j)) b₀
          ∀ (e : ↥(univ \ S) ≃ Fin n'),
            n₀ ≤ n' →
            b₀ + 1 ≤ Nat.clog 2 n' ^ 1 →
            max (k * (W * 2 ^ k)) 1 ≤ Nat.clog 2 n' ^ 1 →
            (∀ b : V → Bool,
              Feasible 1 n' (b₀ + 1) (max (k * (W * 2 ^ k)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n',
                  #(branchAugmentedScope S e univ (φ.parityRowSystem rows) b f))) ∧
            ∃ D : (b : V → Bool) →
                ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
                  (numNodes n') (numGroups n') (intervalStart 1 n') (rowBound 1 n') (tauRat n'),
              (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
                (∑ b ∈ branchAssignments S,
                  ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                    (φ.branchParityRowSystem rows S e b)
                    (commonDenom (numNodes n') (rowBound 1 n') : ℤ) k
                    (branchPrecision (Fintype.card V))
                    (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                      clearedProductDenom (commonDenom (numNodes n') (rowBound 1 n') : ℤ) k
                        (branchPrecision (Fintype.card V))
                        #(univ : Finset (Fin rows.length))) %
                          ((2 : ℤ) ^ branchPrecision (Fintype.card V))) ∧
              ∀ b : V → Bool,
                (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S e b)
                  (commonDenom (numNodes n') (rowBound 1 n') : ℤ) k
                  (branchPrecision (Fintype.card V))
                  (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
                (k * (rowBound 1 n' - 1)) *
                  (rows.length + 2 * (branchPrecision (Fintype.card V) - 1)) :=
  CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq.{0} le_rfl

example : ∃ n₀ : ℕ, 20 ≤ n₀ := by
  obtain ⟨n₀, hn₀, _⟩ := CNF.exists_schedule_design_numPassing_eq.{0} (β := 1) le_rfl
  exact ⟨n₀, hn₀⟩

example : ∃ N₀ : ℕ, 20 ≤ N₀ := by
  obtain ⟨N₀, hN₀, _⟩ :=
    CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow.{0} 3 2 1
  exact ⟨N₀, hN₀⟩

example : ∃ N₀ : ℕ, 20 ≤ N₀ := by
  obtain ⟨N₀, hN₀, _⟩ :=
    CNF.exists_schedule_design_numPassing_of_le_clog_pow.{0} 3 2 1
  exact ⟨N₀, hN₀⟩

example : ∃ n₀ : ℕ, 20 ≤ n₀ := by
  obtain ⟨n₀, hn₀, _⟩ :=
    CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_eq.{0} (β := 1) le_rfl
  exact ⟨n₀, hn₀⟩

example : ∃ N₀ : ℕ, 20 ≤ N₀ := by
  obtain ⟨N₀, hN₀, _⟩ :=
    CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow.{0} 3 2 1
  exact ⟨N₀, hN₀⟩

end Cslib.Complexity.SubexponentialSAT.ReplacementParams.SparseCNFDesignScheduleTests
