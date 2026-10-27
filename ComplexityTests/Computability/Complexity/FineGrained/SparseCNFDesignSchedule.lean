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

Concrete tests and nonvacuous recovery witnesses on a formula with a nonzero parity row for the
index-equivalence bridge and schedule-instantiated exact recovery theorems in
`Complexity.Computability.Complexity.FineGrained.SparseCNFDesignSchedule`.
-/

@[expose] public noncomputable section

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
        (CNF.parityRowAugmentedInl j) =
      branchEquationScope ∅ e (sampleCNF3.parityRowSystem sampleRows3) b j :=
  sampleCNF3.branchAugmentedScope_parityRowAugmentedInl sampleRows3 ∅ e b j

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

/-! ### 2. Nonzero-row CNF fixture and schedule-instantiated exact recovery witnesses -/

/-- A 1-clause CNF `(x₀)` over `Fin (n + 1)` of width `1 ≤ 3`. -/
def unitClauseCNF (n : ℕ) : CNF (Fin (n + 1)) :=
  [[⟨0, true⟩]]

/-- Nonzero parity-row list selecting the unique clause of `unitClauseCNF n`. -/
def unitClauseRows (n : ℕ) : List (Fin (unitClauseCNF n).length → Bool) :=
  [fun _ => true]

theorem width_unitClauseCNF_le_three (n : ℕ) :
    ∀ c ∈ unitClauseCNF n, c.length ≤ 3 := by
  intro c hc
  rcases List.mem_singleton.mp hc with rfl
  simp

theorem weight_unitClauseRows_le_one (n : ℕ) :
    ∀ r_row ∈ unitClauseRows n, weight r_row ≤ 1 := by
  intro r_row hr
  rcases List.mem_singleton.mp hr with rfl
  refine (card_filter_le _ _).trans ?_
  rw [card_univ, Fintype.card_fin]
  simp [unitClauseCNF]

theorem heavyVars_unitClauseCNF_eq_empty (n : ℕ) {b₀ : ℕ} (hb₀ : 1 ≤ b₀) :
    heavyVars (univ : Finset (Fin (n + 1)))
      (univ : Finset (Fin (unitClauseRows n).length))
      (fun j => equationScope ((unitClauseCNF n).parityRowSystem (unitClauseRows n) j)) b₀ =
    ∅ := by
  ext v
  simp only [heavyVars, varIncidence, mem_filter, mem_univ, true_and, notMem_empty, iff_false,
    not_lt]
  refine (card_filter_le _ _).trans ?_
  rw [card_univ, Fintype.card_fin]
  simpa [unitClauseRows] using hb₀

/-- Free-variable equivalence for `unitClauseCNF n` and `unitClauseRows n` at any threshold
`1 ≤ b₀`, since `heavyVars` is empty. -/
def unitClauseEquiv (n : ℕ) {b₀ : ℕ} (hb₀ : 1 ≤ b₀) :
    ↥((univ : Finset (Fin (n + 1))) \
      heavyVars (univ : Finset (Fin (n + 1)))
        (univ : Finset (Fin (unitClauseRows n).length))
        (fun j => equationScope ((unitClauseCNF n).parityRowSystem (unitClauseRows n) j)) b₀) ≃
      Fin (n + 1) where
  toFun v := v.1
  invFun v := ⟨v, by rw [heavyVars_unitClauseCNF_eq_empty n hb₀]; simp⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

private theorem five_le_clog_succ {n : ℕ} (hn : 20 ≤ n) : 5 ≤ Nat.clog 2 (n + 1) := by
  have h16 : 2 ^ 4 < n + 1 := by omega
  exact (Nat.lt_clog_iff_pow_lt one_lt_two).mpr h16

/-- Nonvacuous recovery check for `CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq`
and `CNF.exists_schedule_design_numPassing_eq` on `unitClauseCNF n₀` with the nonzero parity row
`unitClauseRows n₀` (`W = 1`, `b₀ = 1`, `k = 3`, `β = 5`). -/
example :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧
      let φ := unitClauseCNF n₀
      let rows := unitClauseRows n₀
      let S := heavyVars univ (univ : Finset (Fin rows.length))
        (fun j => equationScope (φ.parityRowSystem rows j)) 1
      let e := unitClauseEquiv n₀ (b₀ := 1) le_rfl
      ∃ (D₁ D₂ : (b : Fin (n₀ + 1) → Bool) →
          ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
            (numNodes (n₀ + 1)) (numGroups (n₀ + 1)) (intervalStart 5 (n₀ + 1))
            (rowBound 5 (n₀ + 1)) (tauRat (n₀ + 1))),
        (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
          (∑ b ∈ branchAssignments S,
            ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes (n₀ + 1)) (rowBound 5 (n₀ + 1)) : ℤ) 3
              (branchPrecision (Fintype.card (Fin (n₀ + 1))))
              (designReplacementScaledIntMap (D₁ b) CNF.parityRowAugmentedInl)).eval 0 /
                clearedProductDenom
                  (commonDenom (numNodes (n₀ + 1)) (rowBound 5 (n₀ + 1)) : ℤ) 3
                  (branchPrecision (Fintype.card (Fin (n₀ + 1))))
                  #(univ : Finset (Fin rows.length))) %
                    ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin (n₀ + 1))))) ∧
        (numPassing φ.violations rows : ℤ) =
          (∑ b ∈ branchAssignments S,
            ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes (n₀ + 1)) (rowBound 5 (n₀ + 1)) : ℤ) 3
              (branchPrecision (Fintype.card (Fin (n₀ + 1))))
              (designReplacementScaledIntMap (D₂ b) CNF.parityRowAugmentedInl)).eval 0 /
                clearedProductDenom
                  (commonDenom (numNodes (n₀ + 1)) (rowBound 5 (n₀ + 1)) : ℤ) 3
                  (branchPrecision (Fintype.card (Fin (n₀ + 1))))
                  #(univ : Finset (Fin rows.length))) %
                    ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin (n₀ + 1))))) := by
  obtain ⟨n₁, hn₁, hcz⟩ :=
    CNF.exists_schedule_design_commonZeroCount_parityRowSystem_eq.{0} (β := 5) (by decide)
  obtain ⟨n₂, hn₂, hnp⟩ :=
    CNF.exists_schedule_design_numPassing_eq.{0} (β := 5) (by decide)
  let n₀ := max n₁ n₂
  have hn₀ : 20 ≤ n₀ := hn₁.trans (le_max_left n₁ n₂)
  refine ⟨n₀, hn₀, ?_⟩
  intro φ rows S e
  have h5 : 5 ^ 5 ≤ Nat.clog 2 (n₀ + 1) ^ 5 :=
    Nat.pow_le_pow_left (five_le_clog_succ hn₀) 5
  have hb₀ : 1 + 1 ≤ Nat.clog 2 (n₀ + 1) ^ 5 := (by decide : 1 + 1 ≤ 5 ^ 5).trans h5
  have hw : max (3 * (1 * 2 ^ 3)) 1 ≤ Nat.clog 2 (n₀ + 1) ^ 5 :=
    (by decide : max (3 * (1 * 2 ^ 3)) 1 ≤ 5 ^ 5).trans h5
  obtain ⟨_, D₁, hD₁, _⟩ := hcz (width_unitClauseCNF_le_three n₀) (weight_unitClauseRows_le_one n₀)
    e ((le_max_left n₁ n₂).trans (Nat.le_succ n₀)) hb₀ hw
  obtain ⟨_, D₂, hD₂, _⟩ := hnp (width_unitClauseCNF_le_three n₀) (weight_unitClauseRows_le_one n₀)
    e ((le_max_right n₁ n₂).trans (Nat.le_succ n₀)) hb₀ hw
  exact ⟨D₁, D₂, hD₁, hD₂⟩

/-- Nonvacuous recovery check for
`CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow` and
`CNF.exists_schedule_design_numPassing_of_le_clog_pow` on `unitClauseCNF N₀` (`k = 3`, `C_B = 1`,
`β_B = 1`, `B = 1`). -/
example :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      let φ := unitClauseCNF N₀
      let W := CNF.initialRowWeightBound 1 φ.length
      let b₀ := CNF.parityBranchThreshold 3 W (Fintype.card (Fin (N₀ + 1)))
      ∃ rows : List (Fin φ.length → Bool),
        rows.length ≤ 6 * Fintype.card (Fin (N₀ + 1)) ∧
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        let n' := Fintype.card ↥((univ : Finset (Fin (N₀ + 1))) \ S)
        let e := Fintype.equivFin ↥((univ : Finset (Fin (N₀ + 1))) \ S)
        ∃ (D₁ D₂ : (b : Fin (N₀ + 1) → Bool) →
            ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
              (numNodes n') (numGroups n') (intervalStart 7 n')
              (rowBound 7 n') (tauRat n')),
          (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                (designReplacementScaledIntMap (D₁ b) CNF.parityRowAugmentedInl)).eval 0 /
                  clearedProductDenom
                    (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                    (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin (N₀ + 1))))) ∧
          (numPassing φ.violations rows : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                (designReplacementScaledIntMap (D₂ b) CNF.parityRowAugmentedInl)).eval 0 /
                  clearedProductDenom
                    (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                    (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin (N₀ + 1))))) := by
  obtain ⟨N₁, hN₁, hcz⟩ :=
    CNF.exists_schedule_design_commonZeroCount_parityRowSystem_of_le_clog_pow.{0} 3 1 1
  obtain ⟨N₂, hN₂, hnp⟩ :=
    CNF.exists_schedule_design_numPassing_of_le_clog_pow.{0} 3 1 1
  let N₀ := max N₁ N₂
  have hN₀ : 20 ≤ N₀ := hN₁.trans (le_max_left N₁ N₂)
  refine ⟨N₀, hN₀, ?_⟩
  intro φ W b₀
  have hcard₁ : N₁ ≤ Fintype.card (Fin (N₀ + 1)) := by
    rw [Fintype.card_fin]
    exact (le_max_left N₁ N₂).trans (Nat.le_succ N₀)
  have hcard₂ : N₂ ≤ Fintype.card (Fin (N₀ + 1)) := by
    rw [Fintype.card_fin]
    exact (le_max_right N₁ N₂).trans (Nat.le_succ N₀)
  have hm : φ.length ≤ 1 * Fintype.card (Fin (N₀ + 1)) := by simp [φ, unitClauseCNF]
  have hB : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin (N₀ + 1))) ^ 1 := by
    rw [Fintype.card_fin, one_mul, pow_one]
    exact (by decide : 1 ≤ 5).trans (five_le_clog_succ hN₀)
  have hn1 : 1 ≤ Fintype.card (Fin (N₀ + 1)) := by rw [Fintype.card_fin]; omega
  obtain ⟨A₀, hlen0, hw0, _⟩ :=
    φ.exists_initialTests_commonZeroCount_greedy (width_unitClauseCNF_le_three N₀) hn1 le_rfl hm
  have hlen : A₀.length ≤ 6 * Fintype.card (Fin (N₀ + 1)) :=
    hlen0.trans (Nat.mul_le_mul_right _ (by decide))
  refine ⟨A₀, hlen, ?_⟩
  intro S n' e
  obtain ⟨_, _, _, _, D₁, hD₁, _⟩ := hcz (width_unitClauseCNF_le_three N₀) hcard₁ hm hB le_rfl
    hw0 hlen e
  obtain ⟨_, _, _, _, D₂, hD₂, _⟩ := hnp (width_unitClauseCNF_le_three N₀) hcard₂ hm hB le_rfl
    hw0 hlen e
  exact ⟨D₁, D₂, hD₁, hD₂⟩

/-- Nonvacuous end-to-end greedy model-count recovery check for
`CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow` and
`CNF.exists_greedy_testRow_trajectory` on `unitClauseCNF N₀` (`k = 3`, `C_B = 1`, `β_B = 1`,
`B = 1`). -/
example :
    ∃ N₀ : ℕ, 20 ≤ N₀ ∧
      let φ := unitClauseCNF N₀
      let D₀ := CNF.initialRowWeightBound 1 φ.length
      let b₀ := CNF.parityBranchThreshold 3 D₀ (Fintype.card (Fin (N₀ + 1)))
      ∃ (rows : List (Fin φ.length → Bool)),
        rows.length ≤ 6 * Fintype.card (Fin (N₀ + 1)) ∧
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        let n' := Fintype.card ↥((univ : Finset (Fin (N₀ + 1))) \ S)
        let e := Fintype.equivFin ↥((univ : Finset (Fin (N₀ + 1))) \ S)
        ∃ D : (b : Fin (N₀ + 1) → Bool) →
            ReplacementDesign (branchAugmentedScope S e univ (φ.parityRowSystem rows) b)
              (numNodes n') (numGroups n') (intervalStart 7 n') (rowBound 7 n') (tauRat n'),
          (φ.modelCountOn Finset.univ : ℤ) =
            (∑ b ∈ branchAssignments S,
              ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S e b)
                (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).eval 0 /
                  clearedProductDenom
                    (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
                    (branchPrecision (Fintype.card (Fin (N₀ + 1))))
                    #(univ : Finset (Fin rows.length))) %
                      ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin (N₀ + 1))))) ∧
          ∀ b : Fin (N₀ + 1) → Bool,
            (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
              (φ.branchParityRowSystem rows S e b)
              (commonDenom (numNodes n') (rowBound 7 n') : ℤ) 3
              (branchPrecision (Fintype.card (Fin (N₀ + 1))))
              (designReplacementScaledIntMap (D b) CNF.parityRowAugmentedInl)).natDegree ≤
            (3 * (rowBound 7 n' - 1)) * (8 * Fintype.card (Fin (N₀ + 1))) := by
  obtain ⟨N₀, hN₀, hgreedy_sched⟩ :=
    CNF.exists_greedy_parityRowSystem_schedule_design_modelCountOn_of_le_clog_pow.{0} 3 1 1
  refine ⟨N₀, hN₀, ?_⟩
  intro φ D₀ b₀
  have hcard : N₀ ≤ Fintype.card (Fin (N₀ + 1)) := by
    rw [Fintype.card_fin]
    exact Nat.le_succ N₀
  have hB : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin (N₀ + 1))) ^ 1 := by
    rw [Fintype.card_fin, one_mul, pow_one]
    exact (by decide : 1 ≤ 5).trans (five_le_clog_succ hN₀)
  have hm : φ.length ≤ 1 * Fintype.card (Fin (N₀ + 1)) := by simp [φ, unitClauseCNF]
  obtain ⟨A₀, _, _, hgreedy⟩ :=
    hgreedy_sched φ (width_unitClauseCNF_le_three N₀) hcard le_rfl hB hm
  let P := CNF.greedyRowListLength 1 φ.length
  have : Nonempty (Fin P → Fin φ.length × Bool) :=
    ⟨fun _ => (⟨0, by simp [φ, unitClauseCNF]⟩, false)⟩
  obtain ⟨A, γ, h0, hA, hγ⟩ := φ.exists_greedy_testRow_trajectory P A₀
  obtain ⟨_, hstage, hrec⟩ := hgreedy A γ h0 hA hγ
  have hlen : (A (3 * Fintype.card (Fin (N₀ + 1)))).length ≤
      6 * Fintype.card (Fin (N₀ + 1)) :=
    (hstage (3 * Fintype.card (Fin (N₀ + 1))) le_rfl).1
  refine ⟨A (3 * Fintype.card (Fin (N₀ + 1))), hlen, ?_⟩
  intro S n' e
  exact hrec e

end Cslib.Complexity.SubexponentialSAT.ReplacementParams.SparseCNFDesignScheduleTests
