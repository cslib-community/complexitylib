/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.GeneralCNFBranchSchedule`

Nonvacuous checks for Section 6.4 Proposition 6.4 disjoint sparsification leaf-to-root schedule and
`ReplacementDesign` recovery.
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.GeneralCNFBranchScheduleTests

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL
open Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

example : CNF.prop64ScheduleExponent 3 = 13 := rfl

/-- Concrete 3-CNF on `Fin 4` with `11` satisfying assignments out of `16`. -/
def sampleGen3CNF : CNF (Fin 4) :=
  [[(0, true), (1, false), (2, true)], [(1, false), (3, false)]]

-- Concrete numerical verification of `CNF.sum_modelCountOn_prop64Leaves` on `sampleGen3CNF`.
example :
    ((sampleGen3CNF.prop64Leaves 3).map fun L => L.toCNF.modelCountOn Finset.univ).sum = 11 := by
  rw [CNF.sum_modelCountOn_prop64Leaves 3 sampleGen3CNF Finset.univ]
  decide

-- Concrete verification of both branches (`1` and `0`) of `CNF.countP_eval_toCNF_prop64Leaves`.
example :
    ((sampleGen3CNF.prop64Leaves 3).map ClauseSet.toCNF).countP
        (fun F => F.eval (fun _ => false)) = 1 ∧
      ((sampleGen3CNF.prop64Leaves 3).map ClauseSet.toCNF).countP
        (fun F => F.eval (fun _ => true)) = 0 := by
  rw [CNF.countP_eval_toCNF_prop64Leaves, CNF.countP_eval_toCNF_prop64Leaves]
  decide

-- Compose `CNF.length_le_of_mem_prop64Leaves`, `CNF.exists_prop64ThresholdBase_le_mul_clog_sq`,
-- and `CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow` on `sampleGen3CNF` at `n = 4`
-- (`Nat.clog 2 4 = 2`).
example :
    ∃ C_M C_B : ℕ, 2 ≤ C_M * 4 ∧ 1 ≤ C_B * 16 ∧
      CNF.prop64ThresholdBase 3 4 ≤ C_M * 4 ∧
      CNF.prop64LeafClauseRatio 3 4 ≤ C_B * 16 ∧
      ∀ L ∈ sampleGen3CNF.prop64Leaves 3,
        (∀ c ∈ L.toCNF, c.length ≤ 3) ∧
        L.toCNF.length ≤ (C_B * 16) * 4 := by
  obtain ⟨C_M, _, hCM⟩ := CNF.exists_prop64ThresholdBase_le_mul_clog_sq (by decide : 2 ≤ 3)
  obtain ⟨C_B, _, hCB⟩ := CNF.exists_prop64LeafClauseRatio_le_mul_clog_pow (by decide : 2 ≤ 3)
  have h4 : Nat.clog 2 4 ^ 2 = 4 := by decide
  have h16 : Nat.clog 2 4 ^ 4 = 16 := by decide
  have hM4 : CNF.prop64ThresholdBase 3 4 ≤ C_M * 4 := by
    rw [← h4]
    exact hCM 4 (by decide)
  have hB4 : CNF.prop64LeafClauseRatio 3 4 ≤ C_B * 16 := by
    rw [← h16]
    exact hCB 4 (by decide)
  refine ⟨C_M, C_B, (CNF.two_le_prop64ThresholdBase 3 4).trans hM4,
    (CNF.one_le_prop64LeafClauseRatio 3 4).trans hB4, hM4, hB4, fun L hL => ?_⟩
  have hk : ∀ c ∈ sampleGen3CNF, c.length ≤ 3 := by decide
  obtain ⟨hwidth, -, hlen⟩ := CNF.length_le_of_mem_prop64Leaves hk hL
  exact ⟨hwidth, (hlen (by decide)).trans (Nat.mul_le_mul_right 4 hB4)⟩

/-- Empty CNF on `n` variables for nonvacuous test instantiation. -/
def emptyGenCNF (n : ℕ) : CNF (Fin n) := []

/-- Canonical free-variable equivalence on `emptyGenCNF n` (`heavyVars = ∅`). -/
def emptyGenCNFEquiv (n b₀ : ℕ) :
    ↥(univ \ heavyVars univ
      (univ : Finset (Fin ([] : List (Fin (emptyGenCNF n).length → Bool)).length))
      (fun j => equationScope ((emptyGenCNF n).parityRowSystem [] j)) b₀) ≃ Fin n where
  toFun v := v.1
  invFun v := ⟨v, by
    have h0 :
        heavyVars (univ : Finset (Fin n))
          (univ : Finset (Fin ([] : List (Fin (emptyGenCNF n).length → Bool)).length))
          (fun j => equationScope ((emptyGenCNF n).parityRowSystem [] j)) b₀ = ∅ := by
      ext u
      simp [heavyVars, varIncidence, emptyGenCNF]
    rw [h0]
    exact mem_sdiff.mpr ⟨mem_univ v, notMem_empty v⟩⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

/-- Concrete witness for
`CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow` at `k = 3`,
`C_B = 1`, `β_B = 1`. -/
example :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ n ≥ N₁,
        let φ := emptyGenCNF n
        let W := initialRowWeightBound 1 φ.length
        let rows : List (Fin φ.length → Bool) := []
        let b₀ := CNF.parityBranchThreshold 3 W (Fintype.card (Fin n))
        let S := heavyVars univ (univ : Finset (Fin rows.length))
          (fun j => equationScope (φ.parityRowSystem rows j)) b₀
        (Fintype.card (Fin n) ≤ 2 * n ∧ n ≤ Fintype.card (Fin n)) ∧
        ∃ (hF : ∀ b : Fin n → Bool,
              Feasible 7 n (b₀ + 1) (max (3 * (W * 2 ^ 3)) 1)
                (∑ f : {j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n,
                  #(branchAugmentedScope S (emptyGenCNFEquiv n b₀) univ
                    (φ.parityRowSystem rows) b f)))
            (D : ∀ b : Fin n → Bool,
              ReplacementDesign
                (branchAugmentedScope S (emptyGenCNFEquiv n b₀) univ (φ.parityRowSystem rows) b)
                (numNodes n) (numGroups n) (intervalStart 7 n) (rowBound 7 n) (tauRat n)),
            (commonZeroCount (univ : Finset (Fin rows.length)) (φ.parityRowSystem rows) : ℤ) =
              (∑ b ∈ branchAssignments S,
                ((univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                  (φ.branchParityRowSystem rows S (emptyGenCNFEquiv n b₀) b)
                  (commonDenom (numNodes n) (rowBound 7 n) : ℤ) 3
                  (branchPrecision (Fintype.card (Fin n)))
                  (designReplacementScaledIntMap (D b)
                    (fun j => Sum.inl ⟨j, mem_univ j⟩))).eval 0 /
                    clearedProductDenom
                      (commonDenom (numNodes n) (rowBound 7 n) : ℤ) 3
                      (branchPrecision (Fintype.card (Fin n)))
                      #(univ : Finset (Fin rows.length))) %
                        ((2 : ℤ) ^ branchPrecision (Fintype.card (Fin n)))) ∧
            (∀ b : Fin n → Bool,
              (univariateClearedParityTruncatedSum (univ : Finset (Fin rows.length))
                (φ.branchParityRowSystem rows S (emptyGenCNFEquiv n b₀) b)
                (commonDenom (numNodes n) (rowBound 7 n) : ℤ) 3
                (branchPrecision (Fintype.card (Fin n)))
                (designReplacementScaledIntMap (D b)
                  (fun j => Sum.inl ⟨j, mem_univ j⟩))).natDegree ≤
                (3 * (rowBound 7 n - 1)) * (8 * Fintype.card (Fin n))) ∧
            ∀ (b : Fin n → Bool)
                (s_active : Finset
                  ({j : Fin rows.length // j ∈ (univ : Finset (Fin rows.length))} ⊕ Fin n)),
              let d := 3 * (rows.length + 2 * (branchPrecision (Fintype.card (Fin n)) - 1))
              let q := (d * rowBound 7 n) / numNodes n
              let C := (hF b).toCountingDesign (D b) s_active
              (∑ t : Fin (numNodes n),
                  (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                    (2 * (#(C.measurementBox t) : ℝ) *
                      ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
                (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff 3 1 : ℝ) *
                  interpolationScale (Fintype.card (Fin n))) := by
  obtain ⟨N₁, hN₁, hsched⟩ :=
    CNF.exists_branch_schedule_recovery_and_examBound_parityRowSystem_of_le_clog_pow 3 1 1
  refine ⟨N₁, hN₁, fun n hn => ?_⟩
  intro φ W rows b₀ S
  have hk : ∀ c ∈ φ, c.length ≤ 3 := by simp [φ, emptyGenCNF]
  have hcard : N₁ ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  have hm : φ.length ≤ 1 * Fintype.card (Fin n) := by simp [φ, emptyGenCNF]
  have hB : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin n)) ^ 1 := by
    rw [Fintype.card_fin, one_mul, pow_one]
    have : 2 ^ 0 < n := by omega
    exact (Nat.lt_clog_iff_pow_lt one_lt_two).mpr this
  have hW : ∀ r ∈ rows, weight r ≤ W := by simp [rows]
  have hlen : rows.length ≤ 6 * Fintype.card (Fin n) := by simp [rows]
  have h := hsched hk hcard hm hB le_rfl hW hlen (emptyGenCNFEquiv n b₀)
  exact ⟨h.1, h.2.1⟩

/-- Concrete witness for `CNF.exists_prop64Leaves_modelCountOn_recovery_and_examBound` at `k = 3`.
-/
example :
    ∃ N₂ : ℕ, 16384 ≤ N₂ ∧
      let φ := emptyGenCNF N₂
      ((φ.prop64Leaves 3).map fun L => L.toCNF.modelCountOn Finset.univ).sum =
        φ.modelCountOn Finset.univ ∧
      ∀ L ∈ φ.prop64Leaves 3,
        let ψ := L.toCNF
        let B := CNF.prop64LeafClauseRatio 3 (Fintype.card (Fin N₂))
        (∀ c ∈ ψ, c.length ≤ 3) ∧
        ψ.length ≤ B * Fintype.card (Fin N₂) ∧
        ∃ rows : List (Fin ψ.length → Bool),
          rows.length ≤ 6 * Fintype.card (Fin N₂) ∧
          commonZeroCount univ (ψ.parityRowSystem rows) = ψ.modelCountOn Finset.univ := by
  obtain ⟨N₂, hN₂, hprop64⟩ :=
    CNF.exists_prop64Leaves_modelCountOn_recovery_and_examBound (by decide : 2 ≤ 3)
  refine ⟨N₂, hN₂, ?_⟩
  have hcard : N₂ ≤ Fintype.card (Fin N₂) := by simp
  have hk : ∀ c ∈ emptyGenCNF N₂, c.length ≤ 3 := by simp [emptyGenCNF]
  obtain ⟨hsum, hleaves⟩ := hprop64 (emptyGenCNF N₂) hk hcard
  refine ⟨hsum, fun L hL => ?_⟩
  obtain ⟨hk_L, hm_L, rows, hlen_r, hcount_r, _⟩ := hleaves L hL
  exact ⟨hk_L, hm_L, rows, hlen_r, hcount_r⟩

end Cslib.Complexity.SubexponentialSAT.GeneralCNFBranchScheduleTests
