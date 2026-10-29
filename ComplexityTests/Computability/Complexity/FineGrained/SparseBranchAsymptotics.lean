/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics

/-!
# Tests for `Complexity.Computability.Complexity.FineGrained.SparseBranchAsymptotics`

Nonvacuous checks for the Section 5.5 and Section 6.3 post-branching `interpolationScale`
domain-examination bounds.
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.SparseBranchAsymptoticsTests

open Finset
open Cslib.BitString
open Cslib.LinearAlgebra
open Cslib.Logic.PL
open Cslib.Complexity.SubexponentialSAT
open Cslib.Complexity.SubexponentialSAT.ReplacementParams

-- 1. Concrete check of `mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale`,
--    `div_sqrt_clog_le_interpolationScale`, and
--    `two_mul_numNodes_mul_numGroups_le_interpolationScale` at `n = 16384`.
example :
    (16384 : ℝ) * (Nat.clog 2 (Nat.clog 2 16384) : ℝ) ^ 2 / Real.sqrt (Nat.clog 2 16384) ≤
      16 * interpolationScale 16384 ∧
    ((16384 / (Nat.clog 2 16384).sqrt : ℕ) : ℝ) ≤ 32 * interpolationScale 16384 ∧
    2 * (numNodes 16384 : ℝ) * (numGroups 16384 : ℝ) ≤ interpolationScale 16384 :=
  ⟨mul_iter_clog_sq_div_sqrt_clog_le_interpolationScale le_rfl,
    div_sqrt_clog_le_interpolationScale le_rfl,
    two_mul_numNodes_mul_numGroups_le_interpolationScale le_rfl le_rfl⟩

-- 2. Nonvacuous end-to-end check of
--    `CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow` at `k = 3`,
--    `C_B = 1`, `β_B = 1` on `emptyCNF n` (`n ≥ N₁`).
/-- Empty CNF on `n` variables for nonvacuous test instantiation. -/
def emptyCNF (n : ℕ) : CNF (Fin n) := []

/-- Canonical free-variable equivalence on `emptyCNF n` (`heavyVars = ∅`). -/
def emptyCNFEquiv (n b₀ : ℕ) :
    ↥(univ \ heavyVars univ
      (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))
      (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) b₀) ≃ Fin n where
  toFun v := v.1
  invFun v := ⟨v, by
    have h0 :
        heavyVars (univ : Finset (Fin n))
          (univ : Finset (Fin ([] : List (Fin (emptyCNF n).length → Bool)).length))
          (fun j => equationScope ((emptyCNF n).parityRowSystem [] j)) b₀ = ∅ := by
      ext u
      simp [heavyVars, varIncidence, emptyCNF]
    rw [h0]
    exact mem_sdiff.mpr ⟨mem_univ v, notMem_empty v⟩⟩
  left_inv v := by ext; rfl
  right_inv v := rfl

example :
    ∃ N₁ : ℕ, 16384 ≤ N₁ ∧
      ∀ n ≥ N₁,
        let φ := emptyCNF n
        let W := initialRowWeightBound 1 φ.length
        let b₀ := CNF.parityBranchThreshold 3 W (Fintype.card (Fin n))
        let S := heavyVars univ
          (univ : Finset (Fin ([] : List (Fin φ.length → Bool)).length))
          (fun j => equationScope (φ.parityRowSystem [] j)) b₀
        ∀ b : Fin n → Bool,
          ∃ (hF : Feasible (2 * 1 + 5) n (b₀ + 1) (max (3 * (W * 2 ^ 3)) 1)
              (∑ f : {j : Fin ([] : List (Fin φ.length → Bool)).length //
                  j ∈ (univ : Finset (Fin ([] : List (Fin φ.length → Bool)).length))} ⊕ Fin n,
                #(branchAugmentedScope S (emptyCNFEquiv n b₀) univ (φ.parityRowSystem []) b f)))
            (D : ReplacementDesign
              (branchAugmentedScope S (emptyCNFEquiv n b₀) univ (φ.parityRowSystem []) b)
              (numNodes n) (numGroups n) (intervalStart (2 * 1 + 5) n)
              (rowBound (2 * 1 + 5) n) (tauRat n)),
            let d := 3 * (([] : List (Fin φ.length → Bool)).length +
              2 * (branchPrecision (Fintype.card (Fin n)) - 1))
            let q := (d * rowBound (2 * 1 + 5) n) / numNodes n
            let C := hF.toCountingDesign D univ
            (∑ t : Fin (numNodes n),
                (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
                  (2 * (#(C.measurementBox t) : ℝ) *
                    ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
              (2 : ℝ) ^ ((CNF.parityBranchExamScaleCoeff 3 1 : ℝ) *
                interpolationScale (Fintype.card (Fin n))) := by
  obtain ⟨N₁, hN₁, hsched⟩ :=
    CNF.exists_branch_schedule_and_examBound_parityRowSystem_of_le_clog_pow 3 1 1
  refine ⟨N₁, hN₁, fun n hn => ?_⟩
  intro φ W b₀ S b
  have hk : ∀ c ∈ φ, c.length ≤ 3 := by simp [φ, emptyCNF]
  have hcard : N₁ ≤ Fintype.card (Fin n) := by simpa only [Fintype.card_fin] using hn
  have hm : φ.length ≤ 1 * Fintype.card (Fin n) := by simp [φ, emptyCNF]
  have hB : 1 ≤ 1 * Nat.clog 2 (Fintype.card (Fin n)) ^ 1 := by
    rw [Fintype.card_fin, one_mul, pow_one]
    have : 2 ^ 0 < n := by omega
    exact (Nat.lt_clog_iff_pow_lt one_lt_two).mpr this
  have hW : ∀ r ∈ ([] : List (Fin φ.length → Bool)), weight r ≤ W := by simp
  have hlen : ([] : List (Fin φ.length → Bool)).length ≤ 6 * Fintype.card (Fin n) := by simp
  obtain ⟨hF, D, hexam⟩ :=
    (hsched hk hcard hm hB le_rfl hW hlen (emptyCNFEquiv n b₀)).2.1 b
  exact ⟨hF, D, hexam univ⟩

end Cslib.Complexity.SubexponentialSAT.SparseBranchAsymptoticsTests
