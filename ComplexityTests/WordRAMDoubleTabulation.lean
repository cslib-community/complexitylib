/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.HashFamily.WordRAM.DoubleTabulation

/-!
# Tests for Word-RAM Double Tabulation (`DoubleTabulation.lean`)

Verifies:
* concrete symbolic execution (`Code.eval`) of `DoubleTabulation.evalCode` matching
  `Probability.doubleTabHash`;
* non-vacuity of `impl`, `obliviousSequenceImpl`, `provableImpl`,
  and `provableObliviousSequenceImpl` over `Basis.exact` and `Basis.standard`;
* uniform `O_{c_exp, k}(1)` evaluation time (`provableImpl_evalSteps_le`) and
  `O_{c_exp, k}(n_max + 1)` space (`provableSpace_le`).
-/

@[expose] public section

namespace ComplexityTests.WordRAMDoubleTabulation

open Cslib Cslib.DataStructure Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation
open Cslib.Probability Cslib.WordRAM Cslib.WordRAM.Randomized
open Cslib.Algorithms.WordRAM.ExactLog
open Cslib.Algorithms.WordRAM.Hashing
open scoped ENNReal

/-- Concrete top-level table `T₁ : DoubleTabTopSeed 2 2 2` for symbolic execution test. -/
def testTopSeed : DoubleTabTopSeed 2 2 2 :=
  fun i j ch => ⟨(i.val + 2 * j.val + ch.val) % 4, Nat.mod_lt _ (by decide)⟩

/-- Concrete bottom-level table `T₂ : DoubleTabBotSeed 2 2 3` for symbolic execution test. -/
def testBotSeed : DoubleTabBotSeed 2 2 3 :=
  fun j y => ⟨(3 * j.val + y.val + 1) % 8, Nat.mod_lt _ (by decide)⟩

/-- Initial machine state on `Data 12` storing `testTopSeed` at `[0, 16)` and `testBotSeed` at
`[16, 24)`, with `reg 0 = 0` (`base`) and `reg 1 = 9` (`u : Fin 16`). -/
def testEvalInitData : Data 12 where
  regs
    | 0 => 0
    | 1 => 9
    | _ => 0
  mem a :=
    if h1 : a < 16 then
      let ch : Fin 4 := ⟨a % 4, Nat.mod_lt _ (by decide)⟩
      let ij := a / 4
      let i : Fin 2 := ⟨ij % 2, Nat.mod_lt _ (by decide)⟩
      let j : Fin 2 := ⟨ij / 2, by omega⟩
      (testTopSeed i j ch).val
    else if h2 : a < 24 then
      let off := a - 16
      let y : Fin 4 := ⟨off % 4, Nat.mod_lt _ (by decide)⟩
      let j : Fin 2 := ⟨off / 4, by omega⟩
      (testBotSeed j y).val
    else 0

/-- Symbolic execution of `evalCode 2 2 2` on `testEvalInitData` produces the exact output of
`doubleTabHash 2 2 2 16 3 testTopSeed testBotSeed ⟨9, _⟩`. -/
theorem evalCode_concrete_matches_doubleTabHash :
    ((evalCode 2 2 2).eval 64 100 testEvalInitData).map (fun y => y.1.regs 2) =
      some (doubleTabHash 2 2 2 16 3 testTopSeed testBotSeed ⟨9, by decide⟩).val := by
  decide

/-- Concrete non-vacuity check for `obliviousSequenceImpl` at `w = 64`, `base = 0`,
`c = 2`, `d = 2`, `b = 2`, `U = 16`, `M = 3`, `k = 2`. -/
theorem obliviousSequenceImpl_nonvacuous :
    let ops : List (HashFamily.Op 16) := [.eval 1, .eval 2, .resample, .eval 3]
    let x₀ : Data 17 := Data.init []
    ∃ (hU : 16 ≤ 2 ^ (2 * 2))
      (hfit_space : Fits 64 (0 + space 2 2 2))
      (hfit_pow_b : Fits 64 (2 ^ 2))
      (hfit_pow_M : Fits 64 (2 ^ 3))
      (hfit_keys : ∀ u : Fin 16, Fits 64 u.val),
      let H := impl (M := 3) hfit_space hfit_pow_b hfit_pow_M hfit_keys
      let O := obliviousSequenceImpl (k := 2) hU hfit_space hfit_pow_b hfit_pow_M hfit_keys
      ∃ (ν₀ : PMF (LatentState O.Latent 17))
        (ν_final : PMF (SeqOutcome O.Latent (@HashFamily.Result 16 (2 ^ 3)) 17)) (T_ops : ℝ≥0∞),
        ExecCodeDist 64 H.subroutineCode.initFresh x₀ (ν₀.map LatentState.data) O.initTime ∧
        O.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
        (∀ t ∈ ν_final.support, t.data.Bounded 64) ∧
        (HashFamily.whpKWiseSpec 2 16 (2 ^ 3) (doubleTabFailureProb 2 2 2 2)).Contract ops
          (ν_final.map SeqOutcome.transcript) ∧
        O.initTime + T_ops ≤ O.initTime + (O.totalCharge ops : ℝ≥0∞) := by
  intro ops x₀
  have hU : 16 ≤ 2 ^ (2 * 2) := by decide
  have hfit_space : Fits 64 (0 + space 2 2 2) := by decide
  have hfit_pow_b : Fits 64 (2 ^ 2) := by decide
  have hfit_pow_M : Fits 64 (2 ^ 3) := by decide
  have hfit_keys : ∀ u : Fin 16, Fits 64 u.val := fun u =>
    (by decide : Fits 64 16).of_le (le_of_lt u.isLt)
  refine ⟨hU, hfit_space, hfit_pow_b, hfit_pow_M, hfit_keys, ?_⟩
  let O := obliviousSequenceImpl (M := 3) (k := 2) hU hfit_space hfit_pow_b hfit_pow_M
    hfit_keys
  have hx₀ : x₀.Bounded 64 := Data.Bounded.init (by simp [InputFits])
  have hfr : x₀.regs (frontierReg 12) = 0 := by decide
  have hz : ∀ a ∈ (Block.mk 0 (space 2 2 2)).footprint, x₀.mem a = 0 := by
    intro a _
    simp [x₀, Data.init]
  have hv : HashFamily.BoundedEpochKeys 2 ops := by
    dsimp only [ops]
    rw [HashFamily.BoundedEpochKeys]
    refine ⟨by decide, ?_⟩
    change HashFamily.BoundedEpochKeys 2 [HashFamily.Op.eval 3]
    rw [HashFamily.BoundedEpochKeys]
    exact ⟨by decide, trivial⟩
  obtain ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbdd, hcontract, hcost⟩ :=
    O.seq_expected ops hx₀ hfr (fun j => Fin.elim0 j) hz hv
  have hpot : O.initPotential = 0 := rfl
  rw [hpot] at hcost
  exact ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbdd, hcontract, by simpa using hcost⟩

/-- Concrete non-vacuity check for `provableObliviousSequenceImpl` at `c_exp = 2`, `k = 3`,
`n_max = 8`, `U = 16`, `M = 4`, `w = 64`, `base = 0`. -/
theorem provableObliviousSequenceImpl_nonvacuous :
    let ops : List (HashFamily.Op 16) := [.eval 1, .eval 2, .resample, .eval 3]
    let x₀ : Data 23 :=
      (((Data.init [] : Data 23).set (coreReg 1) 8).set (coreReg 2) 16).set
        (coreReg 3) 4
    ∃ (hU : 16 ≤ max 8 4 ^ 2)
      (hw : 2 * trinomialDeg 16 4 ≤ 64)
      (hfit_space : Fits 64 (0 + provableSpace 2 3 8))
      (hfit_n : Fits 64 (max 8 2))
      (hfit_U : Fits 64 (max 16 2 + 1)),
      let H := provableImpl 2 3 8 16 4 hw hfit_space hfit_n hfit_U
      let O := provableObliviousSequenceImpl 2 3 8 16 4 hU hw hfit_space hfit_n hfit_U
      H.evalSteps ≤ provableEvalBound 2 3 ∧
      H.space ≤ provableSpaceFactor 2 3 * (8 + 1) ∧
      ∃ (ν₀ : PMF (LatentState O.Latent 23))
        (ν_final : PMF (SeqOutcome O.Latent (@HashFamily.Result 16 (2 ^ 4)) 23)) (T_ops : ℝ≥0∞),
        ExecCodeDist 64 H.subroutineCode.initFresh x₀ (ν₀.map LatentState.data) O.initTime ∧
        O.Steps ops (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
        (∀ t ∈ ν_final.support, t.data.Bounded 64) ∧
        (HashFamily.whpKWiseSpec 3 16 (2 ^ 4) (provableFailureProb 2 3 8)).Contract ops
          (ν_final.map SeqOutcome.transcript) ∧
        O.initTime + T_ops ≤
          O.initTime + (O.initPotential : ℝ≥0∞) + (O.totalCharge ops : ℝ≥0∞) := by
  intro ops x₀
  have hU : 16 ≤ max 8 4 ^ 2 := by decide
  have hdeg := trinomialDeg_le_three_mul 16 4
  have htb : 3 * max (Nat.clog 2 (max 16 2)) (max 4 1) = 12 := by decide
  rw [htb] at hdeg
  have hw : 2 * trinomialDeg 16 4 ≤ 64 := by omega
  have hfit_space : Fits 64 (0 + provableSpace 2 3 8) :=
    (by decide : Fits 64 (0 + provableSpaceFactor 2 3 * (8 + 1))).of_le
      (Nat.add_le_add_left (provableSpace_le 2 3 8) 0)
  have hfit_n : Fits 64 (max 8 2) := by decide
  have hfit_U : Fits 64 (max 16 2 + 1) := by decide
  refine ⟨hU, hw, hfit_space, hfit_n, hfit_U, ?_, ?_, ?_⟩
  · exact provableImpl_evalSteps_le hU (by decide) hw hfit_space hfit_n hfit_U
  · rw [provableImpl_space]
    exact provableSpace_le 2 3 8
  · let O := provableObliviousSequenceImpl 2 3 8 16 4 hU hw hfit_space hfit_n hfit_U
    have hx₀ : x₀.Bounded 64 :=
      (((Data.Bounded.init (by simp [InputFits])).set (by decide)).set (by decide)).set (by decide)
    have hfr : x₀.regs (provableImpl 2 3 8 16 4 hw hfit_space hfit_n
        hfit_U).subroutineCode.frontierReg = 0 := by
      rw [provableImpl_subroutineCode_frontierReg]
      decide
    have hpar : ∀ j : Fin 3, x₀.regs ((provableImpl 2 3 8 16 4 hw hfit_space hfit_n
        hfit_U).subroutineCode.initParams j) = (![8, 16, 4] : Fin 3 → ℕ) j := by
      rw [provableImpl_subroutineCode_initParams]
      intro j; fin_cases j <;> decide
    have hz : ∀ a ∈ (Block.mk 0 O.space).footprint, x₀.mem a = 0 := by
      intro a _
      simp [x₀, Data.init, Data.set]
    have hv : HashFamily.BoundedEpochKeys 3 ops := by
      dsimp only [ops]
      rw [HashFamily.BoundedEpochKeys]
      refine ⟨by decide, ?_⟩
      change HashFamily.BoundedEpochKeys 3 [HashFamily.Op.eval 3]
      rw [HashFamily.BoundedEpochKeys]
      exact ⟨by decide, trivial⟩
    obtain ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbdd, hcontract, hcost⟩ :=
      O.seq_expected ops hx₀ hfr hpar hz hv
    exact ⟨ν₀, ν_final, T_ops, hinit, hsteps, hbdd, hcontract, hcost⟩

end ComplexityTests.WordRAMDoubleTabulation
