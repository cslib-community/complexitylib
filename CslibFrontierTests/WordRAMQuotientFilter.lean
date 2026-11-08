/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.WordRAM.QuotientFilter

/-!
# Two-Stage Reduced `k`-Wise Hashing and Quotient Filter Tests

Exercises:
1. `Cslib.DataStructure.HashFamily.WordRAM.ReducedKWise` (shared two-stage hash):
   - concrete parameter, space, and instruction-budget evaluations;
   - `ReducedKWise.space_le` asymptotic sublinear table + `O(k)` seed bound;
   - non-vacuous instantiation of `ReducedKWise.impl` and `ReducedKWise.implStandard` for full
     32-bit keys (`U = 2 ^ 32`, `w₀ = 32`, `w = 64`, `b = 7`, `b' = 7`, `k = 5`).
2. `Cslib.DataStructure.ApproximateMembership` and `QuotientFilter`:
   - concrete evaluations of `effCap`, `quotBits`, `remBits`, `slotPackShift`, `packedWords`,
     `space`, `epsLog`, `setupSteps`, and `charge`;
   - valid operation sequences with insertions, queries, and deletions (`ValidOpSeq`, `activeSet`,
     `stepSet`), canonical run invariant preservation (`FilterInv.insertState_filterInv`,
     `FilterInv.deleteState_filterInv`), and zero false negatives (`FilterInv.querySlot_of_mem`);
   - non-vacuous instantiation of `QuotientFilter.impl`, `QuotientFilter.implStandard`,
     `QuotientFilter.implOfEps`, `QuotientFilter.implOfEpsStandard`, `QuotientFilter.impl_space_le`,
     and `QuotientFilter.implOfEps_space_le` on
     `(U, n, ε, w, w₀, base) = (2 ^ 32, 16, 1 / 16, 64, 32, 100)`.
-/

@[expose] public section

namespace ComplexityTests.WordRAMQuotientFilter

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.ApproximateMembership
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.ApproximateMembership.QuotientFilter
open scoped NNReal ENNReal Finset

/-! ## 1. Shared Two-Stage Reduced `k`-Wise Hash (`ReducedKWise`) -/

theorem reducedTrinomialStep_32_7_7 : reducedTrinomialStep 32 7 7 = 3 := by
  dsimp only [reducedTrinomialStep, reducedTargetBits]
  rw [trinomialStepAux, trinomialStepAux, trinomialStepAux, trinomialStepAux]
  decide

example : reducedChunkBits (reducedTrinomialStep 32 7 7) = 1 := by
  rw [reducedTrinomialStep_32_7_7]; decide

example : reducedLimbCount (reducedTrinomialStep 32 7 7) = 54 := by
  rw [reducedTrinomialStep_32_7_7]; decide

example : ReducedKWise.seedWords 32 7 7 5 = 271 := by
  dsimp only [ReducedKWise.seedWords]
  rw [reducedTrinomialStep_32_7_7]; decide

example : ReducedKWise.tableWords 64 32 7 7 = 1 := by
  dsimp only [ReducedKWise.tableWords]
  rw [reducedTrinomialStep_32_7_7]; decide

theorem reducedKWise_space_64_32_7_7_5 : ReducedKWise.space 64 32 7 7 5 = 272 := by
  dsimp only [ReducedKWise.space, ReducedKWise.seedWords, ReducedKWise.tableWords]
  rw [reducedTrinomialStep_32_7_7]; decide

example : ReducedKWise.initTableSteps 32 7 7 = 137 := by
  dsimp only [ReducedKWise.initTableSteps]
  rw [reducedTrinomialStep_32_7_7]; decide

example : ReducedKWise.resampleSteps 32 7 7 5 = 1368 := by
  dsimp only [ReducedKWise.resampleSteps, ReducedKWise.seedWords]
  rw [reducedTrinomialStep_32_7_7]; decide

example : ReducedKWise.evalSteps 32 7 7 5 = 192576 := by
  dsimp only [ReducedKWise.evalSteps, ReducedKWise.hornerStepSteps]
  rw [reducedTrinomialStep_32_7_7]; decide

theorem reducedKWise_space_le_example :
    ReducedKWise.space 64 32 7 7 5 ≤
      2 + 54 * 5 + 2 * max 8 (2 ^ (7 / 2)) / 64 :=
  ReducedKWise.space_le (by decide) (by decide) (by decide) (by decide)

theorem reducedKWise_hc_lt_example :
    2 * reducedChunkBits (reducedTrinomialStep 32 7 7) < 64 := by
  rw [reducedTrinomialStep_32_7_7]; decide

theorem reducedKWise_fits_space_example :
    Fits 64 (16 + ReducedKWise.space 64 32 7 7 5) := by
  dsimp only [Fits]
  rw [reducedKWise_space_64_32_7_7_5]
  decide

/-- Non-vacuous instantiation of `ReducedKWise.impl` and `ReducedKWise.implStandard` for
`U = 2 ^ 32`, `w = 64`, `w₀ = 32`, `b = 7`, `b' = 7`, `k = 5`, `base = 16`. -/
noncomputable def sampleReducedKWiseImpl :
    HashFamily.WordRAM.Impl .exact 240 0 64 16 (2 ^ 32) (2 ^ 7) ![] :=
  ReducedKWise.impl (w₀ := 32) (b := 7) (b' := 7) (k := 5)
    (by decide) (by decide) le_rfl (by decide)
    reducedKWise_hc_lt_example reducedKWise_fits_space_example

noncomputable def sampleReducedKWiseImplStandard :
    HashFamily.WordRAM.Impl .standard 240 0 64 16 (2 ^ 32) (2 ^ 7) ![] :=
  ReducedKWise.implStandard (w₀ := 32) (b := 7) (b' := 7) (k := 5)
    (by decide) (by decide) le_rfl (by decide)
    reducedKWise_hc_lt_example reducedKWise_fits_space_example

example : sampleReducedKWiseImpl.space = 272 :=
  reducedKWise_space_64_32_7_7_5

/-! ## 2. Quotient Filter Parameter and Space Checks -/

example : effCap 32 16 = 16 := by decide
example : quotBits 32 16 = 7 := by decide
example : remBits 32 4 = 5 := by decide
example : slotPackShift 7 1 64 = 5 := by decide
example : slotPackShift 7 5 64 = 2 := by decide
example : packedWords 7 1 64 = 4 := by decide
example : packedWords 7 5 64 = 32 := by decide

theorem qf_space_64_32_16_4 : space 64 32 16 4 = 317 := by
  dsimp only [space]
  have hq : quotBits 32 16 = 7 := by decide
  rw [hq, reducedKWise_space_64_32_7_7_5]
  decide

theorem qf_setupSteps_32_16 : setupSteps 32 16 = 1510 := by
  dsimp only [setupSteps, ReducedKWise.initTableSteps, ReducedKWise.resampleSteps,
    ReducedKWise.seedWords]
  have hq : quotBits 32 16 = 7 := by decide
  rw [hq, reducedTrinomialStep_32_7_7]
  decide

example : charge = opStepBound 290 := rfl

example : 248 ≤ rQF := le_rQF

theorem epsLog_inv_16 : epsLog (1 / 16 : ℝ≥0∞) = 4 := by
  dsimp only [epsLog]
  have h1 : (1 / 16 : ℝ≥0∞)⁻¹ = 16 := by
    rw [one_div, inv_inv]
  have h2 : ((16 : ℝ≥0∞).toNNReal : ℝ≥0) = 16 := rfl
  have h3 : ⌈((1 / 16 : ℝ≥0∞)⁻¹.toNNReal : ℝ≥0)⌉₊ = 16 := by
    rw [h1, h2]
    exact Nat.ceil_natCast 16
  rw [h3]
  decide

/-! ## 3. Valid Operation Sequence with Insertions, Queries, and Deletions -/

abbrev keyA : Fin (2 ^ 32) := ⟨3, by decide⟩
abbrev keyB : Fin (2 ^ 32) := ⟨7, by decide⟩

/-- Six-operation sequence inserting `keyA` and `keyB`, querying `keyA` (present), deleting `keyA`,
querying `keyA` (now absent), and querying `keyB` (still present). -/
def sampleFilterOps : List (Op (2 ^ 32)) :=
  [ .insert keyA
  , .insert keyB
  , .query keyA
  , .delete keyA
  , .query keyA
  , .query keyB ]

theorem validOpSeq_sampleFilterOps : ValidOpSeq 16 sampleFilterOps := by
  dsimp only [sampleFilterOps, ValidOpSeq, ValidOpSeqFrom, ValidOp, stepSet]
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    trivial,
    by decide,
    trivial,
    trivial,
    trivial⟩

theorem activeSet_sampleFilterOps : activeSet sampleFilterOps = {keyB} := by
  decide

/-- Canonical run invariant `FilterInv` preservation and zero false negatives along
`FilterInv.insertState` and `FilterInv.deleteState` for any seed `p : FilterSeed 32 16`. -/
theorem filterInv_and_noFalseNegatives_trace (p : FilterSeed 32 16) :
    let qHash := quotHash (2 ^ 32) 32 16 p.1
    let rHash := remHash (2 ^ 32) 32 4 p.2
    let st0 := FilterState.empty (quotBits 32 16) (remBits 32 4)
    let hinv0 : FilterInv 16 ∅ qHash rHash st0 := filterInv_empty 16 qHash rHash
    let hlt0 : #(∅ : Finset (Fin (2 ^ 32))) < 2 ^ quotBits 32 16 := by decide
    let st1 := hinv0.insertState hlt0 keyA
    let hinv1 : FilterInv 16 {keyA} qHash rHash st1 :=
      hinv0.insertState_filterInv (by decide) (by decide) (by decide)
    let hlt1 : #({keyA} : Finset (Fin (2 ^ 32))) < 2 ^ quotBits 32 16 := by decide
    let st2 := hinv1.insertState hlt1 keyB
    let hinv2 : FilterInv 16 (insert keyB {keyA}) qHash rHash st2 :=
      hinv1.insertState_filterInv (u := keyB) (by decide) (by decide) (by decide)
    let hlt2 : #(insert keyB {keyA} : Finset (Fin (2 ^ 32))) < 2 ^ quotBits 32 16 := by decide
    let st3 := hinv2.deleteState hlt2 keyA
    let hinv3 : FilterInv 16 (Finset.erase (insert keyB {keyA}) keyA) qHash rHash st3 :=
      hinv2.deleteState_filterInv (u := keyA) (by decide) hlt2
    let hlt3 : #(Finset.erase (insert keyB {keyA}) keyA : Finset (Fin (2 ^ 32))) <
      2 ^ quotBits 32 16 := by decide
    hinv2.querySlot hlt2 keyA = true ∧
    hinv3.querySlot hlt3 keyB = true := by
  intro qHash rHash st0 hinv0 hlt0 st1 hinv1 hlt1 st2 hinv2 hlt2 st3 hinv3 hlt3
  exact ⟨hinv2.querySlot_of_mem hlt2 (by decide), hinv3.querySlot_of_mem hlt3 (by decide)⟩

/-! ## 4. Non-Vacuous Instantiation of `QuotientFilter.impl` and `QuotientFilter.implOfEps` -/

theorem hfit_qf_space_example :
    Fits 64 (100 + space 64 32 16 4) := by
  dsimp only [Fits]
  rw [qf_space_64_32_16_4]
  decide

theorem hfit_qf_space_eps_example :
    Fits 64 (100 + space 64 32 16 (epsLog (1 / 16 : ℝ≥0∞))) := by
  rw [epsLog_inv_16]
  exact hfit_qf_space_example

/-- Exact-basis `ObliviousSequenceImpl` certificate for `U = 2 ^ 32, n = 16, k = 4, w = 64,
w₀ = 32, base = 100`. -/
noncomputable def sampleQFImpl :
    ObliviousSequenceImpl (subroutineCode 64 32 16 4)
      (spec (2 ^ 32) 16 ((1 / 2 : ℝ≥0∞) ^ 4)) 64 100 ![] :=
  QuotientFilter.impl (by decide) (by decide) le_rfl hfit_qf_space_example

/-- Standard-basis `ObliviousSequenceImpl` certificate for `U = 2 ^ 32, n = 16, k = 4, w = 64,
w₀ = 32, base = 100`. -/
noncomputable def sampleQFImplStandard :
    ObliviousSequenceImpl (subroutineCode 64 32 16 4).toStandard
      (spec (2 ^ 32) 16 ((1 / 2 : ℝ≥0∞) ^ 4)) 64 100 ![] :=
  QuotientFilter.implStandard (by decide) (by decide) le_rfl hfit_qf_space_example

/-- Exact-basis `ObliviousSequenceImpl` certificate for `ε = 1 / 16`. -/
noncomputable def sampleQFImplOfEps :
    ObliviousSequenceImpl (subroutineCode 64 32 16 (epsLog (1 / 16 : ℝ≥0∞)))
      (spec (2 ^ 32) 16 (1 / 16 : ℝ≥0∞)) 64 100 ![] :=
  QuotientFilter.implOfEps (by norm_num) (by decide) (by decide) le_rfl hfit_qf_space_eps_example

/-- Standard-basis `ObliviousSequenceImpl` certificate for `ε = 1 / 16`. -/
noncomputable def sampleQFImplOfEpsStandard :
    ObliviousSequenceImpl (subroutineCode 64 32 16 (epsLog (1 / 16 : ℝ≥0∞))).toStandard
      (spec (2 ^ 32) 16 (1 / 16 : ℝ≥0∞)) 64 100 ![] :=
  QuotientFilter.implOfEpsStandard
    (by norm_num) (by decide) (by decide) le_rfl hfit_qf_space_eps_example

theorem sampleQFImpl_space_le :
    sampleQFImpl.space ≤ 640 * ((16 * 4 + 64 - 1) / 64 + 1) :=
  QuotientFilter.impl_space_le (by decide) (by decide) le_rfl hfit_qf_space_example
    (by decide) (by decide)

theorem sampleQFImplOfEps_space_le :
    sampleQFImplOfEps.space ≤
      640 * ((16 * epsLog (1 / 16 : ℝ≥0∞) + 64 - 1) / 64 + 1) :=
  QuotientFilter.implOfEps_space_le (by norm_num) (by decide) (by decide) le_rfl
    hfit_qf_space_eps_example (by decide)

/-- Non-vacuous end-to-end execution of `sampleQFImplOfEps.steps_exec` on `sampleFilterOps`:
from any initial state distribution `ν₀` satisfying `sampleQFImplOfEps.initInv ν₀`, executing the
6-operation sequence `sampleFilterOps` produces a final distribution `ν_final` whose transcript
satisfies `(spec (2 ^ 32) 16 (1 / 16)).Contract sampleFilterOps` (zero false negatives and
false-positive probability `≤ 1 / 16`) with total expected operation time at most
`6 * charge`. -/
theorem nonvacuous_sampleQFImplOfEps_steps
    (ν₀ : PMF (LatentState (FilterSeed 32 16) rQF))
    (hinv : sampleQFImplOfEps.initInv ν₀) :
    ∃ (ν_final : PMF (SeqOutcome (FilterSeed 32 16) (@Result (2 ^ 32)) rQF)) (T_ops : ℝ≥0∞),
      ExecSteps (subroutineCode 64 32 16 (epsLog (1 / 16 : ℝ≥0∞)))
        (spec (2 ^ 32) 16 (1 / 16 : ℝ≥0∞))
        (FilterSeed 32 16) 64 100 sampleQFImplOfEps.space encode decode
        sampleFilterOps (ν₀.map SeqOutcome.ofLatentState) ν_final T_ops ∧
      (spec (2 ^ 32) 16 (1 / 16 : ℝ≥0∞)).Contract sampleFilterOps
        (ν_final.map SeqOutcome.transcript) ∧
      T_ops ≤ ((sampleFilterOps.length * charge : ℕ) : ℝ≥0∞) := by
  obtain ⟨ν_final, T_ops, hex, hcontract, hcost⟩ :=
    sampleQFImplOfEps.steps_exec sampleFilterOps ν₀ validOpSeq_sampleFilterOps hinv
  refine ⟨ν_final, T_ops, hex, hcontract, ?_⟩
  simpa only [sampleQFImplOfEps, implOfEps, implOfLe, Nat.cast_zero, zero_add,
    List.map_const', List.sum_replicate, smul_eq_mul] using hcost

end ComplexityTests.WordRAMQuotientFilter
