/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import CslibFrontierAbstracts.ApproximateMembershipAbstract

/-!
# Formal Abstract Tests: Two-Stage Quotient Filter (`ApproximateMembershipAbstract`)

Non-vacuity and concrete evaluation checks for
`CslibFrontierAbstracts.ApproximateMembershipAbstract`.
-/

namespace CslibFrontierTests.Abstracts.ApproximateMembershipTests

open scoped NNReal ENNReal
open CslibFrontierAbstracts.ApproximateMembershipAbstract

/-! ## Concrete Parameter and Space Evaluations (`w = 64, w₀ = 32, n = 16, k = 4`) -/

example : qfEffCap 32 16 = 16 := by decide
example : qfQuotBits 32 16 = 7 := by decide
example : qfRemBits 32 4 = 5 := by decide
example : qfSlotPackShift 7 1 64 = 5 := by decide
example : qfSlotPackShift 7 5 64 = 2 := by decide
example : qfPackedWords 7 1 64 = 4 := by decide
example : qfPackedWords 7 5 64 = 32 := by decide
example : qfReducedStep 32 7 7 = 3 := by decide
example : qfReducedChunkBits (qfReducedStep 32 7 7) = 1 := by decide
example : qfReducedLimbCount (qfReducedStep 32 7 7) = 54 := by decide
example : qfReducedSeedWords 32 7 7 5 = 271 := by decide
example : qfReducedTableWords (qfReducedStep 32 7 7) 64 = 1 := by decide
example : qfReducedKWiseSpace 64 32 7 7 5 = 272 := by decide
example : qfSpace 64 32 16 4 = 317 := by decide
example : qfInitSteps 32 16 = 1513 := by decide

example : qfSpace 64 32 16 4 ≤ 640 * ((16 * 4 + 64 - 1) / 64 + 1) :=
  qfSpace_le (by decide) (by decide) (by decide) (by decide) (by decide)

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

theorem qfSpaceOfEps_64_32_16_inv16 :
    qfSpaceOfEps 64 32 16 (1 / 16 : ℝ≥0∞) = 317 := by
  dsimp only [qfSpaceOfEps]
  rw [epsLog_inv_16]
  decide

example :
    qfSpaceOfEps 64 32 16 (1 / 16 : ℝ≥0∞) ≤
      640 * ((16 * epsLog (1 / 16 : ℝ≥0∞) + 64 - 1) / 64 + 1) :=
  qfSpaceOfEps_le (by decide) (by decide) (by decide) (by decide)

/-! ## Sample Valid Operation Sequence and Filter Semantics -/

abbrev k1 : Fin 16 := ⟨1, by decide⟩
abbrev k5 : Fin 16 := ⟨5, by decide⟩

example :
    decodeFilterEntry (⟨1, by decide⟩ : Fin 248) (.insert k1) (fun _ => 99) =
      (.insert k1, false) :=
  rfl

example :
    decodeFilterEntry (⟨1, by decide⟩ : Fin 248) (.delete k1) (fun _ => 99) =
      (.delete k1, false) :=
  rfl

example :
    decodeFilterEntry (⟨1, by decide⟩ : Fin 248) (.query k1) (fun _ => 0) =
      (.query k1, false) :=
  rfl

example :
    decodeFilterEntry (⟨1, by decide⟩ : Fin 248) (.query k1) (fun _ => 1) =
      (.query k1, true) :=
  rfl

/-- Six-operation sequence (`insert 1`, `insert 5`, `query 1`, `delete 1`, `query 1`, `query 5`)
on `Fin 16`, exercising two insertions, a present-key query, a deletion, a post-deletion absent-key
query, and a remaining present-key query. -/
def sampleOps : List (FilterOp 16) :=
  [ .insert k1
  , .insert k5
  , .query k1
  , .delete k1
  , .query k1
  , .query k5 ]

theorem validFilterSeq_sampleOps : ValidFilterSeq 4 sampleOps := by
  dsimp only [ValidFilterSeq, ValidFilterSeqFrom, ValidFilterOp, stepSet, sampleOps]
  refine ⟨⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩,
    trivial,
    by decide,
    trivial,
    trivial,
    trivial⟩

theorem activeSet_sampleOps : activeSet sampleOps = {k5} := by
  decide

lemma wordBounded_zero {r : ℕ} : WordBounded 64 (fun (_ : Fin r) => 0) (fun _ => 0) :=
  ⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩

/-! ## Headline Theorem Non-Vacuity (`(w, w₀, n, ε, U, base) = (64, 4, 4, 1 / 16, 16, 0)`) -/

theorem qfSpaceOfEps_64_4_4_inv16 :
    qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞) = 40 := by
  dsimp only [qfSpaceOfEps]
  rw [epsLog_inv_16]
  decide

/-- Non-vacuity of `quotientFilter` on `sampleOps` at `(w, w₀, n, ε, U, base) =
(64, 4, 4, 1 / 16, 16, 0)`: produces `r`, `C_op`, `p_init`, `p_op`, `Seed`, `μ_init`, `μ_final`,
and `T_ops` satisfying compact single-block space (`≤ 640 * ((4 * 4 + 64 - 1) / 64 + 1)`),
bounded-time initialization, per-operation expected time `≤ C_op`, zero false negatives on every
branch, and false-positive probability `≤ 1 / 16` for every absent-key query. -/
theorem nonvacuous_quotientFilter :
    ∃ (r C_op : ℕ) (hr : 248 ≤ r) (p_init p_op : List (Instr r))
      (Seed : Type) (μ_init μ_final : PMF (CoupledOutcome Seed 16 r)) (T_ops : ℝ≥0∞),
      qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞) ≤
        640 * ((4 * epsLog (1 / 16 : ℝ≥0∞) + 64 - 1) / 64 + 1) ∧
      ExecProgramDist 64 p_init ⟨1, by omega⟩ (fun _ => 0) (fun _ => 0)
        (μ_init.map CoupledOutcome.toRegMem) (qfInitSteps 4 4) ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨0, by omega⟩ = 0 ∧
        p.reg ⟨240, by omega⟩ = 0 + qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞) ∧
        p.transcript = [] ∧
        UnchangedOutside 0 (qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞)) (fun _ => 0) p.mem) ∧
      ExecFilterOps 64 p_op
        ⟨1, by omega⟩ ⟨247, by omega⟩ ⟨1, by omega⟩
        0 (qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞)) C_op sampleOps
        μ_init μ_final T_ops ∧
      FilterContract (1 / 16 : ℝ≥0∞) sampleOps (μ_final.map CoupledOutcome.transcript) ∧
      T_ops ≤ ((sampleOps.length * C_op : ℕ) : ℝ≥0∞) := by
  have hsp : 0 + qfSpaceOfEps 64 4 4 (1 / 16 : ℝ≥0∞) < 2 ^ 64 := by
    rw [qfSpaceOfEps_64_4_4_inv16]
    decide
  obtain ⟨r, C_op, hr, hqf⟩ := quotientFilter
  obtain ⟨p_init, p_op, hexec⟩ := hqf 64 4 4 (1 / 16 : ℝ≥0∞)
  obtain ⟨hsp_le, hrun⟩ :=
    hexec 16 0 (by norm_num) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hrun (fun _ => 0) (fun _ => 0) wordBounded_zero rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, hcontract, hbound⟩ :=
    hseq sampleOps validFilterSeq_sampleOps
  exact ⟨r, C_op, hr, p_init, p_op, Seed, μ_init, μ_final, T_ops,
    hsp_le, hinit, hsupp, hops, hcontract, hbound⟩

end CslibFrontierTests.Abstracts.ApproximateMembershipTests
