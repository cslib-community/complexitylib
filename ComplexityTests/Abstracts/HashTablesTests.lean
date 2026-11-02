/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.HashTablesAbstract

/-!
# Formal Abstract Tests: Word-RAM Hash Tables

Non-vacuity and concrete evaluation checks for `ComplexityAbstracts.HashTablesAbstract`.
-/

namespace ComplexityTests.Abstracts.HashTablesTests

open scoped ENNReal
open ComplexityAbstracts.HashTablesAbstract

/-! ## Concrete Resource and Constant Evaluations -/

lemma lt_pow_4 {N : ℕ} (hN : 2 < N) : 4 < 2 ^ N := by
  change 2 ^ 2 < 2 ^ N
  exact Nat.pow_lt_pow_right (by decide) hN

lemma lt_regimeThreshold_4 : 4 < regimeThreshold :=
  lt_pow_4 (by decide)

example : regimeThreshold = 2 ^ 320000 := rfl

-- Table 1: Chained Hashing (`n_max = 4, U = 4`)
example : chainedBucketBits 4 = 2 := by decide
example : chainedNumBuckets 4 = 4 := by decide
example : chainedHashBits 4 4 = 2 := by decide
example : chainedSpace 4 = 20 := by decide
example : chainedSpace 4 ≤ 8 * (4 + 1) := chainedSpace_le 4

-- Table 2: Linear Probing (`n_max = 4, U = 4`)
example : chunkBits 4 = 1 := by decide
example : lpTableLog 4 = 5 := by decide
example : lpTableSize 4 = 32 := by decide
example : trinomialStep 4 5 = 1 := by decide
example : trinomialDeg 4 5 = 6 := by decide
example : limbCount 4 4 5 = 6 := by decide
example : kWiseSpace 4 5 = 17 := by decide
example : lpSpace 4 = 113 := by decide
example : lpInitSteps 4 4 = 209 := by decide
example : lpOpCharge 4 4 = 5992 := by decide
example : lpOpChargeBound = 559652 := rfl
example : lpSpace 4 ≤ 209 * (4 + 1) := linearProbingSpace_le 4
example : lpOpCharge 4 4 ≤ lpOpChargeBound := linearProbingCharge_le (by decide)

-- Table 3: Uniform Probing (`n_max = 4`)
example : charBits 4 = 1 := by decide
example : tableBits32 4 = 7 := by decide
example : tableSize32 4 = 128 := by decide
example : upSingleTabSpace 4 = 1152 := by decide
example : upSpace 4 = 2688 := by decide
example : upSpaceFactor = 19200 := rfl
example : upInitSteps 4 = 11553 := by decide
example : upHashEvalSteps = 13731 := rfl
example : upOpCharge = 13 * 2 ^ 320000 + 13739 := by
  have h : upHashEvalSteps = 13731 := rfl
  unfold upOpCharge regimeThreshold
  rw [h, Nat.add_assoc]
example : upSpace 4 ≤ upSpaceFactor * (4 + 1) := uniformProbingSpace_le 4

-- Table 4: Cuckoo Hashing (`n_max = 4, U = 4`)
example : cuckooMaxEvictions 4 = 24 := by decide
example : cuckooK 4 = 50 := by decide
example : cuckooKBound = 3840026 := rfl

lemma cuckooSingleHashSpace_4 : cuckooSingleHashSpace 4 = 62 := by
  dsimp only [cuckooSingleHashSpace]
  simp only [lt_regimeThreshold_4, ↓reduceIte]
  decide

lemma cuckooSpace_4 : cuckooSpace 4 = 408 := by
  dsimp only [cuckooSpace, cuckooHashPairSpace]
  rw [cuckooSingleHashSpace_4]
  decide

lemma cuckooResampleSingleSteps_4 : cuckooResampleSingleSteps 4 = 260 := by
  dsimp only [cuckooResampleSingleSteps]
  simp only [lt_regimeThreshold_4, ↓reduceIte]
  decide

lemma cuckooInitSteps_4_4 : cuckooInitSteps 4 4 = 1131 := by
  dsimp only [cuckooInitSteps]
  rw [cuckooSingleHashSpace_4, cuckooResampleSingleSteps_4]
  decide

example : cuckooSpaceFactor = 7699050 := rfl
example : cuckooEvalHashBound = 427126092003 := rfl
example : cuckooGetStepsBound = 854252184109 := rfl
example : cuckooGetCharge = 854252184111 := rfl
example : cuckooEvictIterBound = 854252184173 := rfl
example : cuckooInsertBaseBound = 854252184154 := rfl
example : cuckooResampleAtBaseFactor = 38400295 := rfl
example : cuckooRehashAmortizedBound = 2562833357400 := rfl
example : cuckooInsertCharge = 27336684332552 := rfl
example : cuckooSpace 4 ≤ cuckooSpaceFactor * (4 + 1) := cuckooSpace_le 4
example : cuckooOpCharge (.get (⟨0, by decide⟩ : Fin 4)) ≤ cuckooInsertCharge :=
  cuckooOpCharge_le _
example : cuckooOpCharge (.insert (⟨0, by decide⟩ : Fin 4) 5) ≤ cuckooInsertCharge :=
  cuckooOpCharge_le _

/-! ## Sample Valid Operation History and Dictionary Semantics -/

example : decodeLookup 0 = none := rfl
example : decodeLookup 8 = some 7 := rfl

example (sampleState : DictState 4) :
    sampleState =
      stepDict (stepDict (stepDict (emptyDict 4)
        (.insert ⟨0, by decide⟩ 5))
        (.insert ⟨1, by decide⟩ 3))
        (.insert ⟨0, by decide⟩ 7) →
    sampleState ⟨0, by decide⟩ = some 7 ∧
    sampleState ⟨1, by decide⟩ = some 3 ∧
    sampleState ⟨2, by decide⟩ = none := by
  rintro rfl
  decide

/-- Six-operation sequence (`insert 0 5`, `insert 1 3`, `insert 0 7`, `get 0`, `get 1`, `get 2`)
on `Fin 4`, exercising two distinct keys, an overwrite, two hits, and a miss. -/
def sampleOps : List (DictOp 4) :=
  [ .insert ⟨0, by decide⟩ 5,
    .insert ⟨1, by decide⟩ 3,
    .insert ⟨0, by decide⟩ 7,
    .get ⟨0, by decide⟩,
    .get ⟨1, by decide⟩,
    .get ⟨2, by decide⟩ ]

lemma validDictHistory_sampleOps : ValidDictHistory 8 4 (emptyDict 4) sampleOps := by
  refine ⟨⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inr (by decide), by decide⟩,
    trivial, trivial, trivial, trivial⟩

lemma wordBounded_zero (r : ℕ) : WordBounded 64 (fun (_ : Fin r) => 0) (fun _ => 0) :=
  ⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩

/-! ## Headline Theorem Non-Vacuity (`(U, V, n_max, w, base) = (4, 8, 4, 64, 0)`) -/

/-- Non-vacuity of `chainedHashing` on `sampleOps`. -/
theorem nonvacuous_chainedHashing :
    ∃ (p_init p_op : List (Instr 22))
      (Seed : Type) (μ_init μ_final : PMF (CoupledState Seed 22)) (T_ops : ℝ≥0∞),
      ExecProgramDist 64 p_init ⟨10, by decide⟩ (fun _ => 0) (fun _ => 0)
        (μ_init.map CoupledState.toRegMem) 16 ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨5, by decide⟩ = 0 ∧
        p.reg ⟨6, by decide⟩ = 0 + chainedSpace 4 ∧
        UnchangedOutside 0 (chainedSpace 4) (fun _ => 0) p.mem) ∧
      ExecDictOps 64 p_op true
        ⟨5, by decide⟩ ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨9, by decide⟩ ⟨10, by decide⟩
        0 (chainedSpace 4) (emptyDict 4) sampleOps μ_init μ_final T_ops ∧
      (16 : ℝ≥0∞) + T_ops ≤ ((16 + 73 * sampleOps.length : ℕ) : ℝ≥0∞) := by
  obtain ⟨p_init, p_op, hexec⟩ := chainedHashing 4 4
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hexec 8 64 0 (by decide) (by decide) (by decide)
      (fun _ => 0) (fun _ => 0) (wordBounded_zero 22) rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, hbound⟩ := hseq sampleOps validDictHistory_sampleOps
  exact ⟨p_init, p_op, Seed, μ_init, μ_final, T_ops, hinit, hsupp, hops, hbound⟩

/-- Non-vacuity of `linearProbing` on `sampleOps`. -/
theorem nonvacuous_linearProbing :
    ∃ (p_init p_op : List (Instr 24))
      (Seed : Type) (μ_init μ_final : PMF (CoupledState Seed 24)) (T_ops : ℝ≥0∞),
      ExecProgramDist 64 p_init ⟨2, by decide⟩ (fun _ => 0) (fun _ => 0)
        (μ_init.map CoupledState.toRegMem) (lpInitSteps 4 4) ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨0, by decide⟩ = 0 ∧
        p.reg ⟨18, by decide⟩ = 0 + lpSpace 4 ∧
        UnchangedOutside 0 (lpSpace 4) (fun _ => 0) p.mem) ∧
      ExecDictOps 64 p_op false
        ⟨0, by decide⟩ ⟨22, by decide⟩ ⟨1, by decide⟩ ⟨23, by decide⟩ ⟨2, by decide⟩
        0 (lpSpace 4) (emptyDict 4) sampleOps μ_init μ_final T_ops ∧
      (lpInitSteps 4 4 : ℝ≥0∞) + T_ops ≤
        ((lpInitSteps 4 4 + sampleOps.length * lpOpChargeBound : ℕ) : ℝ≥0∞) := by
  obtain ⟨p_init, p_op, hexec⟩ := linearProbing 4 4
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hexec 8 64 0 (by decide) (by decide) (by decide) (by decide)
      (fun _ => 0) (fun _ => 0) (wordBounded_zero 24) rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, _, hbound⟩ := hseq sampleOps validDictHistory_sampleOps
  exact ⟨p_init, p_op, Seed, μ_init, μ_final, T_ops, hinit, hsupp, hops, hbound⟩

/-- Non-vacuity of `uniformProbing` on `sampleOps`. -/
theorem nonvacuous_uniformProbing :
    ∃ (p_init p_op : List (Instr 16))
      (Seed : Type) (μ_init μ_final : PMF (CoupledState Seed 16)) (T_ops : ℝ≥0∞),
      ExecProgramDist 64 p_init ⟨12, by decide⟩ (fun _ => 0) (fun _ => 0)
        (μ_init.map CoupledState.toRegMem) (upInitSteps 4) ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨0, by decide⟩ = 0 ∧
        p.reg ⟨14, by decide⟩ = 0 + upSpace 4 ∧
        UnchangedOutside 0 (upSpace 4) (fun _ => 0) p.mem) ∧
      ExecDictOps 64 p_op true
        ⟨0, by decide⟩ ⟨12, by decide⟩ ⟨13, by decide⟩ ⟨14, by decide⟩ ⟨12, by decide⟩
        0 (upSpace 4) (emptyDict 4) sampleOps μ_init μ_final T_ops ∧
      (upInitSteps 4 : ℝ≥0∞) + T_ops ≤
        ((upInitSteps 4 + sampleOps.length * upOpCharge : ℕ) : ℝ≥0∞) := by
  obtain ⟨p_init, p_op, hexec⟩ := uniformProbing 4
  have hfit_U : ∀ u : Fin 4, u.val < 2 ^ 64 := fun u => u.isLt.trans (by decide)
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hexec 4 8 64 0 (by decide) (by decide) hfit_U (by decide)
      (fun _ => 0) (fun _ => 0) (wordBounded_zero 16) rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, hbound⟩ := hseq sampleOps validDictHistory_sampleOps
  exact ⟨p_init, p_op, Seed, μ_init, μ_final, T_ops, hinit, hsupp, hops, hbound⟩

/-- Initial register bank for `cuckooHashing` at `(n_max, U, base) = (4, 4, 0)`. -/
def cuckooTestReg : Fin 19 → ℕ
  | ⟨1, _⟩ => 0
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 4
  | _ => 0

lemma wordBounded_cuckooTestReg : WordBounded 64 cuckooTestReg (fun _ => 0) := by
  refine ⟨fun i => ?_, fun _ => (by decide : 0 < 2 ^ 64)⟩
  fin_cases i <;> decide

/-- Non-vacuity of `cuckooHashing` on `sampleOps`. -/
theorem nonvacuous_cuckooHashing :
    ∃ (p_init p_op : List (Instr 19))
      (Seed : Type) (μ_init μ_final : PMF (CoupledState Seed 19)) (T_ops : ℝ≥0∞),
      ExecProgramDist 64 p_init ⟨2, by decide⟩ cuckooTestReg (fun _ => 0)
        (μ_init.map CoupledState.toRegMem) (cuckooInitSteps 4 4) ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨0, by decide⟩ = 0 ∧
        p.reg ⟨1, by decide⟩ = 0 + cuckooSpace 4 ∧
        UnchangedOutside 0 (cuckooSpace 4) (fun _ => 0) p.mem) ∧
      ExecDictOps 64 p_op true
        ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ ⟨4, by decide⟩ ⟨2, by decide⟩
        0 (cuckooSpace 4) (emptyDict 4) sampleOps μ_init μ_final T_ops ∧
      (cuckooInitSteps 4 4 : ℝ≥0∞) + T_ops ≤
        ((cuckooInitSteps 4 4 + (sampleOps.map cuckooOpCharge).sum : ℕ) : ℝ≥0∞) ∧
      (cuckooInitSteps 4 4 : ℝ≥0∞) + T_ops ≤
        ((cuckooInitSteps 4 4 + sampleOps.length * cuckooInsertCharge : ℕ) : ℝ≥0∞) := by
  obtain ⟨p_init, p_op, hexec⟩ := cuckooHashing 4
  have hsp : 0 + cuckooSpace 4 < 2 ^ 64 := by
    rw [cuckooSpace_4]
    decide
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hexec 4 8 64 0 (by decide) (by decide) hsp (by decide) (by decide) (by decide)
      cuckooTestReg (fun _ => 0) wordBounded_cuckooTestReg rfl rfl rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, hbound1, hbound2⟩ := hseq sampleOps validDictHistory_sampleOps
  exact ⟨p_init, p_op, Seed, μ_init, μ_final, T_ops, hinit, hsupp, hops, hbound1, hbound2⟩

end ComplexityTests.Abstracts.HashTablesTests
