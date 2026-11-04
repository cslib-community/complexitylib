/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.WordRAM.Succinct

/-!
# Fixed-Capacity Succinct Dynamic Dictionary Tests

Exercises:
1. `Cslib.DataStructure.Dictionary.Dynamic`:
   - concrete evaluations of `optBits`, `logLogFactor`, `succinctWords`, `dom`, `step`, and
     `ValidHistory` across insertions, overwrites, queries, and deletions;
2. `Cslib.DataStructure.Dictionary.FeistelQuotient`:
   - concrete evaluations of `bucketBits`, `numBuckets`, `quotientBits`, and round-trip
     verification of `feistelReconstruct_feistelBucket` and `quotient_val_bits_le_optBits`;
3. `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray`:
   - concrete evaluations of `packedWords` and verification of `readPacked_writePacked_self` and
     `readPacked_writePacked_of_ne`;
4. `Cslib.DataStructure.Dictionary.SuccinctBucket` and
   `Cslib.DataStructure.Dictionary.WordRAM.Succinct`:
   - concrete evaluations of `slabSize`, `maxFullSlabs`, `maxTailItems`, `totalMicroBits`,
     `microBits`, `qBits`, `hashB`, `hashSpace`, `space`, and `initSteps` for
     `(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 16, 100)`;
   - verification of `space_le_succinctWords`, `initSteps_le`, `initSteps_le_mul`,
     `initTime_impl_le`, `impl`, `implStandard`, and `seq_expected_amortized` on a multi-operation
     sequence with insertions, overwrites, present/absent queries, and deletions.
-/

@[expose] public section

namespace ComplexityTests.WordRAMSuccinctDictionary

open Cslib Cslib.WordRAM Cslib.Probability
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open scoped ENNReal Finset

/-! ## 1. Dynamic Dictionary Specification (`Dynamic.spec`) -/

example : Dynamic.logLogFactor 4 = 1 := by decide
example : Dynamic.logLogFactor 16 = 2 := by decide
example : Dynamic.optBits 16 8 4 = 23 := by decide
example : Dynamic.succinctWords 81 213 16 8 64 4 = 219 := by decide

abbrev key3 : Fin (2 ^ 32) := ⟨3, by decide⟩
abbrev key7 : Fin (2 ^ 32) := ⟨7, by decide⟩

/-- Seven-operation sequence on `Fin (2 ^ 32)` with value bound `V = 2 ^ 16` and capacity
`n_max = 16`: insert `key3 ↦ 100`, insert `key7 ↦ 200`, overwrite `key3 ↦ 300`, query `key3`
(present), delete `key3`, query `key3` (now absent), and query `key7` (still present). -/
def sampleDictOps : List (Dynamic.Op (2 ^ 32)) :=
  [ .insert key3 100
  , .insert key7 200
  , .insert key3 300
  , .query key3
  , .delete key3
  , .query key3
  , .query key7 ]

theorem validHistory_sampleDictOps :
    (Dynamic.spec (2 ^ 32) (2 ^ 16) 16).ValidHistory (Dynamic.empty (2 ^ 32)) sampleDictOps := by
  have hcard0 : (Dynamic.dom (Dynamic.empty (2 ^ 32))).card < 16 := by simp
  have hcard1 :
      (Dynamic.dom (Function.update (Dynamic.empty (2 ^ 32)) key3 (some 100))).card < 16 := by
    have hle := Dictionary.card_dom_insert_le (Dynamic.empty (2 ^ 32)) key3 100
    simp only [Dynamic.empty, Dictionary.dom_empty, Finset.card_empty, zero_add] at hle
    exact lt_of_le_of_lt hle (by decide)
  have hisSome2 :
      (Function.update
        (Function.update (Dynamic.empty (2 ^ 32)) key3 (some 100))
        key7 (some 200) key3).isSome := by
    have hne : key3 ≠ key7 := by decide
    rw [Function.update_of_ne hne, Function.update_self]
    rfl
  dsimp only [sampleDictOps, Dynamic.spec, StateTransitionSpec.ValidHistory,
    StateTransitionSpec.ofFn, Dynamic.valid, Dynamic.step]
  exact ⟨⟨Or.inl hcard0, by decide⟩,
    ⟨Or.inl hcard1, by decide⟩,
    ⟨Or.inr hisSome2, by decide⟩,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-! ## 2. One-Round Feistel Quotienting (`FeistelQuotient`) -/

example : bucketBits 16 = 0 := by decide
example : numBuckets 16 = 1 := by decide
example : quotientBits (2 ^ 32) 16 = 32 := by decide
example : bucketBits (2 ^ 16) = 4 := by decide
example : numBuckets (2 ^ 16) = 16 := by decide
example : quotientBits (2 ^ 32) (2 ^ 16) = 28 := by decide

example (h₁ : ℕ → ℕ) (u : Fin (2 ^ 32)) :
    feistelReconstruct (bucketBits (2 ^ 16)) h₁
      (feistelBucket (bucketBits (2 ^ 16)) h₁ u.val)
      (keyQuotient (bucketBits (2 ^ 16)) u.val) = u.val :=
  feistelReconstruct_feistelBucket (bucketBits (2 ^ 16)) h₁ u.val

example :
    16 * (quotientBits (2 ^ 32) 16 + valBits (2 ^ 16)) ≤
      Dynamic.optBits (2 ^ 32) (2 ^ 16) 16 + 5 * 16 * Dynamic.logLogFactor 16 :=
  quotient_val_bits_le_optBits (by decide : 16 ≤ 2 ^ 32)

/-! ## 3. Bit-Packed Array Primitive (`BitPackedArray`) -/

example : packedWords 16 12 64 = 5 := by decide

example (mem : ℕ → ℕ) :
    readPacked 100 12 64 (writePacked 100 12 64 mem 5 1234) 5 = 1234 :=
  readPacked_writePacked_self 100 12 64 mem 5 (by decide)

example (mem : ℕ → ℕ) :
    readPacked 100 12 64 (writePacked 100 12 64 mem 5 1234) 6 =
      readPacked 100 12 64 mem 6 :=
  readPacked_writePacked_of_ne (by decide) mem (by decide) 1234

/-! ## 4. Bucket & Word-RAM Succinct Dictionary Parameters (`SuccinctBucket`, `Succinct`) -/

example : slabSize 16 = 1 := by decide
example : maxFullSlabs 16 = 0 := by decide
example : maxTailItems 16 = 0 := by decide
example : slabSize (2 ^ 16) = 256 := by decide
example : maxFullSlabs (2 ^ 16) = 256 := by decide
example : maxTailItems (2 ^ 16) = 8192 := by decide
example : totalMicroBits 16 = 4 := by decide
example : microBits 16 = 4 := by decide
example : qBits (2 ^ 32) 16 = 32 := by decide
example : hashB 16 = 5 := by decide

theorem trinomialStep_32_5_4 :
    reducedTrinomialStep (qBits (2 ^ 32) 16) (hashB 16) (totalMicroBits 16) = 2 := by
  dsimp only [qBits, quotientBits, keyBits, bucketBits, hashB, totalMicroBits, microBits,
    Dynamic.logLogFactor, reducedTrinomialStep, reducedTargetBits]
  rw [trinomialStepAux, trinomialStepAux, trinomialStepAux]
  decide

theorem hashSpace_32_64_16 :
    hashSpace (2 ^ 32) 64 16 = 56 := by
  dsimp only [hashSpace, ReducedKWise.space, ReducedKWise.seedWords, ReducedKWise.tableWords]
  rw [trinomialStep_32_5_4]
  decide

theorem succinct_space_32_16_64_16 :
    space (2 ^ 32) (2 ^ 16) 64 16 = 111 := by
  dsimp only [space, totalSpace, offGM, offLM, offVal, offQuot, lmSubWords,
    globalMetaLen, globalPtrBits, effBucketPosBits, totalMicroBuckets]
  rw [hashSpace_32_64_16]
  decide

theorem succinct_initSteps_32_16 :
    initSteps (2 ^ 32) 16 = 427 := by
  dsimp only [initSteps, ReducedKWise.initTableSteps, ReducedKWise.resampleSteps,
    ReducedKWise.seedWords]
  rw [trinomialStep_32_5_4]
  decide

theorem hfit_succinct_example :
    Fits 64 (100 + space (2 ^ 32) (2 ^ 16) 64 16) := by
  dsimp only [Fits]
  rw [succinct_space_32_16_64_16]
  decide

example :
    space (2 ^ 32) (2 ^ 16) 64 16 ≤
      Dynamic.succinctWords 81 213 (2 ^ 32) (2 ^ 16) 64 16 :=
  space_le_succinctWords (by decide) (by decide) (by decide)

example : initSteps (2 ^ 32) 16 ≤ 31 * 16 + 1091 :=
  initSteps_le (2 ^ 32) 16

example : initSteps (2 ^ 32) 16 ≤ 1091 * (16 + 1) :=
  initSteps_le_mul (2 ^ 32) 16

/-- Exact-basis `Randomized.StateTransitionImpl` certificate for
`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 16, 100)`. -/
noncomputable abbrev sampleSuccinctImpl :
    Randomized.StateTransitionImpl (subroutineCode (2 ^ 32) (2 ^ 16) 64 16)
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dynamic.empty (2 ^ 32)) :=
  impl (by decide) (by decide) (by decide) (by decide) hfit_succinct_example

/-- Standard-basis `Randomized.StateTransitionImpl` certificate for
`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 16, 100)`. -/
noncomputable abbrev sampleSuccinctImplStandard :
    Randomized.StateTransitionImpl (subroutineCode (2 ^ 32) (2 ^ 16) 64 16).toStandard
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dynamic.empty (2 ^ 32)) :=
  implStandard (by decide) (by decide) (by decide) (by decide) hfit_succinct_example

example : sampleSuccinctImpl.space = 111 :=
  succinct_space_32_16_64_16

example :
    sampleSuccinctImpl.initTime ≤ (initSteps (2 ^ 32) 16 + 1 : ℕ) ∧
    initSteps (2 ^ 32) 16 + 1 ≤ 31 * 16 + 1092 :=
  initTime_impl_le (by decide) (by decide) (by decide) (by decide) hfit_succinct_example

/-- Non-vacuous end-to-end execution of `seq_expected_amortized` on `sampleDictOps`
starting from an initial machine state with `reg 240 = 100` and zeroed memory. -/
theorem nonvacuous_seq_expected_amortized :
    let x₀ : Data rSuccinct :=
      ⟨Function.update (fun _ => 0) WordRAM.Succinct.frontierReg 100, fun _ => 0⟩
    ∃ (ν₀ ν_final : PMF (sampleSuccinctImpl.Seed × Data rSuccinct))
      (T_ops : ℝ≥0∞),
      ExecCodeDist 64 (subroutineCode (2 ^ 32) (2 ^ 16) 64 16).initFresh x₀ (ν₀.map Prod.snd)
        sampleSuccinctImpl.initTime ∧
      sampleSuccinctImpl.ExecStepsOfFn (Dynamic.empty (2 ^ 32)) sampleDictOps ν₀ ν_final T_ops ∧
      (∀ p ∈ ν_final.support,
        Rep (2 ^ 32) (2 ^ 16) 64 16 100 p.1
          ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dynamic.empty (2 ^ 32)) sampleDictOps).1
          p.2) ∧
      sampleSuccinctImpl.initTime + T_ops +
        (∑' q, ν_final q * (potential (2 ^ 32) (2 ^ 16) 64 16 100 q.1 q.2 : ℝ≥0∞)) ≤
        sampleSuccinctImpl.initTime +
          (sampleDictOps.length * chargeVal : ℕ) := by
  intro x₀
  have hx₀ : x₀.Bounded 64 := by
    refine ⟨fun i => ?_, fun _ => (by decide : 0 < 2 ^ 64)⟩
    dsimp only [x₀]
    by_cases h : i = WordRAM.Succinct.frontierReg
    · subst h
      rw [Function.update_self]
      decide
    · rw [Function.update_of_ne h]
      decide
  have hfr₀ : x₀.regs WordRAM.Succinct.frontierReg = 100 := by
    dsimp only [x₀]
    exact Function.update_self WordRAM.Succinct.frontierReg 100 (fun _ => 0)
  have hmain := seq_expected_amortized
    (by decide) (by decide) (by decide) (by decide) hfit_succinct_example
    sampleDictOps hx₀ hfr₀ (fun _ _ => rfl) validHistory_sampleDictOps
  rcases hmain with ⟨ν₀, ν_final, T_ops, hinit, hsteps, _, hrep, hamort⟩
  exact ⟨ν₀, ν_final, T_ops, hinit, hsteps, hrep, hamort⟩

end ComplexityTests.WordRAMSuccinctDictionary
