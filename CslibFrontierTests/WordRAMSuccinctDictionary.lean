/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.Succinct

/-!
# Fixed-Capacity Succinct Dynamic Dictionary Tests

Exercises:
1. `Cslib.DataStructure.Dictionary.Dynamic`:
   - concrete evaluations of `optBits`, `logLogFactor`, and `succinctWords`, and verification of
     `ValidHistory` across insertions, overwrites, queries, and deletions;
2. `Cslib.DataStructure.Dictionary.FeistelQuotient`:
   - concrete evaluations of `bucketBits`, `numBuckets`, and `quotientBits`, round-trip
     verification of `feistelReconstruct_feistelBucket`, and verification of the
     `quotient_val_bits_le_optBits` bound;
3. `Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray`:
   - concrete evaluations of `packedWords`, evaluated cross-word read/write verification at index
     `5` of `12`-bit entries in `64`-bit words (`4` bits in word `100` and `8` bits in word `101`),
     and symbolic verification of `readPacked_writePacked_self` and `readPacked_writePacked_of_ne`;
4. `Cslib.DataStructure.Dictionary.SuccinctBucket` and
   `Cslib.DataStructure.Dictionary.WordRAM.Succinct`:
   - in the single-bucket regime (`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 16, 100)`):
     concrete evaluations of `slabSize`, `maxFullSlabs`, `maxTailItems`, `totalMicroBits`,
     `microBits`, `qBits`, `hashB`, `reducedTrinomialStep`, `hashSpace`, `space`, and `initSteps`,
     plus verification of `space_le_succinctWords`, `initSteps_le`, `initSteps_le_mul`,
     `initTime_impl_le`, `impl`, `implStandard`, and `seq_expected_amortized` on `sampleDictOps`;
   - in the multi-bucket regime (`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 2 ^ 16, 100)`,
     where `numBuckets (2 ^ 16) = 16`): concrete evaluations of `slabSize`, `maxFullSlabs`,
     `maxTailItems`, `reducedTrinomialStep`, `hashSpace`, and `space`, plus verification of
     `space_le_succinctWords`, `impl`, and `seq_expected_amortized` on `sampleDictOps`.
-/

@[expose] public section

namespace CslibFrontierTests.WordRAMSuccinctDictionary

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
    (Dynamic.spec (2 ^ 32) (2 ^ 16) 16).ValidHistory (Dictionary.empty (2 ^ 32)) sampleDictOps := by
  have hcard0 : (Dictionary.dom (Dictionary.empty (2 ^ 32))).card < 16 := by simp
  have hcard1 :
      (Dictionary.dom (Function.update (Dictionary.empty (2 ^ 32)) key3 (some 100))).card < 16 := by
    have hle := Dictionary.card_dom_insert_le (Dictionary.empty (2 ^ 32)) key3 100
    simp only [Dictionary.dom_empty, Finset.card_empty, zero_add] at hle
    exact lt_of_le_of_lt hle (by decide)
  have hisSome2 :
      (Function.update
        (Function.update (Dictionary.empty (2 ^ 32)) key3 (some 100))
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
  quotient_val_bits_le_optBits

/-! ## 3. Bit-Packed Array Primitive (`BitPackedArray`) -/

example : packedWords 16 12 64 = 5 := by decide

-- Index 5 of 12-bit entries in 64-bit words starts at bit 60
-- (4 bits in word 100, 8 bits in word 101):
example : writePacked 100 12 64 (fun _ => 0) 5 0xABC 100 = 0xC * 2 ^ 60 ∧
    writePacked 100 12 64 (fun _ => 0) 5 0xABC 101 = 0xAB ∧
    readPacked 100 12 64 (writePacked 100 12 64 (fun _ => 0) 5 0xABC) 4 = 0 ∧
    readPacked 100 12 64 (writePacked 100 12 64 (fun _ => 0) 5 0xABC) 5 = 0xABC ∧
    readPacked 100 12 64 (writePacked 100 12 64 (fun _ => 0) 5 0xABC) 6 = 0 := by decide

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
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
  impl (by decide) (by decide) (by decide) (by decide) hfit_succinct_example

/-- Standard-basis `Randomized.StateTransitionImpl` certificate for
`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 16, 100)`. -/
noncomputable abbrev sampleSuccinctImplStandard :
    Randomized.StateTransitionImpl (subroutineCode (2 ^ 32) (2 ^ 16) 64 16).toStandard
      (Dynamic.spec (2 ^ 32) (2 ^ 16) 16) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
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
      sampleSuccinctImpl.ExecStepsOfFn (Dictionary.empty (2 ^ 32)) sampleDictOps ν₀ ν_final T_ops ∧
      (∀ p ∈ ν_final.support,
        Rep (2 ^ 32) (2 ^ 16) 64 16 100 p.1
          ((Dynamic.spec (2 ^ 32) (2 ^ 16) 16).run (Dictionary.empty (2 ^ 32)) sampleDictOps).1
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

/-! ## 5. Multi-Bucket Regime (`n_max = 2 ^ 16 = 65536`, `numBuckets (2 ^ 16) = 16`) -/

theorem validHistory_sampleDictOps_multi :
    (Dynamic.spec (2 ^ 32) (2 ^ 16) (2 ^ 16)).ValidHistory
      (Dictionary.empty (2 ^ 32)) sampleDictOps := by
  have hcard0 : (Dictionary.dom (Dictionary.empty (2 ^ 32))).card < 2 ^ 16 := by simp
  have hcard1 :
      (Dictionary.dom (Function.update (Dictionary.empty (2 ^ 32)) key3 (some 100))).card <
        2 ^ 16 := by
    have hle := Dictionary.card_dom_insert_le (Dictionary.empty (2 ^ 32)) key3 100
    simp only [Dictionary.dom_empty, Finset.card_empty, zero_add] at hle
    exact lt_of_le_of_lt hle (by decide)
  have hisSome2 :
      (Function.update
        (Function.update (Dictionary.empty (2 ^ 32)) key3 (some 100))
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

theorem trinomialStep_28_17_16 :
    reducedTrinomialStep (qBits (2 ^ 32) (2 ^ 16)) (hashB (2 ^ 16)) (totalMicroBits (2 ^ 16)) =
      3 := by
  dsimp only [qBits, quotientBits, keyBits, bucketBits, hashB, totalMicroBits, microBits,
    Dynamic.logLogFactor, reducedTrinomialStep, reducedTargetBits]
  rw [trinomialStepAux, trinomialStepAux, trinomialStepAux, trinomialStepAux]
  decide

theorem hashSpace_32_64_65536 :
    hashSpace (2 ^ 32) 64 (2 ^ 16) = 164 := by
  dsimp only [hashSpace, ReducedKWise.space, ReducedKWise.seedWords, ReducedKWise.tableWords]
  rw [trinomialStep_28_17_16]
  decide

theorem succinct_space_32_16_64_65536 :
    space (2 ^ 32) (2 ^ 16) 64 (2 ^ 16) = 188394 := by
  dsimp only [space, totalSpace, offGM, offLM, offVal, offQuot, lmSubWords,
    globalMetaLen, globalPtrBits, effBucketPosBits, totalMicroBuckets]
  rw [hashSpace_32_64_65536]
  decide

theorem hfit_succinct_multi :
    Fits 64 (100 + space (2 ^ 32) (2 ^ 16) 64 (2 ^ 16)) := by
  dsimp only [Fits]
  rw [succinct_space_32_16_64_65536]
  decide

example :
    space (2 ^ 32) (2 ^ 16) 64 (2 ^ 16) ≤
      Dynamic.succinctWords 81 213 (2 ^ 32) (2 ^ 16) 64 (2 ^ 16) :=
  space_le_succinctWords (by decide) (by decide) (by decide)

/-- Exact-basis `Randomized.StateTransitionImpl` certificate in the multi-bucket regime
`(U, V, w, n_max, base) = (2 ^ 32, 2 ^ 16, 64, 2 ^ 16, 100)`. -/
noncomputable abbrev sampleSuccinctImplMulti :
    Randomized.StateTransitionImpl (subroutineCode (2 ^ 32) (2 ^ 16) 64 (2 ^ 16))
      (Dynamic.spec (2 ^ 32) (2 ^ 16) (2 ^ 16)) 64 100 Fin.elim0 (Dictionary.empty (2 ^ 32)) :=
  impl (by decide) (by decide) (by decide) (by decide) hfit_succinct_multi

/-- End-to-end execution of `seq_expected_amortized` in the multi-bucket regime
(`n_max = 2 ^ 16`, `numBuckets (2 ^ 16) = 16`). -/
theorem nonvacuous_seq_expected_amortized_multi :
    let x₀ : Data rSuccinct :=
      ⟨Function.update (fun _ => 0) WordRAM.Succinct.frontierReg 100, fun _ => 0⟩
    ∃ (ν₀ ν_final : PMF (sampleSuccinctImplMulti.Seed × Data rSuccinct))
      (T_ops : ℝ≥0∞),
      ExecCodeDist 64 (subroutineCode (2 ^ 32) (2 ^ 16) 64 (2 ^ 16)).initFresh x₀ (ν₀.map Prod.snd)
        sampleSuccinctImplMulti.initTime ∧
      sampleSuccinctImplMulti.ExecStepsOfFn (Dictionary.empty (2 ^ 32)) sampleDictOps
        ν₀ ν_final T_ops ∧
      (∀ p ∈ ν_final.support,
        Rep (2 ^ 32) (2 ^ 16) 64 (2 ^ 16) 100 p.1
          ((Dynamic.spec (2 ^ 32) (2 ^ 16) (2 ^ 16)).run
            (Dictionary.empty (2 ^ 32)) sampleDictOps).1
          p.2) ∧
      sampleSuccinctImplMulti.initTime + T_ops +
        (∑' q, ν_final q * (potential (2 ^ 32) (2 ^ 16) 64 (2 ^ 16) 100 q.1 q.2 : ℝ≥0∞)) ≤
        sampleSuccinctImplMulti.initTime +
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
    (by decide) (by decide) (by decide) (by decide) hfit_succinct_multi
    sampleDictOps hx₀ hfr₀ (fun _ _ => rfl) validHistory_sampleDictOps_multi
  rcases hmain with ⟨ν₀, ν_final, T_ops, hinit, hsteps, _, hrep, hamort⟩
  exact ⟨ν₀, ν_final, T_ops, hinit, hsteps, hrep, hamort⟩

end CslibFrontierTests.WordRAMSuccinctDictionary
