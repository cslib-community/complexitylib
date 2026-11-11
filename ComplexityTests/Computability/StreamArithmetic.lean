/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: local-only (tests of stream arithmetic and estimator recipes)

public import Complexity.Computability.StreamArithmetic.EstimatorRecipes
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Stream arithmetic, conditional query programs, and estimator recipes

Concrete evaluations and non-vacuous end-to-end semantic/resource checks across the signed-digit
stream representation, conditional query programs, primitive stream operations, smooth estimator
recipes, and two-coordinate row-compression recipes.
-/

@[expose] public section

namespace ComplexityTests.StreamArithmetic

open Cslib Cslib.SignedDigitStream Cslib.StreamArithmetic Finset

section ConcreteStreamChecks

/-- Explicit signed-digit stream `0 + 1 * 2⁻¹ = 1 / 2`. -/
def halfStream (j : ℕ) : ℤ := if j = 1 then 1 else 0

/-- Explicit alternating signed-digit stream with `1` at positive even places (`= 1 / 3`). -/
def evenOneStream (j : ℕ) : ℤ := if 0 < j ∧ j % 2 = 0 then 1 else 0

/-- Explicit signed-digit stream with redundant negative and positive digits (`-2` at `1`, `5` at
`3`). -/
def mixedSignedStream (j : ℕ) : ℤ := if j = 1 then -2 else if j = 3 then 5 else 0

/-- Explicit signed-digit stream `2⁻¹ + 2⁻³ = 3 / 8`. -/
def threeEighthsStream (j : ℕ) : ℤ := if j = 1 ∨ j = 3 then 1 else 0

/-- Explicit signed-digit stream `2⁻³ = 1 / 8`. -/
def oneEighthStream (j : ℕ) : ℤ := if j = 3 then 1 else 0

example : centeredResidue 4 15 = -1 := by decide

example : centeredResidue 4 6 = 6 := by decide

example : decodeDiffResidue 4 13 7 1 = -1 := by decide

example : ((-37 : ℤ) / (2 : ℤ) ^ 3) % (2 : ℤ) ^ 4 =
    ((-37 : ℤ) % (2 : ℤ) ^ 7) / (2 : ℤ) ^ 3 := by
  decide

example : List.ofFn (fun j : Fin 5 => ratStream (1 / 3) j.val) = [0, 0, 1, 0, 1] := by
  ext
  simp only [List.ofFn_succ, List.ofFn_zero, ratStream, ratApprox, diffDigit]
  norm_num

example : intPrefix (ratStream (1 / 3)) 5 = ratApprox (1 / 3) 5 :=
  intPrefix_diffDigit (ratApprox (1 / 3)) 5

example : intPrefix mixedSignedStream 7 % 16 =
    windowPrefix mixedSignedStream 4 7 % 16 := by
  decide

example : 0 < cmpPrefix halfStream evenOneStream 5 := by
  decide

example : cmpPrefix mixedSignedStream oneEighthStream 5 < 0 := by
  decide

example : mulResidue (ratStream (1 / 2)) (ratStream (1 / 2)) 4 4 ∈ Set.Icc (3 : ℤ) 5 := by
  have hr : |(1 / 2 : ℚ)| ≤ 1 := by norm_num
  have hsc := mulApprox_isScaledApprox (ratStream_isSignedStream hr) (ratStream_isSignedStream hr) 4
  rw [streamVal_ratStream hr] at hsc
  set m := mulApprox (ratStream (1 / 2)) (ratStream (1 / 2)) 4
  have habs : |(m : ℝ) - 4| < 2 := by
    convert hsc using 2
    norm_num
  obtain ⟨hlo, hhi⟩ := abs_lt.mp habs
  have hlo' : (2 : ℤ) < m := by
    have hlo_real : (2 : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast hlo_real
  have hhi' : m < (6 : ℤ) := by
    have hhi_real : (m : ℝ) < (6 : ℝ) := by linarith
    exact_mod_cast hhi_real
  rw [mulResidue_eq_mulApprox_emod]
  change 3 ≤ m % 16 ∧ m % 16 ≤ 5
  omega

example : bufferedTest 0 0 threeEighthsStream oneEighthStream = true := by
  have hs : IsSignedStream threeEighthsStream := fun j => by
    unfold threeEighthsStream IsSignedDigit; split_ifs <;> decide
  have hu : IsSignedStream oneEighthStream := fun j => by
    unfold oneEighthStream IsSignedDigit; split_ifs <;> decide
  unfold bufferedTest
  rw [decide_eq_true_eq, cmpBuffered_eq_clamp hs hu]
  simp [intPrefix, Finset.sum_range_succ, threeEighthsStream, oneEighthStream]

example : bufferedTest 0 0 oneEighthStream oneEighthStream = false := by
  have hu : IsSignedStream oneEighthStream := fun j => by
    unfold oneEighthStream IsSignedDigit; split_ifs <;> decide
  unfold bufferedTest
  rw [decide_eq_false_iff_not, cmpBuffered_eq_clamp hu hu]
  simp [intPrefix, oneEighthStream]

example : bufferedTest 2 3 (ratStream (3 / 8)) (ratStream (1 / 8)) = true := by
  have h38 : |(3 / 8 : ℚ)| ≤ 1 := by norm_num
  have h18 : |(1 / 8 : ℚ)| ≤ 1 := by norm_num
  exact bufferedTest_eq_true_of_two_mul_lt
    (ratStream_isSignedStream h38) (ratStream_isSignedStream h18)
    (sVal := 3 / 2) (uVal := 1 / 2) (ρ := 1 / 8)
    (by rw [streamVal_ratStream h38]; norm_num)
    (by rw [streamVal_ratStream h18]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

example : bufferedTest 2 3 (ratStream (1 / 8)) (ratStream (1 / 8)) = false := by
  have h18 : |(1 / 8 : ℚ)| ≤ 1 := by norm_num
  exact bufferedTest_eq_false_of_le
    (ratStream_isSignedStream h18) (ratStream_isSignedStream h18)
    (sVal := 1 / 2) (uVal := 1 / 2) (ρ := 1 / 8)
    (by rw [streamVal_ratStream h18]; norm_num)
    (by rw [streamVal_ratStream h18]; norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end ConcreteStreamChecks

section ConditionalQueryTreeChecks

/-- Conditional circuit selecting between operand `false` at place `2` and operand `true` at
place `9` based on a clock-zero structural bit. -/
def branchCircuit : CondBoolTree Bool Unit :=
  .condGate (.structLeaf ()) (.digitBit false 2 (0 < ·)) (.digitBit true 9 (0 < ·))

/-- Sample digit environment where `(false, 2)` is positive and `(true, 9)` is negative. -/
def sampleBoolEnv : Bool → ℕ → ℤ
  | false, j => if j = 2 then 3 else 0
  | true, j => if j = 9 then -4 else 0

example : (branchCircuit.toQueryProg 8).eval sampleBoolEnv (fun _ => true) = true := by
  decide

example : (branchCircuit.toQueryProg 8).eval sampleBoolEnv (fun _ => false) = false := by
  decide

/-- Predicate checking that a query event never touches operand `true` at place `9`. -/
def avoidsUnselectedBranch : QueryEvent Bool Unit → Bool
  | .digit op j _ => !(op && decide (j = 9))
  | .struct _ _ => true

/-- When the structural selector is `true`, the unselected `false` branch at `(true, 9)` is never
queried in `activeQueries`. -/
example :
    ((branchCircuit.toQueryProg 8).activeQueries sampleBoolEnv (fun _ => true)).all
      avoidsUnselectedBranch = true := by
  decide

example {ev : QueryEvent Bool Unit}
    (hev : ev ∈ (branchCircuit.toQueryProg 8).activeQueries sampleBoolEnv (fun _ => true)) :
    ev.retained ≤ 2 ∧
      (branchCircuit.toQueryProg 8).maxIntrinsicBits sampleBoolEnv (fun _ => true) ≤ 10 := by
  have hdepth : branchCircuit.depth = 1 := rfl
  refine ⟨?_, ?_⟩
  · simpa [hdepth] using
      CondBoolTree.toQueryProg_retainedBits_le 8 branchCircuit sampleBoolEnv (fun _ => true) hev
  · simpa [hdepth] using
      CondBoolTree.toQueryProg_intrinsic_le 8 branchCircuit sampleBoolEnv (fun _ => true)

end ConditionalQueryTreeChecks

section CertifiedPrimitiveChecks

theorem isNormSignedStream_ratStream {q : ℚ} (hq : |q| ≤ 1) :
    IsNormSignedStream (ratStream q) := by
  refine ⟨ratStream_isSignedStream hq, ?_⟩
  rw [streamVal_ratStream hq]
  exact_mod_cast hq

/-- Two-operand rational environment `(1 / 2, -1 / 4)`. -/
def pairRatEnv : Fin 2 → ℕ → ℤ
  | 0 => ratStream (1 / 2)
  | 1 => ratStream (-1 / 4)

theorem pairRatEnv_norm (i : Fin 2) : IsNormSignedStream (pairRatEnv i) := by
  fin_cases i
  · exact isNormSignedStream_ratStream (by norm_num)
  · exact isNormSignedStream_ratStream (by norm_num)

theorem streamVal_pairRatEnv_zero : streamVal (pairRatEnv 0) = 1 / 2 := by
  simpa [pairRatEnv] using streamVal_ratStream (r := 1 / 2) (by norm_num)

theorem streamVal_pairRatEnv_one : streamVal (pairRatEnv 1) = -1 / 4 := by
  simpa [pairRatEnv] using streamVal_ratStream (r := -1 / 4) (by norm_num)

/-- End-to-end check for `varRecipe`, `ratRecipe`, `.neg`, `.abs`, `.pairAvg`, `.max`, `.min`,
`.shiftClip`, `.mul`, and `.recip64` at slack `d = 2`. -/
example :
    let v0 := varRecipe (Struct := Unit) 2 (by decide) (0 : Fin 2)
    let v1 := varRecipe (Struct := Unit) 2 (by decide) (1 : Fin 2)
    let cQuarter := ratRecipe (Op := Fin 2) (Struct := Unit) 2 (by decide) (1 / 4) (by norm_num)
    let sEnv : Unit → Bool := fun _ => false
    let rAbs := v1.abs
    let rAvg := v0.pairAvg v1.neg rfl
    let rMax := v0.max v1 rfl
    let rMin := v0.min cQuarter rfl
    let rClip := v0.shiftClip 2 1 (by decide)
    let rMul := v0.mul v1 rfl
    let rRecip := v0.recip64
    streamVal (fun t => (rAbs.digitProg t).eval pairRatEnv sEnv) = 1 / 4 ∧
      streamVal (fun t => (rAvg.digitProg t).eval pairRatEnv sEnv) = 3 / 8 ∧
      streamVal (fun t => (rMax.digitProg t).eval pairRatEnv sEnv) = 1 / 2 ∧
      streamVal (fun t => (rMin.digitProg t).eval pairRatEnv sEnv) = 1 / 4 ∧
      streamVal (fun t => (rClip.digitProg t).eval pairRatEnv sEnv) = 1 ∧
      streamVal (fun t => (rMul.digitProg t).eval pairRatEnv sEnv) = -1 / 8 ∧
      streamVal (fun t => (rRecip.digitProg t).eval pairRatEnv sEnv) = 1 / 32 ∧
      IsSignedStream (fun t => (rRecip.digitProg t).eval pairRatEnv sEnv) ∧
      (rRecip.digitProg 3).maxIntrinsicBits pairRatEnv sEnv ≤ rRecip.intrinsicCoeff * 5 := by
  intro v0 v1 cQuarter sEnv rAbs rAvg rMax rMin rClip rMul rRecip
  have hv0 : v0.ValidEnv pairRatEnv sEnv := pairRatEnv_norm 0
  have hv1 : v1.ValidEnv pairRatEnv sEnv := pairRatEnv_norm 1
  have hcQ : cQuarter.ValidEnv pairRatEnv sEnv := trivial
  have hRecipV : rRecip.ValidEnv pairRatEnv sEnv := by
    refine ⟨hv0, ?_⟩
    change streamVal (pairRatEnv 0) ∈ Set.Icc (1 / 4 : ℝ) 1
    rw [streamVal_pairRatEnv_zero]
    exact ⟨by norm_num, by norm_num⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, rRecip.emits_signed hRecipV, rRecip.intrinsic_bound 3 _ _⟩
  · rw [rAbs.emits_exact hv1]
    change |streamVal (pairRatEnv 1)| = 1 / 4
    rw [streamVal_pairRatEnv_one]
    norm_num
  · rw [rAvg.emits_exact ⟨hv0, hv1⟩]
    change (streamVal (pairRatEnv 0) + -streamVal (pairRatEnv 1)) / 2 = 3 / 8
    rw [streamVal_pairRatEnv_zero, streamVal_pairRatEnv_one]
    norm_num
  · rw [rMax.emits_exact ⟨hv0, hv1⟩]
    change max (streamVal (pairRatEnv 0)) (streamVal (pairRatEnv 1)) = 1 / 2
    rw [streamVal_pairRatEnv_zero, streamVal_pairRatEnv_one]
    norm_num
  · rw [rMin.emits_exact ⟨hv0, hcQ⟩]
    change min (streamVal (pairRatEnv 0)) ((1 / 4 : ℚ) : ℝ) = 1 / 4
    rw [streamVal_pairRatEnv_zero]
    push_cast
    norm_num
  · rw [rClip.emits_exact hv0]
    change shiftClipVal 2 (streamVal (pairRatEnv 0)) = 1
    rw [streamVal_pairRatEnv_zero]
    unfold shiftClipVal
    norm_num
  · rw [rMul.emits_exact ⟨hv0, hv1⟩]
    change streamVal (pairRatEnv 0) * streamVal (pairRatEnv 1) = -1 / 8
    rw [streamVal_pairRatEnv_zero, streamVal_pairRatEnv_one]
    norm_num
  · rw [rRecip.emits_exact hRecipV]
    change 1 / (64 * streamVal (pairRatEnv 0)) = 1 / 32
    rw [streamVal_pairRatEnv_zero]
    norm_num

/-- Four-operand rational environment `(1 / 2, -1 / 4, 1 / 4, 3 / 4)` for `balancedAvgRecipe` and
`zeroPaddedRankFinsetRecipe`. -/
def quadRat : Fin 4 → ℚ
  | 0 => 1 / 2
  | 1 => -1 / 4
  | 2 => 1 / 4
  | 3 => 3 / 4

def quadRatEnv (i : Fin 4) : ℕ → ℤ := ratStream (quadRat i)

theorem quadRatEnv_norm (i : Fin 4) : IsNormSignedStream (quadRatEnv i) := by
  fin_cases i <;> exact isNormSignedStream_ratStream (by unfold quadRat; norm_num)

theorem streamVal_quadRatEnv (i : Fin 4) : streamVal (quadRatEnv i) = (quadRat i : ℝ) := by
  fin_cases i <;> exact streamVal_ratStream (by unfold quadRat; norm_num)

/-- End-to-end check for `balancedAvgRecipe` over `2 ^ 2 = 4` streams, producing exact average
`5 / 16`. -/
example :
    let children : Fin (2 ^ 2) → UniformStreamRecipe (Fin 4) Unit :=
      fun i => varRecipe 2 (by decide) i
    let avgR := balancedAvgRecipe 2 (by decide) 2 1 (by decide) children 4 0 0 4
      (fun _ => rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)
    streamVal (fun t => (avgR.digitProg t).eval quadRatEnv (fun _ => false)) = 5 / 16 := by
  intro children avgR
  have hV : avgR.ValidEnv quadRatEnv (fun _ => false) := fun i => quadRatEnv_norm i
  rw [avgR.emits_exact hV]
  change (∑ i : Fin 4, streamVal (quadRatEnv i)) / (2 : ℝ) ^ 2 = 5 / 16
  rw [Fin.sum_univ_four]
  simp only [streamVal_quadRatEnv, quadRat]
  push_cast
  norm_num

/-- End-to-end check for `zeroPaddedRankFinsetRecipe` computing the 2nd largest value of
`{1 / 2, -1 / 4, 1 / 4, 3 / 4}`, which equals `1 / 2`. -/
example :
    let rankR := zeroPaddedRankFinsetRecipe (Op := Fin 4) (Struct := Unit) 2 (by decide) 2 univ 1
      (by decide)
    streamVal (fun t => (rankR.digitProg t).eval quadRatEnv (fun _ => false)) = 1 / 2 := by
  intro rankR
  have hV : rankR.ValidEnv quadRatEnv (fun _ => false) := fun i _ => quadRatEnv_norm i
  rw [rankR.emits_exact hV]
  change kthLargest 2 (univ : Finset (Fin 4)) (fun i => streamVal (quadRatEnv i)) = 1 / 2
  have hcongr : kthLargest 2 (univ : Finset (Fin 4)) (fun i => streamVal (quadRatEnv i)) =
      kthLargest 2 (univ : Finset (Fin 4)) (fun i => (quadRat i : ℝ)) :=
    kthLargest_congr fun i _ => streamVal_quadRatEnv i
  rw [hcongr]
  apply le_antisymm
  · rw [← not_lt]
    intro hlt
    have hcard := (lt_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hlt
    have hsub : ({i ∈ (univ : Finset (Fin 4)) | (1 / 2 : ℝ) < (quadRat i : ℝ)} : Finset (Fin 4)) ⊆
        {3} := by
      intro i hi
      have hgt : (1 / 2 : ℝ) < (quadRat i : ℝ) := (mem_filter.mp hi).2
      fin_cases i <;> dsimp only at hgt ⊢ <;> simp only [quadRat] at hgt <;> try norm_num at hgt
      simp
    have hle1 := (card_le_card hsub).trans_eq (card_singleton (3 : Fin 4))
    omega
  · rw [le_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) < 1 / 2)]
    have hsub : ({0, 3} : Finset (Fin 4)) ⊆
        {i ∈ (univ : Finset (Fin 4)) | (1 / 2 : ℝ) ≤ (quadRat i : ℝ)} := by
      intro i hi
      rw [mem_filter]
      refine ⟨mem_univ i, ?_⟩
      rcases mem_insert.mp hi with rfl | hi
      · simp [quadRat]
      · rw [mem_singleton.mp hi]
        simp only [quadRat]
        norm_num
    exact (by decide : 2 ≤ #({0, 3} : Finset (Fin 4))).trans (card_le_card hsub)

/-- Regression check for zero-padded detector-rank clamping: when all candidates are negative
(`{-1 / 2, -3 / 4}` at `k = 1 ≤ 2`), both `zeroPaddedRankListRecipe` and
`zeroPaddedRankFinsetRecipe` clamp the selected value up to `0` (`Finset.kthLargest`) rather than
returning `-1 / 2`. -/
example :
    let negEnv : Fin 2 → ℕ → ℤ := fun i =>
      if i = 0 then ratStream (-1 / 2) else ratStream (-3 / 4)
    let sEnv : Unit → Bool := fun _ => false
    let listR := zeroPaddedRankListRecipe (Op := Fin 2) (Struct := Unit) 2 (by decide) 1 [0, 1]
      (by decide) 1 (by decide)
    let finsetR := zeroPaddedRankFinsetRecipe (Op := Fin 2) (Struct := Unit) 2 (by decide) 1 univ
      1 (by decide)
    streamVal (fun t => (listR.digitProg t).eval negEnv sEnv) = 0 ∧
      streamVal (fun t => (finsetR.digitProg t).eval negEnv sEnv) = 0 := by
  intro negEnv sEnv listR finsetR
  have hNorm : ∀ i : Fin 2, IsNormSignedStream (negEnv i) := fun i => by
    fin_cases i
    · exact isNormSignedStream_ratStream (by norm_num)
    · exact isNormSignedStream_ratStream (by norm_num)
  have hValLe : ∀ i : Fin 2, streamVal (negEnv i) ≤ 0 := fun i => by
    fin_cases i
    · change streamVal (ratStream (-1 / 2)) ≤ 0
      rw [streamVal_ratStream (by norm_num)]
      norm_num
    · change streamVal (ratStream (-3 / 4)) ≤ 0
      rw [streamVal_ratStream (by norm_num)]
      norm_num
  refine ⟨?_, ?_⟩
  · rw [listR.emits_exact (fun i _ => hNorm i)]
    exact le_antisymm (kthLargest_le le_rfl fun i _ => hValLe i) kthLargest_nonneg
  · rw [finsetR.emits_exact (fun i _ => hNorm i)]
    exact le_antisymm (kthLargest_le le_rfl fun i _ => hValLe i) kthLargest_nonneg

/-- End-to-end check for `bufferedTestRecipe` completeness (`sVal > 2 * uVal`) and soundness
(`sVal ≤ uVal`) with `AllowanceBound` verification. -/
example :
    let bEnv : Fin 2 → ℕ → ℤ := fun i => if i = 0 then ratStream (3 / 8) else ratStream (1 / 8)
    let sEnv : Unit → Bool := fun _ => false
    let testAcc := bufferedTestRecipe (Op := Fin 2) (Struct := Unit) 3 (by decide) 0 1 2 3 2
      (by decide)
    let testRej := bufferedTestRecipe (Op := Fin 2) (Struct := Unit) 3 (by decide) 1 1 2 3 2
      (by decide)
    testAcc.prog.eval bEnv sEnv = true ∧
      testRej.prog.eval bEnv sEnv = false ∧
      testAcc.prog.maxIntrinsicBits bEnv sEnv ≤ testAcc.intrinsicCoeff * testAcc.slack := by
  intro bEnv sEnv testAcc testRej
  have hs0 : IsSignedStream (bEnv 0) := ratStream_isSignedStream (by norm_num)
  have hs1 : IsSignedStream (bEnv 1) := ratStream_isSignedStream (by norm_num)
  have hv0 : (3 / 2 : ℝ) = (2 : ℝ) ^ 2 * streamVal (bEnv 0) := by
    change (3 / 2 : ℝ) = (2 : ℝ) ^ 2 * streamVal (ratStream (3 / 8))
    rw [streamVal_ratStream (by norm_num)]
    norm_num
  have hv1 : (1 / 2 : ℝ) = (2 : ℝ) ^ 2 * streamVal (bEnv 1) := by
    change (1 / 2 : ℝ) = (2 : ℝ) ^ 2 * streamVal (ratStream (1 / 8))
    rw [streamVal_ratStream (by norm_num)]
    norm_num
  refine ⟨?_, ?_, testAcc.intrinsic_bound bEnv sEnv⟩
  · exact bufferedTestRecipe_true_of_two_mul_lt 3 (by decide) 0 1 (by decide) sEnv hs0 hs1
      hv0 hv1 (ρ := 1 / 8) (by norm_num) (by norm_num) (by norm_num)
  · exact bufferedTestRecipe_false_of_le 3 (by decide) 1 1 (by decide) sEnv hs1 hs1
      hv1 hv1 (ρ := 1 / 8) (by norm_num) (by norm_num) le_rfl

/-- Check structural short-circuiting of `UniformStreamRecipe.guardStruct` on an invalid operand
environment when the structural flag is `false`, plus clamped prefix accuracy via
`clippedUnitPrefixProg`. -/
example :
    let guarded := (varRecipe (Op := Unit) (Struct := Unit) 1 le_rfl ()).guardStruct ()
    let badEnv : Unit → ℕ → ℤ := fun _ _ => 99
    let goodEnv : Unit → ℕ → ℤ := fun _ => ratStream (3 / 4)
    streamVal (fun t => (guarded.digitProg t).eval badEnv (fun _ => false)) = 0 ∧
      streamVal (fun t => (guarded.digitProg t).eval goodEnv (fun _ => true)) = 3 / 4 ∧
      (clippedUnitPrefixProg (Op := Unit) (Struct := Unit) () 4).eval goodEnv (fun _ => false) ≤
        16 := by
  intro guarded badEnv goodEnv
  refine ⟨?_, ?_, ?_⟩
  · rw [guarded.emits_exact (fun h => Bool.noConfusion h)]
    rfl
  · have hgood : IsNormSignedStream (goodEnv ()) :=
      ⟨ratStream_isSignedStream (by norm_num), by rw [streamVal_ratStream (by norm_num)]; norm_num⟩
    rw [guarded.emits_exact (fun _ => hgood)]
    change streamVal (ratStream (3 / 4)) = 3 / 4
    rw [streamVal_ratStream (by norm_num)]
    norm_num
  · rw [eval_clippedUnitPrefixProg]
    exact clipUnitPrefix_le_two_pow 4 _

end CertifiedPrimitiveChecks

section EstimatorAndRowCompressionChecks

/-- End-to-end exact evaluation of `clippedAtomInvRecipe`, `polynomialTransition4Recipe`,
`dyadicSwitchNormRecipe`, `dyadicWeightNormRecipe`, `invOneAddScaledRecipe`, and
`rationalRamp4NormRecipe` on concrete rational inputs. -/
example :
    let sEnv : Unit → Bool := fun _ => false
    let rThreeQuarters :=
      ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (3 / 4) (by norm_num)
    let rQuarter := ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (1 / 4) (by norm_num)
    let rHalf := ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (1 / 2) (by norm_num)
    let rThreeSixteenths :=
      ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (3 / 16) (by norm_num)
    let atom34 := clippedAtomInvRecipe rThreeQuarters
    let atom14 := clippedAtomInvRecipe rQuarter
    let polyHalf := polynomialTransition4Recipe rHalf
    let dySw := dyadicSwitchNormRecipe 2 1 rThreeSixteenths (by decide) 0 (by decide)
    let dyWt := dyadicWeightNormRecipe 2 1 rThreeSixteenths (by decide) 0
    let invOne := invOneAddScaledRecipe 2 1 rQuarter (by decide)
    let ramp := rationalRamp4NormRecipe 2 1 rQuarter (by decide)
    let uEnv : Unit → ℕ → ℤ := fun _ _ => 0
    streamVal (fun t => (atom34.digitProg t).eval uEnv sEnv) = 2 / 3 ∧
      streamVal (fun t => (atom14.digitProg t).eval uEnv sEnv) = 1 ∧
      streamVal (fun t => (polyHalf.digitProg t).eval uEnv sEnv) = 1 / 2 ∧
      streamVal (fun t => (dySw.digitProg t).eval uEnv sEnv) = 1 / 2 ∧
      streamVal (fun t => (dyWt.digitProg t).eval uEnv sEnv) = 1 / 2 ∧
      streamVal (fun t => (invOne.digitProg t).eval uEnv sEnv) = 1 / 2 ∧
      streamVal (fun t => (ramp.digitProg t).eval uEnv sEnv) = 1 / 32 := by
  intro sEnv rThreeQuarters rQuarter rHalf rThreeSixteenths atom34 atom14 polyHalf dySw dyWt invOne
    ramp uEnv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [atom34.emits_exact trivial]
    change 1 / (2 * max (1 / 2 : ℝ) (min 1 ((3 / 4 : ℚ) : ℝ))) = 2 / 3
    push_cast
    norm_num
  · rw [atom14.emits_exact trivial]
    change 1 / (2 * max (1 / 2 : ℝ) (min 1 ((1 / 4 : ℚ) : ℝ))) = 1
    push_cast
    norm_num
  · rw [polyHalf.emits_exact trivial]
    change polynomialTransition4 ((1 / 2 : ℚ) : ℝ) = 1 / 2
    unfold polynomialTransition4 transitionPolynomial4
    push_cast
    norm_num
  · rw [dySw.emits_exact trivial]
    change dyadicSwitch 0 ((2 : ℝ) ^ 3 * max 0 ((3 / 16 : ℚ) : ℝ)) = 1 / 2
    unfold dyadicSwitch polynomialSwitch4 polynomialTransition4 transitionPolynomial4
    push_cast
    norm_num
  · rw [dyWt.emits_exact trivial]
    change dyadicWeight 2 0 ((2 : ℝ) ^ 3 * max 0 ((3 / 16 : ℚ) : ℝ)) = 1 / 2
    unfold dyadicWeight dyadicSwitch polynomialSwitch4 polynomialTransition4 transitionPolynomial4
    push_cast
    norm_num
  · rw [invOne.emits_exact trivial]
    change 1 / (1 + max 0 ((2 : ℝ) ^ 2 * ((1 / 4 : ℚ) : ℝ))) = 1 / 2
    push_cast
    norm_num
  · rw [ramp.emits_exact trivial]
    change rationalRamp4Unit ((2 : ℝ) ^ 2 * ((1 / 4 : ℚ) : ℝ)) / (2 : ℝ) ^ 2 = 1 / 32
    push_cast
    have hmul : (2 : ℝ) ^ 2 * (1 / 4 : ℝ) = 1 := by norm_num
    rw [hmul, rationalRamp4Unit_eq_poly_add_inv]
    norm_num

/-- Rational two-coordinate row on `Fin 2`:
* coordinate `0` has large entry `(3 / 4, -1 / 4)` (`entrySize = 3 / 4 ≥ 3 * (1 / 8)`),
* coordinate `1` has small entry `(1 / 8, 1 / 16)` (`entrySize = 1 / 8 ≤ 2 * (1 / 8)`). -/
def rowRatVal : Fin 2 → Fin 2 → ℚ
  | 0, 0 => 3 / 4
  | 0, 1 => -1 / 4
  | 1, 0 => 1 / 8
  | 1, 1 => 1 / 16

theorem rowThreshold_eq :
    RowCompression.threshold ({0, 1} : Finset (Fin 2)) 2 (1 / 8) (1 / 8)
      (fun x μ => (rowRatVal x μ : ℝ)) = 1 / 8 := by
  unfold RowCompression.threshold
  have hkth : kthLargest 2 ({0, 1} : Finset (Fin 2))
      (fun x => RowCompression.entrySize (fun μ => (rowRatVal x μ : ℝ))) = 1 / 8 := by
    apply le_antisymm
    · rw [← not_lt]
      intro hlt
      have hcard := (lt_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp hlt
      have hsub : ({x ∈ ({0, 1} : Finset (Fin 2)) |
          (1 / 8 : ℝ) < RowCompression.entrySize (fun μ => (rowRatVal x μ : ℝ))} :
            Finset (Fin 2)) ⊆ {0} := by
        intro x hx
        have hgt := (mem_filter.mp hx).2
        fin_cases x <;> dsimp only at hgt ⊢
        · simp
        · unfold RowCompression.entrySize rowRatVal at hgt
          push_cast at hgt
          norm_num at hgt
      have hle1 := (card_le_card hsub).trans_eq (card_singleton (0 : Fin 2))
      omega
    · rw [le_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) < 1 / 8)]
      have hsub : ({0, 1} : Finset (Fin 2)) ⊆
          {x ∈ ({0, 1} : Finset (Fin 2)) |
            (1 / 8 : ℝ) ≤ RowCompression.entrySize (fun μ => (rowRatVal x μ : ℝ))} := by
        intro x hx
        rw [mem_filter]
        refine ⟨hx, ?_⟩
        fin_cases x <;> dsimp only <;> unfold RowCompression.entrySize rowRatVal <;>
          push_cast <;> norm_num
      exact (by decide : 2 ≤ #({0, 1} : Finset (Fin 2))).trans (card_le_card hsub)
  rw [hkth]
  norm_num

theorem rowNewDefault_eq :
    RowCompression.newDefault ({0, 1} : Finset (Fin 2)) 2 2 (1 / 8) (1 / 8)
      (fun x μ => (rowRatVal x μ : ℝ)) = 1 / 8 := by
  unfold RowCompression.newDefault
  rw [rowThreshold_eq]
  have hkth : kthLargest 2 ({0, 1} : Finset (Fin 2)) (fun x => (rowRatVal x 0 : ℝ)) = 1 / 8 := by
    apply le_antisymm
    · rw [← not_lt]
      intro hlt
      have hcard := (lt_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) ≤ 1 / 8)).mp hlt
      have hsub : ({x ∈ ({0, 1} : Finset (Fin 2)) | (1 / 8 : ℝ) < (rowRatVal x 0 : ℝ)} :
          Finset (Fin 2)) ⊆ {0} := by
        intro x hx
        have hgt := (mem_filter.mp hx).2
        fin_cases x <;> dsimp only at hgt ⊢
        · simp
        · simp only [rowRatVal] at hgt
          norm_num at hgt
      have hle1 := (card_le_card hsub).trans_eq (card_singleton (0 : Fin 2))
      omega
    · rw [le_kthLargest_iff (by decide : 0 < 2) (by norm_num : (0 : ℝ) < 1 / 8)]
      have hsub : ({0, 1} : Finset (Fin 2)) ⊆
          {x ∈ ({0, 1} : Finset (Fin 2)) | (1 / 8 : ℝ) ≤ (rowRatVal x 0 : ℝ)} := by
        intro x hx
        rw [mem_filter]
        refine ⟨hx, ?_⟩
        fin_cases x <;> dsimp only <;> simp only [rowRatVal] <;> norm_num
      exact (by decide : 2 ≤ #({0, 1} : Finset (Fin 2))).trans (card_le_card hsub)
  rw [hkth]
  norm_num

/-- End-to-end check for `rowCompressionNewDefaultRecipe` and `rowCompressionUpdateRecipe`:
* `newDefault` evaluates to `1 / 8`,
* large entry `(0, 1)` (`-1 / 4`) is preserved unchanged (`= -1 / 4`),
* small entry `(1, 1)` (`1 / 16`) is compressed to the default second coordinate `0`. -/
example :
    let uEnv : Unit → ℕ → ℤ := fun _ _ => 0
    let sEnv : Unit → Bool := fun _ => false
    let floorR := ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (1 / 8) (by norm_num)
    let defR := ratRecipe (Op := Unit) (Struct := Unit) 2 (by decide) (1 / 8) (by norm_num)
    let entryR : Fin 2 → Fin 2 → UniformStreamRecipe Unit Unit := fun x μ =>
      ratRecipe 2 (by decide) (rowRatVal x μ) (by fin_cases x <;> fin_cases μ <;>
        (unfold rowRatVal; norm_num))
    let items : List (Fin 2) := [0, 1]
    let hNodup : items.Nodup := by decide
    let newDefR := rowCompressionNewDefaultRecipe 2 (by decide) items hNodup 1 (by decide) 2 2
      floorR defR entryR 0 0 0 8 rfl rfl (fun _ _ _ => rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
    let updLargeR := rowCompressionUpdateRecipe 2 (by decide) items hNodup 1 (by decide) 2 2 0 1
      floorR defR entryR 0 0 0 8 rfl rfl (fun _ _ _ => rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
    let updSmallR := rowCompressionUpdateRecipe 2 (by decide) items hNodup 1 (by decide) 2 2 1 1
      floorR defR entryR 0 0 0 8 rfl rfl (fun _ _ _ => rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
      le_rfl le_rfl (fun _ _ _ => le_rfl)
    streamVal (fun t => (newDefR.digitProg t).eval uEnv sEnv) = 1 / 8 ∧
      streamVal (fun t => (updLargeR.digitProg t).eval uEnv sEnv) = -1 / 4 ∧
      streamVal (fun t => (updSmallR.digitProg t).eval uEnv sEnv) = 0 := by
  intro uEnv sEnv floorR defR entryR items hNodup newDefR updLargeR updSmallR
  have hItems : items.toFinset = ({0, 1} : Finset (Fin 2)) := by decide
  have hVDef : newDefR.ValidEnv uEnv sEnv := ⟨trivial, trivial, fun _ _ _ => trivial⟩
  have hVLarge : updLargeR.ValidEnv uEnv sEnv :=
    ⟨trivial, trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  have hVSmall : updSmallR.ValidEnv uEnv sEnv :=
    ⟨trivial, trivial, fun _ => trivial, fun _ _ _ => trivial⟩
  set wReal : Fin 2 → Fin 2 → ℝ := fun x μ => (rowRatVal x μ : ℝ)
  refine ⟨?_, ?_, ?_⟩
  · rw [newDefR.emits_exact hVDef]
    change RowCompression.newDefault items.toFinset 2 2
      ((1 / 8 : ℚ) : ℝ) ((1 / 8 : ℚ) : ℝ) wReal = 1 / 8
    rw [hItems]
    push_cast
    exact rowNewDefault_eq
  · rw [updLargeR.emits_exact hVLarge]
    change RowCompression.update items.toFinset 2 2
      ((1 / 8 : ℚ) : ℝ) ((1 / 8 : ℚ) : ℝ) wReal 0 1 = -1 / 4
    rw [hItems]
    have hval18 : ((1 / 8 : ℚ) : ℝ) = 1 / 8 := by norm_num
    rw [hval18]
    have hlarge : 3 * RowCompression.threshold ({0, 1} : Finset (Fin 2)) 2 (1 / 8) (1 / 8) wReal ≤
        RowCompression.entrySize (wReal 0) := by
      rw [rowThreshold_eq]
      unfold RowCompression.entrySize wReal rowRatVal
      push_cast
      norm_num
    have hpres := congrFun
      (RowCompression.update_eq_self_of_three_mul_le (w := wReal) (y := 0) (K := 2) hlarge) 1
    rw [hpres]
    simp only [wReal, rowRatVal]
    norm_num
  · rw [updSmallR.emits_exact hVSmall]
    change RowCompression.update items.toFinset 2 2
      ((1 / 8 : ℚ) : ℝ) ((1 / 8 : ℚ) : ℝ) wReal 1 1 = 0
    rw [hItems]
    have hval18 : ((1 / 8 : ℚ) : ℝ) = 1 / 8 := by norm_num
    rw [hval18]
    have hsmall : RowCompression.entrySize (wReal 1) ≤
        2 * RowCompression.threshold ({0, 1} : Finset (Fin 2)) 2 (1 / 8) (1 / 8) wReal := by
      rw [rowThreshold_eq]
      unfold RowCompression.entrySize wReal rowRatVal
      push_cast
      norm_num
    have hdef := congrFun
      (RowCompression.update_eq_default_of_size_le (w := wReal) (y := 1) (K := 2) hsmall) 1
    rw [hdef]
    simp [RowCompression.defaultEntry]

end EstimatorAndRowCompressionChecks

end ComplexityTests.StreamArithmetic
