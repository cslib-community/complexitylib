/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
import CslibFrontier.Crypto.Primitives.BlockCipher.CBCMAC

/-!
# Tests for CBC-MAC Concrete Bounds and Forgery Separations

Concrete evaluations, non-vacuity witnesses, and axiom checks for
`CslibFrontier.Crypto.Primitives.BlockCipher.CBCMAC`.
-/
namespace Cslib.Crypto.CBCMACTests
open Cslib.Crypto
/-- Concrete 4-bit block permutation `x ↦ x + 1^4`. -/
def testPerm : BitString 4 → BitString 4 := fun x => x + (1 : BitString 4)
/-- Concrete 4-bit zero block. -/
def b0 : BitString 4 := 0
/-- Concrete 4-bit all-ones block. -/
def b1 : BitString 4 := (1 : BitString 4)
/-- The final block of `cbcEncryptBlocks` equals `cbcMacBlocks` on `[b0, b1, b0]`. -/
example : (cbcEncryptBlocks testPerm b0 [b0, b1, b0]).getLast (by simp) =
      cbcMacBlocks testPerm b0 [b0, b1, b0] :=
  getLast_cbcEncryptBlocks_eq_cbcMacBlocks testPerm b0 b0 [b1, b0]
/-- Chaining append identity on concrete 4-bit blocks. -/
example : cbcMacBlocks testPerm b0 ([b0, b1] ++ [b1, b0]) =
      cbcMacBlocks testPerm (cbcMacBlocks testPerm b0 [b0, b1]) [b1, b0] :=
  cbcMacBlocks_append testPerm b0 [b0, b1] [b1, b0]
/-- Concrete 1-block `CBCInput 8 2` representing `[0]`. -/
def inputZero8 : CBCInput 8 2 := ⟨⟨0, by decide⟩, fun _ => 0⟩
/-- Concrete 1-block `CBCInput 8 2` representing `[(1 : BitString 8)]`. -/
def inputOne8 : CBCInput 8 2 := ⟨⟨0, by decide⟩, fun _ => (1 : BitString 8)⟩
/-- Concrete 2-block `CBCInput 8 2` representing `[(1 : BitString 8), 0]`. -/
def inputTwo8 : CBCInput 8 2 := ⟨⟨1, by decide⟩, ![(1 : BitString 8), 0]⟩
/-- Non-vacuous instantiation of prefix-free CBC-MAC smoothness at `n = 8, q = 2, ℓ = 2`, where
  `δ = 16 / 256 = 1 / 16 < 1` so the lower-bound factor `1 - δ = 15 / 16` is strictly positive. -/
example : CBCSmooth 8 2 2 ((2 : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (2 : ℝ) ^ 8) ∧
      (0 : ℝ) < 1 - (2 : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (2 : ℝ) ^ 8 :=
  ⟨cbcSmooth_of_prefixFree 8 2 2, by norm_num⟩
/-- Adaptive 2-query oracle program querying `inputZero8`, then adaptively querying either
  `inputOne8` (when the first tag is `0`) or `inputTwo8` (otherwise). -/
def twoQueryAdaptiveTree : OracleComp (CBCOracleSpec 8 2) Bool := do
  let tag1 ← OracleComp.query inputZero8
  if tag1 = 0 then
    let tag2 ← OracleComp.query inputOne8
    return decide (tag2 = 0)
  else
    let tag2 ← OracleComp.query inputTwo8
    return decide (tag2 = 0)
private theorem head_cbcInputBlocks_zero_ne_one :
    (cbcInputBlocks inputZero8).head? ≠ (cbcInputBlocks inputOne8).head? := by
  intro h
  have hval : (0 : BitString 8) ⟨0, by decide⟩ = (1 : BitString 8) ⟨0, by decide⟩ := by
    have h0 : (cbcInputBlocks inputZero8).head? = some 0 := rfl
    have h1 : (cbcInputBlocks inputOne8).head? = some ((1 : BitString 8)) := rfl
    rw [h0, h1, Option.some.injEq] at h
    exact congrFun h ⟨0, by decide⟩
  exact Bool.false_ne_true hval
private theorem head_cbcInputBlocks_zero_ne_two :
    (cbcInputBlocks inputZero8).head? ≠ (cbcInputBlocks inputTwo8).head? := by
  intro h
  have hval : (0 : BitString 8) ⟨0, by decide⟩ = (1 : BitString 8) ⟨0, by decide⟩ := by
    have h0 : (cbcInputBlocks inputZero8).head? = some 0 := rfl
    have h2 : (cbcInputBlocks inputTwo8).head? = some ((1 : BitString 8)) := rfl
    rw [h0, h2, Option.some.injEq] at h
    exact congrFun h ⟨0, by decide⟩
  exact Bool.false_ne_true hval
private theorem not_isPrefix_of_head_ne {α : Type*} {l₁ l₂ : List α}
    (h1 : l₁ ≠ []) (h : l₁.head? ≠ l₂.head?) : ¬ l₁ <+: l₂ := by
  rcases l₁ with _ | ⟨a, tl₁⟩
  · exact absurd rfl h1
  rintro ⟨t, ht⟩
  rw [← ht] at h
  exact h rfl
/-- `twoQueryAdaptiveTree` is `2`-admissible along every oracle branch. -/
theorem twoQueryAdaptiveTree_admissible : CBCAdmissible 2 twoQueryAdaptiveTree := by
  intro oracle
  simp only [twoQueryAdaptiveTree, cbcQueryRun_query_bind]
  split_ifs with htag
  · refine ⟨?_, by
      simp only [cbcQueryRun_query_bind, cbcQueryRun_pure, List.length_cons, List.length_nil]
      omega⟩
    intro x hx y hy hxy
    simp only [cbcQueryRun_query_bind, cbcQueryRun_pure, List.mem_cons, List.not_mem_nil,
      or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact not_isPrefix_of_head_ne (cbcInputBlocks_ne_nil _) head_cbcInputBlocks_zero_ne_one
    · exact not_isPrefix_of_head_ne (cbcInputBlocks_ne_nil _) head_cbcInputBlocks_zero_ne_one.symm
    · exact absurd rfl hxy
  · refine ⟨?_, by
      simp only [cbcQueryRun_query_bind, cbcQueryRun_pure, List.length_cons, List.length_nil]
      omega⟩
    intro x hx y hy hxy
    simp only [cbcQueryRun_query_bind, cbcQueryRun_pure, List.mem_cons, List.not_mem_nil,
      or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact not_isPrefix_of_head_ne (cbcInputBlocks_ne_nil _) head_cbcInputBlocks_zero_ne_two
    · exact not_isPrefix_of_head_ne (cbcInputBlocks_ne_nil _) head_cbcInputBlocks_zero_ne_two.symm
    · exact absurd rfl hxy
/-- Non-vacuous instantiation of the adaptive PRF bound for `PMF.pure twoQueryAdaptiveTree` at
  `n = 8, q = 2, ℓ = 2` (advantage bound `16 / 256 = 1 / 16 < 1`). -/
noncomputable example :
    |cbcRealSuccess 8 2 (PMF.pure twoQueryAdaptiveTree) -
        cbcIdealSuccess 8 2 (PMF.pure twoQueryAdaptiveTree)| ≤
      (2 : ℝ) ^ 2 * (2 : ℝ) ^ 2 / (2 : ℝ) ^ 8 := by
  simpa using abs_cbcRealSuccess_sub_cbcIdealSuccess_le 8 2 2 (PMF.pure twoQueryAdaptiveTree)
    (fun tree htree => by
      have hEq : tree = twoQueryAdaptiveTree := (PMF.mem_support_pure_iff _ _).1 htree
      subst hEq; exact twoQueryAdaptiveTree_admissible)
/-- Concrete instantiation of the 2-to-4-block forgery (`cbcTwoToFourAttack_valid`). -/
example : let trace := cbcTwoToFourAttack (cbcMacBlocks testPerm 0)
    trace.1.length = 1 ∧ (∀ q ∈ trace.1, q.length = 2) ∧
      trace.2.1.length = 4 ∧ cbcForgeryValid testPerm trace :=
  cbcTwoToFourAttack_valid testPerm
/-- Concrete instantiation of the 1/2-to-3-block splicing forgery (`cbcToThreeAttack_valid`). -/
example : let trace := cbcToThreeAttack (cbcMacBlocks testPerm 0)
    trace.1.length = 2 ∧ trace.2.1.length = 3 ∧ cbcForgeryValid testPerm trace :=
  cbcToThreeAttack_valid testPerm
/-- Concrete instantiation of the leaked-intermediate-tags forgery (`cbcLeakedTagsAttack_valid`). -/
example : let trace := cbcLeakedTagsAttack (cbcAllTagsTwo testPerm)
    trace.1.length = 3 ∧ trace.2.1 ∉ trace.1 ∧
      (cbcAllTagsTwo testPerm trace.2.1).2 = trace.2.2.2 :=
  cbcLeakedTagsAttack_valid (by decide) testPerm
/-- Concrete instantiation of the random-IV CBC-MAC forgery (`cbcRandomIVAttack_valid`). -/
example : let forged := cbcRandomIVAttack (cbcRandomIVMac testPerm b0 [0])
    forged.1 ≠ 0 ∧ cbcRandomIVMac testPerm forged.2.1 [forged.1] = forged.2 :=
  cbcRandomIVAttack_valid (by decide) testPerm b0
/-- Concrete instantiation of the append-length CBC-MAC forgery (`cbcLengthSuffixAttack_valid`). -/
example : let encodeLength : ℕ → List (BitString 4) := fun _ => [b0]
    let trace := cbcLengthSuffixAttack encodeLength (lengthAppendedCBC testPerm encodeLength)
    trace.1.length = 3 ∧ (∀ q ∈ trace.1, q.length * 4 < 2 ^ 4) ∧
      trace.2.1.length * 4 < 2 ^ 4 ∧ trace.2.1 ∉ trace.1 ∧
      lengthAppendedCBC testPerm encodeLength trace.2.1 = trace.2.2 :=
  cbcLengthSuffixAttack_valid (by decide) (fun _ => b0) testPerm
/-- Concrete instantiation of the zero-padded CBC-MAC forgery (`zeroPadAttack_valid`). -/
example : let trace := zeroPadAttack (zeroPadCBC testPerm 1)
    trace.1.length = 1 ∧ (∀ q ∈ trace.1, q.length ≤ 1 * 2 ^ 4) ∧
      trace.2.1.length ≤ 1 * 2 ^ 4 ∧ trace.2.1 ∉ trace.1 ∧
      zeroPadCBC testPerm 1 trace.2.1 = trace.2.2 :=
  zeroPadAttack_valid (by decide) (by decide) testPerm
/-- `BitString.padBlocks` reads a right-padded bit list as width-`2` blocks, and the floor block
  count drops the trailing odd bit position. -/
example : BitString.padBlocks 2 4 (List.rightpad 4 false [true]) = [![true, false], 0] ∧
    BitString.padBlocks 2 5 [true, false, true, true, true] = [![true, false], ![true, true]] := by
  decide
/-- info: 'Cslib.Crypto.getLast_cbcEncryptBlocks_eq_cbcMacBlocks' depends on axioms: [propext] -/
#guard_msgs in
#print axioms getLast_cbcEncryptBlocks_eq_cbcMacBlocks
/-- info: 'Cslib.Crypto.cbcTwoToFourAttack_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cbcTwoToFourAttack_valid
/-- info: 'Cslib.Crypto.cbcToThreeAttack_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cbcToThreeAttack_valid
/-- info: 'Cslib.Crypto.cbcRandomIVAttack_valid' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms cbcRandomIVAttack_valid
end Cslib.Crypto.CBCMACTests
