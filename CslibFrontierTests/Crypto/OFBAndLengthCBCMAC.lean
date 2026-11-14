/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
import CslibFrontier.Crypto.Computational.Encryption.OFBMode
import CslibFrontier.Crypto.Primitives.BlockCipher.LengthPrependedCBCMAC

/-!
# Tests for OFB Mode CPA Security and Length-Prepended CBC-MAC

Concrete evaluations and non-vacuity witnesses for
`CslibFrontier/Crypto/Computational/Encryption/OFBMode.lean` and
`CslibFrontier/Crypto/Primitives/BlockCipher/LengthPrependedCBCMAC.lean`. Each headline bound
is instantiated with a concrete adversary whose hypotheses are proved, at parameters where the
bound is strictly below `1`.
-/
namespace CslibFrontierTests.Crypto.OFBAndLengthCBCMAC
open Cslib Cslib.Probability Cslib.Crypto

/-! ### OFB queries and block costs -/

/-- A valid left-or-right query: two messages of two 8-bit blocks each. -/
def ofbQueryLR : BlockModeQuery 8 := ([0, 1], [1, 1])

/-- A query whose two messages differ in length. -/
def ofbQueryUnequal : BlockModeQuery 8 := ([0], [1, 1])

/-- A valid query encrypts the selected message and costs its number of blocks. -/
example : blockModeSelect 2 true ofbQueryLR = [1, 1] ∧
    blockModeSelect 2 false ofbQueryLR = [0, 1] ∧ blockModeBlocks 2 ofbQueryLR = 2 := by
  decide

/-- Messages of different lengths, or longer than the per-query limit, encrypt the empty message
and cost nothing. -/
example : blockModeSelect 2 true ofbQueryUnequal = [] ∧ blockModeBlocks 2 ofbQueryUnequal = 0 ∧
    blockModeSelect 1 false ofbQueryLR = [] ∧ blockModeBlocks 1 ofbQueryLR = 0 := by
  decide

/-- The encrypted plaintext always has `blockModeBlocks ℓ q` blocks. -/
example : (blockModeSelect 2 true ofbQueryUnequal).length = blockModeBlocks 2 ofbQueryUnequal :=
  length_blockModeSelect 2 true ofbQueryUnequal

/-- Answering the keystream calls with a fixed function `f` gives the OFB keystream
`f x, f (f x), f (f (f x))`. -/
example (f : BitString 8 → BitString 8) (x : BitString 8) :
    (ofbChainQueries x 3).run (fun y => pure (f y)) = pure [f x, f (f x), f (f (f x))] :=
  run_ofbChainQueries f x 3

/-! ### A concrete adversary for the OFB bounds -/

/-- A one-query adversary: it asks `ofbQueryLR` and outputs `true` when the first ciphertext
block is zero. -/
def ofbOneQueryAdversary : BlockModeAdversary 8 := do
  let r ← ProbOracleComp.query (spec := BlockModeSpec 8) ofbQueryLR
  return decide (r.2.head? = some 0)

/-- The adversary asks for two blocks in total, with at most two blocks per query. -/
theorem isCostBounded_ofbOneQueryAdversary :
    OracleComp.IsCostBounded (blockModeCost 2) ofbOneQueryAdversary 2 := by
  unfold ofbOneQueryAdversary ProbOracleComp.query
  exact OracleComp.IsCostBounded.mono
    (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (Sum.inr ofbQueryLR)) fun _ =>
      OracleComp.IsCostBounded.pure _ 0)
    (by decide)

/-- The PRF reduction for the adversary makes at most two oracle calls. -/
example : ProbOracleComp.IsQueryBounded (ofbReduction 2 true ofbOneQueryAdversary) 2 :=
  isQueryBounded_ofbReduction 2 true isCostBounded_ofbOneQueryAdversary

/-- The keyed function `F k x = k + x` on 8-bit blocks. It is far from pseudorandom, which the
bound of `advantage_ofbCpaGame_le` reflects through the PRF advantages. -/
def xorKeyed (k x : BitString 8) : BitString 8 := k + x

/-- The OFB experiment for `xorKeyed` is the real PRF experiment for the reduction. -/
example : ofbCpaGame xorKeyed 2 true ofbOneQueryAdversary =
    ProbComp.eval (PRF.realExperiment xorKeyed (ofbReduction 2 true ofbOneQueryAdversary)) :=
  ofbCpaGame_eq_realExperiment xorKeyed 2 true ofbOneQueryAdversary

/-- With a uniform random function on 8-bit blocks, the adversary's view is within
`2 · (2 + 2) / 2 ^ 8 = 1 / 32` of the ideal experiment. -/
example :
    (Game.advantage
        (ProbComp.eval (PRF.idealExperiment (ofbReduction 2 false ofbOneQueryAdversary)))
        (ProbComp.eval (blockModeIdealExperiment 2 ofbOneQueryAdversary)) : ℝ) ≤ 1 / 32 :=
  (advantage_idealExperiment_ofbReduction_le 2 false isCostBounded_ofbOneQueryAdversary).trans_eq
    (by norm_num)

/-- OFB mode with a uniform random function on 8-bit blocks: the adversary's left-or-right
advantage is at most `2 · 2 · (2 + 2) / 2 ^ 8 = 1 / 16`. -/
example :
    (Game.advantage
        (ofbCpaGame (fun f : BitString 8 → BitString 8 => f) 2 false ofbOneQueryAdversary)
        (ofbCpaGame (fun f : BitString 8 → BitString 8 => f) 2 true ofbOneQueryAdversary) :
      ℝ) ≤ 1 / 16 :=
  (advantage_ofbCpaGame_randomFunction_le 2 isCostBounded_ofbOneQueryAdversary).trans_eq
    (by norm_num)

/-- OFB mode with the keyed function `xorKeyed`: the left-or-right advantage is at most the two
PRF advantages plus `1 / 16`. -/
example :
    (Game.advantage (ofbCpaGame xorKeyed 2 false ofbOneQueryAdversary)
        (ofbCpaGame xorKeyed 2 true ofbOneQueryAdversary) : ℝ) ≤
      PRF.advantage xorKeyed (ofbReduction 2 false ofbOneQueryAdversary) +
        PRF.advantage xorKeyed (ofbReduction 2 true ofbOneQueryAdversary) + 1 / 16 :=
  (advantage_ofbCpaGame_le xorKeyed 2 isCostBounded_ofbOneQueryAdversary).trans_eq
    (by norm_num)

/-! ### Length-prepended CBC-MAC -/

/-- The block count `k ≤ 3` written as an 8-bit block is an injective length encoding. -/
theorem blockCountBlock_injective_8_3 :
    Function.Injective (blockCountBlock (n := 8) (L := 3) (by norm_num)) :=
  blockCountBlock_injective _

/-- The length encoding used below. -/
def encode83 : Fin (3 + 1) → BitString 8 := blockCountBlock (by norm_num)

/-- The one-block message whose block is all ones. -/
def lpMsgOne : LengthPrependedInput 8 3 := ⟨⟨1, by decide⟩, ![1]⟩

/-- The two-block message with blocks all ones, then all zeros. It extends `lpMsgOne`. -/
def lpMsgTwo : LengthPrependedInput 8 3 := ⟨⟨2, by decide⟩, ![1, 0]⟩

/-- The empty message. -/
def lpMsgEmpty : LengthPrependedInput 8 3 := ⟨⟨0, by decide⟩, ![]⟩

/-- Without length prepending, the block list of `lpMsgOne` is a prefix of that of `lpMsgTwo`,
so these inputs are not prefix-free for basic CBC-MAC. -/
example : lengthPrependedBlocks lpMsgOne <+: lengthPrependedBlocks lpMsgTwo :=
  ⟨[0], by decide⟩

/-- Length prepending puts the encoded block count in front of the message blocks. -/
example : cbcInputBlocks (prependLength encode83 lpMsgTwo) = [encode83 ⟨2, by decide⟩, 1, 0] := by
  rw [cbcInputBlocks_prependLength]
  rfl

/-- With length prepending, the input for `lpMsgOne` is no longer a prefix of the input for
`lpMsgTwo`. -/
example : ¬(cbcInputBlocks (prependLength encode83 lpMsgOne)).IsPrefix
    (cbcInputBlocks (prependLength encode83 lpMsgTwo)) :=
  not_isPrefix_prependLength blockCountBlock_injective_8_3 (by decide)

/-- Length-prepended CBC-MAC of `lpMsgTwo` chains the blocks `1, 0` from the image of the encoded
block count. -/
example (g : BitString 8 → BitString 8) :
    lengthPrependedCbcMac g encode83 lpMsgTwo = g (g (g (encode83 ⟨2, by decide⟩) + 1) + 0) := by
  rw [lengthPrependedCbcMac_eq]
  rfl

/-- An adaptive two-query distinguisher: it asks `lpMsgOne`, then asks `lpMsgTwo` if the tag is
zero and the empty message otherwise. -/
def lpTree : OracleComp (LengthPrependedSpec 8 3) Bool := do
  let t ← OracleComp.query lpMsgOne
  if t = 0 then
    let t' ← OracleComp.query lpMsgTwo
    return decide (t' = 0)
  else
    let t' ← OracleComp.query lpMsgEmpty
    return decide (t' = t)

/-- The distinguisher makes at most two queries on every path. -/
theorem isQueryBounded_lpTree : OracleComp.IsQueryBounded lpTree 2 := by
  refine .liftBind (n := 1) lpMsgOne _ fun t => ?_
  split
  · exact .liftBind (n := 0) lpMsgTwo _ fun _ => .pure _ 0
  · exact .liftBind (n := 0) lpMsgEmpty _ fun _ => .pure _ 0

/-- Non-vacuous instance of the length-prepended CBC-MAC bound: two queries of at most three
blocks with 8-bit blocks give `2 ^ 2 · (3 + 1) ^ 2 / 2 ^ 8 = 1 / 4`. -/
example :
    |lengthPrependedRealSuccess encode83 (PMF.pure lpTree) -
        lengthPrependedIdealSuccess 8 3 (PMF.pure lpTree)| ≤ 1 / 4 :=
  (abs_lengthPrependedRealSuccess_sub_lengthPrependedIdealSuccess_le 8 2 3
      blockCountBlock_injective_8_3 (PMF.pure lpTree) fun tree htree => by
        have hEq : tree = lpTree :=
          (PMF.mem_support_pure_iff _ _).1 ((PMF.mem_support_iff _ _).2 htree)
        subst hEq
        exact isQueryBounded_lpTree).trans_eq
    (by norm_num)

/-! ### Axiom audits for the choice-free combinatorial results -/

/-- info: 'Cslib.Crypto.length_blockModeSelect' depends on axioms: [propext] -/
#guard_msgs in
#print axioms length_blockModeSelect
/-- info: 'Cslib.Crypto.run_ofbChainQueries' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms run_ofbChainQueries
/-- info: 'Cslib.Crypto.not_isPrefix_prependLength' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_isPrefix_prependLength

end CslibFrontierTests.Crypto.OFBAndLengthCBCMAC
