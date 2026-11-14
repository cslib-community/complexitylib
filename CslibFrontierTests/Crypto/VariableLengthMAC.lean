/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Protocols.MAC.VariableLength
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PolyTime.Init

/-!
# Tests for the blockwise variable-length MAC

Concrete evaluations of the block encoding and API checks for
`CslibFrontier.Crypto.Protocols.MAC.VariableLength`.
-/

public section

namespace Cslib.Crypto.VariableLengthMACTests
open Cslib.Crypto Cslib.Crypto.BlockwiseMAC

/-- A `3`-bit identifier. -/
def ident : List Bool := [true, false, false]

/-- The block `000`. -/
def zeros : List Bool := [false, false, false]

/-- The block `111`. -/
def ones : List Bool := [true, true, true]

/-- `BitString.lowBits` writes the low bit first: `5 = 101₂`. -/
example : BitString.lowBits 3 5 = [true, false, true] := by decide

/-- A `12`-bit fixed-length input has `3`-bit fields. -/
example : fieldWidth 12 = 3 := by decide

/-- A `4`-bit message has two `3`-bit blocks; the second is padded with zeros. -/
example : blockCount 3 4 = 2 ∧ messageBlock 3 [true, false, true, true] 1 = [true, false, false] :=
  by decide

/-- Each block input of the construction is `12` bits long. -/
example : (blockInputs fullEncoder 12 ident (zeros ++ ones)).map List.length = [12, 12] := by
  decide

/-- Messages of length `0` or `2 ^ 3` are outside the domain and get no block inputs. -/
example : blockInputs fullEncoder 12 ident [] = [] ∧
    blockInputs fullEncoder 12 ident (List.replicate 8 true) = [] := by
  decide

/-- Without the index, swapping the two blocks only reverses the block inputs. -/
example : blockInputs noIndexEncoder 12 ident (ones ++ zeros) =
    (blockInputs noIndexEncoder 12 ident (zeros ++ ones)).reverse := by
  decide

/-- With the index, swapping the two blocks changes the block inputs. -/
example : blockInputs fullEncoder 12 ident (ones ++ zeros) ≠
    (blockInputs fullEncoder 12 ident (zeros ++ ones)).reverse := by
  decide

/-- Without the length, the one-block message `zeros` reuses the first block input of
`zeros ++ ones`. -/
example : blockInputs noLengthEncoder 12 ident zeros =
    (blockInputs noLengthEncoder 12 ident (zeros ++ ones)).take 1 := by
  decide

/-- Without the identifier, block inputs of different queries can be combined. -/
example : blockInputs noIdentifierEncoder 12 ident (zeros ++ ones) =
    (blockInputs noIdentifierEncoder 12 [false, true, true] (zeros ++ zeros)).take 1 ++
      (blockInputs noIdentifierEncoder 12 ones (ones ++ ones)).drop 1 := by
  decide

/-- The concrete bound applies to any adversary with at most `Q` signing queries. -/
example (M : MACScheme) (A : BlockwiseMACAdversary) (n Q : ℕ)
    (hA : ProbOracleComp.IsQueryBounded (A n) Q) :
    ProbComp.eval (M.blockwiseGame fullEncoder A n) true ≤
      ProbComp.eval (M.eufCmaGame (M.blockwiseReduction fullEncoder A) n) true +
        ((∑ i ∈ Finset.range Q, i : ℕ) : ENNReal) / 2 ^ fieldWidth (M.msgLen n) :=
  M.blockwiseGame_le A n Q hA

/-- At `L = 12` the separations apply, since `fieldWidth 12 = 3`. -/
example (M : MACScheme) (n : ℕ) (hL : M.msgLen n = 12) :
    ProbComp.eval (M.blockwiseGame noIndexEncoder M.swapBlocksAdversary n) true = 1 :=
  M.blockwiseGame_noIndex n (by rw [hL]; decide)

open Probability Turing.MultiTapeTM in
/-- Honest blockwise signing, verification, and the blockwise EUF-CMA game are polynomial-time. -/
example (M : MACScheme) (F : BlockwiseMACForger) (hF : IsOraclePPT encForgerOutput F) :
    IsPPTOn encSignInput encTag
      (fun p : ℕ × List Bool × List Bool => M.blockwiseSign fullEncoder p.1 p.2.1 p.2.2) ∧
    ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool × Tag =>
        M.blockwiseVerify fullEncoder p.1 p.2.1 p.2.2.1 p.2.2.2)
      encVerifyInput encBool ∧
    IsPPT encBool (fun n _ => M.blockwiseGame fullEncoder F.toAdversary n) :=
  ⟨M.isPPTOn_blockwiseSign isPolyTimeEncoder_fullEncoder,
    M.computableInPolyTime_blockwiseVerify isPolyTimeEncoder_fullEncoder,
    M.isPPT_blockwiseGame isPolyTimeEncoder_fullEncoder hF⟩

open Probability Turing.MultiTapeTM in
/-- The truncated reduction `blockwiseBoundedReduction` is uniformly strict oracle PPT. -/
example (M : MACScheme) (tagBound : ℕ → ℕ)
    (htagBound : ComputableInPolyTime tagBound encUnary encUnary)
    (F : BlockwiseMACForger) (hF : IsOraclePPT encForgerOutput F) :
    IsOraclePPT (encPair encBits encBits)
      (M.blockwiseBoundedReduction fullEncoder tagBound F) :=
  M.isOraclePPT_blockwiseBoundedReduction isPolyTimeEncoder_fullEncoder htagBound hF

/-- Uniform EUF-CMA security lifts to `BlockwiseEUFCMA fullEncoder` when `M.msgLen` is
polynomially lower-bounded. -/
example (M : MACScheme) (h : M.EUFCMA) (hmsgLen : PolynomiallyLowerBounded M.msgLen) :
    M.BlockwiseEUFCMA fullEncoder :=
  h.blockwiseEUFCMA hmsgLen

/-- Omitting any field breaks uniform `BlockwiseEUFCMA` once `3 ≤ fieldWidth (M.msgLen n)`
eventually. -/
example (M : MACScheme) (hw : ∀ᶠ n in Filter.atTop, 3 ≤ fieldWidth (M.msgLen n)) :
    ¬ M.BlockwiseEUFCMA noIndexEncoder ∧
      ¬ M.BlockwiseEUFCMA noLengthEncoder ∧
      ¬ M.BlockwiseEUFCMA noIdentifierEncoder :=
  ⟨M.not_blockwiseEUFCMA_noIndexEncoder hw,
    M.not_blockwiseEUFCMA_noLengthEncoder hw,
    M.not_blockwiseEUFCMA_noIdentifierEncoder hw⟩

open Probability Turing.MultiTapeTM in
/-- Concrete strict oracle-PPT certificates for the three 2-query attack forgers. -/
example (M : MACScheme) :
    IsOraclePPT encForgerOutput (M.swapBlocksAdversary.toForger fun n _ => n) ∧
      IsOraclePPT encForgerOutput (M.truncateAdversary.toForger fun n _ => n) ∧
      IsOraclePPT encForgerOutput (M.mixBlocksAdversary.toForger fun n _ => n) :=
  ⟨M.isOraclePPT_toForger_swapBlocksAdversary (by fun_prop),
    M.isOraclePPT_toForger_truncateAdversary (by fun_prop),
    M.isOraclePPT_toForger_mixBlocksAdversary (by fun_prop)⟩

open Probability Turing.MultiTapeTM in
/-- An ordinary `module` client can establish `IsPolyTimeEncoder` for a custom block encoder from
a machine certificate and apply the generic blockwise efficiency rules. -/
example (M : MACScheme) :
    let zeroEncoder : Encoder := fun _ L _ _ _ _ => List.replicate L false
    IsPolyTimeEncoder zeroEncoder ∧
      IsPPTOn encSignInput encTag
        (fun p : ℕ × List Bool × List Bool => M.blockwiseSign zeroEncoder p.1 p.2.1 p.2.2) ∧
      ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool × Tag =>
          M.blockwiseVerify zeroEncoder p.1 p.2.1 p.2.2.1 p.2.2.2)
        encVerifyInput encBool := by
  intro zeroEncoder
  have hE : IsPolyTimeEncoder zeroEncoder :=
    IsPolyTimeEncoder.of_computableInPolyTime (by dsimp [zeroEncoder]; fun_prop)
  exact ⟨hE, M.isPPTOn_blockwiseSign hE, M.computableInPolyTime_blockwiseVerify hE⟩

end Cslib.Crypto.VariableLengthMACTests
