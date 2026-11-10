/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
import CslibFrontier.Crypto.Protocols.MAC.VariableLength

/-!
# Tests for the blockwise variable-length MAC

Concrete evaluations of the block encoding and API checks for
`CslibFrontier.Crypto.Protocols.MAC.VariableLength`.
-/
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

end Cslib.Crypto.VariableLengthMACTests
