/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.BitPolynomial

/-! Checks of the bit-indexed polynomial design: a concrete reading over `ZMod 5`, a cell shared by
two blocks, and the binary instance used by the AC⁰[2] circuits. -/

open Cslib Cslib.Crypto.PRG.NisanWigderson Finset

namespace CslibFrontierTests.NisanWigdersonBitPolynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Three rows over `ZMod 5`, at the points `0, 1, 2`. -/
def r : Fin 3 ↪ ZMod 5 := Fin.castLEEmb (by decide : 3 ≤ 5)

/-- Columns numbered by the elements of `ZMod 5 = Fin 5` themselves. -/
def num : ZMod 5 ≃ Fin 5 := Equiv.refl _

/-- The string `11` names `A(x) = 1 + x`; at `r₂ = 2` it is `3`, so row `2` reads cell
`3 + 5 · 2 = 13`. -/
example (z : Fin (3 * 5) → Bool) :
    (Design.bitPolynomial 2 r num).restrict (BitString.equivFin 2 ![true, true]) z 2 = z 13 := by
  rw [Design.restrict_bitPolynomial, Equiv.symm_apply_apply]
  congr 1

/-- The strings `10` (`A = 1`) and `11` (`A = 1 + x`) agree at `x = 0`, so cell `1` of row `0`
lies in both blocks; their intersection is nonempty, and by `card_bitPolyBlock_inter_le` it has at
most `ℓ - 1 = 1` cell. -/
example : (1 : Fin (3 * 5)) ∈ bitPolyBlock r num ![true, false] ∩ bitPolyBlock r num ![true, true] ∧
    #(bitPolyBlock r num ![true, false] ∩ bitPolyBlock r num ![true, true]) ≤ 2 - 1 := by
  refine ⟨mem_inter.2 ⟨mem_bitPolyBlock.2 ?_, mem_bitPolyBlock.2 ?_⟩,
    card_bitPolyBlock_inter_le r.injective (by decide)⟩ <;> decide +kernel

/-- The binary instance for `n = 3` rows has `3 · 2 ^ e ≤ 2 · 3²` seed bits. -/
example : 3 * 2 ^ binaryFieldDegree 3 ≤ 2 * 3 ^ 2 :=
  Design.seedLength_binaryPolynomial_le 3

/-- A client reading of the binary instance: the bit of row `j` is the seed bit at the column whose
bits are the parities of `bits_bitPoly_eq_parityOn`. -/
example {n ℓ : ℕ} (i : BitString ℓ) (z : Fin (n * 2 ^ binaryFieldDegree n) → Bool) (j : Fin n) :
    (Design.binaryPolynomial n ℓ).restrict (BitString.equivFin ℓ i) z j =
      z (finProdFinEquiv (j, BitString.equivFin _ fun c =>
        parityOn {t : Fin ℓ | BinaryField.equivBits (binaryFieldDegree_ne_zero n)
          (binaryFieldPoints n j ^ (t : ℕ)) c = true} i)) :=
  Design.restrict_binaryPolynomial i z j _ fun c => by rw [Equiv.symm_apply_apply]

/-- Through `Design.binaryPolynomial_eq`, a client sees the blocks of the binary instance as
`bitPolyBlock`s, so it can use `mem_bitPolyBlock` and `card_bitPolyBlock`. -/
example (n ℓ : ℕ) (i : Fin (2 ^ ℓ)) : #((Design.binaryPolynomial n ℓ).block i) = n := by
  rw [Design.binaryPolynomial_eq, Design.block_bitPolynomial, card_bitPolyBlock]

/-- The field degree for `n = 5` rows is `3 ≤ 5`. -/
example : binaryFieldDegree 5 ≤ 5 :=
  binaryFieldDegree_le_self (by norm_num)

end CslibFrontierTests.NisanWigdersonBitPolynomial
