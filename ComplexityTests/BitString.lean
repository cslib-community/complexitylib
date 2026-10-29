/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.Basic
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.BitString.Block
import Complexity.Foundations.Data.BitString.Counter
import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Foundations.Data.BitString.Flip
import Complexity.Foundations.Data.BitString.List
import Complexity.Foundations.Data.BitString.List.Binary
import Complexity.Foundations.Data.BitString.Parity
import Complexity.Foundations.Data.BitString.Threshold

/-! # Checked examples of the core bit-string API

Concrete values of the numberings, weights, parities, thresholds, blocks and list encodings of
`Cslib.BitString`, evaluated on small words. Each example fixes a convention a client relies on:
`equivFin` and `lsbValue` read the first bit as the least significant one, `binaryValue` reads it
as the most significant one, `ofList` pads with `false`, and blocks are consecutive runs of bits.
-/

namespace ComplexityTests.BitString

open Cslib Cslib.BitString Finset

/-! ### Reading bits as numbers -/

-- `equivFin` and `lsbValue` read the first bit as the least significant digit; `binaryValue`
-- reads the first bit as the most significant digit; `lowBits` writes least significant first;
-- and the numeral bridges connect `equivFin`, `lsbValue`, `binaryValue`, `Nat.ofBits`, and
-- `Nat.testBit`.
example :
    (equivFin 3 ![true, false, true] : ℕ) = 5 ∧
      (equivFin 3 ![false, true, true] : ℕ) = 6 ∧
      lsbValue [false, true, true] = 6 ∧
      binaryValue [false, true, true] = 3 ∧
      binaryValue [true, true, false] = 6 ∧
      lowBits 4 6 = [false, true, true, false] ∧
      lsbValue [true, false, true] = [true, false, true].foldr Nat.bit 0 ∧
      lsbValue (List.ofFn ![true, false, true]) = equivFin 3 ![true, false, true] ∧
      (equivFin 3 ![true, false, true] : ℕ) = Nat.ofBits ![true, false, true] ∧
      (equivFin 3).symm 5 2 = (5 : ℕ).testBit 2 ∧
      binaryValue (List.ofFn ![true, false, true]).reverse = equivFin 3 ![true, false, true] ∧
      Fintype.card (BitString 5) = 32 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    lsbValue_eq_foldr_bit [true, false, true],
    lsbValue_ofFn ![true, false, true],
    val_equivFin_eq_ofBits ![true, false, true],
    equivFin_symm_apply 5 2,
    binaryValue_reverse_ofFn ![true, false, true],
    by rw [BitString.card]; rfl⟩

/-! ### Weight, parity and thresholds -/

example :
    weight ![true, false, true, true] = 3 ∧
      parity 4 ![true, false, true, true] = true ∧
      parity 4 ![true, false, true, false] = false ∧
      threshold 4 3 ![true, false, true, true] = true ∧
      threshold 4 4 ![true, false, true, true] = false ∧
      majority 3 ![true, false, true] = true ∧
      strictMajority 4 ![true, false, true, false] = false ∧
      (weightLayer 5 2).Nonempty ∧
      (weightLayer 5 2).card = 10 ∧
      #{x : BitString 4 | parity 4 x = true} = 8 :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    weightLayer_nonempty (by decide),
    by rw [card_weightLayer]; rfl,
    card_filter_parity_eq_true (by decide)⟩

/-! ### Blocks and list encodings -/

example :
    List.ofFn (block (m := 2) (k := 4)
        ![true, false, true, true, false, true, true, false] 1) = [false, true, true, false] ∧
      List.ofFn (ofList 4 [true, true]) = [true, true, false, false] ∧
      List.ofFn (ofList 2 [true, false, true]) = [true, false] ∧
      listRow 2 1 [true, false, false, true, true] = [false, true] ∧
      listRow 2 2 [true, false, false, true, true] = [true, false] ∧
      (enum 3).length = 8 ∧
      (enumList 2).Nodup ∧
      flipOn ({0, 2} : Finset (Fin 3)) ![true, false, false] 2 = true ∧
      flipOn ({0, 2} : Finset (Fin 3)) (fun _ => false) 1 = false ∧
      flipOn {i | (![true, false, false] : BitString 3) i ≠ ![false, false, true] i}
        ![true, false, false] = ![false, false, true] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by rw [flipOn_apply]; decide,
    by rw [flipOn_false]; decide,
    flipOn_filter_ne ![true, false, false] ![false, false, true]⟩

end ComplexityTests.BitString
