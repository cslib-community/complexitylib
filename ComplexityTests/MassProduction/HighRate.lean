/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.LineCode.HighRate
import Complexity.Foundations.Combinatorics.LineCode.HighRate.Packing
import Complexity.Foundations.FieldTheory.Finite.ReducedMonomial
import Complexity.Foundations.FieldTheory.Finite.Subfield
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# High-rate line-code clients

These clients build actual high-rate line codes over the fields with `2`, `4` and `2 ^ 10`
elements, including the boundary `ℓ = 2 ^ h` and a code of rate above nine tenths, and exercise
the rate bound at its equality case and where its hypotheses fail. A monomial without a common
zero digit breaks line parity, and the packing bounds are checked at exact multiples and where
their positivity hypotheses fail.
-/

namespace ComplexityTests.MassProduction.HighRate

open Cslib Cslib.LineCode Cslib.LineCode.HighRate

/-! ### Concrete codes -/

noncomputable instance (n : ℕ) : Fintype (GaloisField 2 n) := Fintype.ofFinite _

noncomputable instance (n : ℕ) : DecidableEq (GaloisField 2 n) := Classical.decEq _

private theorem card_galoisField {n : ℕ} (hn : n ≠ 0) : Fintype.card (GaloisField 2 n) = 2 ^ n := by
  rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]

-- The prime field: `h = m = 1` and `ℓ = 2`; the code is the constants, one information symbol.
example : ∃ C : LineCode (ZMod 2) 2, C.info.card = 1 :=
  exists_lineCode 1 1 le_rfl rfl

-- `GF(4)` with `h = 1`, `m = 2` and the boundary `ℓ = 2 = 2 ^ h`: 7 of the 16 points carry
-- information, so the information set is nonempty.
example : ∃ C : LineCode (GaloisField 2 2) 2, C.info.card = 7 ∧ C.info.Nonempty := by
  obtain ⟨C, hC⟩ := exists_lineCode (K := GaloisField 2 2) (ℓ := 2) 1 2 le_rfl
    (card_galoisField (by norm_num))
  refine ⟨C, hC.trans (by decide), Finset.card_pos.mp ?_⟩
  rw [hC]
  decide

-- `GF(2 ^ 10)` with `h = 1`, `m = 10`, `ℓ = 2`: `4 ^ 10 - 3 ^ 10 = 989527` of the `1048576`
-- points carry information, a rate above `9 / 10`.
example : ∃ C : LineCode (GaloisField 2 10) 2,
    C.info.card = 989527 ∧ 9 * 1048576 ≤ 10 * C.info.card := by
  obtain ⟨C, hC⟩ := exists_lineCode (K := GaloisField 2 10) (ℓ := 2) 1 10 le_rfl
    (card_galoisField (by norm_num))
  have hC' : C.info.card = 989527 := hC.trans (by decide)
  exact ⟨C, hC', by rw [hC']; decide⟩

-- The codewords of a line code satisfy the recovery identity on every punctured line; without a
-- common zero digit line parity fails, while with a zero column the line sum vanishes.
example (C : LineCode (GaloisField 2 2) 2) (data : (Fin 2 → GaloisField 2 2) → GaloisField 2 2)
    (u v : Fin 2 → GaloisField 2 2) (hv : v ≠ 0) :
    C.extend data u = ∑ c ∈ (Finset.univ : Finset (GaloisField 2 2)).erase 0,
        C.extend data (u + c • v) ∧
      ∑ x : ZMod 2, ((0 : ZMod 2) + x * 1) ^ 1 ≠ 0 ∧
      ∑ x : ZMod 2, ∏ i, ((0 : Fin 2 → ZMod 2) i + x * (fun _ : Fin 2 => (1 : ZMod 2)) i) ^
        (finFunctionFinEquiv fun k => (0 : Fin 1 → Fin 2 → Fin 2) k i : ℕ) = 0 :=
  ⟨(C.sum_extend data u v hv).symm, by decide,
    sum_prod_digits_eq_zero (h := 1) (m := 1) (j := 0) le_rfl rfl 0 rfl 0 (fun _ => 1)⟩

/-! ### Dimension and rate -/

example :
    retainedDimension 4 2 = 7 ∧
    retainedDimension 4 10 = 989527 ∧
    Fintype.card {w : Fin 2 → Fin 3 // ∃ j, w j = 0} = 5 ∧
    0 < retainedDimension 2 1 ∧
    3 * 4 ^ 10 ≤ (3 + 1) * retainedDimension 4 10 ∧
    1 * 2 ^ 1 = (1 + 1) * retainedDimension 2 1 ∧
    ¬1 * 3 ^ 1 ≤ (1 + 1) * retainedDimension 3 1 ∧
    ¬1 * 1 ^ 0 ≤ (1 + 1) * retainedDimension 1 0 :=
  ⟨by decide, by decide,
    by rw [card_exists_eq_retainedDimension]; decide,
    retainedDimension_pos (by norm_num) (by norm_num),
    retainedDimension_rate 4 10 3 (by norm_num) (by norm_num),
    by decide, by decide, by decide⟩

/-! ### Packing -/

example :
    packingCopies 100 7 3 = 5 ∧
    100 ≤ packingCopies 100 7 3 * 7 * 3 ∧
    packingCopies 21 7 3 = 2 ∧
    ¬5 ≤ packingCopies 5 0 3 * 0 * 3 ∧
    1 * (packingCopies 100 7 3 * 14 * 3) ≤ (1 + 1) * 100 + 1 * (14 * 3) ∧
    Nonempty (Fin 100 ↪ Fin (packingCopies 100 7 3) × Fin 7 × Fin 3) :=
  ⟨by decide,
    le_packingCopies_mul 100 7 3 (by norm_num) (by norm_num),
    by decide, by decide,
    mul_packingCopies_mul_le 100 7 14 3 1 (by norm_num),
    by simpa using nonempty_embedding_packingCopies (I := Fin 7) 100 3 (by norm_num) (by norm_num)⟩

/-! ### Binary fields -/

example :
    Nonempty (ZMod 2 ≃+ BitString 1) ∧
    Nonempty (GaloisField 2 3 ≃+ BitString 3) ∧
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), CharP K 2 ∧ Fintype.card K = 2 ^ 5 :=
  ⟨nonempty_addEquiv_bitString rfl,
    nonempty_addEquiv_bitString (card_galoisField (by norm_num)),
    exists_field_card_eq_two_pow (by norm_num)⟩

end ComplexityTests.MassProduction.HighRate
