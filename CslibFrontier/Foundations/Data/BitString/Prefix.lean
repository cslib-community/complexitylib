/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Bit-prefix projection of bit strings as an additive homomorphism

When `M ≤ q`, taking the first `M` bits of a `q`-bit word `v : BitString q` agrees with
`Cslib.BitString.zeroExtend (d' := M) v`, forms a surjective additive group homomorphism
`Cslib.BitString.restrictBitsAddHom hM : BitString q →+ BitString M`, and reduces the unsigned
integer value `Cslib.BitString.equivFin q v` modulo `2 ^ M`
(`Cslib.BitString.val_equivFin_restrictBitsAddHom`).

Placing these declarations in a dedicated topic module avoids expanding the public interface of the
widely imported `CslibFrontier/Foundations/Data/BitString/Basic.lean`.

## Main definitions

* `Cslib.BitString.restrictBitsAddHom`: projecting `BitString q` to its first `M ≤ q` bits as an
  additive group homomorphism `BitString q →+ BitString M`.

## Main results

* `Cslib.BitString.restrictBitsAddHom_eq_zeroExtend`: `restrictBitsAddHom hM v` agrees with
  `zeroExtend (d' := M) v`.
* `Cslib.BitString.restrictBitsAddHom_zeroExtend`, `Cslib.BitString.restrictBitsAddHom_surjective`:
  `zeroExtend` is a right inverse to `restrictBitsAddHom hM`, which is therefore surjective.
* `Cslib.BitString.val_equivFin_restrictBitsAddHom`: the unsigned value of `restrictBitsAddHom hM v`
  is `(equivFin q v).val % 2 ^ M`.
* `Cslib.BitString.val_equivFin_eq_div_mod_of_testBit`: a bit string read off the binary digits
  `s, …, s + d - 1` of a number `N` has value `N / 2 ^ s % 2 ^ d`.
-/

public section

namespace Cslib.BitString

/-- Projecting a `q`-bit string to its first `M ≤ q` bits as an additive group homomorphism. -/
@[expose] def restrictBitsAddHom {q M : ℕ} (hM : M ≤ q) : BitString q →+ BitString M where
  toFun v j := v (Fin.castLE hM j)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- When `M ≤ q`, `restrictBitsAddHom hM v` agrees pointwise with `zeroExtend (d' := M) v`. -/
theorem restrictBitsAddHom_eq_zeroExtend {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    restrictBitsAddHom hM v = zeroExtend (d' := M) v := by
  funext j
  have hj : j.val < q := lt_of_lt_of_le j.isLt hM
  simp [restrictBitsAddHom, zeroExtend, hj, Fin.castLE]

/-- Zero-extending an `M`-bit string to `q ≥ M` bits is a right inverse to
`restrictBitsAddHom hM`. -/
@[simp]
theorem restrictBitsAddHom_zeroExtend {q M : ℕ} (hM : M ≤ q) (w : BitString M) :
    restrictBitsAddHom hM (zeroExtend w) = w := by
  ext j
  simp [restrictBitsAddHom, zeroExtend, j.isLt]

/-- `restrictBitsAddHom hM` is surjective whenever `M ≤ q`. -/
theorem restrictBitsAddHom_surjective {q M : ℕ} (hM : M ≤ q) :
    Function.Surjective (restrictBitsAddHom hM) :=
  fun w => ⟨zeroExtend w, restrictBitsAddHom_zeroExtend hM w⟩

/-- **A window of binary digits.** If the bits of `z : BitString d` are the binary digits
`s, …, s + d - 1` of `N`, then the number of `z` is `N / 2 ^ s % 2 ^ d`. -/
theorem val_equivFin_eq_div_mod_of_testBit {d s N : ℕ} {z : BitString d}
    (hz : ∀ i : Fin d, z i = N.testBit (s + i)) :
    (equivFin d z : ℕ) = N / 2 ^ s % 2 ^ d := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < d
  · rw [testBit_equivFin z ⟨i, hi⟩, hz, Nat.add_comm s i]
    simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow
      ((equivFin d z).isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))

/-- Taking the first `M ≤ q` bits of `v : BitString q` corresponds to taking its unsigned integer
value modulo `2 ^ M`. -/
theorem val_equivFin_restrictBitsAddHom {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    (equivFin M (restrictBitsAddHom hM v)).val = (equivFin q v).val % 2 ^ M := by
  rw [val_equivFin_eq_div_mod_of_testBit (s := 0) (N := equivFin q v)
    (z := restrictBitsAddHom hM v) fun i => ?_]
  · simp
  · rw [Nat.zero_add]
    exact (testBit_equivFin v (Fin.castLE hM i)).symm

/-- Taking the `M`-bit prefix of `v : BitString q` via `zeroExtend` when `M ≤ q` reduces its
unsigned integer value modulo `2 ^ M`. -/
theorem val_equivFin_zeroExtend_of_le {q M : ℕ} (hM : M ≤ q) (v : BitString q) :
    (equivFin M (zeroExtend v)).val = (equivFin q v).val % 2 ^ M := by
  rw [← restrictBitsAddHom_eq_zeroExtend hM v, val_equivFin_restrictBitsAddHom hM v]

end Cslib.BitString
