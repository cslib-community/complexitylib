/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Reduce

/-!
# Shifted partial products of unsigned words

One circuit layer selects the shifted first word by one bit of the second word. Bits shifted
past the output width are discarded; this computes a modular partial product on every input.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.partialProduct`: a shifted partial-product word.

## Main results

* `Cslib.Circuits.Boolean.Modular.val_eval_partialProduct`: its exact unsigned modular value.
* `Cslib.Circuits.Boolean.Modular.depth_partialProduct_le`: one circuit layer suffices.

## References

The carry-save multiplication construction is standard binary partial-product arithmetic;
see [Vollmer, Chapter 1][Vollmer1999].
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open BitString

variable {w : ℕ}

/-- Each retained product digit is one AND gate; lower shifted-out positions are false. -/
private def partialProductBit (w : ℕ) (i j : Fin w) : Formula signature (w + w) :=
  if h : i.val ≤ j.val then
    (Formula.input (Fin.castAdd w ⟨j.val - i.val, by omega⟩)).and
      (.input (Fin.natAdd w i))
  else .const false

/-- Multiply the first word by the `i`th bit of the second word, shifted by `i`. -/
def partialProduct (w : ℕ) (i : Fin w) : Circuit signature (w + w) w :=
  Circuit.pi fun j => (partialProductBit w i j).toCircuit

private theorem eval_partialProduct (i j : Fin w) (a b : BitString w) :
    (partialProduct w i).eval interpretation (Fin.append a b) j =
      if h : i.val ≤ j.val then a ⟨j.val - i.val, by omega⟩ && b i else false := by
  by_cases h : i.val ≤ j.val
  · simp only [partialProduct, Circuit.eval_pi, Formula.eval_toCircuit, partialProductBit,
      h, ↓reduceDIte, Formula.eval_and, Formula.eval_input, Fin.append_left, Fin.append_right]
  · simp only [partialProduct, Circuit.eval_pi, Formula.eval_toCircuit, partialProductBit,
      h, ↓reduceDIte, Formula.eval_const]

/-- The circuit word agrees with the corresponding truncated `BitVec` shift. -/
private theorem word_eval_partialProduct (i : Fin w) (a b : BitString w) :
    word ((partialProduct w i).eval interpretation (Fin.append a b)) =
      if b i then word a <<< i.val else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [getLsbD_word _ ⟨j, hj⟩, eval_partialProduct]
  by_cases h : i.val ≤ j
  · have hji : j - i.val < w := by omega
    have hbit := getLsbD_word a ⟨j - i.val, hji⟩
    cases b i <;> simp_all
  · have hij : j < i.val := Nat.lt_of_not_ge h
    cases b i <;> simp_all

/-- Unsigned value of one shifted partial product, including overflow truncation. -/
theorem val_eval_partialProduct (i : Fin w) (a b : BitString w) :
    (BitString.equivFin w ((partialProduct w i).eval interpretation (Fin.append a b)) : ℕ) =
      if b i then ((BitString.equivFin w a : ℕ) * 2 ^ i.val) % 2 ^ w else 0 := by
  rw [← toNat_word_eq_equivFin, word_eval_partialProduct]
  split_ifs
  · rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, toNat_word_eq_equivFin]
  · rfl

/-- Exactly one gate per output bit, including the false low positions. -/
@[simp] theorem size_partialProduct (i : Fin w) : (partialProduct w i).size = w := by
  simp only [partialProduct, Circuit.size_pi, Formula.size_toCircuit]
  have h (j : Fin w) : (partialProductBit w i j).size = 1 := by
    unfold partialProductBit
    split_ifs <;> simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- All product digits are produced in parallel at depth one. -/
theorem depth_partialProduct_le (i : Fin w) : (partialProduct w i).depth ≤ 1 := by
  apply Circuit.depth_pi_le
  intro j
  apply (Formula.depth_toCircuit_le _).trans
  unfold partialProductBit
  split_ifs <;> simp

end Cslib.Circuits.Boolean.Modular
