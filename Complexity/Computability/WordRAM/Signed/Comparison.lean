/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Arithmetic

/-!
# Comparing encoded signed words

The low bits distinguish opposite signs. Within one sign, the encoded unsigned comparison
has the usual order for nonnegative integers and the reverse order for negative integers.
No signed comparison is added to the target machine.

## Main definitions

* `Signed.less`: an unsigned instruction block comparing the encoded input registers.

## Main results

* `Signed.exec_less`: comparison in at most eleven instructions, with the arithmetic frame.

## References

The instruction block is an original implementation using the sign-and-magnitude encoding.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

variable {r : ℕ}

/-- Compare two encoded signed integers, returning zero or one in `result`. -/
def less : Code .standard (r + 9) := ram[
  two ← #2; zero ← #0; signA ← left % two; signB ← right % two;
  if signA = signB then [
    if signA = zero then [
      if left < right then [ result ← #1 ] else [ result ← #0 ] ]
    else [ if right < left then [ result ← #1 ] else [ result ← #0 ] ] ]
  else [ result ← signA ] ]

private theorem lt_encoded (a b : ℤ) :
    (if (if a < 0 then 1 else 0 : ℕ) = (if b < 0 then 1 else 0) then
      if a < 0 then encode b < encode a else encode a < encode b
    else a < 0) ↔ a < b := by
  have ha := decode_encode a
  have hb := decode_encode b
  simp only [decode, encode_mod_two, encode_div_two] at ha hb
  by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;>
    simp only [encode, hna, hnb, ↓reduceIte, Nat.reduceEqDiff] at ha hb ⊢ <;>
    constructor <;> intro h <;> first | trivial | omega

/-- Signed comparison costs at most eleven unsigned instructions. The input encodings may
be used at any physical width admitting the constant two; the frame preserves the operands. -/
theorem exec_less {w : ℕ} (h2 : Fits w 2) (x : Data (r + 9)) {a b : ℤ}
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin w less x y 11 ∧
      y.regs result = (if a < b then 1 else 0) ∧ Frame x y := by
  let y := ((((x.set two 2).set zero 0).set signA (if a < 0 then 1 else 0)).set
    signB (if b < 0 then 1 else 0)).set result (if a < b then 1 else 0)
  have h1 := h2.of_le (by omega : 1 ≤ 2)
  have hp : ∀ i : Fin (r + 9), i.val < 2 ∨ 9 ≤ i.val → less.Preserves i := by
    intro i hi
    simp only [less, Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq,
      result, two, zero, signA, signB, Fin.ext_iff]
    omega
  have he : ExecWithin w less x y 11 := by
    have hcmp := lt_encoded a b
    by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;>
      by_cases hab : encode a < encode b <;> by_cases hba : encode b < encode a <;>
      by_cases hlt : a < b
    all_goals
      simp only [hna, hnb, hab, hba, ↓reduceIte, Nat.reduceEqDiff] at hcmp
      try (exfalso; tauto)
    all_goals
      ram_eval [less, y, left, right, two, zero, result, signA, signB, Fin.mk.injEq,
        hxa, hxb, encode_mod_two, hna, hnb, hab, hba, hlt, h2, h1]
  obtain ⟨n, hn, hex⟩ := he
  exact ⟨y, ⟨n, hn, hex⟩, by simp [y], rfl, fun i hi => hex.regs_eq (hp i hi)⟩

end Cslib.WordRAM.Signed
