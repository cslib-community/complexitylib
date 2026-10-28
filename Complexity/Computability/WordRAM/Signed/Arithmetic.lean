/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.Encoding
public import Complexity.Computability.WordRAM.Notation
public import Complexity.Computability.WordRAM.Compile

/-!
# Signed arithmetic implemented by unsigned word-RAM instructions

The input registers hold the encodings of two signed integers. The routines use only ordinary
unsigned arithmetic, comparisons and branches; no signed operation is added to the machine.
The bounds exclude the final halt; `Exec.executes` adds exactly one instruction.
Registers `left` (index 0) and `right` (index 1) are inputs, `result` (index 2) is the output,
and indices 3 through 8 are scratch, including `two` (index 3). Memory and all other registers
are preserved. `Code.rename` can place the routines in a larger register file.

The source semantics are `GenericRAM.Signed.Arithmetic.eval`, covering all five operations:
addition, subtraction, multiplication, Euclidean division and Euclidean remainder, including
Lean's total zero-divisor conventions (`a / 0 = 0` and `a % 0 = a`). The common `w + 2`
allowance covers exact out-of-range sums, differences and minimum/`-1` quotients; it is not a
minimal-width claim for results that fit the source range.

## Main definitions

* `Signed.add`, `Signed.subtract`, `Signed.multiply`, `Signed.divide`, `Signed.modulo`:
  fixed unsigned instruction blocks.
* `Signed.Frame`: preservation of memory, operands and registers outside the workspace.

## Main results

* `Signed.exec_add`, `Signed.exec_subtract`, `Signed.exec_multiply`, `Signed.exec_divide`,
  `Signed.exec_modulo`: charged executions with two extra unsigned bits, independent of the
  operands and source width.

## References

The instruction blocks and their representation are original implementation choices.
-/

@[expose] public section

namespace Cslib.WordRAM.Signed

variable {r : ℕ}

/-- First encoded operand. -/
abbrev left : Fin (r + 9) := ⟨0, by omega⟩
/-- Second encoded operand. -/
abbrev right : Fin (r + 9) := ⟨1, by omega⟩
/-- Encoded result. -/
abbrev result : Fin (r + 9) := ⟨2, by omega⟩
/-- Constant two, used to extract magnitudes and signs. -/
abbrev two : Fin (r + 9) := ⟨3, by omega⟩
/-- Decoded magnitude of the first operand. -/
abbrev magA : Fin (r + 9) := ⟨4, by omega⟩
/-- Decoded magnitude of the second operand. -/
abbrev magB : Fin (r + 9) := ⟨5, by omega⟩
/-- First operand sign, later reused for the result sign. -/
abbrev signA : Fin (r + 9) := ⟨6, by omega⟩
/-- Second operand sign. -/
abbrev signB : Fin (r + 9) := ⟨7, by omega⟩
/-- Constant zero, used to normalize the result. -/
abbrev zero : Fin (r + 9) := ⟨8, by omega⟩

private def signedValue (m s : ℕ) : ℤ := if s = 0 then m else -(m : ℤ)

private def packed (m s : ℕ) : ℕ := 2 * m + if m = 0 then 0 else s

private theorem encode_signedValue {m s : ℕ} (hs : s ≤ 1) :
    encode (signedValue m s) = packed m s := by
  by_cases hz : m = 0
  · simp [signedValue, packed, encode, hz]
  · by_cases hs0 : s = 0
    · simp [signedValue, packed, encode, hs0, hz]
    · have hs1 : s = 1 := by omega
      simp [signedValue, packed, encode, hs1, hz, show 0 < m by omega]

private theorem signedValue_encode (z : ℤ) :
    signedValue z.natAbs (if z < 0 then 1 else 0) = z := by
  by_cases hz : z < 0
  · simp [signedValue, hz, Int.ofNat_natAbs_of_nonpos (by omega : z ≤ 0)]
  · simp [signedValue, hz, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ z)]

/-- Decode the two input words into four scratch registers in six instructions. -/
def unpack : Code .standard (r + 9) := ram[
  two ← #2; zero ← #0;
  magA ← left / two; magB ← right / two;
  signA ← left % two; signB ← right % two ]

/-- Encode a magnitude and sign, setting the sign of zero to zero. -/
def finish : Code .standard (r + 9) := ram[
  if result = zero then [ result ← #0 ]
  else [ result ← result + result; result ← result + signA ] ]

/-- Add equal-sign magnitudes, or subtract the smaller opposite-sign magnitude. -/
def addMagnitudes : Code .standard (r + 9) := ram[
  if signA = signB then [ result ← magA + magB ]
  else [ if magA < magB then [ result ← magB - magA; signA ← signB ]
         else [ result ← magA - magB ] ] ]

/-- Combine decoded operands and encode their sum. -/
def addCore : Code .standard (r + 9) := ram[ ⟪addMagnitudes⟫; ⟪finish⟫ ]

/-- Add two sign-and-magnitude words, normalizing the sign of zero. -/
def add : Code .standard (r + 9) := ram[ ⟪unpack⟫; ⟪addCore⟫ ]

/-- Reverse the right sign bit; the result register temporarily holds the constant one. -/
def flipRightSign : Code .standard (r + 9) := ram[
  result ← #1; signB ← result - signB ]

/-- Subtract by reversing the second operand's sign before the addition block.
The temporary sign of zero is immaterial and the result is normalized. -/
def subtract : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪flipRightSign⟫; ⟪addCore⟫ ]

/-- Multiply the decoded magnitudes and set the product sign. -/
def multiplyMagnitudes : Code .standard (r + 9) := ram[
  result ← magA * magB;
  if signA = signB then [ signA ← #0 ] else [ signA ← #1 ] ]

/-- Multiply the magnitudes and compare the signs, normalizing the sign of zero. -/
def multiply : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪multiplyMagnitudes⟫; ⟪finish⟫ ]

/-- Compute the Euclidean quotient magnitude and sign from decoded operands. -/
def divideMagnitudes : Code .standard (r + 9) := ram[
  if zero < magB then [
    result ← magA / magB;
    magA ← magA % magB;
    if zero < signA then [
      if zero < magA then [ result ← result + signA ] else [ signA ← signA ] ]
    else [ signA ← signA ];
    if signA = signB then [ signA ← #0 ] else [ signA ← #1 ] ]
  else [ result ← #0; signA ← #0 ] ]

/-- Signed Euclidean division on sign-and-magnitude words, matching Lean's `a / 0 = 0`
convention and, for `b ≠ 0`, Lean's Euclidean `Int.ediv`: the quotient for which `a % b` lies in
`[0, |b|)` (rounding toward `-∞` when `b > 0` and toward `+∞` when `b < 0`). -/
def divide : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪divideMagnitudes⟫; ⟪finish⟫ ]

/-- Compute the encoded Euclidean remainder from decoded operands, preserving `a % 0 = a`. -/
def moduloCore : Code .standard (r + 9) := ram[
  if zero < magB then [
    result ← magA % magB;
    if zero < result then [
      if zero < signA then [ result ← magB - result ] else [ result ← result ];
      result ← result + result ]
    else [ result ← #0 ] ]
  else [ result ← left ] ]

/-- Signed Euclidean remainder on sign-and-magnitude words, matching Lean's `a % 0 = a`
convention and returning a nonnegative remainder below `|b|` when `b ≠ 0`. -/
def modulo : Code .standard (r + 9) := ram[
  ⟪unpack⟫; ⟪moduloCore⟫ ]

private def unpacked (x : Data (r + 9)) (a b sa sb : ℕ) : Data (r + 9) :=
  (((((x.set two 2).set zero 0).set magA a).set magB b).set signA sa).set signB sb

private theorem exec_unpack {w : ℕ} (h2 : Fits w 2) (x : Data (r + 9))
    {a b : ℤ} (ha : x.regs left = encode a) (hb : x.regs right = encode b)
    (hfa : Fits w a.natAbs) (hfb : Fits w b.natAbs) :
    Exec w unpack x (unpacked x a.natAbs b.natAbs
      (if a < 0 then 1 else 0) (if b < 0 then 1 else 0)) 6 := by
  have h1 := h2.of_le (by omega : 1 ≤ 2)
  by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;>
    ram_eval [unpack, unpacked, left, right, two, zero, magA, magB, signA, signB,
      Fin.mk.injEq, ha, hb, encode_div_two, encode_mod_two, h2, h1, hfa, hfb, hna, hnb]

private theorem exec_finish {w : ℕ} (x : Data (r + 9)) {m s : ℕ}
    (hm : x.regs result = m) (hs : x.regs signA = s) (hz : x.regs zero = 0)
    (hfit : Fits w (2 * m + s)) :
    ∃ y, ExecWithin w finish x y 4 ∧ y.regs result = packed m s ∧ y.mem = x.mem := by
  have hd : Fits w (m + m) := hfit.of_le (by omega)
  have hf : Fits w (m + m + s) := by simpa only [two_mul] using hfit
  by_cases hm0 : m = 0
  · refine ⟨x.set result 0, ?_, ?_, rfl⟩
    · ram_eval [finish, result, zero, Fin.mk.injEq, hm, hz, hm0]
    · simp [packed, hm0]
  · refine ⟨(x.set result (m + m)).set result (m + m + s), ?_, ?_, rfl⟩
    · ram_eval [finish, result, signA, zero, Fin.mk.injEq, hm, hs, hz, hm0, hd, hf]
    · simp [packed, hm0, two_mul]

private def sumMagnitude (a b sa sb : ℕ) : ℕ :=
  if sa = sb then a + b else if a < b then b - a else a - b

private def sumSign (a b sa sb : ℕ) : ℕ :=
  if sa = sb then sa else if a < b then sb else sa

private def sumData (x : Data (r + 9)) (a b sa sb : ℕ) : Data (r + 9) :=
  if sa = sb then x.set result (a + b)
  else if a < b then (x.set result (b - a)).set signA sb
  else x.set result (a - b)

private theorem sum_value {a b sa sb : ℕ} (ha : sa ≤ 1) (hb : sb ≤ 1) :
    signedValue (sumMagnitude a b sa sb) (sumSign a b sa sb) =
      signedValue a sa + signedValue b sb := by
  unfold sumMagnitude sumSign signedValue
  split_ifs <;> omega

private theorem exec_addMagnitudes {w : ℕ} (x : Data (r + 9)) {a b sa sb : ℕ}
    (ha : x.regs magA = a) (hb : x.regs magB = b)
    (hsa : x.regs signA = sa) (hsb : x.regs signB = sb) (hf : Fits w (a + b)) :
    ExecWithin w addMagnitudes x (sumData x a b sa sb) 5 := by
  have hab := hf.of_le (show a - b ≤ a + b by omega)
  have hba := hf.of_le (show b - a ≤ a + b by omega)
  by_cases hs : sa = sb <;> by_cases hlt : a < b <;>
    ram_eval [addMagnitudes, sumData, result, signA, signB, magA, magB,
      Fin.mk.injEq, ha, hb, hsa, hsb, hs, hlt, hf, hab, hba]

private theorem exec_addCore {w : ℕ} (x : Data (r + 9)) {a b sa sb : ℕ}
    (ha : x.regs magA = a) (hb : x.regs magB = b)
    (hsa : x.regs signA = sa) (hsb : x.regs signB = sb) (hz : x.regs zero = 0)
    (hsa1 : sa ≤ 1) (hsb1 : sb ≤ 1) (hf : Fits w (2 * (a + b) + 1)) :
    ∃ y, ExecWithin w addCore x y 9 ∧
      y.regs result = encode (signedValue a sa + signedValue b sb) ∧ y.mem = x.mem := by
  let z := sumData x a b sa sb
  have hmag : z.regs result = sumMagnitude a b sa sb := by
    unfold z sumData sumMagnitude
    split_ifs <;> simp [result, signA, Fin.mk.injEq]
  have hsign : z.regs signA = sumSign a b sa sb := by
    unfold z sumData sumSign
    split_ifs <;> simp [result, signA, Fin.mk.injEq, hsa]
  have hzero : z.regs zero = 0 := by
    unfold z sumData
    split_ifs <;> simp [result, signA, zero, Fin.mk.injEq, hz]
  have hmle : sumMagnitude a b sa sb ≤ a + b := by
    unfold sumMagnitude
    split_ifs <;> omega
  have hsle : sumSign a b sa sb ≤ 1 := by
    unfold sumSign
    split_ifs <;> omega
  have hfit : Fits w (2 * sumMagnitude a b sa sb + sumSign a b sa sb) :=
    hf.of_le (by omega)
  obtain ⟨y, hy, hyr, hym⟩ := exec_finish z hmag hsign hzero hfit
  refine ⟨y, (exec_addMagnitudes x ha hb hsa hsb (hf.of_le (by omega))).seq hy, ?_, ?_⟩
  · rw [hyr, ← encode_signedValue hsle, sum_value hsa1 hsb1]
  · exact hym.trans (by unfold z sumData; split_ifs <;> rfl)

private theorem two_fits {w : ℕ} : Fits (w + 2) 2 := by
  unfold Fits
  have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 2 ≤ w + 2)
  omega

private theorem magnitude_fits {w : ℕ} {z : ℤ} (h : GenericRAM.Signed.Fits w z) :
    Fits (w + 2) z.natAbs :=
  (encode_fits h).mono (by omega) |>.of_le (by unfold encode; split_ifs <;> omega)

private theorem arithmetic_fits {w m : ℕ} (hw : 0 < w) (hm : m ≤ 2 * 2 ^ (w - 1)) :
    Fits (w + 2) (2 * m + 1) := by
  have hp : 2 ^ (w + 2) = 8 * 2 ^ (w - 1) := by
    have he : w + 2 = (w - 1) + 3 := by omega
    rw [he, pow_add]
    omega
  have := Nat.two_pow_pos (w - 1)
  unfold Fits
  omega

/-- Memory and registers outside the output and six scratch registers are unchanged. -/
def Frame (x y : Data (r + 9)) : Prop :=
  y.mem = x.mem ∧ ∀ i, i.val < 2 ∨ 9 ≤ i.val → y.regs i = x.regs i

private theorem preserves {i : Fin (r + 9)} (hi : i.val < 2 ∨ 9 ≤ i.val) :
    (add (r := r)).Preserves i ∧ (subtract (r := r)).Preserves i ∧
      (multiply (r := r)).Preserves i ∧ (divide (r := r)).Preserves i ∧
      (modulo (r := r)).Preserves i := by
  simp only [add, subtract, multiply, divide, modulo,
    multiplyMagnitudes, divideMagnitudes, moduloCore, unpack, flipRightSign,
    addCore, addMagnitudes, finish,
    Code.Preserves, Op.bin, Op.dest, ne_eq, Option.some.injEq,
    result, two, zero, magA, magB, signA, signB, Fin.ext_iff]
  omega

/-- Signed addition runs within fifteen instructions at unsigned width `w + 2`.
The result is exact even when the sum does not fit the source signed range. -/
theorem exec_add {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) add x y 15 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .add a b) ∧ Frame x y := by
  let z := unpacked x a.natAbs b.natAbs (if a < 0 then 1 else 0) (if b < 0 then 1 else 0)
  have hu := exec_unpack two_fits x hxa hxb (magnitude_fits ha) (magnitude_fits hb)
  have hab : a.natAbs + b.natAbs ≤ 2 * 2 ^ (w - 1) := by
    have := ha.natAbs_le
    have := hb.natAbs_le
    omega
  obtain ⟨y, hy, hyr, hym⟩ := exec_addCore z (a := a.natAbs) (b := b.natAbs)
    (sa := if a < 0 then 1 else 0) (sb := if b < 0 then 1 else 0)
    (by simp [z, unpacked, magA, magB, signA, signB, Fin.mk.injEq])
    (by simp [z, unpacked, magB, signA, signB, Fin.mk.injEq])
    (by simp [z, unpacked, signA, signB, Fin.mk.injEq])
    (by simp [z, unpacked])
    (by simp [z, unpacked, zero, magA, magB, signA, signB, Fin.mk.injEq])
    (by split_ifs <;> omega) (by split_ifs <;> omega) (arithmetic_fits ha.1 hab)
  have he : ExecWithin (w + 2) add x y 15 := hu.within.seq hy
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨y, ⟨n, hn, hex⟩, ?_, hym, fun i hi => hex.regs_eq (preserves hi).1⟩
  simpa only [signedValue_encode, GenericRAM.Signed.Arithmetic.eval] using hyr

/-- Signed subtraction runs within seventeen instructions at unsigned width `w + 2`.
The result is exact even when the difference does not fit the source signed range. -/
theorem exec_subtract {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) subtract x y 17 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .sub a b) ∧ Frame x y := by
  let z := unpacked x a.natAbs b.natAbs (if a < 0 then 1 else 0) (if b < 0 then 1 else 0)
  let q := (z.set result 1).set signB (1 - if b < 0 then 1 else 0)
  have hu := exec_unpack two_fits x hxa hxb (magnitude_fits ha) (magnitude_fits hb)
  have h1 : Fits (w + 2) 1 := two_fits.of_le (by omega : 1 ≤ 2)
  have hf : Fits (w + 2) (1 - if b < 0 then 1 else 0) := h1.of_le (Nat.sub_le ..)
  have hflip : Exec (w + 2)
      (ram[ result ← #1; signB ← result - signB ]) z q 2 := by
    ram_eval [q, z, unpacked, result, signB, Fin.mk.injEq, h1, hf]
  have hab : a.natAbs + b.natAbs ≤ 2 * 2 ^ (w - 1) := by
    have := ha.natAbs_le
    have := hb.natAbs_le
    omega
  obtain ⟨y, hy, hyr, hym⟩ := exec_addCore q (a := a.natAbs) (b := b.natAbs)
    (sa := if a < 0 then 1 else 0) (sb := 1 - if b < 0 then 1 else 0)
    (by simp [q, z, unpacked, result, magA, magB, signA, signB, Fin.mk.injEq])
    (by simp [q, z, unpacked, result, magB, signA, signB, Fin.mk.injEq])
    (by simp [q, z, unpacked, result, signA, signB, Fin.mk.injEq])
    (by simp [q])
    (by simp [q, z, unpacked, result, zero, magA, magB, signA, signB, Fin.mk.injEq])
    (by split_ifs <;> omega) (by split_ifs <;> omega) (arithmetic_fits ha.1 hab)
  have he : ExecWithin (w + 2) subtract x y 17 := hu.within.seq (hflip.within.seq hy)
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨y, ⟨n, hn, hex⟩, ?_, hym, fun i hi => hex.regs_eq (preserves hi).2.1⟩
  have hneg : signedValue b.natAbs (1 - if b < 0 then 1 else 0) = -b := by
    by_cases h : b < 0
    · simp [signedValue, h, Int.ofNat_natAbs_of_nonpos (by omega : b ≤ 0)]
    · simp [signedValue, h, ← Int.eq_natAbs_of_nonneg (by omega : 0 ≤ b)]
  simpa only [signedValue_encode, hneg, sub_eq_add_neg, GenericRAM.Signed.Arithmetic.eval] using hyr

/-- Signed multiplication runs within fourteen instructions at unsigned width `w + 2`,
provided the mathematical product fits the source signed range. No double-width unsigned
product is needed: the magnitudes' product equals the magnitude of the signed result. -/
theorem exec_multiply {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hp : GenericRAM.Signed.Fits w (a * b))
    (x : Data (r + 9)) (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) multiply x y 14 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mul a b) ∧ Frame x y := by
  let sa : ℕ := if a < 0 then 1 else 0
  let sb : ℕ := if b < 0 then 1 else 0
  let s : ℕ := if sa = sb then 0 else 1
  let z := unpacked x a.natAbs b.natAbs sa sb
  let q := (z.set result (a.natAbs * b.natAbs)).set signA s
  have hu := exec_unpack two_fits x hxa hxb (magnitude_fits ha) (magnitude_fits hb)
  have hprod : a.natAbs * b.natAbs ≤ 2 * 2 ^ (w - 1) := by
    have := hp.natAbs_le
    rw [Int.natAbs_mul] at this
    omega
  have hf := arithmetic_fits ha.1 hprod
  have hmul : Fits (w + 2) (a.natAbs * b.natAbs) := hf.of_le (by omega)
  have h1 : Fits (w + 2) 1 := two_fits.of_le (by omega : 1 ≤ 2)
  have hpre : ExecWithin (w + 2) multiplyMagnitudes z q 4 := by
    by_cases hna : a < 0 <;> by_cases hnb : b < 0 <;>
      ram_eval [multiplyMagnitudes, q, z, unpacked, sa, sb, s, result, magA, magB,
        signA, signB, Fin.mk.injEq, hna, hnb, hmul, h1]
  have hsign : s ≤ 1 := by dsimp only [s]; split_ifs <;> omega
  have hfit : Fits (w + 2) (2 * (a.natAbs * b.natAbs) + s) := hf.of_le (by omega)
  obtain ⟨y, hy, hyr, hym⟩ := exec_finish q (m := a.natAbs * b.natAbs) (s := s)
    (by simp [q, result, signA, Fin.mk.injEq]) (by simp [q])
    (by simp [q, z, unpacked, zero, result, magA, magB, signA, signB, Fin.mk.injEq]) hfit
  have he : ExecWithin (w + 2) multiply x y 14 := hu.within.seq (hpre.seq hy)
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨y, ⟨n, hn, hex⟩, ?_, hym, fun i hi => hex.regs_eq (preserves hi).2.2.1⟩
  have hv : signedValue (a.natAbs * b.natAbs) s = a * b := by
    have hsa := signedValue_encode a
    have hsb := signedValue_encode b
    change signedValue a.natAbs sa = a at hsa
    change signedValue b.natAbs sb = b at hsb
    rw [← hsa, ← hsb]
    dsimp only [s, sa, sb, signedValue]
    split_ifs <;> simp_all
  rw [hyr, ← encode_signedValue hsign, hv]
  rfl

private def divMagnitude (a b sa : ℕ) : ℕ :=
  if 0 < b then a / b + if 0 < sa ∧ 0 < a % b then 1 else 0 else 0

private theorem divMagnitude_le (a b sa : ℕ) : divMagnitude a b sa ≤ a / b + 1 := by
  unfold divMagnitude
  generalize a / b = q
  split_ifs <;> omega

private def divSign (b sa sb : ℕ) : ℕ :=
  if 0 < b then if sa = sb then 0 else 1 else 0

private def modMagnitude (a b sa : ℕ) : ℕ :=
  if 0 < a % b then if 0 < sa then b - a % b else a % b else 0

private theorem div_mod_signedValue {m n sa sb : ℕ} (hn : 0 < n) (hsa : sa ≤ 1) (hsb : sb ≤ 1) :
    (modMagnitude m n sa : ℤ) +
      signedValue n sb * signedValue (divMagnitude m n sa) (divSign n sa sb) =
      signedValue m sa := by
  have hrlt : m % n < n := Nat.mod_lt m hn
  have hmn : (n : ℤ) * (m / n : ℕ) + (m % n : ℕ) = (m : ℤ) := by
    exact_mod_cast Nat.div_add_mod m n
  simp only [divMagnitude, divSign, modMagnitude, signedValue, hn, ↓reduceIte]
  generalize m / n = q at hmn ⊢
  generalize m % n = r at hmn hrlt ⊢
  rcases (by omega : sa = 0 ∨ sa = 1) with rfl | rfl <;>
    rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
    by_cases hr0 : 0 < r
  all_goals
    simp only [hr0, ↓reduceIte, Nat.lt_irrefl, zero_lt_one, true_and, false_and,
      Nat.reduceEqDiff, Nat.cast_add, Nat.cast_one, Nat.cast_zero,
      Nat.cast_sub (le_of_lt hrlt), mul_neg, neg_mul, mul_add, mul_one, mul_zero]
    omega

private theorem div_mod_nonzero {a b : ℤ} (hb : b ≠ 0) :
    let sa : ℕ := if a < 0 then 1 else 0
    let sb : ℕ := if b < 0 then 1 else 0
    a / b = signedValue (divMagnitude a.natAbs b.natAbs sa) (divSign b.natAbs sa sb) ∧
      a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) := by
  dsimp only
  set sa : ℕ := if a < 0 then 1 else 0
  set sb : ℕ := if b < 0 then 1 else 0
  have hn : 0 < b.natAbs := Int.natAbs_pos.mpr hb
  have hrlt : a.natAbs % b.natAbs < b.natAbs := Nat.mod_lt a.natAbs hn
  have heq : (modMagnitude a.natAbs b.natAbs sa : ℤ) +
      b * signedValue (divMagnitude a.natAbs b.natAbs sa) (divSign b.natAbs sa sb) = a := by
    have hsa1 : sa ≤ 1 := by dsimp [sa]; split_ifs <;> omega
    have hsb1 : sb ≤ 1 := by dsimp [sb]; split_ifs <;> omega
    simpa only [sa, sb, signedValue_encode] using div_mod_signedValue (m := a.natAbs) hn hsa1 hsb1
  have hmod_lt : (modMagnitude a.natAbs b.natAbs sa : ℤ) < (b.natAbs : ℤ) := by
    simp only [modMagnitude, Nat.cast_lt]
    generalize a.natAbs % b.natAbs = r at hrlt ⊢
    split_ifs <;> omega
  by_cases hbp : 0 < b
  · exact (Int.ediv_emod_unique hbp).mpr
      ⟨heq, Nat.cast_nonneg _, by simpa [← Int.eq_natAbs_of_nonneg (le_of_lt hbp)] using hmod_lt⟩
  · have hbn : b < 0 := by omega
    exact (Int.ediv_emod_unique' hbn).mpr
      ⟨heq, Nat.cast_nonneg _,
        by simpa [Int.ofNat_natAbs_of_nonpos (le_of_lt hbn)] using hmod_lt⟩

private def divPreData (x : Data (r + 9)) (m n sa sb : ℕ) : Data (r + 9) :=
  if 0 < n then
    let x1 := (x.set result (m / n)).set magA (m % n)
    let x2 := if 0 < sa then
      if 0 < m % n then x1.set result (m / n + sa) else x1.set signA sa
    else x1.set signA sa
    x2.set signA (if sa = sb then 0 else 1)
  else (x.set result 0).set signA 0

/-- Signed Euclidean division runs within twenty instructions at unsigned width `w + 2`,
including Lean's `a / 0 = 0` convention. The result is exact even at the minimum/`-1`
signed overflow `(-2 ^ (w - 1)) / (-1) = 2 ^ (w - 1)`, where `GenericRAM.Signed.model` faults and
the compiled block returns `encode (2 ^ (w - 1))` without fault reflection. -/
theorem exec_divide {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) divide x y 20 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .div a b) ∧ Frame x y := by
  let sa : ℕ := if a < 0 then 1 else 0
  let sb : ℕ := if b < 0 then 1 else 0
  let z := unpacked x a.natAbs b.natAbs sa sb
  let q := divPreData z a.natAbs b.natAbs sa sb
  have hu := exec_unpack two_fits x hxa hxb (magnitude_fits ha) (magnitude_fits hb)
  have h1 : Fits (w + 2) 1 := two_fits.of_le (by omega : 1 ≤ 2)
  have hqbound : a.natAbs / b.natAbs + 1 ≤ 2 * 2 ^ (w - 1) := by
    have := ha.natAbs_le
    have := Nat.div_le_self a.natAbs b.natAbs
    have := Nat.two_pow_pos (w - 1)
    omega
  have hf := arithmetic_fits ha.1 hqbound
  have hdiv : Fits (w + 2) (a.natAbs / b.natAbs) := hf.of_le (by omega)
  have hmod : Fits (w + 2) (a.natAbs % b.natAbs) :=
    (magnitude_fits ha).of_le (Nat.mod_le a.natAbs b.natAbs)
  have hinc : Fits (w + 2) (a.natAbs / b.natAbs + 1) := hf.of_le (by omega)
  have hpre : ExecWithin (w + 2) divideMagnitudes z q 10 := by
    by_cases hnz : 0 < b.natAbs <;> by_cases hna : a < 0 <;>
      by_cases hnb : b < 0 <;> by_cases hrem : 0 < a.natAbs % b.natAbs <;>
      ram_eval [divideMagnitudes, q, divPreData, z, unpacked, sa, sb,
        result, zero, magA, magB, signA, signB, Fin.mk.injEq,
        hnz, hna, hnb, hrem, hdiv, hmod, hinc, h1]
  have hqmag : q.regs result = divMagnitude a.natAbs b.natAbs sa := by
    dsimp only [q, divPreData, divMagnitude, sa]
    split_ifs
    all_goals
      simp only [Data.set_regs, Function.update_apply, result, magA, signA, Fin.mk.injEq,
        Nat.reduceEqDiff, ↓reduceIte]
      try omega
  have hqsign : q.regs signA = divSign b.natAbs sa sb := by
    dsimp only [q, divPreData, divSign]
    split_ifs <;> simp [result, signA]
  have hqzero : q.regs zero = 0 := by
    dsimp only [q, divPreData]
    split_ifs <;> simp [z, unpacked, result, zero, magA, magB, signA, signB, Fin.mk.injEq]
  have hqmle : divMagnitude a.natAbs b.natAbs sa ≤ a.natAbs / b.natAbs + 1 :=
    divMagnitude_le a.natAbs b.natAbs sa
  have hqsle : divSign b.natAbs sa sb ≤ 1 := by
    unfold divSign
    split_ifs <;> omega
  have hfit : Fits (w + 2) (2 * divMagnitude a.natAbs b.natAbs sa + divSign b.natAbs sa sb) :=
    hf.of_le (by omega)
  obtain ⟨y, hy, hyr, hym⟩ := exec_finish q hqmag hqsign hqzero hfit
  have hqm : q.mem = x.mem := by
    dsimp only [q, divPreData]
    split_ifs <;> rfl
  have he : ExecWithin (w + 2) divide x y 20 := hu.within.seq (hpre.seq hy)
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨y, ⟨n, hn, hex⟩, ?_, hym.trans hqm, fun i hi => hex.regs_eq (preserves hi).2.2.2.1⟩
  rw [hyr, ← encode_signedValue hqsle]
  by_cases hb0 : b = 0
  · subst hb0
    simp [divMagnitude, divSign, signedValue, GenericRAM.Signed.Arithmetic.eval]
  · simp only [GenericRAM.Signed.Arithmetic.eval, (div_mod_nonzero hb0).1, sa, sb]

private def modData (x : Data (r + 9)) (la m n sa : ℕ) : Data (r + 9) :=
  if 0 < n then
    let x1 := x.set result (m % n)
    if 0 < m % n then
      let rem := if 0 < sa then n - m % n else m % n
      (x1.set result rem).set result (rem + rem)
    else x1.set result 0
  else x.set result la

/-- Signed Euclidean remainder runs within thirteen instructions at unsigned width `w + 2`,
including Lean's `a % 0 = a` convention. -/
theorem exec_modulo {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (x : Data (r + 9))
    (hxa : x.regs left = encode a) (hxb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) modulo x y 13 ∧
      y.regs result = encode (GenericRAM.Signed.Arithmetic.eval .mod a b) ∧ Frame x y := by
  let sa : ℕ := if a < 0 then 1 else 0
  let sb : ℕ := if b < 0 then 1 else 0
  let z := unpacked x a.natAbs b.natAbs sa sb
  let y := modData z (encode a) a.natAbs b.natAbs sa
  have hu := exec_unpack two_fits x hxa hxb (magnitude_fits ha) (magnitude_fits hb)
  have hmod : Fits (w + 2) (a.natAbs % b.natAbs) :=
    (magnitude_fits ha).of_le (Nat.mod_le a.natAbs b.natAbs)
  have hsub : Fits (w + 2) (b.natAbs - a.natAbs % b.natAbs) :=
    (magnitude_fits hb).of_le (Nat.sub_le ..)
  have hdbl1 : Fits (w + 2) (a.natAbs % b.natAbs + a.natAbs % b.natAbs) := by
    have hm : a.natAbs % b.natAbs ≤ 2 * 2 ^ (w - 1) := by
      have := ha.natAbs_le
      have := Nat.mod_le a.natAbs b.natAbs
      omega
    exact (arithmetic_fits ha.1 hm).of_le (by omega)
  have hdbl2 : Fits (w + 2)
      (b.natAbs - a.natAbs % b.natAbs + (b.natAbs - a.natAbs % b.natAbs)) := by
    have hm : b.natAbs - a.natAbs % b.natAbs ≤ 2 * 2 ^ (w - 1) := by
      have := hb.natAbs_le
      omega
    exact (arithmetic_fits hb.1 hm).of_le (by omega)
  have hcore : ExecWithin (w + 2) moduloCore z y 7 := by
    by_cases hnz : 0 < b.natAbs <;> by_cases hrem : 0 < a.natAbs % b.natAbs <;>
      by_cases hna : a < 0 <;>
      ram_eval [moduloCore, y, modData, z, unpacked, sa, sb,
        left, result, two, zero, magA, magB, signA, signB, Fin.mk.injEq,
        hxa, hnz, hrem, hna, hmod, hsub, hdbl1, hdbl2]
  have hym : y.mem = x.mem := by
    dsimp only [y, modData]
    split_ifs <;> rfl
  have he : ExecWithin (w + 2) modulo x y 13 := hu.within.seq hcore
  obtain ⟨n, hn, hex⟩ := he
  refine ⟨y, ⟨n, hn, hex⟩, ?_, hym, fun i hi => hex.regs_eq (preserves hi).2.2.2.2⟩
  by_cases hb0 : b = 0
  · subst hb0
    simp [y, modData, GenericRAM.Signed.Arithmetic.eval]
  · have hnz : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
    have hmod_eq := (div_mod_nonzero (a := a) hb0).2
    change a % b = (modMagnitude a.natAbs b.natAbs sa : ℤ) at hmod_eq
    have hnonneg : ¬((modMagnitude a.natAbs b.natAbs sa : ℤ) < 0) :=
      not_lt.mpr (Nat.cast_nonneg _)
    simp only [GenericRAM.Signed.Arithmetic.eval, hmod_eq, encode, hnonneg, ↓reduceIte,
      Int.natAbs_natCast]
    dsimp only [y, modData, modMagnitude]
    simp only [hnz, ↓reduceIte]
    split_ifs <;> simp [two_mul]

end Cslib.WordRAM.Signed
