/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration

/-!
# Native operator reversal

Backward quarter queries read reversed projected operands. Their numeric
operator indices must be reversed before the corresponding forward full-width
recovery. This module charges that reversal rather than treating list reversal
or packed witness conversion as a free host operation.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Quarter

open Cslib.WordRAM

/-- Accumulator for the reversed packed index. -/
abbrev reversed : Fin 32 := 21

/-- One bit of actual index reversal. -/
@[expose] def reverseBody : Code .standard 32 := ram[
  bit ← bits % two; reversed ← reversed * two; reversed ← reversed + bit;
  bits ← bits / two; position ← position + one ]

/-- Reverse exactly `count` bits, including zero bits at either end. -/
@[expose] def reverseOperators : Code .standard 32 :=
  .seq (ram[ bits ← operators; reversed ← #0; position ← #0; one ← #1; two ← #2 ])
    (.loop (.lt position count) reverseBody)

private def reverseAcc : ℕ → ℕ → ℕ → ℕ
  | 0, _, a => a
  | n + 1, v, a => reverseAcc n (v / 2) (2 * a + v % 2)

private theorem reverseAcc_eq (n v a : ℕ) :
    reverseAcc n v a = 2 ^ n * a + encode (decode n v).reverse := by
  induction n generalizing v a with
  | zero => simp [reverseAcc, decode, encode]
  | succ n ih =>
    have hrem : v % 2 = (decide (v % 2 = 1)).toNat := by
      have := Nat.mod_lt v (by decide : 0 < 2)
      by_cases he : v % 2 = 1
      · simp [he]
      · have hz : v % 2 = 0 := by omega
        simp [hz]
    have encode_append (bs cs : List Bool) :
        encode (bs ++ cs) = encode bs + 2 ^ bs.length * encode cs := by
      induction bs with
      | nil => simp [encode]
      | cons b bs ih => simp only [List.cons_append, encode, ih, List.length_cons, pow_succ]; ring
    rw [reverseAcc, ih, decode, List.reverse_cons, encode_append]
    simp only [List.length_reverse, decode_length, encode, Nat.mul_zero, Nat.add_zero, pow_succ]
    rw [← hrem]
    ring

/-- Native reversal of every packed operator word, with no overflow. The bound
fits intermediate accumulator values, not merely the final reversed word. -/
theorem reverseOperators_exec {W n v : ℕ} (x : Data 32)
    (hc : x.regs count = n) (hv : x.regs operators = v)
    (hfv : Fits W v) (hfit : Fits W (2 ^ n + n + 3)) :
    ∃ y, ExecWithin W reverseOperators x y (7 * n + 7) ∧
      y.regs reversed = encode (decode n v).reverse ∧ y.mem = x.mem := by
  have hpositive : 0 < 2 ^ n := Nat.two_pow_pos n
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  let z := x.set bits v |>.set reversed 0 |>.set position 0 |>.set one 1 |>.set two 2
  have heSetup : ExecWithin (B := .standard) W
      (ram[ bits ← operators; reversed ← #0; position ← #0; one ← #1; two ← #2 ]) x z 5 := by
    ram_eval [z, hv, h1, h2, bits, operators, reversed, position, one, two, Fin.mk.injEq]
  let I (y : Data 32) : Prop :=
    y.regs count = n ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs position ≤ n ∧
    y.regs bits ≤ v ∧ y.regs reversed < 2 ^ y.regs position ∧
    reverseAcc (n - y.regs position) (y.regs bits) (y.regs reversed) = reverseAcc n v 0 ∧
    y.mem = x.mem
  have hi : I z := by
    simp [I, z, hc, bits, reversed, position, one, two, count]
  have step (y : Data 32) (hy : I y) (ht : (Cond.lt position count).Holds y) :
      ∃ u, ExecWithin W reverseBody y u 5 ∧ I u ∧ n - u.regs position < n - y.regs position := by
    obtain ⟨yc, yo, yt, yj, yb, yr, yacc, ym⟩ := hy
    have hj : y.regs position < n := by simpa only [Cond.holds_lt, yc] using ht
    have hrem := Nat.mod_lt (y.regs bits) (by decide : 0 < 2)
    have hpow : 2 * 2 ^ y.regs position ≤ 2 ^ n := by
      simpa only [pow_succ, Nat.mul_comm] using
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt hj))
    have hr2 : Fits W (y.regs reversed * 2) := hfit.of_le (by omega)
    have hrb : Fits W (y.regs reversed * 2 + y.regs bits % 2) := hfit.of_le (by omega)
    have hb : Fits W (y.regs bits % 2) := hfit.of_le (by omega)
    have hd : Fits W (y.regs bits / 2) := hfv.of_le ((Nat.div_le_self _ _).trans yb)
    have hp : Fits W (y.regs position + 1) := hfit.of_le (by omega)
    let u := y.set bit (y.regs bits % 2) |>.set reversed (y.regs reversed * 2)
      |>.set reversed (y.regs reversed * 2 + y.regs bits % 2)
      |>.set bits (y.regs bits / 2) |>.set position (y.regs position + 1)
    have he : ExecWithin W reverseBody y u 5 := by
      ram_eval [reverseBody, u, yo, yt, hr2, hrb, hb, hd, hp,
        bit, bits, reversed, position, one, two, Fin.mk.injEq]
    refine ⟨u, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [u, Data.set_regs, Data.set_mem, Function.update_apply,
        bit, bits, reversed, position, one, two, count, ↓reduceIte]
      · exact yc
      · exact yo
      · exact yt
      · change y.regs position + 1 ≤ n
        omega
      · exact (Nat.div_le_self _ _).trans yb
      · change y.regs reversed * 2 + y.regs bits % 2 < 2 ^ (y.regs position + 1)
        rw [pow_succ]; omega
      · have hn : n - y.regs position = (n - (y.regs position + 1)) + 1 := by omega
        rw [hn, reverseAcc] at yacc
        simpa only [Nat.mul_comm] using yacc
      · exact ym
    · simp only [u, Data.set_regs, Function.update_self]; omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => n - y.regs position) step hi
  have hj : y.regs position = n := by
    have := hy.2.2.2.1
    simp only [Cond.holds_lt, hy.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.2.2.2.2.2.2.2⟩
  · apply (heSetup.seq he).mono
    have hz : z.regs position = 0 := by simp +decide [z, position, one, two]
    rw [hz]; omega
  · have h := hy.2.2.2.2.2.2.1
    rw [hj, Nat.sub_self, reverseAcc, reverseAcc_eq, Nat.mul_zero, Nat.zero_add] at h
    exact h

end Cslib.Cryptanalysis.AddXNOR.Native.Quarter
