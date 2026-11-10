/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Common binary prefixes through exclusive or

Two naturals `A < B` agree above bit `s = (A ^^^ B).size`, i.e. on the common prefix of their
binary expansions, and the dyadic point `(2 (A / 2^s) + 1) 2^(s-1)`, the common prefix followed by
a `1`, separates them. This is the arithmetic content of the compression code in the completeness
proof of [Bogdanov and Trevisan, Claim 20][BogdanovTrevisan2006].

## Main results

* `Nat.div_two_pow_eq_iff_xor_lt`: two naturals have the same quotient by `2 ^ k` exactly when
  their exclusive or is below `2 ^ k`.
* `Nat.lt_commonPrefix_mid_le`: the split of `A < B` at their highest differing bit.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

@[expose] public section

namespace Nat

/-- Two naturals have the same quotient by `2 ^ k` exactly when their exclusive or is below
`2 ^ k`. -/
theorem div_two_pow_eq_iff_xor_lt (A B k : ℕ) : A / 2 ^ k = B / 2 ^ k ↔ A ^^^ B < 2 ^ k := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    have h1 := Nat.testBit_div_two_pow (n := k) A (i - k)
    have h2 := Nat.testBit_div_two_pow (n := k) B (i - k)
    rw [h, h2, show i - k + k = i by omega] at h1
    rw [Nat.testBit_xor, h1]
    simp
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
    have := Nat.testBit_lt_two_pow (x := A ^^^ B) (i := i + k)
      (h.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [Nat.testBit_xor] at this
    revert this
    cases A.testBit (i + k) <;> cases B.testBit (i + k) <;> simp

/-- **Splitting at the highest differing bit.** For `A < B` and `s = (A ^^^ B).size`, the two
numbers have the same quotient `Z` by `2 ^ s`, and the dyadic point `(2 Z + 1) 2^(s-1)` lies
strictly above `A` and at most `B`. -/
theorem lt_commonPrefix_mid_le {A B : ℕ} (hAB : A < B) :
    1 ≤ (A ^^^ B).size ∧ A / 2 ^ (A ^^^ B).size = B / 2 ^ (A ^^^ B).size ∧
      A < (2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) ∧
      (2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) ≤ B := by
  set s := (A ^^^ B).size with hs
  have hne : A ^^^ B ≠ 0 := fun h0 => hAB.ne (by
    simpa using (div_two_pow_eq_iff_xor_lt A B 0).mpr (by rw [h0]; norm_num))
  have hs1 : 1 ≤ s := Nat.size_pos.mpr (Nat.pos_of_ne_zero hne)
  have heq : A / 2 ^ s = B / 2 ^ s := (div_two_pow_eq_iff_xor_lt A B s).mpr (Nat.lt_size_self _)
  have hne' : A / 2 ^ (s - 1) ≠ B / 2 ^ (s - 1) := by
    intro h
    have := (div_two_pow_eq_iff_xor_lt A B (s - 1)).mp h
    have h2 := Nat.lt_size.mp (show s - 1 < s by omega)
    omega
  have hpow : 2 ^ s = 2 ^ (s - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hle : A / 2 ^ (s - 1) ≤ B / 2 ^ (s - 1) := Nat.div_le_div_right hAB.le
  have hA2 : A / 2 ^ s = A / 2 ^ (s - 1) / 2 := by rw [hpow, Nat.div_div_eq_div_mul]
  have hB2 : B / 2 ^ s = B / 2 ^ (s - 1) / 2 := by rw [hpow, Nat.div_div_eq_div_mul]
  set a' := A / 2 ^ (s - 1)
  set b' := B / 2 ^ (s - 1)
  set Z := A / 2 ^ s
  have ha' : a' = 2 * Z := by omega
  have hb' : b' = 2 * Z + 1 := by omega
  have hP : 0 < 2 ^ (s - 1) := by positivity
  have hAlt : A < (a' + 1) * 2 ^ (s - 1) := by
    have := Nat.lt_mul_div_succ A hP
    rw [mul_comm] at this; exact this
  have hBge : b' * 2 ^ (s - 1) ≤ B := Nat.div_mul_le_self B _
  refine ⟨hs1, heq, ?_, ?_⟩
  · rw [ha'] at hAlt; exact hAlt
  · rw [hb'] at hBge; exact hBge

end Nat
