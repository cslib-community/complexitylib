/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Mathlib.Data.Nat.Log

/-!
# Polynomial-time binary ceiling logarithms

The base-two ceiling logarithm of a binary natural is computed from its bit length and a
comparison with the preceding power of two. The result is in unary, with length at most the
binary input length. Zero and one both return zero. The ordinary polynomial-time certificate
uses the existing binary size, power and comparison providers; it never expands the input
natural into a unary word.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.binary_clog_two`: ceiling logarithm from binary
  input to unary output.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem clog_two_eq (n : ℕ) : Nat.clog 2 n =
    if n ≤ 2 ^ (n.size - 1) then n.size - 1 else n.size := by
  have hlo : n.size - 1 ≤ Nat.clog 2 n := by
    have hs : n.size ≤ Nat.clog 2 n + 1 := Nat.size_le.mpr
      ((Nat.le_pow_clog (by decide : 1 < 2) n).trans_lt (by
        rw [pow_succ]
        have := Nat.two_pow_pos (Nat.clog 2 n)
        omega))
    omega
  have hhi : Nat.clog 2 n ≤ n.size := Nat.clog_le_of_le_pow (Nat.lt_size_self n).le
  split
  · rename_i h
    exact Nat.le_antisymm (Nat.clog_le_of_le_pow h) hlo
  · rename_i h
    have := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (Nat.lt_of_not_ge h)
    omega

/-- Compute the base-two ceiling logarithm of a binary natural, returning a unary counter.
The full input, intermediate power of two and output have polynomial bit cost. -/
@[fun_prop]
theorem binary_clog_two : ComputableInPolyTime (Nat.clog 2) encNat encUnary := by
  have hp : ComputableInPolyTime (fun n : ℕ => n.size - 1) encNat encUnary :=
    unary_sub.comp (binary_size.prod (const 1))
  have htest := binary_le' (id' (encIn := encNat)) (binary_two_pow.comp hp)
  convert htest.ite_decide hp binary_size using 1
  exact funext clog_two_eq

end Turing.MultiTapeTM.ComputableInPolyTime
