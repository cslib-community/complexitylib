/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.Nat.Size

/-!
# Numeric bounds for binary-polynomial computations

A polynomial in the binary length of a natural number is bounded by a constant times its
value plus one. Thus every binary-polynomial computation on a natural number runs in time and
space `O(n + 1)`, independently of its output encoding. On a pair of binary naturals the
corresponding bound is `O(a + b + 1)`.

These bounds let constructible clocks and padding algorithms perform binary arithmetic while
charging for the numeric quantities they already process.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.nat_inO`: a binary-polynomial computation on one
  natural number has numeric linear bounds.
* `Turing.MultiTapeTM.ComputableInPolyTime.natPair_inO`: the bound for two natural numbers is
  linear in their sum.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Every polynomial-time computation on a binary natural has time and space bounded by
`O(n + 1)`, where `n` is its numeric value. -/
theorem nat_inO {β : Type} {encOut : β ↪ List Bool} {f : ℕ → β}
    (hf : ComputableInPolyTime f encNat encOut) :
    ComputableInO f encNat encOut (fun n => n) fun n => n := by
  obtain ⟨d, e, hf⟩ := hf.tidy.exists_degree
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le d
  exact .of_tidy (hf.inO.mono C hC hC)

/-- Every polynomial-time computation on a pair of binary naturals has time and space bounded
by `O(a + b + 1)`, where `a` and `b` are their numeric values. -/
theorem natPair_inO {β : Type} {encOut : β ↪ List Bool} {f : ℕ × ℕ → β}
    (hf : ComputableInPolyTime f (encPair encNat encNat) encOut) :
    ComputableInO f (encPair encNat encNat) encOut (fun p => p.1 + p.2)
      fun p => p.1 + p.2 := by
  obtain ⟨d, e, hf⟩ := hf.tidy.exists_degree
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le d
  have hbound (p : ℕ × ℕ) :
      ((encPair encNat encNat p).length + 1) ^ d ≤ 3 ^ d * C * (p.1 + p.2 + 1) := by
    have hleft : (encNat p.1).length ≤ (encNat (p.1 + p.2)).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using
        Nat.size_le_size (Nat.le_add_right p.1 p.2)
    have hright : (encNat p.2).length ≤ (encNat (p.1 + p.2)).length := by
      simpa only [encNat_apply, Nat.size_eq_bits_len] using
        Nat.size_le_size (Nat.le_add_left p.2 p.1)
    have hlen : (encPair encNat encNat p).length + 1 ≤
        3 * ((encNat (p.1 + p.2)).length + 1) := by
      rw [length_encPair]
      omega
    calc ((encPair encNat encNat p).length + 1) ^ d
        ≤ (3 * ((encNat (p.1 + p.2)).length + 1)) ^ d := Nat.pow_le_pow_left hlen d
      _ = 3 ^ d * ((encNat (p.1 + p.2)).length + 1) ^ d := mul_pow _ _ _
      _ ≤ 3 ^ d * (C * (p.1 + p.2 + 1)) := Nat.mul_le_mul_left _ (hC _)
      _ = 3 ^ d * C * (p.1 + p.2 + 1) := by ring
  exact .of_tidy (hf.inO.mono (3 ^ d * C) hbound hbound)

end Turing.MultiTapeTM.ComputableInPolyTime
