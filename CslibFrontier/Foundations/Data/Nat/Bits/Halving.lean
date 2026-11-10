/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Bits.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Bits
public import Mathlib.Logic.Function.Iterate

/-!
# Binary digits by repeated halving

Halving a number `n` repeatedly and recording the parity of each nonzero intermediate value yields
the little-endian binary digits `n.bits`. A machine that halves a unary counter once per round and
emits one bit per round therefore writes `n` in binary, and stops emitting once the counter reaches
zero, so any number of rounds at least `n` suffices.

## Main results

* `Nat.bits_of_pos`: the binary digits of a positive number are its parity followed by the binary
  digits of its half.
* `Nat.iterate_div_two`: halving `i` times divides by `2 ^ i`.
* `Nat.flatten_map_range_halfBit`: for `n ≤ m`, emitting the parity of every nonzero value among the
  first `m` halvings of `n` produces `n.bits`.
-/

@[expose] public section

namespace Nat

/-- The binary digits of a positive number: its remainder by two, then those of its half. -/
theorem bits_of_pos {q : ℕ} (hq : 0 < q) : q.bits = decide (q % 2 = 1) :: (q / 2).bits := by
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · have hq' : q = 2 * (q / 2) := by omega
    conv_lhs => rw [hq']
    rw [Nat.bit0_bits _ (by omega), h]
    rfl
  · have hq' : q = 2 * (q / 2) + 1 := by omega
    conv_lhs => rw [hq']
    rw [Nat.bit1_bits, h]
    rfl

/-- Halving `i` times divides by `2 ^ i`. -/
theorem iterate_div_two (n i : ℕ) : (· / 2)^[i] n = n / 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- The bit a halving machine emits at the value `k`: nothing at zero, else the parity of `k`. -/
def halfBit (k : ℕ) : List Bool := if k = 0 then [] else [decide (k % 2 = 1)]

/-- **Binary digits by repeated halving.** If `n ≤ m`, emitting `halfBit` of each of the first `m`
values `n, n / 2, n / 4, …` writes the little-endian binary digits of `n`. -/
theorem flatten_map_range_halfBit {n m : ℕ} (h : n ≤ m) :
    ((List.range m).map fun i => halfBit ((· / 2)^[i] n)).flatten = n.bits := by
  induction m generalizing n with
  | zero => simp [show n = 0 by omega]
  | succ m ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [halfBit, iterate_div_two]
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons,
        Function.iterate_zero_apply, bits_of_pos hn]
      have hrest : (List.map ((fun i => halfBit ((· / 2)^[i] n)) ∘ Nat.succ)
          (List.range m)).flatten = (n / 2).bits := by
        rw [← ih (by omega)]
        congr 1
      rw [hrest]
      simp only [halfBit, Nat.pos_iff_ne_zero.mp hn, ↓reduceIte, List.singleton_append]

end Nat
