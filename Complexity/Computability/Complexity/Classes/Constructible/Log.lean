/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Data.Nat.Size
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Logarithmic inflation of constructible clocks

A polynomial-time computation on the binary representation of a natural number `m` takes
time polynomial in its number of digits, hence `O(m + 1)`. Consequently a binary-polynomial
transformation that does not decrease a time-constructible clock preserves time constructibility.
The transformation need only dominate the values taken by that clock.

In particular, a clock can be multiplied by one plus its binary length. This is a logarithmic
overhead, smaller than multiplying it by the input length when the clock is polynomially bounded.
These closure lemmas use the library's certified machines and do not assume a faster universal
simulator.

## Main results

* `Cslib.Complexity.TimeConstructible.comp_of_computableInPolyTime`: efficient binary
  postprocessing preserves time constructibility when it does not decrease the clock.
* `Cslib.Complexity.TimeConstructible.mul_size_succ`: a time-constructible `f` remains
  time-constructible after replacing `f n` by `f n * (Nat.size (f n) + 1)`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Binary-polynomial postprocessing of a time-constructible bound is time-constructible,
provided the transformed clock dominates the original one. The cost polynomial in the binary
length of `f n` is absorbed in `O(f n + 1)` before composition. -/
theorem TimeConstructible.comp_of_computableInPolyTime {f g : ℕ → ℕ}
    (hf : TimeConstructible f) (hg : ComputableInPolyTime g encNat encNat)
    (hfg : ∀ n, f n ≤ g (f n)) : TimeConstructible fun n => g (f n) := by
  have h := hg.nat_inO.tidy.comp hf.computableInO.tidy
  refine TimeConstructible.of_computableInO 2 (.of_tidy h)
    (s := fun n => f n + f n) (fun x => ?_) fun _ => le_rfl
  have := hfg x.length
  omega

/-- Multiplying a time-constructible clock by one plus its binary length preserves
time constructibility, including at the zero value of the clock. -/
theorem TimeConstructible.mul_size_succ {f : ℕ → ℕ} (hf : TimeConstructible f) :
    TimeConstructible fun n => f n * (Nat.size (f n) + 1) := by
  have hsize : ComputableTidilyInPolyTime Nat.size encNat encNat := by
    have h := ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.encoding_length encNat)
    simpa only [Function.comp_def, encNat_apply, Nat.size_eq_bits_len] using h
  have hg : ComputableInPolyTime (fun m : ℕ => m * (Nat.size m + 1)) encNat encNat := by
    apply ComputableInPolyTime.of_tidy
    exact ComputableTidilyInPolyTime.binary_mul'
      ComputableTidilyInPolyTime.id'
      (ComputableTidilyInPolyTime.binary_add' hsize (ComputableTidilyInPolyTime.const 1))
  exact hf.comp_of_computableInPolyTime hg fun n =>
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

end Cslib.Complexity
