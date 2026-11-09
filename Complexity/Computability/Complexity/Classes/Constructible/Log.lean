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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCombinators
import Complexity.Foundations.Data.Nat.SqrtLog.Factor

/-!
# Logarithmic inflation of constructible clocks

A polynomial-time computation on the binary representation of a natural number `m` takes
time polynomial in its number of digits, hence `O(m + 1)`. Consequently a binary-polynomial
transformation that does not decrease a time-constructible clock preserves time constructibility.
The transformation need only dominate the values taken by that clock.

In particular, a clock can be multiplied by a positive binary-polynomial function of its own
value, such as one plus its binary length, or the fourth root `⌊√⌊√⌊log₂ f⌋⌋⌋` of its logarithm.
These are logarithmic or smaller overheads, below multiplying the clock by the input length when
it is polynomially bounded. These closure lemmas use the library's certified machines and do not
assume a faster universal simulator.

## Main results

* `Cslib.Complexity.TimeConstructible.comp_of_computableInPolyTime`: efficient binary
  postprocessing preserves time constructibility when it does not decrease the clock.
* `Cslib.Complexity.TimeConstructible.mul_comp_of_computableInPolyTime`: so does multiplying the
  clock by a positive binary-polynomial function of its value.
* `Cslib.Complexity.TimeConstructible.mul_size_succ`: a time-constructible `f` remains
  time-constructible after replacing `f n` by `f n * (Nat.size (f n) + 1)`.
* `Cslib.Complexity.TimeConstructible.mul_sqrt_sqrt_log_two`: likewise for
  `f n * ⌊√⌊√⌊log₂ (f n)⌋⌋⌋` when `2 ≤ f n`.
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
  have h := hg.nat_inO.comp hf.computableInO
  refine TimeConstructible.of_computableInO 2 h
    (s := fun n => f n + f n) (fun x => ?_) fun _ => le_rfl
  have := hfg x.length
  omega

/-- Multiplying a time-constructible clock by a binary-polynomial function of its value preserves
time constructibility, provided that function is positive on the values of the clock. -/
theorem TimeConstructible.mul_comp_of_computableInPolyTime {f g : ℕ → ℕ}
    (hf : TimeConstructible f) (hg : ComputableInPolyTime g encNat encNat)
    (hfg : ∀ n, 1 ≤ g (f n)) : TimeConstructible fun n => f n * g (f n) :=
  hf.comp_of_computableInPolyTime (g := fun m => m * g m)
    (ComputableInPolyTime.binary_mul' ComputableInPolyTime.id' hg) fun n =>
    Nat.le_mul_of_pos_right _ (hfg n)

/-- Multiplying a time-constructible clock by one plus its binary length preserves
time constructibility, including at the zero value of the clock. -/
theorem TimeConstructible.mul_size_succ {f : ℕ → ℕ} (hf : TimeConstructible f) :
    TimeConstructible fun n => f n * (Nat.size (f n) + 1) := by
  have hsize : ComputableInPolyTime Nat.size encNat encNat := by
    have h := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.encoding_length encNat)
    simpa only [Function.comp_def, encNat_apply, Nat.size_eq_bits_len] using h
  exact hf.mul_comp_of_computableInPolyTime (g := fun m => Nat.size m + 1)
    (ComputableInPolyTime.binary_add.comp (hsize.prod (ComputableInPolyTime.const 1)))
    fun _ => Nat.succ_pos _

/-- Multiplying a time-constructible clock `f ≥ 2` by the fourth root `⌊√⌊√⌊log₂ f⌋⌋⌋` of its
logarithm preserves time constructibility. -/
theorem TimeConstructible.mul_sqrt_sqrt_log_two {f : ℕ → ℕ} (hf : TimeConstructible f)
    (hf₂ : ∀ n, 2 ≤ f n) :
    TimeConstructible fun n => f n * Nat.sqrt (Nat.sqrt (Nat.log 2 (f n))) :=
  hf.mul_comp_of_computableInPolyTime (g := fun m => Nat.sqrt (Nat.sqrt (Nat.log 2 m)))
    (ComputableInPolyTime.binary_sqrt.comp (ComputableInPolyTime.binary_sqrt.comp
      (ComputableInPolyTime.unary_to_binary.comp ComputableInPolyTime.binary_log_two)))
    fun n => Nat.one_le_sqrt_sqrt_log_two (hf₂ n)

end Cslib.Complexity
