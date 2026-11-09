/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P.WordRAM
public import Complexity.Algorithms.WordRAM.AKS
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# PRIMES is in `P`

The primes, given in binary, are decidable in deterministic polynomial time
[Agrawal, Kayal, Saxena][AKS2004]. The decider is the AKS algorithm on the word RAM
(`Cslib.Algorithms.WordRAM.AKS.decidesInTime`), with `n` placed in one word, simulated by a
multi-tape Turing machine through `Cslib.WordRAM.Program.DecidesInTime.mem_P_of_width`. The
simulating machine chooses the word size `8 (|n| + 1)` from the length `|n|` of the binary
encoding, and the word-RAM program runs within a polynomial in `|n|` instructions
(`Cslib.Algorithms.WordRAM.AKS.polynomiallyBounded_time`).

The algorithm uses the integer thresholds `⌈log₂ n⌉` in place of `log₂ n`
(`Cslib.AKS.PassesUpTo`); its correctness is Theorem 4.1 of the paper
(`Cslib.AKS.prime_iff_passesUpTo_numTestsNat`).

## Main results

* `Cslib.Complexity.primes_mem_P`: the primes are in `P`, for the binary encoding `encNat`.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.WordRAM Turing.MultiTapeTM

/-- **PRIMES is in `P`** [Agrawal, Kayal, Saxena][AKS2004]: primality of naturals given by their
binary digits is decidable in polynomial time. -/
theorem primes_mem_P : {n : ℕ | n.Prime} ∈ P encNat :=
  Algorithms.WordRAM.AKS.decidesInTime.mem_P_of_width checkedOp_polyTime
    (width := fun n => 8 * ((encNat n).length + 1))
    (ComputableInPolyTime.unary_mul' (.const 8)
      (ComputableInPolyTime.unary_add' (ComputableInPolyTime.encoding_length _) (.const 1)))
    (fun n => by simp [encNat_apply, Nat.size_eq_bits_len])
    (fun n => inputFits_of_length_encList_le (by simp; omega)) (by fun_prop)
    ((PolyBounded.of_polynomiallyBounded _
      (Algorithms.WordRAM.AKS.polynomiallyBounded_time.add (.const 1))).mono
      fun n => by simp [encNat_apply, Nat.size_eq_bits_len])

end Cslib.Complexity
