/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Basic

/-!
# Ideal batched 1-out-of-2 oblivious transfer

The two-party ideal oracle for `k` parallel 1-out-of-2 oblivious transfers of values in a type
`L`. The sender (slot `0`) submits two values for each of the `k` transfers, as a function
`Fin k → Bool → L`, and receives nothing. The receiver (slot `1`) submits a choice bit for each
transfer and receives the chosen values. This is Goldreich's 1-out-of-`k` transfer
(Section 7.3.2, Eq. 7.20, p. 640) for `k = 2` over values in `L` rather than bits, invoked `k`
times in one round; the library's `ot14Spec` is the 1-out-of-4 transfer of bits.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.batchOTSpec`, `Cslib.Crypto.Protocols.MPC.batchOTAnswer`,
  `Cslib.Crypto.Protocols.MPC.batchOTWorld`: the oracle specification, its answer and its ideal
  world.
* `Cslib.Crypto.Protocols.MPC.batchOTFunctionality`: the same transfer as a two-party
  functionality, for protocols that realize it.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.MPC

/-- `k` parallel 1-out-of-2 oblivious transfers of values in `L`: slot `0` (sender) submits two
values per transfer and receives `Unit`; slot `1` (receiver) submits one choice bit per transfer
and receives the chosen values. -/
@[reducible] def batchOTSpec (k : ℕ) (L : Type) : MultiOracleSpec where
  Op := Unit
  arity _ := 2
  Query _ := Fin.cases (Fin k → Bool → L) (fun _ => Fin k → Bool)
  Answer _ := Fin.cases Unit (fun _ => Fin k → L)

/-- The answer of `batchOTSpec k L` on query `q`: `()` to the sender and the values
`q 0 j (q 1 j)` to the receiver. -/
def batchOTAnswer {k : ℕ} {L : Type} (q : (s : Fin 2) → (batchOTSpec k L).Query () s) (s : Fin 2) :
    (batchOTSpec k L).Answer () s :=
  Fin.cases () (fun _ j => q 0 j (q 1 j)) s

/-- The ideal memoryless world of `batchOTSpec k L`. -/
def batchOTWorld (k : ℕ) (L : Type) : MultiOracleWorld (batchOTSpec k L) :=
  fun _ q => pure (batchOTAnswer q)

/-- `batchOTSpec k L` as a two-party functionality: the inputs are the query parts of the two
slots and the outputs are their answer parts. -/
def batchOTFunctionality (k : ℕ) (L : Type) :
    Functionality 2 ((batchOTSpec k L).Query ()) ((batchOTSpec k L).Answer ()) :=
  .ofDeterministic batchOTAnswer

end Cslib.Crypto.Protocols.MPC
