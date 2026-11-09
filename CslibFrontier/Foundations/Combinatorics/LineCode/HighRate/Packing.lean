/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Packing source bits into copies of a code

A table of `S` source bits is stored in copies of a code with `k` information symbols of `b` bits
each. `packingCopies S k b = S / (k * b) + 1` copies hold all source bits
(`le_packingCopies_mul`), so every source bit can be assigned its own copy, information symbol
and bit (`nonempty_embedding_packingCopies`). If every copy has `N` symbols and the code has rate
at least `P / (P + 1)`, the total storage of `N * b` bits per copy exceeds `(P + 1) / P` times
the source by at most one copy (`mul_packingCopies_mul_le`).

## Main definitions

* `Cslib.LineCode.HighRate.packingCopies`: the number of copies.

## Main results

* `Cslib.LineCode.HighRate.le_packingCopies_mul`: the copies hold all source bits.
* `Cslib.LineCode.HighRate.mul_packingCopies_mul_le`: the storage bound.
* `Cslib.LineCode.HighRate.nonempty_embedding_packingCopies`: a placement of the source bits.

## References

* Adapted from MassProduction/HighRate/Packing.lean and
  MassProduction/HighRate/CodePacking.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.LineCode.HighRate

/-- The number `S / (k * b) + 1` of copies of a code with `k` information symbols of `b` bits
used to store `S` source bits. -/
def packingCopies (S k b : ℕ) : ℕ :=
  S / (k * b) + 1

/-- If `0 < k` and `0 < b`, then `packingCopies S k b` copies with `k` information symbols of `b`
bits hold `S` bits: `S ≤ packingCopies S k b * k * b`. -/
theorem le_packingCopies_mul (S k b : ℕ) (hk : 0 < k) (hb : 0 < b) :
    S ≤ packingCopies S k b * k * b := by
  rw [packingCopies, mul_assoc, add_mul, one_mul]
  exact (Nat.lt_div_mul_add (Nat.mul_pos hk hb)).le

/-- **Storage bound.** If a code with `k` information symbols has `N` symbols with
`P * N ≤ (P + 1) * k`, then `packingCopies S k b` copies of it, with `b` bits per symbol, occupy
`packingCopies S k b * N * b` bits, and
`P * (packingCopies S k b * N * b) ≤ (P + 1) * S + P * (N * b)`: the storage exceeds `(P + 1) / P`
times the `S` source bits by at most one copy. -/
theorem mul_packingCopies_mul_le (S k N b P : ℕ) (hrate : P * N ≤ (P + 1) * k) :
    P * (packingCopies S k b * N * b) ≤ (P + 1) * S + P * (N * b) := by
  calc P * (packingCopies S k b * N * b)
        = S / (k * b) * (P * N) * b + P * (N * b) := by rw [packingCopies]; ring
    _ ≤ S / (k * b) * ((P + 1) * k) * b + P * (N * b) := by gcongr
    _ = (P + 1) * (S / (k * b) * (k * b)) + P * (N * b) := by ring
    _ ≤ (P + 1) * S + P * (N * b) := by gcongr; exact Nat.div_mul_le_self S (k * b)

/-- If `I` is nonempty and `0 < b`, the `S` source bits embed into the bits of the information
symbols `I` of `packingCopies S (Fintype.card I) b` code copies. -/
theorem nonempty_embedding_packingCopies {I : Type*} [Fintype I] (S b : ℕ)
    (hI : 0 < Fintype.card I) (hb : 0 < b) :
    Nonempty (Fin S ↪ Fin (packingCopies S (Fintype.card I) b) × I × Fin b) := by
  apply Function.Embedding.nonempty_of_card_le
  simpa only [Fintype.card_fin, Fintype.card_prod, mul_assoc] using
    le_packingCopies_mul S (Fintype.card I) b hI hb

end Cslib.LineCode.HighRate
