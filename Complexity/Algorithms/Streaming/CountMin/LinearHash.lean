/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Probability.BitString.LinearHash

/-!
# Binary-matrix hashes for Count-Min tables

The existing binary linear hash family sends an `n`-bit item to `m` bits. Numbering that output
with `BitString.equivFin m` gives a concrete universal family into `Fin (2 ^ m)`, suitable for
the stored counters of a Count-Min table. The numbering is injective, so it does not change any
collision event or require a stronger randomness assumption.

A row seed consists of `m * n` bits. Sampling a tuple of these seeds uniformly gives the
independent row seeds used by the Count-Min accuracy theorem. The seed-size statement below
counts the seed space; hash evaluation and machine running times are separate obligations.

## Main definitions

* `Cslib.CountMin.indexedHash`: binary linear hashing with a finite bucket index as output.

## Main results

* `Cslib.CountMin.isTwoUniversal_indexedHash`: the concrete family is universal.
* `Cslib.CountMin.card_indexedHash_seed`: a row has `2 ^ (m * n)` possible seeds.

## References

* [G. Cormode, S. Muthukrishnan, *An Improved Data Stream Summary: The Count-Min Sketch and its
  Applications*, Sections 3 and 4.1][CormodeMuthukrishnan2005]
* [I. Haitner, S. Vadhan, *The Many Entropies in One-Way Functions*][HaitnerVadhan2017],
  Section 2.4.1, the Boolean-matrix example following Definition 4.
-/

@[expose] public section

namespace Cslib.CountMin

open Probability

/-- Hash an `n`-bit item to one of `2 ^ m` numbered buckets using a binary `m × n` matrix. -/
def indexedHash {n m : ℕ} (rows : Fin m → BitString n) (input : BitString n) : Fin (2 ^ m) :=
  BitString.equivFin m (BitString.LinearHash.hash rows input)

/-- Numbering the output bits leaves every collision event unchanged. -/
@[simp] theorem indexedHash_eq_iff {n m : ℕ} (rows : Fin m → BitString n)
    (x y : BitString n) :
    indexedHash rows x = indexedHash rows y ↔
      BitString.LinearHash.hash rows x = BitString.LinearHash.hash rows y :=
  (BitString.equivFin m).injective.eq_iff

/-- Uniform binary matrices give a universal family of Count-Min bucket indices. -/
theorem isTwoUniversal_indexedHash (n m : ℕ) :
    IsTwoUniversal (PMF.uniformOfFintype (Fin m → BitString n))
      (indexedHash (n := n) (m := m)) := by
  intro x y hxy
  simpa only [indexedHash_eq_iff, Fintype.card_fin, BitString.card] using
    BitString.LinearHash.isTwoUniversal n m x y hxy

/-- A binary-matrix row seed has `m * n` Boolean coordinates. -/
theorem card_indexedHash_seed (n m : ℕ) :
    Fintype.card (Fin m → BitString n) = 2 ^ (m * n) := by
  rw [Fintype.card_fun, BitString.card, Fintype.card_fin, ← pow_mul, Nat.mul_comm]

end Cslib.CountMin
