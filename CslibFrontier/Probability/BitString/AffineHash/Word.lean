/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.BitString.AffineHash

import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Affine hashes of bit strings read from words

An affine hash `x ↦ A x + b` to `m` bits of strings of `M` bits
(`Cslib.BitString.LinearHash.affineHash`) has a seed of `m * M + m` bits: the `m` rows of the
matrix `A`, then the offset `b` (`Cslib.Complexity.SetLowerBound.seedEquiv`). The test whether
the hash sends a string to zero, `Cslib.Complexity.SetLowerBound.hashZero`, works on words (lists
of bits). On strings of the right lengths it agrees with the hash
(`Cslib.Complexity.SetLowerBound.hashZero_ofFn`). Its polynomial-time certificate,
`Cslib.Complexity.SetLowerBound.computableInPolyTime_hashZero`, is in
`CslibFrontier.Computability.Probabilistic.AffineHash`.

Arthur's test in the set lower bound protocol of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09] (`Cslib.Complexity.SetLowerBound.verifier`) and in
the public-coin emulation of private coins (`Cslib.Complexity.Emulation.check`) is this zero test.
The declarations keep the `Cslib.Complexity.SetLowerBound` namespace of the protocol that
introduced them.

## Main definitions

* `Cslib.Complexity.SetLowerBound.seedEquiv`: the seed of an affine hash read from a bit string.
* `Cslib.Complexity.SetLowerBound.hashZero`: whether the affine hash sends a word to zero.

## Main results

* `Cslib.Complexity.SetLowerBound.hashZero_ofFn`: on strings, `hashZero` decides whether the
  affine hash sends the string to zero.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.SetLowerBound

/-- The seed of an affine hash to `m` bits of strings of `M` bits, read from `m * M + m` bits: the
rows of the matrix, then the offset. -/
def seedEquiv (m M : ℕ) : BitString (m * M + m) ≃ (Fin m → BitString M) × BitString m :=
  (Fin.appendEquiv (m * M) m).symm.trans (BitString.blocksEquiv.prodCongr (Equiv.refl _))

/-- Whether the affine hash to `m` bits of strings of `M` bits with seed `seed` sends `x` to zero,
computed on words (`Cslib.BitString.LinearHash.wordHash`): the hash of the matrix part of the seed
is the offset part. -/
def hashZero (m M : ℕ) (seed x : List Bool) : Bool :=
  !(List.zipWith Bool.xor (BitString.LinearHash.wordHash m seed x)
    (BitString.listRow m M seed)).any fun b => b

/-- On strings of the right lengths, `hashZero` decides whether the affine hash given by the seed
sends the string to zero. -/
theorem hashZero_ofFn {m M : ℕ} (r : BitString (m * M + m)) (x : BitString M) :
    hashZero m M (List.ofFn r) (List.ofFn x) = true ↔
      BitString.LinearHash.affineHash (seedEquiv m M r) x = 0 := by
  have hoffset : BitString.listRow m M (List.ofFn r) =
      List.ofFn ((Fin.appendEquiv _ _).symm r).2 := by
    rw [List.ofFn_add, BitString.listRow, Nat.mul_comm M,
      List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn]
    rfl
  have hhash : BitString.LinearHash.wordHash m (List.ofFn r) (List.ofFn x) =
      List.ofFn (BitString.LinearHash.hash
        (BitString.block ((Fin.appendEquiv _ _).symm r).1) x) := by
    rw [BitString.LinearHash.wordHash_eq_ofFn, List.ofFn_add, BitString.ofList_ofFn_append]
    rfl
  rw [hashZero, hhash, hoffset, ← BitString.ofFn_add, BitString.not_any_ofFn_eq_true_iff]
  rfl

end Cslib.Complexity.SetLowerBound
