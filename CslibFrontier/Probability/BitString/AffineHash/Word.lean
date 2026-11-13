/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Probability.BitString.AffineHash

import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Word-level Boolean affine hashes and zero tests

An affine hash `x ↦ A x + b` to `k` bits of `n`-bit strings
(`Cslib.BitString.LinearHash.affineHash`) has a `(k * n + k)`-bit seed: the `k` rows of the matrix
`A`, followed by the `k`-bit offset `b`. `packAffineSeed` and `unpackAffineSeed` convert between
`(Fin k → BitString n) × BitString k` and words (`List Bool`), padding missing seed bits with
`false` and ignoring extra trailing bits; on fixed-length bit strings they induce the equivalence
`affineSeedEquiv`.

`wordAffineHash` evaluates `x ↦ A x + b` on words, agreeing with `affineHash` on `List.ofFn` inputs
(`wordAffineHash_eq_ofFn`). `hashZero` decides whether the affine hash sends the `n`-bit view of a
word to zero (`hashZero_eq_true_iff`, `hashZero_ofFn`), providing Arthur's hash test in the set
lower bound protocol of Goldwasser and Sipser [GoldwasserSipser1986]
[Arora and Barak, Section 8.2][AroraBarak09] (`Cslib.Complexity.SetLowerBound.verifier`) and in the
public-coin emulation of private coins (`Cslib.Complexity.Emulation.check`). Plain polynomial-time
certificates for `wordAffineHash` and `hashZero` are proved in
`CslibFrontier.Computability.Probabilistic.AffineHash`.

## Main definitions

* `Cslib.BitString.LinearHash.packAffineSeed`, `Cslib.BitString.LinearHash.unpackAffineSeed`:
  total word-level packing and unpacking of affine seeds `(A, b)`.
* `Cslib.BitString.LinearHash.affineSeedEquiv`: equivalence between `BitString (k * n + k)` and
  `(Fin k → BitString n) × BitString k`.
* `Cslib.BitString.LinearHash.wordAffineHash`: total word-level Boolean affine hash `x ↦ A x + b`.
* `Cslib.BitString.LinearHash.hashZero`: word-level zero test deciding `A x + b = 0` on the `n`-bit
  view of `x`.

## Main results

* `Cslib.BitString.LinearHash.unpackAffineSeed_packAffineSeed`,
  `Cslib.BitString.LinearHash.packAffineSeed_unpackAffineSeed`: round-trip identities for affine
  seed words.
* `Cslib.BitString.LinearHash.wordAffineHash_eq_ofFn`: exact agreement between `wordAffineHash` and
  `affineHash` on unpacked seeds.
* `Cslib.BitString.LinearHash.hashZero_eq_true_iff`,
  `Cslib.BitString.LinearHash.hashZero_ofFn`: exact agreement between `hashZero` and the kernel test
  `affineHash s x = 0`.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Section 4.2, Theorem 4.5, pp. 21–25][HHRVW2020]
-/

public section

namespace Cslib.BitString.LinearHash

/-- Pack an affine seed `(A, b) : (Fin k → BitString n) × BitString k` as a `(k * n + k)`-bit
word: the `k` rows of `A`, then the offset `b`. -/
def packAffineSeed {k n : ℕ} (s : (Fin k → BitString n) × BitString k) : List Bool :=
  List.ofFn (blocksEquiv.symm s.1) ++ List.ofFn s.2

/-- Unpack a word into an affine seed `(A, b) : (Fin k → BitString n) × BitString k`, padding
missing bits with `false` and ignoring extra trailing bits. -/
def unpackAffineSeed (k n : ℕ) (seed : List Bool) :
    (Fin k → BitString n) × BitString k :=
  (block (ofList (k * n) (seed.take (k * n))), ofList k (seed.drop (k * n)))

@[simp] theorem length_packAffineSeed {k n : ℕ} (s : (Fin k → BitString n) × BitString k) :
    (packAffineSeed s).length = k * n + k := by
  unfold packAffineSeed
  simp

@[simp] theorem unpackAffineSeed_packAffineSeed {k n : ℕ}
    (s : (Fin k → BitString n) × BitString k) :
    unpackAffineSeed k n (packAffineSeed s) = s := by
  unfold unpackAffineSeed packAffineSeed
  ext i j
  · simp only [List.take_left' (List.length_ofFn (f := blocksEquiv.symm s.1)), ofList_ofFn]
    exact congrFun (congrFun (blocksEquiv.apply_symm_apply s.1) i) j
  · simp [List.drop_left' (List.length_ofFn (f := blocksEquiv.symm s.1))]

theorem packAffineSeed_unpackAffineSeed {k n : ℕ} {seed : List Bool}
    (hseed : seed.length = k * n + k) :
    packAffineSeed (unpackAffineSeed k n seed) = seed := by
  have htake : (seed.take (k * n)).length = k * n := by simp [hseed]
  have hdrop : (seed.drop (k * n)).length = k := by simp [hseed]
  unfold packAffineSeed unpackAffineSeed
  dsimp only
  rw [blocksEquiv_symm_block, ofFn_ofList htake, ofFn_ofList hdrop, List.take_append_drop]

/-- Packing an affine seed `(A, b)` concatenates the `k` row words of `A` followed by `b`. -/
theorem packAffineSeed_eq_flatten_append {k n : ℕ} (s : (Fin k → BitString n) × BitString k) :
    packAffineSeed s = (List.ofFn fun i => List.ofFn (s.1 i)).flatten ++ List.ofFn s.2 := by
  unfold packAffineSeed
  rw [ofFn_blocksEquiv_symm]

/-- Row `i` of `unpackAffineSeed k n seed` is row `i` of width `n` of the matrix prefix. -/
theorem ofFn_unpackAffineSeed_fst {k n : ℕ} (seed : List Bool) (i : Fin k) :
    List.ofFn ((unpackAffineSeed k n seed).1 i) = listRow n i.val (seed.take (k * n)) := by
  unfold unpackAffineSeed
  exact (listRow_eq_ofFn n i (seed.take (k * n))).symm

/-- The offset of `unpackAffineSeed k n seed` is the `k`-bit prefix after the `k * n` matrix
bits. -/
theorem ofFn_unpackAffineSeed_snd {k n : ℕ} (seed : List Bool) :
    List.ofFn (unpackAffineSeed k n seed).2 = listRow k 0 (seed.drop (k * n)) := by
  unfold unpackAffineSeed
  exact (listRow_zero k (seed.drop (k * n))).symm

/-- The seed of an affine hash to `k` bits of `n`-bit strings, read from `k * n + k` bits: the `k`
rows of the matrix, then the offset. -/
def affineSeedEquiv (k n : ℕ) : BitString (k * n + k) ≃ (Fin k → BitString n) × BitString k where
  toFun r := unpackAffineSeed k n (List.ofFn r)
  invFun s := ofList (k * n + k) (packAffineSeed s)
  left_inv r := by
    dsimp only
    rw [packAffineSeed_unpackAffineSeed List.length_ofFn, ofList_ofFn]
  right_inv s := by
    dsimp only
    rw [ofFn_ofList (length_packAffineSeed s), unpackAffineSeed_packAffineSeed]

@[simp] theorem affineSeedEquiv_apply {k n : ℕ} (r : BitString (k * n + k)) :
    affineSeedEquiv k n r = unpackAffineSeed k n (List.ofFn r) := by
  rfl

@[simp] theorem ofFn_affineSeedEquiv_symm {k n : ℕ} (s : (Fin k → BitString n) × BitString k) :
    List.ofFn ((affineSeedEquiv k n).symm s) = packAffineSeed s := by
  exact ofFn_ofList (length_packAffineSeed s)

/-- Word-level Boolean affine hash `x ↦ A x + b`, reading `k * input.length` matrix bits followed
by `k` shift bits. -/
@[expose] def wordAffineHash (k : ℕ) (seed input : List Bool) : List Bool :=
  listXor k [wordHash k (seed.take (k * input.length)) input, seed.drop (k * input.length)]

@[simp] theorem length_wordAffineHash (k : ℕ) (seed input : List Bool) :
    (wordAffineHash k seed input).length = k := by
  simp [wordAffineHash]

/-- On a fixed-width input, `wordAffineHash` computes `affineHash` on the unpacked seed. -/
theorem wordAffineHash_eq_ofFn {k n : ℕ} (seed : List Bool) (x : BitString n) :
    wordAffineHash k seed (List.ofFn x) =
      List.ofFn (affineHash (unpackAffineSeed k n seed) x) := by
  unfold unpackAffineSeed
  simp only [wordAffineHash, List.length_ofFn, wordHash_eq_ofFn, listXor_pair, ofList_ofFn,
    affineHash]

/-- Whether the affine hash to `k` bits of `n`-bit strings with seed `seed` sends the `n`-bit view
of `x` to zero, padding missing bits with `false` and ignoring extra trailing bits. -/
@[expose] def hashZero (k n : ℕ) (seed x : List Bool) : Bool :=
  !(wordAffineHash k seed (listRow n 0 x)).any fun b => b

/-- On arbitrary words, `hashZero` decides whether the unpacked affine hash sends the `n`-bit view
of `x` to zero. -/
theorem hashZero_eq_true_iff (k n : ℕ) (seed x : List Bool) :
    hashZero k n seed x = true ↔
      affineHash (unpackAffineSeed k n seed) (ofList n x) = 0 := by
  rw [hashZero, listRow_zero, wordAffineHash_eq_ofFn, not_any_ofFn_eq_true_iff]

/-- On strings of the right lengths, `hashZero` decides whether the affine hash given by the seed
sends the string to zero. -/
theorem hashZero_ofFn {k n : ℕ} (r : BitString (k * n + k)) (x : BitString n) :
    hashZero k n (List.ofFn r) (List.ofFn x) = true ↔
      affineHash (affineSeedEquiv k n r) x = 0 := by
  rw [hashZero_eq_true_iff, ofList_ofFn, affineSeedEquiv_apply]

end Cslib.BitString.LinearHash
