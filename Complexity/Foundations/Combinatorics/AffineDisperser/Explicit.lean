/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.AffineDisperser.AffineSubspace
public import Complexity.Foundations.Combinatorics.AffineDisperser.BinaryField
public import Complexity.Foundations.Combinatorics.AffineDisperser.Bits
public import Complexity.Foundations.Data.Nat.Prime
public import Mathlib.Algebra.BigOperators.Fin
import Complexity.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Data.List.Nodup

/-!
# An explicit affine disperser

For every input length `N` we fix the parameters of Ben-Sasson and Kopparty's construction
explicitly. With `ℓ = ⌊log₂ N⌋`:

* `L = ⌊ℓ / 3⌋` (`Cslib.AffineDisperser.Explicit.primeBound`);
* the field degree `n` is the product of the primes chosen greedily, in increasing order, from
  the primes in `(L, 4 L]` with product at most `N / (ℓ + 1) ^ 2`
  (`Cslib.AffineDisperser.Explicit.degreePrimes`, `Cslib.AffineDisperser.Explicit.fieldDegree`);
* `F = 𝔽_{2 ^ n}` with the monomial basis in roots of the irreducible polynomials of least code of
  the prime degrees (`Cslib.AffineDisperser.compositeBasis`); each of these polynomials is found
  by an exhaustive search over fewer than `2 ^ (4 L + 1) ≤ 2 N ^ (4 / 3)` codes;
* `r = ⌊N / n⌋` blocks of `n` bits, read from the first `r n` input bits, block after block, each
  block in the mixed-radix order of the monomials (`Cslib.AffineDisperser.explicitPos`);
* `t = ℓ + 1` and `μ = 1`.

The function `Cslib.AffineDisperser.explicitDisperser N : BitString N → Bool` is
`traceSym 1 r t` on these blocks. Every prime factor of `n` exceeds `L`, so proper subfields of
`F` have at most `2 ^ s` elements, `s = ⌊n / (L + 1)⌋`, and the function is nonconstant on every
affine subspace of `BitString N` of dimension greater than
`d(N) = N - r n + r * max (r + 1) s + r * (r + 1) + n t + ⌊n r / t⌋`
(`Cslib.AffineDisperser.exists_explicitDisperser_ne`), so it is an affine disperser for dimension
`d(N) + 1` (`Cslib.AffineDisperser.isAffineDisperser_explicitDisperser`). Downstream, in the
computability layer, the function is shown not to depend on the roots chosen for the basis
(`Cslib.AffineDisperser.traceSymBits_rootBasis_eq_explicitDisperser`) and to be computable in
polynomial time (`Cslib.AffineDisperser.computableInPolyTime_explicitDisperser`).

Ben-Sasson and Kopparty take `n` prime and reach dimension `6 N ^ (4 / 5)`
[BenSassonKopparty2012]; the field then needs an irreducible polynomial of large prime degree,
which exhaustive search cannot find in polynomial time. The composite degree keeps every search
small at the price of the subfield term `r s ≤ N / (L + 1)`, so our threshold is `O(N / log N)`
(`Cslib.AffineDisperser.eventually_explicitThreshold_le`). This is far from the best explicit
dispersers known: Li's dispersers work for dimension `O(log N)` [Li2023].

## Main definitions

* `Cslib.AffineDisperser.Explicit.degreePrime`: the `j`-th prime of the field degree on `N` bits.
* `Cslib.AffineDisperser.Explicit.numBlocks`: the number of blocks `r = ⌊N / n⌋`.
* `Cslib.AffineDisperser.Explicit.symDegree`: the degree `t = ⌊log₂ N⌋ + 1` of the elementary
  symmetric polynomial.
* `Cslib.AffineDisperser.Explicit.subfieldExp`: the subfield exponent `s = ⌊n / (L + 1)⌋`.
* `Cslib.AffineDisperser.ExplicitField`: the field `𝔽_{2 ^ n}` of the explicit disperser on `N`
  bits.
* `Cslib.AffineDisperser.ExplicitMonomial`: the monomials indexing the basis of
  `ExplicitField N`.
* `Cslib.AffineDisperser.explicitBasis`: the monomial basis of `ExplicitField N`.
* `Cslib.AffineDisperser.explicitDisperser`: the explicit function on `N` bits.
* `Cslib.AffineDisperser.explicitThreshold`: the dimension threshold `d(N)`.

## Main results

* `Cslib.AffineDisperser.exists_explicitDisperser_ne`: `explicitDisperser N` is nonconstant on
  every affine subspace of `BitString N` of dimension greater than `explicitThreshold N`.
* `Cslib.AffineDisperser.isAffineDisperser_explicitDisperser`: `explicitDisperser N` is an affine
  disperser for dimension `explicitThreshold N + 1`.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module

namespace Explicit

/-- The prime bound `L = ⌊⌊log₂ N⌋ / 3⌋`: the field degree is a product of primes in
`(L, 4 L]`. -/
def primeBound (N : ℕ) : ℕ :=
  Nat.log 2 N / 3

/-- The primes whose product is the field degree on `N` bits: chosen greedily, in increasing order,
from the primes in `(L, 4 L]` with product at most `N / (⌊log₂ N⌋ + 1) ^ 2`. -/
def degreePrimes (N : ℕ) : List ℕ :=
  selectBelow (N / (Nat.log 2 N + 1) ^ 2) (primesIoc (primeBound N) (4 * primeBound N))

/-- The `j`-th prime of the field degree on `N` bits. -/
def degreePrime (N : ℕ) (j : Fin (degreePrimes N).length) : ℕ :=
  (degreePrimes N).get j

/-- The field degree `n` on `N` bits: the product of `degreePrimes N`. -/
def fieldDegree (N : ℕ) : ℕ :=
  ∏ j, degreePrime N j

/-- The number of blocks `r = ⌊N / n⌋`. -/
def numBlocks (N : ℕ) : ℕ :=
  N / fieldDegree N

/-- The degree `t = ⌊log₂ N⌋ + 1` of the elementary symmetric polynomial. -/
def symDegree (N : ℕ) : ℕ :=
  Nat.log 2 N + 1

/-- The subfield exponent `s = ⌊n / (L + 1)⌋`: proper subfields of `𝔽_{2 ^ n}` have at most
`2 ^ s` elements. -/
def subfieldExp (N : ℕ) : ℕ :=
  fieldDegree N / (primeBound N + 1)

/-- Every member of `degreePrimes N` is a prime in `(L, 4 L]`. -/
theorem prime_of_mem_degreePrimes {N p : ℕ} (hp : p ∈ degreePrimes N) :
    primeBound N < p ∧ p ≤ 4 * primeBound N ∧ p.Prime :=
  mem_primesIoc.1 ((selectBelow_sublist _ _).subset hp)

/-- The primes in `degreePrimes N` are distinct. -/
theorem nodup_degreePrimes (N : ℕ) : (degreePrimes N).Nodup :=
  (nodup_primesIoc _ _).sublist (selectBelow_sublist _ _)

/-- Each `degreePrime N j` is prime. -/
theorem degreePrime_prime (N : ℕ) (j : Fin (degreePrimes N).length) : (degreePrime N j).Prime :=
  (prime_of_mem_degreePrimes (List.get_mem _ j)).2.2

/-- Distinct indices give distinct primes: `degreePrime N` is injective. -/
theorem degreePrime_injective (N : ℕ) : Function.Injective (degreePrime N) :=
  (nodup_degreePrimes N).injective_get

/-- The field degree is the product of the list `degreePrimes N`. -/
theorem fieldDegree_eq_prod (N : ℕ) : fieldDegree N = (degreePrimes N).prod := by
  rw [fieldDegree, ← List.prod_ofFn]
  exact congrArg List.prod (List.ofFn_get _)

/-- The field degree is nonzero. -/
theorem fieldDegree_ne_zero (N : ℕ) : fieldDegree N ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j _ => (degreePrime_prime N j).ne_zero

/-- The `r` blocks of `n` bits fit in the input: `r n ≤ N`. -/
theorem numBlocks_mul_le (N : ℕ) : numBlocks N * fieldDegree N ≤ N :=
  Nat.div_mul_le_self N _

/-- Every prime factor of the field degree exceeds `L`. -/
theorem lt_of_prime_dvd_fieldDegree {N q : ℕ} (hq : q.Prime) (hqn : q ∣ fieldDegree N) :
    primeBound N < q := by
  obtain ⟨j, -, hj⟩ := (Nat.prime_iff.1 hq).exists_mem_finset_dvd hqn
  rw [(Nat.prime_dvd_prime_iff_eq hq (degreePrime_prime N j)).1 hj]
  exact (prime_of_mem_degreePrimes (List.get_mem _ j)).1

end Explicit

open Explicit

/-- **The dimension threshold** `d(N) = N - r n + r * max (r + 1) s + r * (r + 1) + n t + ⌊n r / t⌋`
of the explicit disperser on `N` bits. -/
def explicitThreshold (N : ℕ) : ℕ :=
  N - numBlocks N * fieldDegree N +
    (numBlocks N * max (numBlocks N + 1) (subfieldExp N) + numBlocks N * (numBlocks N + 1) +
      fieldDegree N * symDegree N + fieldDegree N * numBlocks N / symDegree N)

/-- The field `𝔽_{2 ^ n}` of the explicit disperser on `N` bits. -/
abbrev ExplicitField (N : ℕ) : Type :=
  GaloisField 2 (fieldDegree N)

/-- The monomials indexing the basis of `ExplicitField N`. -/
abbrev ExplicitMonomial (N : ℕ) : Type :=
  (j : Fin (degreePrimes N).length) → Fin (degreePrime N j)

/-- The monomial basis of `ExplicitField N` in roots of the irreducible polynomials of least code of
the prime degrees. -/
noncomputable def explicitBasis (N : ℕ) : Basis (ExplicitMonomial N) (ZMod 2) (ExplicitField N) :=
  compositeBasis (degreePrime N) (degreePrime_prime N) (degreePrime_injective N)

/-- The input position of coordinate `J` of block `i`: blocks follow each other, and coordinates
within a block are numbered in the mixed-radix order of `finPiFinEquiv`. -/
def explicitPos (N : ℕ) (q : Fin (numBlocks N) × ExplicitMonomial N) : Fin N :=
  Fin.castLE (numBlocks_mul_le N) (finProdFinEquiv (q.1, finPiFinEquiv q.2))

/-- Distinct coordinates are read from distinct input positions: `explicitPos N` is injective. -/
theorem explicitPos_injective (N : ℕ) : Function.Injective (explicitPos N) := by
  intro q q' h
  have h' := Fin.castLE_injective _ h
  obtain ⟨h1, h2⟩ := Prod.mk.inj (finProdFinEquiv.injective h')
  exact Prod.ext h1 (finPiFinEquiv.injective h2)

/-- **The explicit affine disperser** on `N` bits: Ben-Sasson and Kopparty's function
`traceSym 1 r t` on the `r = numBlocks N` elements of `𝔽_{2 ^ n}`, `n = fieldDegree N`, read
from the first `r n` input bits in the monomial basis `explicitBasis N`, with
`t = symDegree N`. -/
noncomputable def explicitDisperser (N : ℕ) : BitString N → Bool :=
  traceSymBits (1 : ExplicitField N) (numBlocks N) (symDegree N) (explicitBasis N) (explicitPos N)

/-- **An explicit affine disperser**, after [BenSassonKopparty2012, Theorem 7.3]:
`explicitDisperser N` is nonconstant on every affine subspace of `BitString N` of dimension greater
than `explicitThreshold N`. -/
theorem exists_explicitDisperser_ne {N : ℕ} (A : AffineSubspace Bool (BitString N))
    (hA : explicitThreshold N < finrank Bool A.direction) :
    ∃ x ∈ A, ∃ y ∈ A, explicitDisperser N x ≠ explicitDisperser N y :=
  exists_traceSymBits_ne (GaloisField.finrank 2 (fieldDegree_ne_zero N))
    (card_subfield_le_of_lt_prime (GaloisField.finrank 2 (fieldDegree_ne_zero N))
      fun _ hq hqn => lt_of_prime_dvd_fieldDegree hq hqn)
    one_ne_zero (Nat.succ_pos _) (explicitBasis N) (explicitPos_injective N) A hA

/-- **The explicit function is an affine disperser** for dimension `explicitThreshold N + 1`: it
is nonconstant on the image of every injective affine map from `BitString (explicitThreshold N + 1)`
(`Cslib.BitString.IsAffineDisperser`). -/
theorem isAffineDisperser_explicitDisperser (N : ℕ) :
    BitString.IsAffineDisperser (explicitDisperser N) (explicitThreshold N + 1) :=
  BitString.isAffineDisperser_of_forall_exists_ne fun A hA =>
    exists_explicitDisperser_ne A (by omega)

end Cslib.AffineDisperser
