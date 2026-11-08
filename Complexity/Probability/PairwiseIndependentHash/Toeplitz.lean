/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.Toeplitz
public import Complexity.Probability.PairwiseIndependentHash.Affine
public import Complexity.Probability.PairwiseIndependentHash.Shift

/-!
# Toeplitz hashing

Over a finite field `F`, the maps `x ↦ T x + v` from `F^n` to `F^m`, for a uniformly random
`m × n` Toeplitz matrix `T` (`Matrix.toeplitz`) and an independent uniformly random vector `v`,
form a pairwise independent hash family (`Cslib.Probability.isPairwiseIndependentHash_toeplitzHash`)
[Katz and Lindell, Exercise 4.26][KatzLindell2020]. This is the affine family
`Cslib.Probability.affineHash` restricted to Toeplitz matrices, with seeds of `n + 2 m - 1`
field elements instead of `m n + m` (`Cslib.Probability.card_toeplitzHash_seed`). The proof
uses the shift criterion `Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`: for
every nonzero `d : F^n`, the Toeplitz matrices `T` reach every vector `T d`
(`Matrix.toeplitz_mulVec_surjective`).

## Main definitions

* `Cslib.Probability.toeplitzHash`: the map `x ↦ T x + v` with seed a Toeplitz matrix `T` and a
  vector `v`.

## Main results

* `Cslib.Probability.isPairwiseIndependentHash_toeplitzHash`: the Toeplitz hash family over a
  finite field is pairwise independent.
* `Cslib.Probability.card_toeplitzHash_seed`: its seeds consist of `n + 2 m - 1` field elements.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.Probability

open Matrix

variable {F : Type*} {m n : ℕ}

/-- The affine map `x ↦ T x + v` from `F^n` to `F^m`, with seed `(a, v)` where `T` is the
Toeplitz matrix `Matrix.toeplitz a` with diagonals `a` [Katz and Lindell, Exercise 4.26]
[KatzLindell2020]. -/
def toeplitzHash [NonUnitalNonAssocSemiring F] (p : (Fin (m + n - 1) → F) × (Fin m → F))
    (x : Fin n → F) : Fin m → F :=
  toeplitz p.1 *ᵥ x + p.2

/-- The Toeplitz hash with seed `(a, v)` sends `x` to `T x + v`, where `T = Matrix.toeplitz a`. -/
@[simp]
theorem toeplitzHash_apply [NonUnitalNonAssocSemiring F] (a : Fin (m + n - 1) → F)
    (v : Fin m → F) (x : Fin n → F) : toeplitzHash (a, v) x = toeplitz a *ᵥ x + v :=
  rfl

/-- The Toeplitz hash is the affine hash `Cslib.Probability.affineHash` restricted to Toeplitz
matrices. -/
theorem toeplitzHash_eq_affineHash [NonUnitalNonAssocSemiring F]
    (p : (Fin (m + n - 1) → F) × (Fin m → F)) :
    toeplitzHash p = affineHash (toeplitz p.1, p.2) :=
  rfl

/-- **Toeplitz hashing is pairwise independent**: over a finite field `F`, the maps `x ↦ T x + v`
from `F^n` to `F^m`, for a uniformly random `m × n` Toeplitz matrix `T` and an independent
uniformly random vector `v`, form a pairwise independent hash family [Katz and Lindell,
Exercise 4.26][KatzLindell2020]. -/
theorem isPairwiseIndependentHash_toeplitzHash [Field F] [Fintype F] [DecidableEq F] :
    IsPairwiseIndependentHash
      (toeplitzHash : (Fin (m + n - 1) → F) × (Fin m → F) → (Fin n → F) → Fin m → F) :=
  isPairwiseIndependentHash_add_of_surjective
    (AddMonoidHom.mk' (fun (a : Fin (m + n - 1) → F) (x : Fin n → F) => toeplitz a *ᵥ x)
      fun a b => funext fun x => by rw [Pi.add_apply, toeplitz_add, add_mulVec])
    fun x₁ x₂ hx c => by
      obtain ⟨a, ha⟩ := toeplitz_mulVec_surjective (m := m) (sub_ne_zero.2 hx) c
      refine ⟨a, ?_⟩
      simpa only [AddMonoidHom.mk'_apply, mulVec_sub] using ha

/-- **The seed length of Toeplitz hashing**: the Toeplitz hash family from `F^n` to `F^m` has
`|F| ^ (n + 2 m - 1)` seeds, `m + n - 1` field elements for the matrix and `m` for the offset.
The affine family `Cslib.Probability.affineHash` with the same domain and range has
`|F| ^ (m n + m)` seeds, which is at least as many once `m` and `n` are positive, and strictly
more once they both exceed `1`. -/
theorem card_toeplitzHash_seed [Fintype F] :
    Fintype.card ((Fin (m + n - 1) → F) × (Fin m → F)) = Fintype.card F ^ (n + 2 * m - 1) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    ← pow_add]
  congr 1
  omega

end Cslib.Probability
