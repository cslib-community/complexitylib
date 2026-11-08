/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.ZModTwo
public import Complexity.Probability.PairwiseIndependentHash.Toeplitz
import Complexity.Probability.PairwiseIndependentHash.Shift

/-!
# Toeplitz hashing of bit strings

The Toeplitz hash `Cslib.Probability.toeplitzHash` over `Bool`, the maps `x ↦ T x + v` of bit
strings for a Toeplitz matrix `T` and an offset `v`, is pairwise independent
(`Cslib.BitString.isPairwiseIndependentHash_toeplitzHash_bool`) [Katz and Lindell,
Exercise 4.26][KatzLindell2020]. Mathlib has no `Field Bool` instance, so the field case
`Cslib.Probability.isPairwiseIndependentHash_toeplitzHash` does not apply directly; the
surjectivity of `a ↦ toeplitz a *ᵥ d` for `d ≠ 0` transfers from `ZMod 2` along the ring isomorphism
`Cslib.BitString.bitEquiv` (`Cslib.BitString.toeplitz_mulVec_surjective_bool`). From `n` bits to
`m` bits, its seeds have `n + 2 m - 1` bits, against `m n + m` for the affine family
`Cslib.BitString.LinearHash.affineHash`.

## Main results

* `Cslib.BitString.toeplitz_mulVec_surjective_bool`: Boolean Toeplitz matrices reach every vector
  from a nonzero vector.
* `Cslib.BitString.isPairwiseIndependentHash_toeplitzHash_bool`: Toeplitz hashing of bit strings
  is pairwise independent.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, Section 4.6][KatzLindell2020]
-/

@[expose] public section

namespace Cslib.BitString

open Cslib.Probability Matrix

variable {m n : ℕ}

/-- **Boolean Toeplitz matrices reach every vector**: for every nonzero bit string `d`, every bit
string is `T d` for some `m × n` Toeplitz matrix `T` over `Bool`. -/
theorem toeplitz_mulVec_surjective_bool {d : Fin n → Bool} (hd : d ≠ 0) :
    Function.Surjective fun a : Fin (m + n - 1) → Bool => toeplitz a *ᵥ d := by
  intro c
  have hd' : (bitEquiv.symm ∘ d : Fin n → ZMod 2) ≠ 0 := fun h =>
    hd (funext fun j => by simpa using congrArg bitEquiv (congrFun h j))
  obtain ⟨a, ha⟩ := toeplitz_mulVec_surjective (m := m) hd' (bitEquiv.symm ∘ c)
  refine ⟨bitEquiv ∘ a, funext fun i => ?_⟩
  have hi := congrArg bitEquiv (congrFun ha i)
  simp only [Function.comp_apply, RingEquiv.apply_symm_apply] at hi
  rw [← hi]
  simp only [mulVec, dotProduct, toeplitz_apply, map_sum, map_mul, Function.comp_apply,
    RingEquiv.apply_symm_apply]

/-- **Toeplitz hashing of bit strings is pairwise independent**: the maps `x ↦ T x + v` from
`n`-bit strings to `m`-bit strings, for a uniformly random `m × n` Toeplitz matrix `T` over `Bool`
and an independent uniformly random offset `v`, form a pairwise independent hash family [Katz and
Lindell, Exercise 4.26][KatzLindell2020]. -/
theorem isPairwiseIndependentHash_toeplitzHash_bool :
    IsPairwiseIndependentHash
      (toeplitzHash : (Fin (m + n - 1) → Bool) × (Fin m → Bool) → (Fin n → Bool) → Fin m → Bool) :=
  isPairwiseIndependentHash_add_of_surjective
    (AddMonoidHom.mk' (fun (a : Fin (m + n - 1) → Bool) (x : Fin n → Bool) => toeplitz a *ᵥ x)
      fun a b => funext fun x => by rw [Pi.add_apply, toeplitz_add, add_mulVec])
    fun x₁ x₂ hx c => by
      obtain ⟨a, ha⟩ := toeplitz_mulVec_surjective_bool (m := m) (sub_ne_zero.2 hx) c
      refine ⟨a, ?_⟩
      simpa only [AddMonoidHom.mk'_apply, mulVec_sub] using ha

end Cslib.BitString
