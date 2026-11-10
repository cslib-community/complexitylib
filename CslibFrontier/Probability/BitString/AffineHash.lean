/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.LinearHash
public import CslibFrontier.Probability.PairwiseIndependentHash.Affine
import CslibFrontier.Probability.PairwiseIndependentHash.Shift

/-!
# Affine hashing of bit strings

The affine maps `x ↦ A x + b` of bit strings, with a Boolean matrix `A` of `k` rows given by its
rows and an offset `b` (`Cslib.BitString.LinearHash.affineHash`), form a pairwise independent hash
family (`Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash`): masking the
two-universal linear family `Cslib.BitString.LinearHash.hash` with a uniformly random offset
satisfies the shift criterion `Cslib.Probability.isPairwiseIndependentHash_add_of_surjective`.
This is the family of the set lower bound protocol of Goldwasser and Sipser
[GoldwasserSipser1986] [Arora and Barak, Section 8.2][AroraBarak09] and of the lemma of Valiant
and Vazirani [ValiantVazirani1986]. It is the affine hash `Cslib.Probability.affineHash` over
`Bool` (`Cslib.BitString.LinearHash.affineHash_eq_affineHash`), whose pairwise independence is
proved over fields; Mathlib has no `Field Bool` instance, so it is proved here separately.

## Main definitions

* `Cslib.BitString.LinearHash.affineHash`: the affine map `x ↦ A x + b` of bit strings.

## Main results

* `Cslib.BitString.LinearHash.affineHash_eq_affineHash`: it is the affine hash over `Bool`.
* `Cslib.BitString.LinearHash.isPairwiseIndependentHash_affineHash`: affine hashing of bit strings
  is pairwise independent.

## References

* [S. Goldwasser, M. Sipser, *Private coins versus public coins in interactive proof
  systems*][GoldwasserSipser1986]
* [L. G. Valiant, V. V. Vazirani, *NP is as easy as detecting unique
  solutions*][ValiantVazirani1986]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.BitString.LinearHash

open Cslib.Probability

/-- The affine map `x ↦ A x + b` of bit strings, with seed the `k` rows of the matrix `A` and the
offset `b`. -/
def affineHash {k n : ℕ} (seed : (Fin k → BitString n) × BitString k) (x : BitString n) :
    BitString k :=
  hash seed.1 x + seed.2

/-- Affine hashing of bit strings is the affine hash `Cslib.Probability.affineHash` over `Bool`,
with the rows as bit strings. -/
theorem affineHash_eq_affineHash {k n : ℕ} (seed : (Fin k → BitString n) × BitString k)
    (x : BitString n) :
    affineHash seed x = Probability.affineHash (m := Fin k) (n := Fin n) (F := Bool) seed x :=
  rfl

/-- **Affine hashing of bit strings is pairwise independent**: for distinct inputs, the difference
of the linear hashes is the linear hash of a nonzero difference, which takes every value. -/
theorem isPairwiseIndependentHash_affineHash (k n : ℕ) :
    IsPairwiseIndependentHash (affineHash (k := k) (n := n)) := by
  let g : (Fin k → BitString n) →+ (BitString n → BitString k) :=
    { toFun := hash
      map_zero' := by
        funext x i
        simp [hash]
      map_add' := by
        intro A B
        funext x i
        simp [hash, add_dotProduct] }
  refine isPairwiseIndependentHash_add_of_surjective g fun x₁ x₂ hx c => ?_
  obtain ⟨j, hj⟩ : ∃ j, (x₁ - x₂) j = true := by
    by_contra! h
    exact hx (sub_eq_zero.1 (funext fun j => by simpa [Bool.zero_eq_false] using h j))
  refine ⟨fun i => Pi.single j (c i), funext fun i => ?_⟩
  change (Pi.single j (c i) : BitString n) ⬝ᵥ x₁ - (Pi.single j (c i) : BitString n) ⬝ᵥ x₂ = c i
  rw [← dotProduct_sub, single_dotProduct, hj, Bool.mul_eq_and, Bool.and_true]

end Cslib.BitString.LinearHash
