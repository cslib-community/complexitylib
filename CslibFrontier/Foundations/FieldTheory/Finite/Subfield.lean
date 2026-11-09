/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Subfields of finite binary fields and additive bit-string encodings

A proper subfield `K` of a finite field `F` has degree `[F : K] ≥ 2`, so `|K| ^ 2 ≤ |F|`
(`Cslib.card_sq_le_of_ne_top`). When `F` has `2 ^ n` elements and every prime factor of `n`
exceeds `L`, the degree `[F : K]` is at least `L + 1`, so `|K| ≤ 2 ^ (n / (L + 1))`
(`Cslib.card_subfield_le_of_lt_prime`), and in particular `|K| ≤ 2 ^ (n / 2)` for every proper
subfield (`Cslib.card_subfield_le`).

Every finite field `K` of characteristic two with `2 ^ b` elements is a `b`-dimensional vector
space over `ZMod 2`; coordinates in a basis identify its additive group with `BitString b`, whose
addition is coordinatewise exclusive or (`Cslib.nonempty_addEquiv_bitString`). Fields of
characteristic two with `2 ^ n` elements exist for every `n ≠ 0`
(`Cslib.exists_field_card_eq_two_pow`).

## Main results

* `Cslib.card_sq_le_of_ne_top`: a proper subfield `K` of a finite field `F` satisfies
  `|K| ^ 2 ≤ |F|`.
* `Cslib.card_subfield_le_of_lt_prime`: if every prime factor of `n` exceeds `L`, every proper
  subfield of a field with `2 ^ n` elements has at most `2 ^ (n / (L + 1))` elements.
* `Cslib.card_subfield_le`: every proper subfield of a field with `2 ^ n` elements has at most
  `2 ^ (n / 2)` elements.
* `Cslib.nonempty_addEquiv_bitString`: a field of characteristic two with `2 ^ b` elements is
  additively equivalent to `BitString b`.
* `Cslib.exists_field_card_eq_two_pow`: there is a field of characteristic two with `2 ^ n`
  elements for every `n ≠ 0`.

## References

* [R. Lidl, H. Niederreiter, *Finite Fields*, Chapter 2][LidlNiederreiter1997]
* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
* Adapted from MassProduction/BinaryField.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib

open Module

variable {F : Type*} [Field F] [Finite F]

/-- A proper subfield `K` of a finite field `F` satisfies `|K| ^ 2 ≤ |F|`. -/
theorem card_sq_le_of_ne_top {K : Subfield F} (hK : K ≠ ⊤) : Nat.card K ^ 2 ≤ Nat.card F := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := F)]
  refine Nat.pow_le_pow_right Nat.card_pos ?_
  by_contra h
  have h1 : finrank K F = 1 := by
    have := Module.finrank_pos (R := K) (M := F)
    omega
  apply hK
  have hbij : Function.Bijective (Subtype.val : K → F) :=
    Subtype.val_injective.bijective_of_nat_card_le
      (by rw [Module.natCard_eq_pow_finrank (K := K) (V := F), h1, pow_one])
  exact eq_top_iff.2 fun x _ => by
    obtain ⟨y, rfl⟩ := hbij.2 x
    exact y.2

variable [Algebra (ZMod 2) F]

/-- A nontrivial `𝔽₂`-algebra has characteristic two. -/
instance charP_two_of_algebra_zmod_two (R : Type*) [Ring R] [Nontrivial R] [Algebra (ZMod 2) R] :
    CharP R 2 :=
  charP_of_injective_algebraMap' (ZMod 2) 2

/-- **Subfields of `𝔽_{2 ^ n}`**: if every prime factor of `n` exceeds `L`, every proper subfield
of a field with `2 ^ n` elements has at most `2 ^ (n / (L + 1))` elements. -/
theorem card_subfield_le_of_lt_prime {n L : ℕ} (hn : finrank (ZMod 2) F = n)
    (hL : ∀ q, q.Prime → q ∣ n → L < q) (K : Subfield F) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ (n / (L + 1)) := by
  cases nonempty_fintype F
  have : CharP K 2 := K.subtype.charP Subtype.val_injective 2
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨a, -, ha⟩ := FiniteField.card K 2
  have hF : Nat.card F = 2 ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F), Nat.card_zmod, hn]
  -- `|F| = |K| ^ e` with `e = [F : K] ≥ 2`, so `n = a e`
  have hFe : Nat.card F = Nat.card K ^ finrank K F := Module.natCard_eq_pow_finrank (K := K)
  rw [hF, Nat.card_eq_fintype_card (α := K), ha, ← pow_mul] at hFe
  have hne : n = a * finrank K F := Nat.pow_right_injective le_rfl hFe
  have hsq := card_sq_le_of_ne_top hK
  rw [Nat.card_eq_fintype_card (α := K), ha, hF, ← pow_mul] at hsq
  have he2 : 2 ≤ finrank K F := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hsq
    rw [hne] at this
    exact Nat.le_of_mul_le_mul_left this a.pos
  -- a prime factor `q` of `e` divides `n`, so `q > L` and `a ≤ n / q`
  have hq := Nat.minFac_prime (by omega : finrank K F ≠ 1)
  have hqL : L < (finrank K F).minFac :=
    hL _ hq ((Nat.minFac_dvd _).trans (hne ▸ dvd_mul_left _ _))
  rw [Nat.card_eq_fintype_card (α := K), ha]
  refine Nat.pow_le_pow_right two_pos ((Nat.le_div_iff_mul_le (by omega)).2 ?_)
  calc a * (L + 1) ≤ a * finrank K F :=
        Nat.mul_le_mul_left _ (hqL.trans_le (Nat.minFac_le (by omega)))
    _ = n := hne.symm

/-- In a field with `2 ^ n` elements every proper subfield has at most `2 ^ (n / 2)` elements. -/
theorem card_subfield_le {n : ℕ} (hn : finrank (ZMod 2) F = n) (K : Subfield F) (hK : K ≠ ⊤) :
    Nat.card K ≤ 2 ^ (n / 2) :=
  card_subfield_le_of_lt_prime (L := 1) hn (fun _ hq _ => hq.one_lt) K hK

/-- A field of characteristic two with `2 ^ b` elements is additively equivalent to `BitString b`,
whose addition is coordinatewise exclusive or. -/
theorem nonempty_addEquiv_bitString {K : Type*} [Field K] [Fintype K] [CharP K 2] {b : ℕ}
    (hK : Fintype.card K = 2 ^ b) : Nonempty (K ≃+ BitString b) := by
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hrank : Module.finrank (ZMod 2) K = b := by
    have hcard := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, ZMod.card] at hcard
    exact (Nat.pow_right_injective le_rfl hcard).symm
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) K hrank).equivFun.toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (ZMod.ringEquivOfPrime Bool Nat.prime_two rfl).toAddEquiv)⟩

/-- For every `n ≠ 0` there is a field of characteristic two with exactly `2 ^ n` elements, for
example the Galois field `GaloisField 2 n`. -/
theorem exists_field_card_eq_two_pow {n : ℕ} (hn : n ≠ 0) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), CharP K 2 ∧ Fintype.card K = 2 ^ n :=
  ⟨GaloisField 2 n, inferInstance, Fintype.ofFinite _, inferInstance, by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 n hn]⟩

end Cslib
