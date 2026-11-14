/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/ZMod/Units.lean` for the unit CRT and squares,
-- `Mathlib/FieldTheory/Finite/Basic.lean` for the square count)

public import CslibFrontier.Init
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The Chinese remainder theorem on units, and squares modulo a prime

For coprime `p` and `q`, the Chinese remainder isomorphism `ZMod (p * q) ≃+* ZMod p × ZMod q`
restricts to the unit groups. A unit modulo `p * q` is a square exactly when both of its
components are, and half of the units modulo an odd prime are squares. These facts underlie the
quadratic residuosity assumption and Goldwasser–Micali decryption ([KatzLindell2020],
Section 15.4).

## Main definitions

* `ZMod.unitsChineseRemainder`: `(ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ` for coprime `p`, `q`.

## Main results

* `ZMod.coe_unitsChineseRemainder_fst`, `ZMod.coe_unitsChineseRemainder_snd`: the components are
  the images under the Chinese remainder isomorphism.
* `ZMod.isSquare_iff_unitsChineseRemainder`: a unit modulo `p * q` is a square iff both
  components are.
* `ZMod.two_mul_card_squares_units`, `ZMod.card_nonsquares_units`: an odd prime `p` has as many
  square units as nonsquare units, `(p - 1) / 2` of each.
* `ZMod.isSquare_mul_of_not_isSquare_units`: the product of two nonsquare units modulo a prime is
  a square.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020],
  Section 15.4.
-/

public section

namespace ZMod

/-- The Chinese remainder theorem on unit groups: `(ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ` for
coprime `p` and `q`. -/
@[expose] def unitsChineseRemainder {p q : ℕ} (h : p.Coprime q) :
    (ZMod (p * q))ˣ ≃* (ZMod p)ˣ × (ZMod q)ˣ :=
  (Units.mapEquiv (chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- The first component of `unitsChineseRemainder h u` is the first component of the Chinese
remainder image of `u`. -/
theorem coe_unitsChineseRemainder_fst {p q : ℕ} (h : p.Coprime q) (u : (ZMod (p * q))ˣ) :
    ((unitsChineseRemainder h u).1 : ZMod p) = (chineseRemainder h (u : ZMod (p * q))).1 :=
  rfl

/-- The second component of `unitsChineseRemainder h u` is the second component of the Chinese
remainder image of `u`. -/
theorem coe_unitsChineseRemainder_snd {p q : ℕ} (h : p.Coprime q) (u : (ZMod (p * q))ˣ) :
    ((unitsChineseRemainder h u).2 : ZMod q) = (chineseRemainder h (u : ZMod (p * q))).2 :=
  rfl

/-- A unit modulo `p * q` is a square iff both of its Chinese remainder components are. -/
theorem isSquare_iff_unitsChineseRemainder {p q : ℕ} (h : p.Coprime q) (u : (ZMod (p * q))ˣ) :
    IsSquare u ↔
      IsSquare (unitsChineseRemainder h u).1 ∧ IsSquare (unitsChineseRemainder h u).2 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨⟨(unitsChineseRemainder h r).1, by simp⟩, ⟨(unitsChineseRemainder h r).2, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(unitsChineseRemainder h).symm (a, b), (unitsChineseRemainder h).injective ?_⟩
    ext <;> simp [ha, hb]

/-- Half of the units modulo an odd prime are squares. -/
theorem two_mul_card_squares_units (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    2 * (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card = Fintype.card (ZMod p)ˣ := by
  have hrange : (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card =
      Nat.card (powMonoidHom 2 : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
    rw [Nat.card_eq_fintype_card]
    symm
    apply Fintype.card_of_subtype
    intro u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, MonoidHom.mem_range,
      powMonoidHom_apply, isSquare_iff_exists_sq, eq_comm]
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have hdvd : 2 ∣ p - 1 := by
    have hodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two (by omega))
    omega
  rw [hrange, IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, hcard,
    Nat.gcd_eq_right hdvd]
  omega

/-- An odd prime has as many nonsquare units as square units. -/
theorem card_nonsquares_units (p : ℕ) [Fact p.Prime] (hp : 2 < p) :
    (Finset.univ.filter fun u : (ZMod p)ˣ => ¬ IsSquare u).card =
      (Finset.univ.filter fun u : (ZMod p)ˣ => IsSquare u).card := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun u : (ZMod p)ˣ => IsSquare u)
  rw [Finset.card_univ] at h
  have := two_mul_card_squares_units p hp
  omega

/-- The product of two nonsquare units modulo a prime is a square: the quadratic character takes
the value `-1` on each factor. -/
theorem isSquare_mul_of_not_isSquare_units {p : ℕ} [Fact p.Prime] {u v : (ZMod p)ˣ}
    (hu : ¬ IsSquare u) (hv : ¬ IsSquare v) : IsSquare (u * v) := by
  rw [← Units.isSquare_coe_iff] at hu hv ⊢
  rw [← quadraticChar_one_iff_isSquare (u * v).ne_zero, Units.val_mul, map_mul,
    quadraticChar_neg_one_iff_not_isSquare.mpr hu, quadraticChar_neg_one_iff_not_isSquare.mpr hv,
    neg_one_mul, neg_neg]

end ZMod
