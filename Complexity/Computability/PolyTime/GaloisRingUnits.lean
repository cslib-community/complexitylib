/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.GaloisRingArithmetic
public import Complexity.Foundations.RingTheory.GaloisRing
import Mathlib.FieldTheory.Finite.Basic

/-!
# Newton inversion inverts every unit of a Galois ring

`Complexity/Computability/PolyTime/GaloisRingArithmetic.lean` computes in
`A_p = (ℤ / 2 ^ p)[U] / (f)` on coefficient lists, and inverts by `p` Newton steps from the seed
`x ^ (2 ^ e - 2)`, `e = deg f` (`GaloisRingArith.inv`). Its correctness
(`GaloisRingArith.val_mul_inv`) assumes that the seed inverts `x` modulo `2`. This file discharges
that assumption when `f` is irreducible modulo `2`, so that `A_p` is the Galois ring
`GaloisRing 2 p f`.

Reduction modulo `2` maps `A_p` onto the field `𝔽_2[U] / (f)` with `2 ^ e` elements, where every
nonzero `r` has `r ^ (2 ^ e - 1) = 1`. A unit `y` reduces to a nonzero element, so
`y y ^ (2 ^ e - 2) - 1` lies in the kernel `(2)` of reduction (`GaloisRing.ker_residue`). The seed
is computed natively (`GaloisRingArith.seed`), so no inversion modulo `2` is needed separately.

So `GaloisRingArith.inv` inverts every unit, that is every element that is nonzero modulo `2`
(`GaloisRing.isUnit_iff`), in polynomial time (`GaloisRingArith.computableInPolyTime_inv`). This
is the inversion of units by inversion modulo two and Newton lifting of [OpenAI2026ETH]
(Appendix D.4.1, p. 58), with `ℓ = 1`.

## Main results

* `Cslib.GaloisRingArith.natDegree_monicOf`: `monicOf fl` has degree `fl.length`.
* `Cslib.GaloisRingArith.exists_mul_pow_eq_one_add_two_mul`: the seed inverts a unit modulo `2`.
* `Cslib.GaloisRingArith.val_mul_inv_of_isUnit`, `Cslib.GaloisRingArith.val_inv_of_isUnit`:
  Newton inversion inverts every unit.
* `Cslib.GaloisRingArith.val_mul_inv_of_residue_ne_zero`: it inverts every element that is nonzero
  modulo `2`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.1 (pp. 57–58).
-/

public section

namespace Cslib.GaloisRingArith

open Polynomial Finset

/-- `monicOf fl` has degree `fl.length`. -/
theorem natDegree_monicOf (fl : List ℕ) : (monicOf fl).natDegree = fl.length := by
  unfold monicOf
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (mem_range.mp hi))

variable {p : ℕ} {fl : List ℕ}

/-- `A_p` is the Galois ring `GaloisRing 2 p (monicOf fl)`. -/
theorem ring_eq_galoisRing : Ring p fl = GaloisRing 2 p (monicOf fl) := rfl

/-- **The seed inverts a unit modulo `2`.** In a Galois ring of rank `e`, the residue field has
`2 ^ e` elements, so a unit `y` satisfies `y y ^ (2 ^ e - 2) = 1 + 2 w`. -/
theorem exists_mul_pow_eq_one_add_two_mul [NeZero p]
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) {y : Ring p fl}
    (hy : IsUnit y) : ∃ w : Ring p fl, y * y ^ (2 ^ fl.length - 2) = 1 + 2 * w := by
  set F := AdjoinRoot ((monicOf fl).map (Int.castRingHom (ZMod 2)))
  have : Fact (Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) := ⟨hirr⟩
  have hcard : Nat.card F = 2 ^ fl.length := by
    rw [GaloisRing.natCard_adjoinRoot (monic_monicOf fl), natDegree_monicOf]
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let : Fintype F := Fintype.ofFinite F
  have he : 1 ≤ fl.length := by
    have := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr)
    rwa [(monic_monicOf fl).natDegree_map, natDegree_monicOf] at this
  have h2 : 2 ≤ 2 ^ fl.length := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ fl.length := Nat.pow_le_pow_right (by norm_num) he
  -- The residue of `y` is nonzero, so its `(2 ^ e - 1)`-th power is `1`.
  have hr : GaloisRing.residue 2 p (monicOf fl) y ≠ 0 :=
    (GaloisRing.isUnit_iff (monic_monicOf fl) hirr).mp hy
  have hpow : GaloisRing.residue 2 p (monicOf fl) y ^ (2 ^ fl.length - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one _ hr
    rwa [Fintype.card_eq_nat_card, hcard] at this
  have hker : y * y ^ (2 ^ fl.length - 2) - 1 ∈
      RingHom.ker (GaloisRing.residue 2 p (monicOf fl)) := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_one, ← pow_succ',
      show 2 ^ fl.length - 2 + 1 = 2 ^ fl.length - 1 by omega, hpow, sub_self]
  rw [GaloisRing.ker_residue (monic_monicOf fl), Ideal.mem_span_singleton] at hker
  obtain ⟨w, hw⟩ := hker
  exact ⟨w, by rw [← sub_eq_iff_eq_add', hw]; push_cast; rfl⟩

/-- **Newton inversion inverts every unit** of the Galois ring `A_p`, `f` irreducible modulo
`2`. -/
theorem val_mul_inv_of_isUnit (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    {x : List ℕ} (hx : IsUnit (val p fl x)) : val p fl x * val p fl (inv p fl x) = 1 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · -- `A_0` is the zero ring.
    have : Subsingleton (ZMod (2 ^ 0)) := by rw [pow_zero]; infer_instance
    have := (AdjoinRoot.of ((monicOf fl).map (Int.castRingHom (ZMod (2 ^ 0))))).codomain_trivial
    exact Subsingleton.elim _ _
  · have : NeZero p := ⟨hp.ne'⟩
    obtain ⟨w, hw⟩ := exists_mul_pow_eq_one_add_two_mul hirr hx
    exact val_mul_inv x hw

/-- **Newton inversion computes the inverse of a unit.** -/
theorem val_inv_of_isUnit (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
    {x : List ℕ} (hx : IsUnit (val p fl x)) :
    val p fl (inv p fl x) = _root_.Ring.inverse (val p fl x) := by
  rw [← _root_.Ring.inverse_mul_cancel_left _ (val p fl (inv p fl x)) hx,
    val_mul_inv_of_isUnit hirr hx, mul_one]

/-- **Newton inversion inverts every element that is nonzero modulo `2`.** -/
theorem val_mul_inv_of_residue_ne_zero [NeZero p]
    (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2)))) {x : List ℕ}
    (hx : GaloisRing.residue 2 p (monicOf fl) (val p fl x) ≠ 0) :
    val p fl x * val p fl (inv p fl x) = 1 :=
  val_mul_inv_of_isUnit hirr ((GaloisRing.isUnit_iff (monic_monicOf fl) hirr).mpr hx)

end Cslib.GaloisRingArith
