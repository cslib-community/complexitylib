/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Truncated
public import Complexity.Computability.PolyTime.GaloisRingArithmetic
import Mathlib.Data.List.GetD

/-!
# `B_{P,ℓ}` as a ring of coefficient lists

Theorem D.1 of [OpenAI2026ETH] (p. 53) contracts networks with entries in
`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)`. This ring is the ring `GaloisRingArith.Ring P fl` of
coefficient-list arithmetic modulo `2 ^ P` and a monic polynomial, for the monic polynomial
`V ^ ℓ`, whose lower coefficients `truncFl ℓ` are all zero (`monicOf_truncFl`). So the
coefficient-list operations of `GaloisRingArith` (`add`, `mul`, `neg`, `sub`, `one`, `zero`),
with their correctness (`GaloisRingArith.val_mul`, …) and polynomial-time certificates
(`GaloisRingArith.computableInPolyTime_mul`, …), are arithmetic in `B_{P,ℓ}`; no separate
multiplication of truncated coefficient lists is needed.

The bridge to the contraction over `ℕ[V]` is the ring map `truncNatHom P ℓ : ℕ[X] → B_{P,ℓ}`.
It sends the polynomial of a coefficient list to its value (`truncNatHom_coeffPoly`), and two
polynomials have the same image exactly when their coefficients below `ℓ` agree modulo `2 ^ P`
(`truncNatHom_eq_iff`). So the image of the contraction over `ℕ[V]` is the contraction of the
values of the entries in `B_{P,ℓ}` (`truncNatHom_polyContraction`). The same holds over `ℤ[X]`
(`truncRingHom`, `truncRingHom_eq_iff`), where the incidence expansion of Lemma D.2 (pp. 54–56)
lives.

## Main definitions

* `Cslib.Circuits.Frontier.truncFl`: the lower coefficients of `V ^ ℓ`.
* `Cslib.Circuits.Frontier.truncRingHom`, `Cslib.Circuits.Frontier.truncNatHom`: the maps
  `ℤ[X] → B_{P,ℓ}` and `ℕ[X] → B_{P,ℓ}`.

## Main results

* `Cslib.Circuits.Frontier.monicOf_truncFl`: the monic polynomial is `V ^ ℓ`.
* `Cslib.Circuits.Frontier.truncRingHom_eq_iff`, `Cslib.Circuits.Frontier.truncNatHom_eq_iff`:
  equality in `B_{P,ℓ}` is agreement of the coefficients below `ℓ` modulo `2 ^ P`.
* `Cslib.Circuits.Frontier.truncNatHom_coeffPoly`: a coefficient list maps to its value.
* `Cslib.Circuits.Frontier.DescribedNetwork.truncNatHom_polyContraction`: the contraction over
  `ℕ[V]` maps to the contraction of the values.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53) and
  Lemma D.2 (pp. 54–56).
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial Finset GaloisRingArith

/-- **The lower coefficients of `V ^ ℓ`**: `ℓ` zeros. With this modulus,
`GaloisRingArith.Ring P (truncFl ℓ)` is `B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)`. -/
@[expose] def truncFl (ℓ : ℕ) : List ℕ := List.replicate ℓ 0

@[simp] theorem length_truncFl (ℓ : ℕ) : (truncFl ℓ).length = ℓ := List.length_replicate

theorem getD_truncFl (ℓ i : ℕ) : (truncFl ℓ).getD i 0 = 0 := by
  unfold truncFl
  by_cases h : i < ℓ
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

/-- The monic polynomial with lower coefficients `truncFl ℓ` is `V ^ ℓ`. -/
theorem monicOf_truncFl (ℓ : ℕ) : monicOf (truncFl ℓ) = X ^ ℓ := by
  rw [monicOf, length_truncFl, add_eq_left]
  refine sum_eq_zero fun i _ => ?_
  rw [getD_truncFl]
  simp

variable {P ℓ : ℕ}

/-- The defining polynomial of `B_{P,ℓ}` is `V ^ ℓ` over `ℤ / 2 ^ P`. -/
theorem map_monicOf_truncFl :
    (monicOf (truncFl ℓ)).map (Int.castRingHom (ZMod (2 ^ P))) = X ^ ℓ := by
  rw [monicOf_truncFl, Polynomial.map_pow, map_X]

/-- **The map `ℤ[V] → B_{P,ℓ}`**: reduce the coefficients modulo `2 ^ P`, then modulo `V ^ ℓ`. -/
noncomputable def truncRingHom (P ℓ : ℕ) : ℤ[X] →+* Ring P (truncFl ℓ) :=
  (AdjoinRoot.mk _).comp (mapRingHom (Int.castRingHom (ZMod (2 ^ P))))

theorem truncRingHom_X : truncRingHom P ℓ X = AdjoinRoot.root _ := by
  simp [truncRingHom]

theorem truncRingHom_C (z : ℤ) : truncRingHom P ℓ (C z) = (z : Ring P (truncFl ℓ)) := by
  simp [truncRingHom]

/-- **Equality in `B_{P,ℓ}`** of the images of two integer polynomials is agreement of their
coefficients below `ℓ` modulo `2 ^ P`. -/
theorem truncRingHom_eq_iff {p q : ℤ[X]} :
    truncRingHom P ℓ p = truncRingHom P ℓ q ↔ ∀ j < ℓ, p.coeff j ≡ q.coeff j [ZMOD 2 ^ P] := by
  rw [truncRingHom, RingHom.comp_apply, RingHom.comp_apply, AdjoinRoot.mk_eq_mk,
    map_monicOf_truncFl, X_pow_dvd_iff]
  refine forall₂_congr fun j _ => ?_
  rw [coeff_sub, sub_eq_zero, coe_mapRingHom, coeff_map, coeff_map, eq_intCast, eq_intCast,
    ZMod.intCast_eq_intCast_iff, Nat.cast_pow, Nat.cast_ofNat]

/-- `V ^ ℓ = 0` in `B_{P,ℓ}`. -/
theorem root_pow_truncFl : (AdjoinRoot.root _ : Ring P (truncFl ℓ)) ^ ℓ = 0 := by
  have h := root_pow_length (p := P) (fl := truncFl ℓ)
  rw [length_truncFl] at h
  rw [h, neg_eq_zero]
  refine sum_eq_zero fun i _ => ?_
  rw [getD_truncFl]
  simp

/-- **The map `ℕ[V] → B_{P,ℓ}`**, through `ℤ[V]`. -/
noncomputable def truncNatHom (P ℓ : ℕ) : ℕ[X] →+* Ring P (truncFl ℓ) :=
  (truncRingHom P ℓ).comp (mapRingHom (Nat.castRingHom ℤ))

/-- **Equality in `B_{P,ℓ}`** of the images of two natural polynomials is agreement of their
coefficients below `ℓ` modulo `2 ^ P`. -/
theorem truncNatHom_eq_iff {p q : ℕ[X]} :
    truncNatHom P ℓ p = truncNatHom P ℓ q ↔ ∀ j < ℓ, p.coeff j % 2 ^ P = q.coeff j % 2 ^ P := by
  rw [truncNatHom, RingHom.comp_apply, RingHom.comp_apply, truncRingHom_eq_iff]
  refine forall₂_congr fun j _ => ?_
  simp only [coe_mapRingHom, coeff_map, Nat.coe_castRingHom]
  rw [show (2 : ℤ) ^ P = ((2 ^ P : ℕ) : ℤ) by push_cast; rfl, Int.natCast_modEq_iff]
  rfl

/-- **A coefficient list maps to its value**: the image of `coeffPoly c` in `B_{P,ℓ}` is
`GaloisRingArith.val P (truncFl ℓ) c`. -/
theorem truncNatHom_coeffPoly (c : List ℕ) :
    truncNatHom P ℓ (coeffPoly c) = GaloisRingArith.val P (truncFl ℓ) c := by
  have hterm (i : ℕ) : truncNatHom P ℓ (C (c.getD i 0) * X ^ i) =
      ((c.getD i 0 : ℕ) : Ring P (truncFl ℓ)) * AdjoinRoot.root _ ^ i := by
    simp [truncNatHom, truncRingHom]
  rw [coeffPoly, map_sum, GaloisRingArith.val, length_truncFl]
  simp only [hterm]
  -- Both sums agree with the sum below `max |c| ℓ`.
  have hzero : ∀ i, ¬ (i < c.length ∧ i < ℓ) →
      ((c.getD i 0 : ℕ) : Ring P (truncFl ℓ)) * AdjoinRoot.root _ ^ i = 0 := by
    intro i hi
    by_cases hc : i < c.length
    · have hℓ : ℓ ≤ i := by omega
      rw [← Nat.add_sub_cancel' hℓ, pow_add, root_pow_truncFl, zero_mul, mul_zero]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp
  rw [← sum_subset (range_subset_range.mpr (Nat.min_le_left c.length ℓ)) fun i _ hi =>
      hzero i (by simp only [mem_range] at hi; omega),
    ← sum_subset (range_subset_range.mpr (Nat.min_le_right c.length ℓ)) fun i _ hi =>
      hzero i (by simp only [mem_range] at hi; omega)]

namespace DescribedNetwork

variable {T : Type*}

/-- **The contraction over `ℕ[V]` in `B_{P,ℓ}`** is the contraction of the values of the
entries. -/
theorem truncNatHom_polyContraction (entry : T → List Bool → List ℕ) (G : DescribedNetwork T) :
    truncNatHom P ℓ (G.polyContraction entry) =
      G.contraction fun t bs => GaloisRingArith.val P (truncFl ℓ) (entry t bs) := by
  rw [polyContraction, map_contraction]
  simp only [truncNatHom_coeffPoly]

end DescribedNetwork

end Cslib.Circuits.Frontier
