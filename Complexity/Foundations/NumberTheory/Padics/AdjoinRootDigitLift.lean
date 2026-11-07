/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/Padics/`)

public import Complexity.Foundations.NumberTheory.Padics.AdjoinRootValuation
import Complexity.Foundations.RingTheory.AdjoinRoot
import Complexity.Foundations.RingTheory.GaloisRing

/-!
# Digit lifts in `ℤ_(p)[X] / (f)`

Let `p` be a prime and `f` a monic integer polynomial that is irreducible modulo `p`, and let
`O = ℤ_(p)[X] / (f)` be the valuation ring of `AdjoinRoot.padicValuation` in `K = ℚ[X] / (f)`.
The *digit lift* of a digit vector `c : Fin (deg f) → ZMod p` is `∑ i, c i * X ^ i` in `O`, with
each digit read as an integer in `{0, …, p - 1}` (`AdjoinRoot.integerDigitLift`). For `p = 2`
these are the binary-coordinate lifts of the residue-field elements of [OpenAI2026ETH] (§D.4.1,
p. 58).

**Distinct digit lifts differ by a unit of `O`** (`AdjoinRoot.isUnit_integerDigitLift_sub`). The
difference of two lifts is the image of `∑ i, (c i - c' i) * X ^ i ∈ ℤ[X] / (f)`, which is nonzero
modulo `p` because the digit lifts reduce to distinct elements of `𝔽_p[X] / (f)`
(`GaloisRing.residue_digitLift_injective`). So it has valuation one
(`AdjoinRoot.padicValuation_map_eq_one_iff`), and is a unit of the valuation ring
(`AdjoinRoot.isUnit_of_padicValuation_eq_one`). This is the counterpart in `O` of
`GaloisRing.isUnit_digitLift_sub`, and it supplies the interpolation points of the contraction
recursion (`Cslib.Circuits.Frontier.TensorNetwork.exists_contractRec_eq_add`) over `B = O`.

## Main definitions

* `AdjoinRoot.integerDigitLift`: the digit lift of a digit vector, in `O`.

## Main results

* `AdjoinRoot.coe_integerDigitLift`: the digit lift is `∑ i, c i * X ^ i`.
* `AdjoinRoot.isUnit_integerDigitLift_sub`: distinct digit lifts differ by a unit of `O`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1, p. 58.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {p : ℕ} [Fact p.Prime] {f : ℤ[X]} (hf : f.Monic)
  (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))

variable (p f) in
/-- The integer polynomial `∑ i, c i * X ^ i` of a digit vector, with each digit read as an
integer in `{0, …, p - 1}`. -/
private noncomputable def digitPoly (c : Fin f.natDegree → ZMod p) : ℤ[X] :=
  ∑ i, C ((c i).val : ℤ) * X ^ (i : ℕ)

/-- Modulo `p`, the digit polynomial is `∑ i, c i * X ^ i`. -/
private theorem map_digitPoly (c : Fin f.natDegree → ZMod p) :
    (digitPoly p f c).map (Int.castRingHom (ZMod p)) = ∑ i, C (c i) * X ^ (i : ℕ) := by
  simp only [digitPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  simp only [eq_intCast, Int.cast_natCast, ZMod.natCast_zmod_val]

include hf hirr

/-- The image in `ℚ[X] / (f)` of the class of the digit polynomial lies in the valuation ring. -/
private theorem map_mk_digitPoly_mem (c : Fin f.natDegree → ZMod p) :
    map (Int.castRingHom ℚ) f _ dvd_rfl (mk f (digitPoly p f c)) ∈
      (padicValuation p hf hirr).integer :=
  padicValuation_map_le_one hf hirr _

/-- **The digit lift** of a digit vector `c`: the element `∑ i, c i * X ^ i` of the valuation ring
`O = ℤ_(p)[X] / (f)`, with each digit `c i ∈ ZMod p` read as an integer in `{0, …, p - 1}`. For
`p = 2` these are the binary-coordinate lifts of [OpenAI2026ETH] (§D.4.1, p. 58). -/
noncomputable def integerDigitLift (c : Fin f.natDegree → ZMod p) :
    (padicValuation p hf hirr).integer :=
  ⟨_, map_mk_digitPoly_mem hf hirr c⟩

/-- The digit lift is `∑ i, c i * X ^ i` in `ℚ[X] / (f)`. -/
theorem coe_integerDigitLift (c : Fin f.natDegree → ZMod p) :
    (integerDigitLift hf hirr c : AdjoinRoot (f.map (Int.castRingHom ℚ))) =
      ∑ i, ((c i).val : AdjoinRoot (f.map (Int.castRingHom ℚ))) * root _ ^ (i : ℕ) := by
  simp only [integerDigitLift, digitPoly, map_sum, map_mul, map_pow, mk_X, map_natCast, map_root]

/-- **Distinct digit lifts differ by a unit of `O`**: the difference reduces modulo `p` to a
nonzero element of `𝔽_p[X] / (f)`, so it has valuation one. -/
theorem isUnit_integerDigitLift_sub {c c' : Fin f.natDegree → ZMod p} (h : c ≠ c') :
    IsUnit (integerDigitLift hf hirr c - integerDigitLift hf hirr c') := by
  have hx : ((integerDigitLift hf hirr c - integerDigitLift hf hirr c' :
      (padicValuation p hf hirr).integer) : AdjoinRoot (f.map (Int.castRingHom ℚ))) =
      map (Int.castRingHom ℚ) f _ dvd_rfl (mk f (digitPoly p f c - digitPoly p f c')) := by
    rw [map_sub, map_sub]
    rfl
  have h1 : padicValuation p hf hirr
      ((integerDigitLift hf hirr c - integerDigitLift hf hirr c' :
        (padicValuation p hf hirr).integer) : AdjoinRoot (f.map (Int.castRingHom ℚ))) = 1 := by
    rw [hx, padicValuation_map_eq_one_iff hf hirr, map_mk, Polynomial.map_sub, map_digitPoly,
      map_digitPoly, map_sub, sub_ne_zero]
    intro heq
    refine h (GaloisRing.residue_digitLift_injective (n := 1) hf ?_)
    simp only [GaloisRing.residue_digitLift]
    exact heq
  exact isUnit_of_padicValuation_eq_one hf hirr _ h1

/-- **Digit lifts are interpolation points**: distinct digit vectors have lifts with unit
differences. -/
theorem pairwise_isUnit_integerDigitLift_sub :
    Pairwise fun c c' : Fin f.natDegree → ZMod p =>
      IsUnit (integerDigitLift hf hirr c - integerDigitLift hf hirr c') :=
  fun _ _ h => isUnit_integerDigitLift_sub hf hirr h

end AdjoinRoot
