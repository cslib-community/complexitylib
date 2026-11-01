/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.PacketEvaluator
public import Complexity.Foundations.NumberTheory.Padics.AdjoinRootReduction
import Mathlib.Data.ZMod.QuotientRing

/-!
# The Galois ring maps into `O / 2 ^ n`

The contraction recursion of [OpenAI2026ETH] reasons over `O = ℤ_(2)[U] / (f)` and its quotients
`O / (2 ^ n)` (the children of a call live over `O / (2 ^ {p_t})`, `TensorNetwork.callSplitting`),
while the native algorithm computes in `A_n = (ℤ / 2 ^ n)[U] / (f)`, the Galois ring
`GaloisRing 2 n f`. Reduction `O → A_n` (`AdjoinRoot.reduction`) factors through `O / (2 ^ n)`;
this file gives the map back, `reductionLift : A_n → O / (2 ^ n)`, with
`reductionLift ∘ reduction = mk` (`reductionLift_comp_reduction`). It sends `U` to the
class of `U` and is the unique ring map from `ℤ / 2 ^ n` on scalars. So a value computed natively
in `A_n` and mapped along `reductionLift` is the class of any element of `O` reducing to it: the
canonical lift of a coefficient list (`reductionLift_reduction`).

## Main definitions

* `Cslib.Circuits.Frontier.reductionLift`: the map `A_n → O / (2 ^ n)`.

## Main results

* `Cslib.Circuits.Frontier.reductionLift_comp_reduction`: `reductionLift ∘ reduction = mk`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1, p. 57.
-/

public section

open Polynomial AdjoinRoot

namespace Cslib.Circuits.Frontier

variable {f : ℤ[X]} (hf : f.Monic) (hirr : Irreducible (f.map (Int.castRingHom (ZMod 2))))
  (n : ℕ)

/-- `2 ^ n = 0` in `O / (2 ^ n)`. -/
private theorem two_pow_eq_zero_quotient : (2 : ((padicValuation 2 hf hirr).integer ⧸
    Ideal.span {(2 : (padicValuation 2 hf hirr).integer) ^ n})) ^ n = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {(2 : (padicValuation 2 hf hirr).integer) ^ n})
      ((2 : (padicValuation 2 hf hirr).integer) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_ofNat] at this

/-- The scalars `ℤ / 2 ^ n → O / (2 ^ n)`. -/
private noncomputable def scalarLift : ZMod (2 ^ n) →+* ((padicValuation 2 hf hirr).integer ⧸
    Ideal.span {(2 : (padicValuation 2 hf hirr).integer) ^ n}) :=
  (Ideal.Quotient.lift _ (Int.castRingHom _) fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, eq_intCast, Int.cast_natCast, Nat.cast_pow, Nat.cast_ofNat,
      two_pow_eq_zero_quotient hf hirr n, zero_mul]).comp
    (Int.quotientSpanNatEquivZMod (2 ^ n)).symm.toRingHom

/-- The class of `U` in `O / (2 ^ n)`. -/
private noncomputable def rootClass : ((padicValuation 2 hf hirr).integer ⧸
    Ideal.span {(2 : (padicValuation 2 hf hirr).integer) ^ n}) :=
  Ideal.Quotient.mk _ (integerEquiv hf hirr (root _))

private theorem eval₂_rootClass :
    (f.map (Int.castRingHom (ZMod (2 ^ n)))).eval₂ (scalarLift hf hirr n) (rootClass hf hirr n) =
      0 := by
  rw [eval₂_map]
  have hcomp : (scalarLift hf hirr n).comp (Int.castRingHom (ZMod (2 ^ n))) =
      ((Ideal.Quotient.mk _).comp (integerEquiv hf hirr).toRingHom).comp
        ((of _).comp (Int.castRingHom (Rat.padicValuation 2).integer)) :=
    RingHom.ext_int _ _
  rw [hcomp, rootClass, show Ideal.Quotient.mk _ (integerEquiv hf hirr (root _)) =
      ((Ideal.Quotient.mk _).comp (integerEquiv hf hirr).toRingHom) (root _) from rfl,
    ← Polynomial.hom_eval₂, ← eval₂_map, eval₂_root, map_zero]

/-- **The Galois ring maps into `O / (2 ^ n)`**: `ℤ / 2 ^ n` by its unique ring map, and `U` to
its class. -/
noncomputable def reductionLift : GaloisRing 2 n f →+* ((padicValuation 2 hf hirr).integer ⧸
    Ideal.span {(2 : (padicValuation 2 hf hirr).integer) ^ n}) :=
  lift (scalarLift hf hirr n) (rootClass hf hirr n) (eval₂_rootClass hf hirr n)

/-- **`reductionLift` undoes reduction modulo `2 ^ n`**: reducing an element of `O` to `A_n` and
mapping back gives its class in `O / (2 ^ n)`. -/
theorem reductionLift_comp_reduction :
    (reductionLift hf hirr n).comp (reduction hf hirr n) = Ideal.Quotient.mk _ := by
  -- `U` of `O` is the class of `U` of `ℤ[X] / (f)`.
  have hroot : integerEquiv hf hirr (root _) = ⟨map (Int.castRingHom ℚ) f _ dvd_rfl (root f),
      (Valuation.mem_integer_iff _ _).mpr (padicValuation_map_le_one hf hirr _)⟩ := by
    apply Subtype.ext
    change (integerEquiv hf hirr (root _) : AdjoinRoot (f.map (Int.castRingHom ℚ))) =
      map (Int.castRingHom ℚ) f _ dvd_rfl (root f)
    rw [map_root, coe_integerEquiv]
    conv_lhs => rw [← mk_X]
    rw [integerMap_mk, Polynomial.map_X, mk_X]
  have key : (reductionLift hf hirr n).comp (integerReduction 2 f n) =
      (Ideal.Quotient.mk _).comp (integerEquiv hf hirr).toRingHom := by
    refine ringHom_ext ?_ ?_
    · exact padicInteger_ringHom_ext
        (two_pow_eq_zero_quotient hf hirr n) _ _
    · rw [RingHom.comp_apply, ← reduction_integerEquiv hf hirr, hroot, reduction_toRat hf hirr,
        map_root,
        reductionLift, lift_root, rootClass]
      rfl
  ext x
  obtain ⟨y, rfl⟩ := (integerEquiv hf hirr).surjective x
  rw [RingHom.comp_apply, reduction_integerEquiv, ← RingHom.comp_apply, key]
  rfl

/-- `reductionLift (reduction x)` is the class of `x`. -/
theorem reductionLift_reduction (x : (padicValuation 2 hf hirr).integer) :
    reductionLift hf hirr n (reduction hf hirr n x) = Ideal.Quotient.mk _ x :=
  RingHom.congr_fun (reductionLift_comp_reduction hf hirr n) x

end Cslib.Circuits.Frontier
