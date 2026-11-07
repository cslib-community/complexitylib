/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/Padics/`)

public import Complexity.Foundations.NumberTheory.Padics.AdjoinRootValuation
public import Complexity.Foundations.NumberTheory.Padics.RatValuation
public import Complexity.Foundations.RingTheory.GaloisRing
import Complexity.Foundations.RingTheory.AdjoinRoot

/-!
# Reduction of `ℤ_(p)[X] / (f)` modulo `p ^ n`

Let `p` be a prime and `f` a monic integer polynomial that is irreducible modulo `p`, and let
`O = ℤ_(p)[X] / (f)` be the valuation ring of `AdjoinRoot.padicValuation` in `K = ℚ[X] / (f)`.

**`O` is `AdjoinRoot (f.map ℤ_(p))`.** Reducing modulo `f` commutes with the inclusion
`ℤ_(p) → ℚ` because `f` is monic, so the map `ℤ_(p)[X] / (f) → ℚ[X] / (f)` is injective
(`AdjoinRoot.integerMap_injective`). By `AdjoinRoot.mem_integer_padicValuation_iff`, its image is
`O` (`AdjoinRoot.integerEquiv`).

**Reduction modulo `p ^ n`** (`AdjoinRoot.reduction`) is the ring homomorphism
`O → (ℤ / p ^ n)[X] / (f) = GaloisRing p n f` that reduces each coordinate in the basis
`1, X, …, X ^ (deg f - 1)` modulo `p ^ n` (`Rat.padicIntegerToZModPow`). The reductions are
compatible: reducing modulo `p ^ N` and then modulo `p ^ n` is reducing modulo `p ^ n`
(`AdjoinRoot.castHom_comp_reduction`). On the image of `ℤ[X] / (f)` the reduction reduces the
integer coefficients (`AdjoinRoot.reduction_toRat`), and on `ℤ_(p)` it is
`Rat.padicIntegerToZModPow` (`AdjoinRoot.reduction_algebraMap`).

For `p = 2` these maps let a computation in the Galois rings `(ℤ / 2 ^ n)[U] / (f)` follow the
contraction recursion of [OpenAI2026ETH] over `O`.

## Main definitions

* `AdjoinRoot.integerEquiv`: `ℤ_(p)[X] / (f)` is the valuation ring `O`.
* `AdjoinRoot.reduction`: reduction `O → GaloisRing p n f`.

## Main results

* `AdjoinRoot.castHom_comp_reduction`: the reductions are compatible.
* `AdjoinRoot.reduction_toRat`: on `ℤ[X] / (f)` the reduction reduces the integer coefficients.
* `AdjoinRoot.reduction_algebraMap`: on `ℤ_(p)` it is `Rat.padicIntegerToZModPow`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
-/

public section

open Polynomial

namespace AdjoinRoot

variable {p : ℕ} [Fact p.Prime] {f : ℤ[X]}

variable (p f) in
/-- `f` over `ℤ_(p)` maps to `f` over `ℚ`. -/
theorem map_subtype_map_integer :
    (f.map (Int.castRingHom (Rat.padicValuation p).integer)).map
      (Rat.padicValuation p).integer.subtype = f.map (Int.castRingHom ℚ) := by
  rw [Polynomial.map_map]
  congr 1

variable (p f) in
/-- The map `ℤ_(p)[X] / (f) → ℚ[X] / (f)`. -/
noncomputable def integerMap :
    AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer)) →+*
      AdjoinRoot (f.map (Int.castRingHom ℚ)) :=
  map (Rat.padicValuation p).integer.subtype _ _ (map_subtype_map_integer p f).symm.dvd

theorem integerMap_mk (P : (Rat.padicValuation p).integer[X]) :
    integerMap p f (mk _ P) = mk _ (P.map (Rat.padicValuation p).integer.subtype) :=
  map_mk _ _ _ P

variable (hf : f.Monic) (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))

include hf in
/-- **The map `ℤ_(p)[X] / (f) → ℚ[X] / (f)` is injective**, as `f` is monic. -/
theorem integerMap_injective : Function.Injective (integerMap p f) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have hg := hf.map (Int.castRingHom (Rat.padicValuation p).integer)
  rw [integerMap, map_eq_zero_iff _ hg _ (map_subtype_map_integer p f).symm] at hx
  have h0 : modByMonicHom hg x = 0 := Polynomial.ext fun i => Subtype.ext (by simpa using hx i)
  rw [← mk_leftInverse hg x, h0, map_zero]

include hf in
/-- The image of `ℤ_(p)[X] / (f)` lies in the valuation ring. -/
theorem integerMap_mem (x : AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer))) :
    integerMap p f x ∈ (padicValuation p hf hirr).integer := by
  obtain ⟨P, rfl⟩ := mk_surjective x
  rw [integerMap_mk, mem_integer_padicValuation_iff]
  intro i
  rw [modByMonicHom_mk, ← map_subtype_map_integer p f,
    ← map_modByMonic _ (hf.map (Int.castRingHom (Rat.padicValuation p).integer)), coeff_map]
  exact ((P %ₘ f.map (Int.castRingHom (Rat.padicValuation p).integer)).coeff i).2

/-- Every element of the valuation ring comes from `ℤ_(p)[X] / (f)`. -/
theorem exists_integerMap_eq {x : AdjoinRoot (f.map (Int.castRingHom ℚ))}
    (hx : x ∈ (padicValuation p hf hirr).integer) :
    ∃ y, integerMap p f y = x := by
  rw [mem_integer_padicValuation_iff] at hx
  have hl : modByMonicHom (hf.map (Int.castRingHom ℚ)) x ∈
      lifts (Rat.padicValuation p).integer.subtype :=
    (lifts_iff_coeff_lifts _).mpr fun i => ⟨⟨_, (Valuation.mem_integer_iff _ _).mpr (hx i)⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := (mem_lifts _).mp hl
  refine ⟨mk _ Q, ?_⟩
  rw [integerMap_mk, hQ]
  exact mk_leftInverse (hf.map _) x

/-- **`ℤ_(p)[X] / (f)` is the valuation ring** `O` of `AdjoinRoot.padicValuation`. -/
noncomputable def integerEquiv :
    AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer)) ≃+*
      (padicValuation p hf hirr).integer :=
  RingEquiv.ofBijective ((integerMap p f).codRestrict _ (integerMap_mem hf hirr))
    (show Function.Bijective _ from
      ⟨fun _ _ h => integerMap_injective hf (congrArg Subtype.val h), fun x => by
        obtain ⟨y, hy⟩ := exists_integerMap_eq hf hirr x.2
        exact ⟨y, Subtype.ext hy⟩⟩)

theorem coe_integerEquiv (y : AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer))) :
    (integerEquiv hf hirr y : AdjoinRoot (f.map (Int.castRingHom ℚ))) = integerMap p f y := by
  rw [integerEquiv, RingEquiv.ofBijective_apply]
  rfl

variable (n : ℕ)

variable (p f) in
/-- `f` over `ℤ_(p)` reduces to `f` over `ℤ / p ^ n`. -/
theorem map_padicIntegerToZModPow_map_integer :
    (f.map (Int.castRingHom (Rat.padicValuation p).integer)).map (Rat.padicIntegerToZModPow p n) =
      f.map (Int.castRingHom (ZMod (p ^ n))) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

variable (p f) in
/-- Reduction `ℤ_(p)[X] / (f) → (ℤ / p ^ n)[X] / (f)` of the coefficients. -/
noncomputable def integerReduction :
    AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer)) →+* GaloisRing p n f :=
  map (Rat.padicIntegerToZModPow p n) _ _ (map_padicIntegerToZModPow_map_integer p f n).symm.dvd

/-- **Reduction modulo `p ^ n`** of the valuation ring `O = ℤ_(p)[X] / (f)`: reduce each
coordinate in the basis `1, X, …, X ^ (deg f - 1)` modulo `p ^ n`. -/
noncomputable def reduction : (padicValuation p hf hirr).integer →+* GaloisRing p n f :=
  (integerReduction p f n).comp (integerEquiv hf hirr).symm.toRingHom

theorem reduction_integerEquiv
    (y : AdjoinRoot (f.map (Int.castRingHom (Rat.padicValuation p).integer))) :
    reduction hf hirr n (integerEquiv hf hirr y) = integerReduction p f n y := by
  simp [reduction]

variable {n} in
/-- **The reductions are compatible**: reducing modulo `p ^ N` and then modulo `p ^ n`, `n ≤ N`,
is reducing modulo `p ^ n`. -/
theorem castHom_comp_reduction {N : ℕ} (h : n ≤ N) :
    (map (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))) _ _
      (GaloisRing.map_castHom_map f (pow_dvd_pow p h)).symm.dvd).comp (reduction hf hirr N) =
        reduction hf hirr n := by
  have key : (map (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n))) _ _
      (GaloisRing.map_castHom_map f (pow_dvd_pow p h)).symm.dvd).comp (integerReduction p f N) =
        integerReduction p f n := by
    refine ringHom_ext (RingHom.ext fun a => ?_) ?_
    · simp only [integerReduction, RingHom.comp_apply, map_of]
      congr 1
      exact RingHom.congr_fun (Rat.castHom_comp_padicIntegerToZModPow p h) a
    · simp only [integerReduction, RingHom.comp_apply, map_root]
  ext x
  obtain ⟨y, rfl⟩ := (integerEquiv hf hirr).surjective x
  rw [RingHom.comp_apply, reduction_integerEquiv, reduction_integerEquiv, ← key,
    RingHom.comp_apply]

/-- **On `ℤ[X] / (f)` the reduction reduces the integer coefficients.** -/
theorem reduction_toRat (o : AdjoinRoot f) :
    reduction hf hirr n ⟨map (Int.castRingHom ℚ) f _ dvd_rfl o,
      (Valuation.mem_integer_iff _ _).mpr (padicValuation_map_le_one hf hirr o)⟩ =
        map (Int.castRingHom (ZMod (p ^ n))) f _ dvd_rfl o := by
  obtain ⟨P, rfl⟩ := mk_surjective o
  have hcoe : (integerEquiv hf hirr
      (mk _ (P.map (Int.castRingHom (Rat.padicValuation p).integer))) :
      AdjoinRoot (f.map (Int.castRingHom ℚ))) = map (Int.castRingHom ℚ) f _ dvd_rfl (mk f P) := by
    rw [coe_integerEquiv, integerMap_mk, map_mk, Polynomial.map_map]
    congr 2
  have hy : integerEquiv hf hirr (mk _ (P.map (Int.castRingHom (Rat.padicValuation p).integer))) =
      ⟨map (Int.castRingHom ℚ) f _ dvd_rfl (mk f P),
        (Valuation.mem_integer_iff _ _).mpr (padicValuation_map_le_one hf hirr _)⟩ :=
    Subtype.ext hcoe
  rw [← hy, reduction_integerEquiv, integerReduction, map_mk, map_mk,
    Polynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

/-- **On `ℤ_(p)` the reduction is `Rat.padicIntegerToZModPow`.** -/
theorem reduction_algebraMap (q : (Rat.padicValuation p).integer)
    (hq : algebraMap ℚ (AdjoinRoot (f.map (Int.castRingHom ℚ))) q ∈
      (padicValuation p hf hirr).integer) :
    reduction hf hirr n ⟨_, hq⟩ =
      algebraMap (ZMod (p ^ n)) _ (Rat.padicIntegerToZModPow p n q) := by
  have hy : integerEquiv hf hirr (of _ q) = ⟨_, hq⟩ := by
    apply Subtype.ext
    rw [coe_integerEquiv, integerMap, map_of]
    rfl
  rw [← hy, reduction_integerEquiv, integerReduction, map_of]
  rfl

end AdjoinRoot
