/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/Padics/`)

public import Complexity.Init
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Valuation.Integers
import Complexity.Foundations.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# The `p`-adic valuation of `ℚ[X] / (f)` for `f` irreducible modulo `p`

Let `p` be a prime and `f` a monic integer polynomial that is irreducible modulo `p`. Then `f` is
irreducible over `ℚ` (`AdjoinRoot.irreducible_map_rat`), so `K = ℚ[X] / (f)` is a field. Give each
element of `K` its coordinates in the basis `1, X, …, X ^ (deg f - 1)`, and let `v x` be the
largest `p`-adic valuation `Rat.padicValuation p` of a coordinate; written additively, `v x` is the
least `p`-adic order of a coordinate. This file proves that `v` is a valuation of `K`
(`AdjoinRoot.padicValuation`): it is multiplicative and ultrametric.

Multiplicativity is the substantial point. Every element of `K` is a rational multiple
`r • x₀` of the image `x₀` of an element of `ℤ[X] / (f)` that is nonzero modulo `p`, and such
`x₀` have `v x₀ = 1`. Reduction modulo `p` is a ring map into the field `𝔽_p[X] / (f)`, so a
product of two such elements is again nonzero modulo `p`.

The valuation ring `O = {x | v x ≤ 1}` of `v` consists of the elements whose coordinates have no
`p` in their denominators, that is `ℤ_(p)[X] / (f)` (`AdjoinRoot.mem_integer_padicValuation_iff`),
and an element of `O` with `v x = 1`, one that is nonzero modulo `p`, is a unit of `O`
(`AdjoinRoot.isUnit_of_padicValuation_eq_one`).

This is the 2-adic valuation `v₂` of the coefficient field `K = ℚ[U] / (f)` of [OpenAI2026ETH]
(§D.4.1, p. 57), with `v₂ x = n` corresponding to `v x = exp (-n)`.

## Main definitions

* `AdjoinRoot.padicValuation`: the `p`-adic valuation of `ℚ[X] / (f)`.

## Main results

* `AdjoinRoot.irreducible_map_rat`: `f` is irreducible over `ℚ`.
* `AdjoinRoot.padicValuation_apply`: `v x` is the largest valuation of a coordinate of `x`.
* `AdjoinRoot.padicValuation_algebraMap`: `v` extends `Rat.padicValuation p`.
* `AdjoinRoot.padicValuation_map_eq_one_iff`: an element of `ℤ[X] / (f)` has valuation one
  exactly when it is nonzero modulo `p`.
* `AdjoinRoot.mem_integer_padicValuation_iff`: the valuation ring is `ℤ_(p)[X] / (f)`.
* `AdjoinRoot.isUnit_of_padicValuation_eq_one`: elements of valuation one are units of it.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1, p. 57.
-/

public section

open Polynomial
open scoped WithZero

namespace AdjoinRoot

variable (p : ℕ) [hp : Fact p.Prime] {f : ℤ[X]}

/-- **Irreducible modulo `p` implies irreducible over `ℚ`**, for monic `f`. -/
theorem irreducible_map_rat (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    Irreducible (f.map (Int.castRingHom ℚ)) :=
  (hf.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp
    (Monic.irreducible_of_irreducible_map _ _ hf hirr)

variable {p}

/-- The reduced representative has degree below `deg g`. -/
private theorem degree_modByMonicHom_lt {R : Type*} [CommRing R] [Nontrivial R] {g : R[X]}
    (hg : g.Monic) (x : AdjoinRoot g) : (modByMonicHom hg x).degree < g.degree := by
  obtain ⟨Q, rfl⟩ := mk_surjective x
  rw [modByMonicHom_mk]
  exact degree_modByMonic_lt _ hg

variable (p) in
/-- The largest `p`-adic valuation of a coordinate of `x` in the basis `1, X, …, X ^ (deg f - 1)`.
-/
private noncomputable def coordVal (hf : f.Monic) (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    ℤᵐ⁰ :=
  (Finset.range f.natDegree).sup fun i =>
    Rat.padicValuation p ((modByMonicHom (hf.map (Int.castRingHom ℚ)) x).coeff i)

private theorem coordVal_smul_le (hf : f.Monic) (r : ℚ)
    (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    coordVal p hf (r • x) ≤ Rat.padicValuation p r * coordVal p hf x := by
  refine Finset.sup_le fun i hi => ?_
  rw [LinearMap.map_smul_of_tower, coeff_smul, smul_eq_mul, map_mul]
  exact mul_le_mul_right (Finset.le_sup (f := fun i => Rat.padicValuation p
    ((modByMonicHom (hf.map (Int.castRingHom ℚ)) x).coeff i)) hi) _

/-- The coordinates scale with rational scalars. -/
private theorem coordVal_smul (hf : f.Monic) (r : ℚ)
    (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    coordVal p hf (r • x) = Rat.padicValuation p r * coordVal p hf x := by
  refine le_antisymm (coordVal_smul_le hf r x) ?_
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have h := coordVal_smul_le (p := p) hf r⁻¹ (r • x)
  rw [inv_smul_smul₀ hr, map_inv₀] at h
  calc
    Rat.padicValuation p r * coordVal p hf x
        ≤ Rat.padicValuation p r * ((Rat.padicValuation p r)⁻¹ * coordVal p hf (r • x)) :=
      mul_le_mul_right h _
    _ = coordVal p hf (r • x) := by
      rw [← mul_assoc, mul_inv_cancel₀ ((Rat.padicValuation p).ne_zero_iff.mpr hr), one_mul]

/-- The image of `ℤ[X] / (f)` in `ℚ[X] / (f)`. -/
private noncomputable abbrev toRat (f : ℤ[X]) :
    AdjoinRoot f →+* AdjoinRoot (f.map (Int.castRingHom ℚ)) :=
  map (Int.castRingHom ℚ) f _ dvd_rfl

/-- Reduction of `ℤ[X] / (f)` modulo `p`. -/
private noncomputable abbrev toZMod (p : ℕ) (f : ℤ[X]) :
    AdjoinRoot f →+* AdjoinRoot (f.map (Int.castRingHom (ZMod p))) :=
  map (Int.castRingHom (ZMod p)) f _ dvd_rfl

/-- The coordinates of the image of `ℤ[X] / (f)` are the integer coordinates. -/
private theorem modByMonicHom_toRat (hf : f.Monic) (o : AdjoinRoot f) :
    modByMonicHom (hf.map (Int.castRingHom ℚ)) (toRat f o) =
      (modByMonicHom hf o).map (Int.castRingHom ℚ) := by
  obtain ⟨Q, rfl⟩ := mk_surjective o
  rw [toRat, map_mk, modByMonicHom_mk, modByMonicHom_mk, map_modByMonic _ hf]

/-- **Images of `ℤ[X] / (f)` have valuation one exactly when they are nonzero modulo `p`**, and at
most one in any case. -/
private theorem coordVal_toRat_eq_one_iff (hf : f.Monic) (o : AdjoinRoot f) :
    coordVal p hf (toRat f o) ≤ 1 ∧
      (coordVal p hf (toRat f o) = 1 ↔ toZMod p f o ≠ 0) := by
  set Q := modByMonicHom hf o
  have hQdeg : ∀ i, f.natDegree ≤ i → Q.coeff i = 0 := fun i hi =>
    coeff_eq_zero_of_degree_lt ((degree_modByMonicHom_lt hf o).trans_le
      ((degree_le_natDegree).trans (by exact_mod_cast hi)))
  have hval : ∀ i, Rat.padicValuation p ((modByMonicHom (hf.map (Int.castRingHom ℚ))
      (toRat f o)).coeff i) = Int.padicValuation p (Q.coeff i) := fun i => by
    rw [modByMonicHom_toRat, coeff_map, eq_intCast, Rat.padicValuation_cast]
  have hle : coordVal p hf (toRat f o) ≤ 1 :=
    Finset.sup_le fun i _ => (hval i).trans_le (Int.padicValuation_le_one p _)
  refine ⟨hle, ?_⟩
  rw [Ne, toZMod, map_eq_zero_iff _ hf dvd_rfl rfl]
  simp only [eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h1 hdvd
    have hlt : coordVal p hf (toRat f o) < 1 := by
      refine (Finset.sup_lt_iff (bot_lt_iff_ne_bot.mpr (by simp))).mpr fun i _ => ?_
      rw [hval]
      exact Int.padicValuation_lt_one_iff.mpr (hdvd i)
    exact hlt.ne h1
  · intro hndvd
    obtain ⟨i, hi⟩ := not_forall.mp hndvd
    have hie : i < f.natDegree := by
      by_contra hie
      exact hi (by rw [hQdeg i (not_lt.mp hie)]; exact dvd_zero _)
    refine le_antisymm hle ?_
    rw [← Int.padicValuation_eq_one_iff.mpr hi, ← hval]
    exact Finset.le_sup (f := fun i => Rat.padicValuation p
      ((modByMonicHom (hf.map (Int.castRingHom ℚ)) (toRat f o)).coeff i)) (Finset.mem_range.mpr hie)

/-- **Every element is a rational multiple of an integral element that is nonzero modulo `p`.**
Clear the denominators of the coordinates and divide by the content. -/
private theorem exists_eq_smul_toRat (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))
    (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    ∃ r : ℚ, ∃ o : AdjoinRoot f, toZMod p f o ≠ 0 ∧ x = r • toRat f o := by
  have := Fact.mk hirr
  set P := modByMonicHom (hf.map (Int.castRingHom ℚ)) x
  have hx : mk _ P = x := mk_leftInverse _ x
  rcases eq_or_ne P 0 with hP | hP
  · refine ⟨0, 1, by rw [map_one]; exact one_ne_zero, ?_⟩
    rw [zero_smul, ← hx, hP, map_zero]
  obtain ⟨b, hb, hQ₀'⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) P
  set Q₀ := IsLocalization.integerNormalization (nonZeroDivisors ℤ) P
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hb
  have hQ₀ : Q₀.map (Int.castRingHom ℚ) = C (b : ℚ) * P := by
    rw [← algebraMap_int_eq, hQ₀', ← Int.cast_smul_eq_zsmul ℚ, smul_eq_C_mul]
  have hQ₀ne : Q₀ ≠ 0 := by
    rintro h
    rw [h, Polynomial.map_zero] at hQ₀
    exact mul_ne_zero (C_ne_zero.mpr hb0) hP hQ₀.symm
  set Q₁ := Q₀.primPart
  have hdeg : Q₁.degree < (f.map (Int.castRingHom (ZMod p))).degree := by
    rw [hf.degree_map, degree_eq_natDegree (primPart_ne_zero Q₀), natDegree_primPart]
    have hPdeg : P.degree < f.degree :=
      (hf.degree_map (Int.castRingHom ℚ)) ▸ degree_modByMonicHom_lt (hf.map _) x
    have : Q₀.degree < f.degree := by
      refine lt_of_le_of_lt ?_ hPdeg
      rw [← degree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)) Q₀, hQ₀]
      exact degree_mul_le_of_le (degree_C_le) le_rfl |>.trans (by simp)
    rwa [degree_eq_natDegree hQ₀ne] at this
  have hred : (Q₁.map (Int.castRingHom (ZMod p))) ≠ 0 := by
    intro h0
    have hdvd : C (p : ℤ) ∣ Q₁ := (C_dvd_iff_dvd_coeff _ _).mpr fun i => by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
        h0, coeff_zero]
    have hu := isPrimitive_primPart Q₀ (p : ℤ) hdvd
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hu
    exact hp.out.one_lt.ne' hu
  refine ⟨Q₀.content / b, mk f Q₁, ?_, ?_⟩
  · rw [toZMod, map_mk, Ne, mk_eq_zero]
    exact (hf.map _).not_dvd_of_degree_lt hred ((degree_map_le).trans_lt hdeg)
  · rw [toRat, map_mk, ← hx, Algebra.smul_def, algebraMap_eq, ← mk_C, ← map_mul]
    congr 1
    have h := congrArg (Polynomial.map (Int.castRingHom ℚ)) (eq_C_content_mul_primPart Q₀)
    rw [Polynomial.map_mul, map_C, hQ₀, eq_intCast] at h
    calc
      P = C (b : ℚ)⁻¹ * (C (b : ℚ) * P) := by
        rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
      _ = C ((Q₀.content : ℚ) / b) * Q₁.map (Int.castRingHom ℚ) := by
        rw [h, ← mul_assoc, ← C_mul, div_eq_inv_mul]

variable (p) in
/-- **The `p`-adic valuation of `ℚ[X] / (f)`**, for `f` monic and irreducible modulo `p`: the
largest `p`-adic valuation of a coordinate in the basis `1, X, …, X ^ (deg f - 1)`. It extends
`Rat.padicValuation p` (`AdjoinRoot.padicValuation_algebraMap`). -/
noncomputable def padicValuation (hf : f.Monic)
    (hirr : Irreducible (f.map (Int.castRingHom (ZMod p)))) :
    Valuation (AdjoinRoot (f.map (Int.castRingHom ℚ))) ℤᵐ⁰ where
  toFun := coordVal p hf
  map_zero' := by
    simp only [coordVal, map_zero, coeff_zero]
    exact Finset.sup_bot _
  map_one' := by
    have := (coordVal_toRat_eq_one_iff (p := p) hf 1).2.mpr (by
      have := Fact.mk hirr
      rw [map_one]; exact one_ne_zero)
    rwa [map_one] at this
  map_mul' x y := by
    have := Fact.mk hirr
    obtain ⟨r, o, ho, rfl⟩ := exists_eq_smul_toRat hf hirr x
    obtain ⟨r', o', ho', rfl⟩ := exists_eq_smul_toRat hf hirr y
    rw [smul_mul_smul_comm, ← map_mul, coordVal_smul, coordVal_smul, coordVal_smul, map_mul,
      (coordVal_toRat_eq_one_iff hf _).2.mpr (by rw [map_mul]; exact mul_ne_zero ho ho'),
      (coordVal_toRat_eq_one_iff hf _).2.mpr ho, (coordVal_toRat_eq_one_iff hf _).2.mpr ho',
      mul_one, mul_one, mul_one]
  map_add_le_max' x y := by
    refine Finset.sup_le fun i hi => ?_
    rw [map_add, coeff_add]
    refine ((Rat.padicValuation p).map_add _ _).trans (max_le_max ?_ ?_) <;>
      exact Finset.le_sup (f := fun i => Rat.padicValuation p _) hi

variable (hf : f.Monic) (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))

/-- The valuation is the largest `p`-adic valuation of a coordinate. -/
theorem padicValuation_apply (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    padicValuation p hf hirr x = (Finset.range f.natDegree).sup fun i =>
      Rat.padicValuation p ((modByMonicHom (hf.map (Int.castRingHom ℚ)) x).coeff i) := by
  simp only [padicValuation]
  rfl

/-- **The valuation extends the `p`-adic valuation of `ℚ`.** -/
theorem padicValuation_algebraMap (r : ℚ) :
    padicValuation p hf hirr (algebraMap ℚ _ r) = Rat.padicValuation p r := by
  rw [Algebra.algebraMap_eq_smul_one, ← mul_one (Rat.padicValuation p r),
    ← (padicValuation p hf hirr).map_one]
  exact coordVal_smul hf r 1

/-- **An element of `ℤ[X] / (f)` has valuation one exactly when it is nonzero modulo `p`.** -/
theorem padicValuation_map_eq_one_iff (o : AdjoinRoot f) :
    padicValuation p hf hirr (map (Int.castRingHom ℚ) f _ dvd_rfl o) = 1 ↔
      map (Int.castRingHom (ZMod p)) f _ dvd_rfl o ≠ 0 :=
  (coordVal_toRat_eq_one_iff hf o).2

/-- Elements of `ℤ[X] / (f)` have valuation at most one. -/
theorem padicValuation_map_le_one (o : AdjoinRoot f) :
    padicValuation p hf hirr (map (Int.castRingHom ℚ) f _ dvd_rfl o) ≤ 1 :=
  (coordVal_toRat_eq_one_iff hf o).1

/-- **The valuation ring is `ℤ_(p)[X] / (f)`**: the elements whose coordinates have no `p` in their
denominators. -/
theorem mem_integer_padicValuation_iff (x : AdjoinRoot (f.map (Int.castRingHom ℚ))) :
    x ∈ (padicValuation p hf hirr).integer ↔
      ∀ i, Rat.padicValuation p ((modByMonicHom (hf.map (Int.castRingHom ℚ)) x).coeff i) ≤ 1 := by
  rw [Valuation.mem_integer_iff, padicValuation_apply, Finset.sup_le_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  rcases lt_or_ge i f.natDegree with hi | hi
  · exact h i (Finset.mem_range.mpr hi)
  · rw [coeff_eq_zero_of_degree_lt, map_zero]
    · exact zero_le
    refine (degree_modByMonicHom_lt (hf.map _) x).trans_le ?_
    rw [hf.degree_map]
    exact (degree_le_natDegree).trans (by exact_mod_cast hi)

/-- **Elements of the valuation ring that are nonzero modulo `p` are units of it**: an element of
valuation one has an inverse of valuation one. -/
theorem isUnit_of_padicValuation_eq_one {x : AdjoinRoot (f.map (Int.castRingHom ℚ))}
    (hx : x ∈ (padicValuation p hf hirr).integer) (h1 : padicValuation p hf hirr x = 1) :
    IsUnit (⟨x, hx⟩ : (padicValuation p hf hirr).integer) := by
  have := Fact.mk (irreducible_map_rat p hf hirr)
  exact (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.mpr h1

end AdjoinRoot
