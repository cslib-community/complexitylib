/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, Galois rings)

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.RingLagrange
public import Complexity.Foundations.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Galois rings

For a prime `p`, an exponent `n ≠ 0` and an integer polynomial `f` that is monic and irreducible
modulo `p`, the *Galois ring* `GaloisRing p n f = (ℤ / p ^ n)[X] / (f)` is a local ring. Its maximal
ideal is `(p)`, and reduction modulo `p` identifies its residue field with `𝔽_p[X] / (f)`, the
finite field with `p ^ deg f` elements. In particular an element is a unit exactly when it is
nonzero modulo `p`.

The *digit lifts* `∑ i, c i * X ^ i` with digits `c i ∈ {0, …, p - 1}` reduce to the `p ^ deg f`
distinct residue-field elements, so any two of them differ by a unit, and Lagrange interpolation
over the ring holds at any set of them (`GaloisRing.eq_ringInterpolate_digitLift`).

This is the base coefficient ring of the Boolean tensor contraction of [OpenAI2026ETH] (§D.4.1,
pp. 57–58), with `p = 2`, a degree `e = 4 ⌈log₂ s⌉` and the precision `n`. The manuscript puts
`O = ℤ_(2)[U] / (f)` and `A = O[V] / (V ^ ℓ)`, and computes in `A / (2 ^ n)` (written `A_p` there,
with `p` the precision). `GaloisRing 2 n f` corresponds to `O / (2 ^ n)`, since
`ℤ_(2) / (2 ^ n) ≅ ℤ / 2 ^ n` (that identification is not formalized here). It is therefore the
manuscript's `A / (2 ^ n)` only when `ℓ = 1`; the truncated `V`-extension for general `ℓ` is not
formalized here. The manuscript's binary-coordinate lifts are the digit lifts for `p = 2`.

The argument is that of a surjection onto a field with nilpotent kernel
(`RingHom.isUnit_iff_ne_zero_of_isNilpotent`): reduction modulo `p` has kernel `(p)`, and
`p ^ n = 0`. The manuscript states the unit criterion for `ℤ_(2)[U] / (f)` and proves it with the
determinant of the multiplication matrix; at a finite precision the nilpotent kernel suffices. The
statement over `ℤ_(p)` is `AdjoinRoot.isUnit_of_padicValuation_eq_one`.

## Main definitions

* `GaloisRing`: the ring `(ℤ / p ^ n)[X] / (f)`.
* `GaloisRing.residue`: reduction modulo `p`, onto `𝔽_p[X] / (f)`.
* `GaloisRing.digitLift`: the lift `∑ i, c i * X ^ i` of a digit vector.

## Main results

* `RingHom.isLocalHom_of_isNilpotent`: a surjection with nilpotent kernel is a local
  homomorphism.
* `GaloisRing.ker_residue`: the kernel of reduction modulo `p` is `(p)`.
* `GaloisRing.isUnit_iff`: an element is a unit exactly when it is nonzero modulo `p`.
* `GaloisRing.instIsLocalRing`, `GaloisRing.maximalIdeal_eq`: the ring is local with maximal ideal
  `(p)`.
* `GaloisRing.residueFieldEquiv`, `GaloisRing.algEquivGaloisField`: its residue field is
  `𝔽_p[X] / (f) ≃ GaloisField p (deg f)`.
* `GaloisRing.isUnit_digitLift_sub`: distinct digit lifts differ by a unit.
* `GaloisRing.eq_ringInterpolate_digitLift`: Lagrange interpolation at digit lifts.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.1, pp. 57–58.
-/

public section

open Polynomial IsLocalRing

/-! ### Surjections with nilpotent kernel -/

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism whose kernel consists of nilpotent elements is local: if `ψ x`
is a unit then `x y = 1 + n` for some `y` and nilpotent `n`. -/
theorem isLocalHom_of_isNilpotent (ψ : R →+* S) (hψ : Function.Surjective ψ)
    (hnil : ∀ x, ψ x = 0 → IsNilpotent x) : IsLocalHom ψ where
  map_nonunit x hx := by
    obtain ⟨u, hu⟩ := hx
    obtain ⟨y, hy⟩ := hψ ↑u⁻¹
    have hn : IsNilpotent (x * y - 1) :=
      hnil _ (by rw [map_sub, map_mul, map_one, hy, ← hu, Units.mul_inv, sub_self])
    have h1 : IsUnit (x * y) := by
      simpa only [add_sub_cancel] using hn.isUnit_one_add
    exact isUnit_of_mul_isUnit_left h1

/-- Over a surjection onto a field with nilpotent kernel, an element is a unit exactly when its
image is nonzero. -/
theorem isUnit_iff_ne_zero_of_isNilpotent {F : Type*} [Field F] (ψ : R →+* F)
    (hψ : Function.Surjective ψ) (hnil : ∀ x, ψ x = 0 → IsNilpotent x) {x : R} :
    IsUnit x ↔ ψ x ≠ 0 := by
  have := ψ.isLocalHom_of_isNilpotent hψ hnil
  exact ⟨fun h => (h.map ψ).ne_zero, fun h => isUnit_of_map_unit ψ x (Ne.isUnit h)⟩

end RingHom

/-! ### Galois rings -/

/-- The ring `(ℤ / p ^ n)[X] / (f)` presented by an integer polynomial `f`. For a prime `p`,
`n ≠ 0` and `f` monic and irreducible modulo `p`, it is the *Galois ring* of characteristic
`p ^ n` and rank `deg f`: a local ring with maximal ideal `(p)` and residue field
`𝔽_{p ^ deg f}`. -/
abbrev GaloisRing (p n : ℕ) (f : ℤ[X]) : Type :=
  AdjoinRoot (f.map (Int.castRingHom (ZMod (p ^ n))))

namespace GaloisRing

variable (p n : ℕ) (f : ℤ[X])

/-- Reducing integer coefficients modulo `m` and then modulo a divisor `d` of `m` is reducing
modulo `d`. -/
theorem map_castHom_map {d m : ℕ} (h : d ∣ m) :
    (f.map (Int.castRingHom (ZMod m))).map (ZMod.castHom h (ZMod d)) =
      f.map (Int.castRingHom (ZMod d)) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

/-- The *digit lift* `∑ i, c i * X ^ i` of a digit vector `c`, with each digit `c i ∈ ZMod p` read
as an integer in `{0, …, p - 1}`. For `p = 2` these are the binary-coordinate lifts of
[OpenAI2026ETH] (§D.4.1, p. 58). -/
@[expose] noncomputable def digitLift (c : Fin f.natDegree → ZMod p) : GaloisRing p n f :=
  ∑ i, ((c i).val : GaloisRing p n f) * AdjoinRoot.root _ ^ (i : ℕ)

variable [NeZero n]

/-- Reduction modulo `p`, from `(ℤ / p ^ n)[X] / (f)` onto `𝔽_p[X] / (f)`. -/
noncomputable def residue : GaloisRing p n f →+* AdjoinRoot (f.map (Int.castRingHom (ZMod p))) :=
  AdjoinRoot.map (ZMod.castHom (dvd_pow_self p (NeZero.ne n)) (ZMod p)) _ _
    (map_castHom_map f _).symm.dvd

@[simp]
theorem residue_mk (P : (ZMod (p ^ n))[X]) :
    residue p n f (AdjoinRoot.mk _ P) =
      AdjoinRoot.mk _ (P.map (ZMod.castHom (dvd_pow_self p (NeZero.ne n)) (ZMod p))) :=
  AdjoinRoot.map_mk _ _ _ P

@[simp]
theorem residue_root : residue p n f (AdjoinRoot.root _) = AdjoinRoot.root _ :=
  AdjoinRoot.map_root _ _ _ _

@[simp]
theorem residue_of (a : ZMod (p ^ n)) :
    residue p n f (AdjoinRoot.of _ a) =
      AdjoinRoot.of _ (ZMod.castHom (dvd_pow_self p (NeZero.ne n)) (ZMod p) a) :=
  AdjoinRoot.map_of _ _ _ _ _

theorem residue_surjective : Function.Surjective (residue p n f) :=
  AdjoinRoot.map_surjective_of_surjective _ _ _ (ZMod.castHom_surjective _)

variable {p n f} [Fact p.Prime]

variable (p n f) in
/-- A digit lift reduces to `∑ i, c i * X ^ i` modulo `p`. -/
theorem residue_digitLift (c : Fin f.natDegree → ZMod p) :
    residue p n f (digitLift p n f c) = AdjoinRoot.mk _ (∑ i, C (c i) * X ^ (i : ℕ)) := by
  simp only [digitLift, map_sum, map_mul, map_pow, map_natCast, residue_root, AdjoinRoot.mk_C,
    AdjoinRoot.mk_X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_natCast (AdjoinRoot.of _), ZMod.natCast_zmod_val]

/-- Digit lifts reduce to distinct elements modulo `p`: the coordinates `1, X, …, X ^ (deg f - 1)`
are independent in `𝔽_p[X] / (f)` for monic `f`. -/
theorem residue_digitLift_injective (hf : f.Monic) :
    Function.Injective fun c : Fin f.natDegree → ZMod p => residue p n f (digitLift p n f c) := by
  intro c c' h
  simp only [residue_digitLift] at h
  rw [AdjoinRoot.mk_eq_mk, ← Finset.sum_sub_distrib] at h
  set P : (ZMod p)[X] := ∑ i, (C (c i) * X ^ (i : ℕ) - C (c' i) * X ^ (i : ℕ))
  have hcoeff : ∀ i : Fin f.natDegree, P.coeff i = c i - c' i := fun i => by
    simp only [P, finsetSum_coeff, coeff_sub, coeff_C_mul, coeff_X_pow, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i (fun j _ hji => ?_) (by simp), ite_eq_left rfl, ite_eq_left rfl]
    rw [ite_eq_right fun h => hji (Fin.ext h.symm), ite_eq_right fun h => hji (Fin.ext h.symm),
      sub_zero]
  have hP : P = 0 := by
    by_contra h0
    refine (hf.map (Int.castRingHom (ZMod p))).not_dvd_of_degree_lt h0 ?_ h
    rw [hf.degree_map, degree_eq_natDegree hf.ne_zero]
    refine (degree_sum_le _ _).trans_lt
      ((Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ => ?_)
    refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_) <;>
      exact (degree_C_mul_X_pow_le _ _).trans_lt (by exact_mod_cast i.isLt)
  funext i
  have := hcoeff i
  rw [hP, coeff_zero] at this
  exact (sub_eq_zero.mp this.symm)


/-- An element of `ℤ / p ^ n` that vanishes modulo `p` is a multiple of `p`. -/
private theorem dvd_of_castHom_eq_zero {a : ZMod (p ^ n)}
    (ha : ZMod.castHom (dvd_pow_self p (NeZero.ne n)) (ZMod p) a = 0) : (p : ZMod (p ^ n)) ∣ a := by
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [map_natCast, ZMod.natCast_eq_zero_iff] at ha
  obtain ⟨m, rfl⟩ := ha
  exact ⟨m, by push_cast; ring⟩

/-- **The kernel of reduction modulo `p` is `(p)`**, when `f` is monic. -/
theorem ker_residue (hf : f.Monic) :
    RingHom.ker (residue p n f) = Ideal.span {(p : GaloisRing p n f)} := by
  ext x
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    rw [residue, AdjoinRoot.map_eq_zero_iff _ (hf.map _) _
      (map_castHom_map f (dvd_pow_self p (NeZero.ne n))).symm] at hx
    obtain ⟨Q, hQ⟩ := (C_dvd_iff_dvd_coeff (p : ZMod (p ^ n)) _).mpr fun i =>
      dvd_of_castHom_eq_zero (hx i)
    refine ⟨AdjoinRoot.mk _ Q, ?_⟩
    rw [← AdjoinRoot.mk_leftInverse (hf.map _) x, hQ, map_mul, AdjoinRoot.mk_C, map_natCast]
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ← map_natCast (AdjoinRoot.of _), ZMod.natCast_self, map_zero,
      zero_mul]

/-- `p ^ n = 0`, so elements that vanish modulo `p` are nilpotent. -/
theorem isNilpotent_of_residue_eq_zero (hf : f.Monic) {x : GaloisRing p n f}
    (hx : residue p n f x = 0) : IsNilpotent x := by
  rw [← RingHom.mem_ker, ker_residue hf, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨n, ?_⟩
  rw [mul_pow, ← Nat.cast_pow, ← map_natCast (AdjoinRoot.of _), ZMod.natCast_self, map_zero,
    zero_mul]

variable (hf : f.Monic) (hirr : Irreducible (f.map (Int.castRingHom (ZMod p))))
include hf hirr

/-- **Units are the elements that are nonzero modulo `p`.** -/
theorem isUnit_iff {x : GaloisRing p n f} : IsUnit x ↔ residue p n f x ≠ 0 :=
  have := Fact.mk hirr
  (residue p n f).isUnit_iff_ne_zero_of_isNilpotent (residue_surjective p n f) fun _ =>
    isNilpotent_of_residue_eq_zero hf

/-- **Distinct digit lifts differ by a unit.** -/
theorem isUnit_digitLift_sub {c c' : Fin f.natDegree → ZMod p} (h : c ≠ c') :
    IsUnit (digitLift p n f c - digitLift p n f c') := by
  rw [isUnit_iff hf hirr, map_sub, sub_ne_zero]
  exact fun h' => h (residue_digitLift_injective hf h')

/-- **Lagrange interpolation at digit lifts.** A polynomial over a Galois ring of degree less than
`#s`, for a set `s` of digit vectors, is the interpolant of its values at their lifts; the lifts
have unit differences. -/
theorem eq_ringInterpolate_digitLift {s : Finset (Fin f.natDegree → ZMod p)}
    {P : (GaloisRing p n f)[X]} (hP : P.degree < s.card) :
    P = Lagrange.ringInterpolate s (digitLift p n f) (fun c => P.eval (digitLift p n f c)) :=
  Lagrange.eq_ringInterpolate (fun _ _ _ _ h => isUnit_digitLift_sub hf hirr h) hP

/-- **A Galois ring is local.** -/
theorem isLocalRing : IsLocalRing (GaloisRing p n f) :=
  have := Fact.mk hirr
  have := (residue p n f).isLocalHom_of_isNilpotent (residue_surjective p n f) fun _ =>
    isNilpotent_of_residue_eq_zero hf
  (residue p n f).domain_isLocalRing

omit hirr in
/-- `𝔽_p[X] / (f)` has `p ^ deg f` elements. -/
theorem natCard_adjoinRoot :
    Nat.card (AdjoinRoot (f.map (Int.castRingHom (ZMod p)))) = p ^ f.natDegree := by
  let b := (AdjoinRoot.powerBasis' (hf.map (Int.castRingHom (ZMod p)))).basis
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, AdjoinRoot.powerBasis'_dim, hf.natDegree_map]

end GaloisRing

/-! ### The residue field -/

namespace GaloisRing

variable {p n : ℕ} {f : ℤ[X]} [NeZero n] [Fact p.Prime] [hf : Fact f.Monic]
  [hirr : Fact (Irreducible (f.map (Int.castRingHom (ZMod p))))]

instance instIsLocalRing : IsLocalRing (GaloisRing p n f) :=
  isLocalRing hf.out hirr.out

/-- **The maximal ideal of a Galois ring is `(p)`.** -/
theorem maximalIdeal_eq : maximalIdeal (GaloisRing p n f) = Ideal.span {(p : GaloisRing p n f)} :=
  by rw [← ker_residue hf.out, IsLocalRing.ker_eq_maximalIdeal _ (residue_surjective p n f)]

/-- **The residue field of a Galois ring** is `𝔽_p[X] / (f)`, by reduction modulo `p`. -/
noncomputable def residueFieldEquiv :
    ResidueField (GaloisRing p n f) ≃+* AdjoinRoot (f.map (Int.castRingHom (ZMod p))) :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal _ (residue_surjective p n f)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (residue_surjective p n f))

@[simp]
theorem residueFieldEquiv_residue (x : GaloisRing p n f) :
    residueFieldEquiv (IsLocalRing.residue _ x) = residue p n f x := by
  simp only [residueFieldEquiv]
  rfl

/-- **The residue field is the Galois field** with `p ^ deg f` elements. -/
noncomputable def algEquivGaloisField :
    AdjoinRoot (f.map (Int.castRingHom (ZMod p))) ≃ₐ[ZMod p] GaloisField p f.natDegree :=
  GaloisField.algEquivGaloisField p f.natDegree (natCard_adjoinRoot hf.out)

end GaloisRing
