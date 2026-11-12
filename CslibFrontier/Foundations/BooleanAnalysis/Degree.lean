/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Total degree and Fourier degree on the Boolean cube

Every function `f` on the cube `ι → Bool` of finitely many coordinates, with values in a
commutative ring `R`, is a unique `R`-linear combination of the monomials `∏_{i ∈ S} xᵢ`, its
multilinear representation. Its *total degree* `BitString.totalDegree f` is the least `D` such that
`f` is a combination of monomials of at most `D` coordinates, that is, the least `D` with
`f ∈ BitString.lowDegree R ι D` (`BitString.totalDegree_le_iff_mem_lowDegree`); by
`BitString.lowDegree_eq_map_restrictTotalDegree` it is also the least total degree of a polynomial
that agrees with `f` on the cube.

Over a field `F` in which `2` is invertible, the characters `chi F S` and the monomials of at most
`D` coordinates span the same functions (`BitString.chi_mem_lowDegree`,
`BitString.lowDegree_le_signSpan`). Over `ℝ`, low degree is therefore the vanishing of the Fourier
coefficients on sets of more than `D` coordinates
(`BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`), and the total degree is the largest size of a
set with a nonzero Fourier coefficient (`BitString.totalDegree_le_iff_fourierCoeff_eq_zero`,
`BitString.exists_card_eq_totalDegree_fourierCoeff_ne_zero`) [NisanSzegedy1994], [ODonnell2014].

## Main definitions

* `Cslib.BitString.signSpan`: the span of the characters of at most `H` coordinates.
* `Cslib.BitString.totalDegree`: the total degree of a function on the cube.

## Main results

* `Cslib.BitString.chi_mem_lowDegree`, `Cslib.BitString.lowDegree_le_signSpan`: characters of at
  most `H` coordinates and monomials of at most `H` coordinates span the same space when `2` is
  invertible.
* `Cslib.BitString.totalDegree_le_iff_mem_lowDegree`: over finitely many coordinates, the total
  degree is the least `D` with `f ∈ lowDegree R ι D`.
* `Cslib.BitString.mem_lowDegree_iff_fourierCoeff_eq_zero`: over `ℝ`, low degree is the vanishing
  of the Fourier coefficients on larger sets.
* `Cslib.BitString.totalDegree_le_iff_fourierCoeff_eq_zero`,
  `Cslib.BitString.exists_card_eq_totalDegree_fourierCoeff_ne_zero`: the total degree over `ℝ` is
  the largest size of a set with a nonzero Fourier coefficient.
* `Cslib.BitString.signVal_comp_mem_lowDegree_iff`, `Cslib.BitString.totalDegree_signVal_comp`:
  reading a Boolean function as `0`/`1` or as `±1` gives the same degree over `ℝ`.

## References

* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-! ### The span of characters -/

section SignSpan

variable {F : Type*} [Field F] {ι : Type*}

variable (F ι) in
/-- The span of the characters of the sets of at most `H` coordinates. -/
def signSpan (H : ℕ) : Submodule F ((ι → Bool) → F) :=
  Submodule.span F (chi F '' {S | #S ≤ H})

/-- The character of `S` has degree at most `|S|`. -/
theorem chi_mem_lowDegree (S : Finset ι) : chi F S ∈ lowDegree F ι #S := by
  have hfun : chi F S = ∏ i ∈ S, (1 - 2 * fun x : ι → Bool => bitVal F (x i)) := by
    funext x
    simp [chi, Finset.prod_apply, neg_one_pow_toNat_eq_one_sub_two_mul_bitVal]
  rw [hfun]
  simpa using prod_mem_lowDegree S (a := 1) fun i _ =>
    Submodule.sub_mem _ (one_mem_lowDegree 1) (by
      simpa [two_mul] using Submodule.add_mem _ (bitVal_mem_lowDegree (R := F) i)
        (bitVal_mem_lowDegree (R := F) i))

/-- The span of the characters of at most `H` coordinates grows with `H`. -/
theorem signSpan_mono {H K : ℕ} (hHK : H ≤ K) : signSpan F ι H ≤ signSpan F ι K :=
  Submodule.span_mono (Set.image_mono fun _ hS => le_trans hS hHK)

/-- Each monomial expands into characters of its subsets. -/
theorem monomial_mem_signSpan [Invertible (2 : F)] (S : Finset ι) :
    monomial F S ∈ signSpan F ι #S := by
  classical
  have hfun : monomial F S = ∑ T ∈ S.powerset,
      (⅟2 ^ #S * (-1) ^ #T : F) • chi F T := by
    funext x
    simp only [monomial, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, chi,
      neg_one_pow_toNat_eq_one_sub_two_mul_bitVal]
    have hsplit : ∏ i ∈ S, bitVal F (x i) = ∏ i ∈ S, (⅟2 * (-(1 - 2 * bitVal F (x i)) + 1)) :=
      Finset.prod_congr rfl fun i _ => by
        rw [show -(1 - 2 * bitVal F (x i)) + 1 = 2 * bitVal F (x i) by ring, ← mul_assoc,
          invOf_mul_self, one_mul]
    rw [hsplit, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.prod_const_one, mul_one, Finset.prod_neg]
    ring
  rw [hfun]
  exact Submodule.sum_mem _ fun T hT => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨T, Finset.card_le_card (Finset.mem_powerset.mp hT), rfl⟩)

/-- When `2` is invertible in `F`, every function of degree at most `H` lies in the span of the
characters of at most `H` coordinates. -/
theorem lowDegree_le_signSpan [Invertible (2 : F)] (H : ℕ) :
    lowDegree F ι H ≤ signSpan F ι H := by
  rw [lowDegree, Submodule.span_le]
  rintro _ ⟨S, hS, rfl⟩
  exact signSpan_mono hS (monomial_mem_signSpan S)

end SignSpan

/-! ### Total degree over a commutative ring -/

section CommRing

variable {R : Type*} [CommRing R] {ι : Type*} {f : (ι → Bool) → R} {D : ℕ}

/-- The total degree of a function on the cube: the least `D` such that `f` is an `R`-linear
combination of monomials of at most `D` coordinates, the degree of its multilinear representation.
It is `0` when there is no such `D`, which can only happen over infinitely many coordinates. -/
noncomputable def totalDegree (f : (ι → Bool) → R) : ℕ :=
  sInf {D | f ∈ lowDegree R ι D}

/-- Membership in `lowDegree R ι D` bounds `totalDegree f` above by `D`. -/
theorem totalDegree_le_of_mem_lowDegree (h : f ∈ lowDegree R ι D) : totalDegree f ≤ D :=
  Nat.sInf_le h

variable [Finite ι]

/-- A function on finitely many coordinates is a combination of monomials of at most its total
degree coordinates. -/
theorem mem_lowDegree_totalDegree (f : (ι → Bool) → R) : f ∈ lowDegree R ι (totalDegree f) :=
  have := Fintype.ofFinite ι
  Nat.sInf_mem (s := {D | f ∈ lowDegree R ι D}) ⟨_, mem_lowDegree_self f⟩

/-- **Total degree as low degree**: the total degree is at most `D` exactly when `f` is a
combination of monomials of at most `D` coordinates. -/
theorem totalDegree_le_iff_mem_lowDegree : totalDegree f ≤ D ↔ f ∈ lowDegree R ι D :=
  ⟨fun h => lowDegree_mono h (mem_lowDegree_totalDegree f), totalDegree_le_of_mem_lowDegree⟩

omit [Finite ι] in
/-- The total degree is at most the number of coordinates. -/
theorem totalDegree_le_card [Fintype ι] (f : (ι → Bool) → R) : totalDegree f ≤ Fintype.card ι :=
  totalDegree_le_of_mem_lowDegree (mem_lowDegree_self f)

omit [Finite ι] in
/-- Negating every input bit preserves the total degree. -/
theorem totalDegree_comp_not (f : (ι → Bool) → R) :
    totalDegree (fun x => f fun i => !x i) = totalDegree f := by
  refine congrArg sInf (Set.ext fun D => ⟨fun h => ?_, comp_not_mem_lowDegree⟩)
  have h' := comp_not_mem_lowDegree h
  simp only [Bool.not_not] at h'
  exact h'

end CommRing

/-! ### Total degree and Fourier coefficients -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {f : (ι → Bool) → ℝ} {D : ℕ}

/-- Characters of at most `D` coordinates have no Fourier weight on sets of more than `D`
coordinates, and neither do their combinations. -/
private theorem signSpan_le_ker_fourierCoeffₗ {S : Finset ι} (hS : D < #S) :
    signSpan ℝ ι D ≤ LinearMap.ker (fourierCoeffₗ S) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, rfl⟩
  have hTS : T ≠ S := by
    rintro rfl
    exact absurd hT (not_le.2 hS)
  change fourierCoeff (chi ℝ T) S = 0
  simp only [fourierCoeff_chi, hTS, ↓reduceIte]

/-- A function of total degree at most `D` has no Fourier weight on sets of more than `D`
coordinates. -/
theorem fourierCoeff_eq_zero_of_mem_lowDegree (hf : f ∈ lowDegree ℝ ι D) {S : Finset ι}
    (hS : D < #S) : fourierCoeff f S = 0 :=
  letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  signSpan_le_ker_fourierCoeffₗ hS (lowDegree_le_signSpan D hf)

/-- **Low degree is Fourier degree**: a real function is a combination of monomials of at most `D`
coordinates exactly when its Fourier coefficients on sets of more than `D` coordinates vanish. -/
theorem mem_lowDegree_iff_fourierCoeff_eq_zero :
    f ∈ lowDegree ℝ ι D ↔ ∀ S : Finset ι, D < #S → fourierCoeff f S = 0 := by
  refine ⟨fun hf S hS => fourierCoeff_eq_zero_of_mem_lowDegree hf hS, fun h => ?_⟩
  have hf : f = ∑ S, fourierCoeff f S • chi ℝ S := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (sum_fourierCoeff_mul_chi f x).symm
  rw [hf]
  refine Submodule.sum_mem _ fun S _ => ?_
  by_cases hS : #S ≤ D
  · exact Submodule.smul_mem _ _ (lowDegree_mono hS (chi_mem_lowDegree S))
  · rw [h S (not_le.1 hS), zero_smul]
    exact Submodule.zero_mem _

/-- A nonzero Fourier coefficient bounds the total degree below. -/
theorem card_le_totalDegree_of_fourierCoeff_ne_zero {S : Finset ι} (h : fourierCoeff f S ≠ 0) :
    #S ≤ totalDegree f :=
  not_lt.1 fun hlt => h (fourierCoeff_eq_zero_of_mem_lowDegree (mem_lowDegree_totalDegree f) hlt)

/-- The total degree of a real function is at most `D` exactly when its Fourier coefficients vanish
on the sets of more than `D` coordinates. -/
theorem totalDegree_le_iff_fourierCoeff_eq_zero :
    totalDegree f ≤ D ↔ ∀ S : Finset ι, D < #S → fourierCoeff f S = 0 :=
  totalDegree_le_iff_mem_lowDegree.trans mem_lowDegree_iff_fourierCoeff_eq_zero

/-- **The total degree is attained**: a real function of positive total degree has a nonzero
Fourier coefficient on a set of exactly its total degree coordinates. -/
theorem exists_card_eq_totalDegree_fourierCoeff_ne_zero (h : totalDegree f ≠ 0) :
    ∃ S : Finset ι, #S = totalDegree f ∧ fourierCoeff f S ≠ 0 := by
  have hlt : ¬ totalDegree f ≤ totalDegree f - 1 := by omega
  rw [totalDegree_le_iff_fourierCoeff_eq_zero] at hlt
  push Not at hlt
  obtain ⟨S, hS, hne⟩ := hlt
  exact ⟨S, le_antisymm (card_le_totalDegree_of_fourierCoeff_ne_zero hne) (by omega), hne⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Reading the values of a Boolean function as `0` and `1` or as the signs `±1` gives the same
low-degree membership: `signVal b = 1 - 2 bitVal ℝ b`. -/
theorem signVal_comp_mem_lowDegree_iff {g : (ι → Bool) → Bool} :
    (fun x => signVal (g x)) ∈ lowDegree ℝ ι D ↔ (fun x => bitVal ℝ (g x)) ∈ lowDegree ℝ ι D := by
  have hsign : (fun x => signVal (g x)) = 1 - (2 : ℝ) • fun x => bitVal ℝ (g x) := by
    funext x
    simp [signVal_eq_one_sub_two_mul_bitVal]
  have hbit : (fun x => bitVal ℝ (g x)) = (2⁻¹ : ℝ) • (1 - fun x => signVal (g x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul,
      signVal_eq_one_sub_two_mul_bitVal]
    ring
  exact ⟨fun h => hbit ▸ Submodule.smul_mem _ _ (one_sub_mem_lowDegree h),
    fun h => hsign ▸ one_sub_mem_lowDegree (Submodule.smul_mem _ _ h)⟩

omit [Fintype ι] [DecidableEq ι] in
/-- Reading the values of a Boolean function as `0` and `1` or as the signs `±1` gives the same
total degree: `signVal b = 1 - 2 bitVal ℝ b`. -/
theorem totalDegree_signVal_comp (g : (ι → Bool) → Bool) :
    totalDegree (fun x => signVal (g x)) = totalDegree (fun x => bitVal ℝ (g x)) :=
  congrArg sInf (Set.ext fun _ => signVal_comp_mem_lowDegree_iff)

end Cslib.BitString
