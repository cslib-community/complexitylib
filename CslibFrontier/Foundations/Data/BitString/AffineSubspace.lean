/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Affine
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine maps and affine subspaces over `𝔽₂`

For maps between `𝔽₂`-vector spaces, preserving sums of three points (`Cslib.BitString.IsAffine`)
is the usual notion of affinity (`Cslib.BitString.isAffine_iff_exists_affineMap`): `g` is a Mathlib
affine map over `Bool` with linear part `x ↦ g x + g 0` (`Cslib.BitString.IsAffine.linearMap`,
`Cslib.BitString.IsAffine.toAffineMap`). The image of an injective affine map from `V` is an
affine subspace whose direction has the dimension of `V`
(`Cslib.BitString.IsAffine.finrank_direction_map_top`).

## Main definitions

* `Cslib.BitString.IsAffine.linearMap`: the linear part `x ↦ g x + g 0` of an affine map over
  `𝔽₂`.
* `Cslib.BitString.IsAffine.toAffineMap`: an affine map over `𝔽₂` as a Mathlib affine map.

## Main results

* `Cslib.BitString.isAffine_iff_exists_affineMap`: a map between `𝔽₂`-vector spaces is `IsAffine`
  if and only if it is a Mathlib affine map over `Bool`.
* `Cslib.BitString.IsAffine.finrank_direction_map_top`: the image of an injective affine map
  from `V` is an affine subspace whose direction has dimension `finrank Bool V`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

open Module

variable {V W : Type*} [AddCommGroup V] [Module Bool V] [AddCommGroup W] [Module Bool W]

/-- In a vector space over `𝔽₂ = Bool` every vector is its own negative. -/
private theorem add_self_eq_zero_of_module_bool (w : W) : w + w = 0 := by
  rw [← one_smul Bool w, ← add_smul, show (1 + 1 : Bool) = 0 from rfl, zero_smul]

/-- The linear part `x ↦ g x + g 0` of a map `g` that is affine over `𝔽₂`. -/
def IsAffine.linearMap {g : V → W} (hg : IsAffine g) : V →ₗ[Bool] W where
  toFun x := g x + g 0
  map_add' x y := by
    have h := hg x y 0
    rw [add_zero] at h
    rw [h]
    abel
  map_smul' c x := by
    cases c
    · change g ((0 : Bool) • x) + g 0 = (0 : Bool) • (g x + g 0)
      rw [zero_smul, zero_smul, add_self_eq_zero_of_module_bool]
    · change g ((1 : Bool) • x) + g 0 = (1 : Bool) • (g x + g 0)
      rw [one_smul, one_smul]

/-- The linear part of `g` sends `x` to `g x + g 0`. -/
@[simp]
theorem IsAffine.linearMap_apply {g : V → W} (hg : IsAffine g) (x : V) :
    hg.linearMap x = g x + g 0 :=
  rfl

/-- The linear part of an injective map that is affine over `𝔽₂` is injective. -/
theorem IsAffine.linearMap_injective {g : V → W} (hg : IsAffine g)
    (hinj : Function.Injective g) : Function.Injective hg.linearMap := fun x y h => by
  rw [hg.linearMap_apply, hg.linearMap_apply, add_left_inj] at h
  exact hinj h

/-- A map that is affine over `𝔽₂` (`IsAffine`) as a Mathlib affine map over `Bool`, with linear
part `x ↦ g x + g 0`. -/
def IsAffine.toAffineMap {g : V → W} (hg : IsAffine g) : V →ᵃ[Bool] W where
  toFun := g
  linear := hg.linearMap
  map_vadd' p v := by
    have h := hg v p 0
    rw [add_zero] at h
    rw [vadd_eq_add, vadd_eq_add, h, hg.linearMap_apply]
    abel

/-- As a function, the Mathlib affine map of `g` is `g` itself. -/
@[simp]
theorem IsAffine.coe_toAffineMap {g : V → W} (hg : IsAffine g) : ⇑hg.toAffineMap = g :=
  rfl

/-- A map between `𝔽₂`-vector spaces is affine (`IsAffine`) if and only if it is a Mathlib
affine map over `Bool`. -/
theorem isAffine_iff_exists_affineMap {g : V → W} :
    IsAffine g ↔ ∃ f : V →ᵃ[Bool] W, ⇑f = g := by
  refine ⟨fun hg => ⟨hg.toAffineMap, rfl⟩, ?_⟩
  rintro ⟨f, rfl⟩ x y z
  have hv (v p : V) : f (v + p) = f.linear v + f p := by
    simpa only [vadd_eq_add] using f.map_vadd p v
  have h0 (v : V) : f v = f.linear v + f 0 := by
    simpa only [add_zero] using hv v 0
  calc f (x + y + z)
      = f.linear x + f.linear y + f z + (f 0 + f 0) := by
        rw [hv (x + y) z, f.linear.map_add, add_self_eq_zero_of_module_bool, add_zero]
    _ = (f.linear x + f 0) + (f.linear y + f 0) + f z := by abel
    _ = f x + f y + f z := by rw [← h0 x, ← h0 y]

/-- The image of an injective map from `V` that is affine over `𝔽₂` is an affine subspace whose
direction has the dimension of `V`. -/
theorem IsAffine.finrank_direction_map_top {g : V → W} (hg : IsAffine g)
    (hinj : Function.Injective g) :
    finrank Bool ((⊤ : AffineSubspace Bool V).map hg.toAffineMap).direction = finrank Bool V := by
  rw [AffineSubspace.map_direction, AffineSubspace.direction_top, Submodule.map_top]
  exact LinearMap.finrank_range_of_inj (hg.linearMap_injective hinj)

end Cslib.BitString
