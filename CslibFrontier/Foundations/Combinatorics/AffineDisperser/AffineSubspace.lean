/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.AffineDisperser.Basic
public import CslibFrontier.Foundations.Data.BitString.AffineSubspace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Affine dispersers from nonconstancy on affine subspaces

Because the image of an injective affine map from `BitString d` is an affine subspace of
`BitString n` of dimension `d` (`Cslib.BitString.IsAffine.finrank_direction_map_top`), any function
nonconstant on every `d`-dimensional affine subspace is an affine disperser for dimension `d`
(`Cslib.BitString.isAffineDisperser_of_forall_exists_ne`). This turns nonconstancy theorems stated
with `AffineSubspace`, such as Ben-Sasson and Kopparty's, into affine dispersers. The converse,
that every affine subspace of dimension `d` contains such an image, is not formalized here: Mathlib
has no `Field Bool` instance, so a basis of the direction is not available over `Bool`.

## Main results

* `Cslib.BitString.isAffineDisperser_of_forall_exists_ne`: a function nonconstant on every affine
  subspace of dimension `d` is an affine disperser for dimension `d`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

public section

namespace Cslib.BitString

open Module

/-- A function nonconstant on every affine subspace of `BitString n` of dimension `d` is an affine
disperser for dimension `d`: the image of an injective affine map from `BitString d` is such a
subspace. -/
theorem isAffineDisperser_of_forall_exists_ne {n d : ℕ} {f : BitString n → Bool}
    (h : ∀ A : AffineSubspace Bool (BitString n), finrank Bool A.direction = d →
      ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y) :
    IsAffineDisperser f d := by
  intro g hg hinj
  obtain ⟨_, hx, _, hy, hne⟩ := h _
    ((hg.finrank_direction_map_top hinj).trans (Module.finrank_fin_fun Bool))
  obtain ⟨x, -, rfl⟩ := AffineSubspace.mem_map.1 hx
  obtain ⟨y, -, rfl⟩ := AffineSubspace.mem_map.1 hy
  exact ⟨x, y, hne⟩

end Cslib.BitString
