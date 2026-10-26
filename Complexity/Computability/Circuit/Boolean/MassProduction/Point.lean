/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.BitString.Block
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Bit encodings of points and lines

Field elements are read through an additive bijection `bits : K ≃+ BitString b`, so adding a
fixed point is a coordinatewise exclusive or. A point of `K ^ ℓ` is `ℓ` consecutive blocks of `b`
bits, and a batch of `t` points is `t` consecutive point blocks. A batch of lines `u + c • v` is
listed point by point in a fixed order of `s` scalars.

## Main definitions

* `Cslib.BitString.pointBits`: the bits of one point.
* `Cslib.BitString.pointEquiv`: the equivalence between points and their bits.
* `Cslib.BitString.targetBits`: the bits of a batch of points.
* `Cslib.BitString.lineBits`: the listed points of a batch of lines.

## Main results

* `Cslib.BitString.pointBits_add`: point encodings preserve addition.
* `Cslib.BitString.pointBits_injective`: distinct points have distinct encodings.

## References

* Adapted from the vector encodings in MassProduction/BinaryEncoding.lean of
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString

variable {K : Type*} {ℓ b s t : ℕ}

/-- The bits of a point: block `i` holds the bits of coordinate `i`. -/
def pointBits (bits : K → BitString b) (u : Fin ℓ → K) : BitString (ℓ * b) :=
  blocksEquiv.symm (bits ∘ u)

/-- Point bits add coordinatewise. -/
theorem pointBits_add [Add K] (bits : K ≃+ BitString b) (u v : Fin ℓ → K) :
    pointBits bits (u + v) = pointBits bits u + pointBits bits v := by
  funext x
  simp only [pointBits, blocksEquiv_symm_apply, Function.comp_apply, Pi.add_apply, map_add]

/-- Points of `K ^ ℓ` are their bits. -/
def pointEquiv (bits : K ≃ BitString b) : (Fin ℓ → K) ≃ BitString (ℓ * b) :=
  (Equiv.arrowCongr (Equiv.refl (Fin ℓ)) bits).trans blocksEquiv.symm

/-- `pointEquiv bits` sends a point to its bits `pointBits bits`. -/
@[simp] theorem pointEquiv_apply (bits : K ≃ BitString b) (u : Fin ℓ → K) :
    pointEquiv bits u = pointBits bits u :=
  rfl

/-- `(pointEquiv bits).symm` decodes coordinate `i` from block `i` (`Cslib.BitString.block`). -/
@[simp] theorem pointEquiv_symm_apply (bits : K ≃ BitString b) (y : BitString (ℓ * b))
    (i : Fin ℓ) : (pointEquiv bits).symm y i = bits.symm (block y i) :=
  rfl

/-- Decoding the bits of a point gives the point back. -/
@[simp] theorem pointEquiv_symm_pointBits (bits : K ≃ BitString b) (u : Fin ℓ → K) :
    (pointEquiv bits).symm (pointBits bits u) = u :=
  (pointEquiv bits).symm_apply_apply u

/-- Decoding the bits of a point (under an additive equivalence) gives the point back. -/
@[simp] theorem pointEquiv_coe_symm_pointBits [Add K] (bits : K ≃+ BitString b)
    (u : Fin ℓ → K) : (pointEquiv bits).symm (pointBits bits u) = u :=
  (pointEquiv (bits : K ≃ BitString b)).symm_apply_apply u

/-- Encoding the point with given bits gives the bits back. -/
@[simp] theorem pointBits_pointEquiv_symm (bits : K ≃ BitString b) (y : BitString (ℓ * b)) :
    pointBits bits ((pointEquiv bits).symm y) = y :=
  (pointEquiv bits).apply_symm_apply y

/-- Distinct points have distinct bits. -/
theorem pointBits_injective {E : Type*} [EquivLike E K (BitString b)] (bits : E) :
    Function.Injective (pointBits (ℓ := ℓ) bits) :=
  (pointEquiv (EquivLike.toEquiv bits)).injective

/-- The bits of a batch of points: block `i` holds the bits of point `i`. -/
def targetBits [Add K] (bits : K ≃+ BitString b) (targets : Fin t → Fin ℓ → K) :
    BitString (t * (ℓ * b)) :=
  blocksEquiv.symm (pointBits bits ∘ targets)

/-- The listed points of a batch of lines: block `i` lists, for each scalar index `j`, the bits of
`targets i + scalar j • directions i`. -/
def lineBits [Semiring K] (bits : K ≃+ BitString b) (scalar : Fin s → K)
    (targets directions : Fin t → Fin ℓ → K) : BitString (t * (s * (ℓ * b))) :=
  blocksEquiv.symm fun i => blocksEquiv.symm fun j =>
    pointBits bits (targets i + scalar j • directions i)

end Cslib.BitString
