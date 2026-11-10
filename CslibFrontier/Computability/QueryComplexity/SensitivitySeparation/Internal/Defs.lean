/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Flip
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Superquadratic sensitivity separation: model

This file fixes the model of Boolean functions `f : (I → Bool) → Bool` used throughout the
separation: the sensitivity of `f` at an input and overall, and the block sensitivity of `f` at an
input and overall, defined in terms of `BitString.flipOn`. All maxima are `Finset.sup`s over the
actual finite input space or the finite space of block families, so the definitions agree literally
with the standard ones. These measures are internal to the construction, which needs arbitrary
finite coordinate types; `Bridge` identifies them on `Fin n` with CSLib's
`BitString.sensitivity` and `QueryComplexity.blockSensitivity`.

## Main definitions

* `sensitivityAt`: the number of coordinates whose flip changes `f x`.
* `sensitivity`: the maximum of `sensitivityAt f x` over all inputs `x`.
* `blockSensitivityAt`: the maximum number of disjoint nonempty blocks whose flips change `f x`.
* `blockSensitivity`: the maximum of `blockSensitivityAt f x` over all inputs `x`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Model.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation.Internal

noncomputable section

open scoped Classical in
/-- The ordinary number of sensitive individual input coordinates. -/
def sensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i => f (BitString.flipOn {i} x) ≠ f x).card

open scoped Classical in
/-- Maximum ordinary sensitivity over all Boolean inputs. -/
def sensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensitivityAt f)

open scoped Classical in
/-- Maximum size of a family of disjoint nonempty sensitive blocks at an input.
The empty family is allowed and contributes zero. Invalid families contribute zero. -/
def blockSensitivityAt {I : Type} [Fintype I]
    (f : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  Finset.univ.sup fun blocks : Finset (Finset I) =>
    if (∀ A ∈ blocks, ∀ B ∈ blocks, A ≠ B → Disjoint A B) ∧
        (∀ B ∈ blocks, B.Nonempty ∧ f (BitString.flipOn B x) ≠ f x)
    then blocks.card else 0

open scoped Classical in
/-- Maximum block sensitivity over all Boolean inputs. -/
def blockSensitivity {I : Type} [Fintype I] (f : (I → Bool) → Bool) : ℕ :=
  Finset.univ.sup (blockSensitivityAt f)

end

end Cslib.QueryComplexity.SensitivitySeparation.Internal
