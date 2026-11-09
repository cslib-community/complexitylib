/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.LpNorm
public import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Fintype

/-!
# `L^p` norms on the Boolean cube

Specializes `Cslib.lpNorm` to functions on the Boolean cube `ι → Bool`
[O'Donnell, Section 1.3][ODonnell2014]. The norm does not see how the coordinates are named
(`BitString.lpNorm_comp_arrowCongr`), on the cube over a disjoint union `ι ⊕ κ` it is the norm,
over the bits in `ι`, of the norms over the bits in `κ` (`BitString.lpNorm_sumElim`), and on the
cube over no coordinates it is the absolute value (`BitString.lpNorm_of_isEmpty`).

## Main results

* `Cslib.BitString.lpNorm_comp_arrowCongr`: invariance under coordinate renaming.
* `Cslib.BitString.lpNorm_sumElim`: the norm over a disjoint union of coordinates is the
  iterated norm.
* `Cslib.BitString.lpNorm_of_isEmpty`: the norm on the empty cube is the absolute value.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Renaming the coordinates preserves the `L^p` norm. -/
theorem lpNorm_comp_arrowCongr (e : ι ≃ κ) (p : ℝ) (f : (κ → Bool) → ℝ) :
    lpNorm p (fun x : ι → Bool => f fun j => x (e.symm j)) = lpNorm p f :=
  lpNorm_equiv (e.arrowCongr (Equiv.refl Bool)) p f

/-- **The `L^p` norm over a disjoint union of coordinates is the iterated norm**: the norm over
the bits in `ι` of the norms over the bits in `κ`. -/
theorem lpNorm_sumElim (p : ℝ) (f : (ι ⊕ κ → Bool) → ℝ) :
    lpNorm p f = lpNorm p fun x₁ => lpNorm p fun x₂ => f (Sum.elim x₁ x₂) := by
  rw [← lpNorm_equiv (Equiv.sumArrowEquivProdArrow ι κ Bool).symm p f, lpNorm_prod]
  rfl

/-- On the cube over no coordinates, a single point, the `L^p` norm is the absolute value. -/
theorem lpNorm_of_isEmpty [IsEmpty ι] {p : ℝ} (hp : p ≠ 0) (f : (ι → Bool) → ℝ)
    (x : ι → Bool) : lpNorm p f = |f x| :=
  lpNorm_subsingleton hp f x

end Cslib.BitString
