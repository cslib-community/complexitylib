/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.CutRank
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

/-!
# Quadratic forms over `𝔽₂` on bit strings

Reading the bits of `x : ι → Bool` as a vector `v` over `𝔽₂ = ZMod 2` (`BitString.bitVal`), a
square matrix `Q` over `𝔽₂` defines the Boolean function `x ↦ v ⬝ᵥ Q *ᵥ v`
(`BitString.quadForm`), the quadratic form of `Q` as in `Matrix.toQuadraticForm'`. Every
quadratic form over `𝔽₂` in the variables `x` arises so. The inner product function
`x ↦ ∑ᵢ xᵢ yᵢ` is the quadratic form of the matrix with the identity in the block of rows `x` and
columns `y`; more generally, a matrix carrying `R` on a block of rows `x` and columns `y` and
vanishing elsewhere has the bilinear form `xᵀ R y` as its quadratic form
(`BitString.quadForm_eq_of_submatrix`).

## Main definitions

* `Cslib.BitString.quadForm Q`: the quadratic form of `Q` over `𝔽₂`, as a Boolean function.

## Main results

* `Cslib.BitString.neg_one_pow_val_eq`: the sign `(-1) ^ (v ⬝ᵥ Q *ᵥ v)` of a quadratic form.
* `Cslib.BitString.quadForm_eq_of_submatrix`: bilinear forms are quadratic forms.
-/

@[expose] public section

namespace Cslib.BitString

open Matrix

variable {ι : Type*} [Fintype ι]

/-- Reading bits in `𝔽₂` is injective. -/
theorem bitVal_zmod_two_injective : Function.Injective (bitVal (ZMod 2)) := by
  decide

/-- Every element of `𝔽₂` is a bit. -/
theorem bitVal_zmod_two_surjective : Function.Surjective (bitVal (ZMod 2)) := by
  decide

/-- The *quadratic form* of a square matrix `Q` over `𝔽₂` as a Boolean function: reading the bits
of `x` as a vector `v` over `𝔽₂`, it is true when `v ⬝ᵥ Q *ᵥ v = 1`. -/
def quadForm (Q : Matrix ι ι (ZMod 2)) (x : ι → Bool) : Bool :=
  decide ((fun i => bitVal (ZMod 2) (x i)) ⬝ᵥ Q *ᵥ (fun i => bitVal (ZMod 2) (x i)) = 1)

/-- The quadratic form of `Q` is true at `x` exactly when `v ⬝ᵥ Q *ᵥ v = 1` for the vector `v`
over `𝔽₂` of the bits of `x`. -/
theorem quadForm_eq_true_iff (Q : Matrix ι ι (ZMod 2)) (x : ι → Bool) :
    quadForm Q x = true ↔
      (fun i => bitVal (ZMod 2) (x i)) ⬝ᵥ Q *ᵥ (fun i => bitVal (ZMod 2) (x i)) = 1 :=
  decide_eq_true_iff

/-- The sign of a quadratic form: `(-1) ^ (v ⬝ᵥ Q *ᵥ v)` is `-1` where the form is true and `1`
where it is false. -/
theorem neg_one_pow_val_eq {R : Type*} [Ring R] (Q : Matrix ι ι (ZMod 2)) (x : ι → Bool) :
    (-1 : R) ^ ((fun i => bitVal (ZMod 2) (x i)) ⬝ᵥ Q *ᵥ (fun i => bitVal (ZMod 2) (x i))).val =
      if quadForm Q x then -1 else 1 := by
  rw [quadForm]
  generalize (fun i => bitVal (ZMod 2) (x i)) ⬝ᵥ Q *ᵥ (fun i => bitVal (ZMod 2) (x i)) = z
  rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) z with rfl | rfl
  · simp
  · rw [show (1 : ZMod 2).val = 1 from rfl]
    simp

/-- **Bilinear forms are quadratic forms.** If `M` carries `R` on the rows `f` and the columns
`g`, both injective, and vanishes elsewhere, its quadratic form is the bilinear form
`(x ∘ f)ᵀ R (x ∘ g)`. -/
theorem quadForm_eq_of_submatrix {κ κ' : Type*} [Fintype κ] [Fintype κ']
    {R : Matrix κ κ' (ZMod 2)} {M : Matrix ι ι (ZMod 2)} {f : κ → ι} {g : κ' → ι}
    (hf : Function.Injective f) (hg : Function.Injective g) (hMR : M.submatrix f g = R)
    (hM : ∀ i j, i ∉ Set.range f ∨ j ∉ Set.range g → M i j = 0) (x : ι → Bool) :
    quadForm M x =
      decide ((fun a => bitVal (ZMod 2) (x (f a))) ⬝ᵥ R *ᵥ (fun b => bitVal (ZMod 2) (x (g b))) =
        1) := by
  rw [quadForm, dotProduct_mulVec_self_eq_of_submatrix hf hg hMR hM]
  rfl

end Cslib.BitString
