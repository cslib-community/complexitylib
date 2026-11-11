/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Noise
public import CslibFrontier.Foundations.BooleanAnalysis.Hypercontractivity.LpNorm
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tensorization of two-function hypercontractivity

For a correlation `ρ`, the expectation `𝔼_x f x · T_ρ g x` of `f` against the noise operator
applied to `g` is the expectation of `f x g y` over a `ρ`-correlated pair `(x, y)`. A
*two-function hypercontractive inequality* bounds it by `‖f‖_p ‖g‖_q`. Such an inequality
*tensorizes*: if it holds on a single bit, it holds on every cube (the **Two-Function
Hypercontractivity Induction Theorem**, `BitString.expect_mul_noiseOp_le_of_unit`)
[O'Donnell, Section 9.4][ODonnell2014].

The proof is *induction by restrictions*. On the cube over `ι ⊕ κ` the noise operator acts on the
two blocks of coordinates independently (`BitString.noiseOp_sumElim`), since a random mask on
`ι ⊕ κ` is a pair of independent masks (`BitString.bernoulliAverage_sumElim`). Fixing the bits in
`ι`, the inequality on `κ` bounds the inner expectation by the product of the norms of the
restrictions; these norms are functions of the bits in `ι`, to which the inequality on `ι`
applies, and their norms are the norms of `f` and `g` (`BitString.lpNorm_sumElim`). The noise
operator also commutes with renaming the coordinates (`BitString.noiseOp_comp_arrowCongr`), so
induction over `Fin n` reaches every finite coordinate type.

## Main results

* `Cslib.BitString.noiseOp_sumElim`: the noise operator on a disjoint union of coordinates is
  the composition of the noise operators on the two blocks.
* `Cslib.BitString.expect_mul_noiseOp_le_of_unit`: the Two-Function Hypercontractivity Induction
  Theorem.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-! ### The noise operator on split coordinates -/

/-- **The noise operator on a disjoint union of coordinates** applies the noise operator on the
bits in `κ` and then the noise operator on the bits in `ι`. -/
theorem noiseOp_sumElim (ρ : ℝ) (g : (ι ⊕ κ → Bool) → ℝ) (x₁ : ι → Bool) (x₂ : κ → Bool) :
    noiseOp ρ g (Sum.elim x₁ x₂) =
      noiseOp ρ (fun y₁ => noiseOp ρ (fun y₂ => g (Sum.elim y₁ y₂)) x₂) x₁ := by
  have h (P₁ : ι → Bool) (P₂ : κ → Bool) :
      Sum.elim x₁ x₂ + Sum.elim P₁ P₂ = Sum.elim (x₁ + P₁) (x₂ + P₂) := by
    funext i
    cases i <;> rfl
  simp only [noiseOp, bernoulliAverage_sumElim, h]

/-! ### Tensorization -/

/-- A two-function inequality transfers along a renaming of the coordinates. -/
private theorem expect_mul_noiseOp_le_of_equiv {p q ρ : ℝ} (e : ι ≃ κ)
    (h : ∀ f g : (ι → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (f g : (κ → Bool) → ℝ) : 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  have h' := h (fun x => f fun j => x (e.symm j)) (fun x => g fun j => x (e.symm j))
  simp only [noiseOp_comp_arrowCongr, lpNorm_comp_arrowCongr] at h'
  rwa [Fintype.expect_comp_arrowCongr e fun y => f y * noiseOp ρ g y] at h'

/-- A two-function inequality holds on the cube over no coordinates. -/
private theorem expect_mul_noiseOp_le_of_isEmpty [IsEmpty ι] {p q ρ : ℝ} (hp : p ≠ 0)
    (hq : q ≠ 0) (f g : (ι → Bool) → ℝ) :
    𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  let x₀ : ι → Bool := isEmptyElim
  have h : (fun x => f x * noiseOp ρ g x) = fun _ => f x₀ * g x₀ :=
    funext fun x => by rw [Subsingleton.elim x x₀, noiseOp_of_isEmpty]
  rw [h, Fintype.expect_const, lpNorm_of_isEmpty hp f x₀, lpNorm_of_isEmpty hq g x₀, ← abs_mul]
  exact le_abs_self _

/-- **The induction step**: two-function inequalities on the cubes over `ι` and over `κ` give
the inequality on the cube over `ι ⊕ κ`. -/
private theorem expect_mul_noiseOp_le_sum {p q ρ : ℝ} (hρ : -1 ≤ ρ) (hρ' : ρ ≤ 1)
    (hι : ∀ f g : (ι → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (hκ : ∀ f g : (κ → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (f g : (ι ⊕ κ → Bool) → ℝ) : 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  -- the norms of the restrictions, as functions of the bits in `ι`
  let F : (ι → Bool) → ℝ := fun x₁ => lpNorm p fun x₂ => f (Sum.elim x₁ x₂)
  let G : (ι → Bool) → ℝ := fun y₁ => lpNorm q fun y₂ => g (Sum.elim y₁ y₂)
  have hr : 0 ≤ (1 - ρ) / 2 := by linarith
  have hr' : (1 - ρ) / 2 ≤ 1 := by linarith
  calc 𝔼 x, f x * noiseOp ρ g x
      = 𝔼 x₁, 𝔼 x₂, f (Sum.elim x₁ x₂) *
          noiseOp ρ (fun y₁ => noiseOp ρ (fun y₂ => g (Sum.elim y₁ y₂)) x₂) x₁ := by
        rw [Fintype.expect_sumElim]
        simp only [noiseOp_sumElim]
    _ = 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => 𝔼 x₂, f (Sum.elim x₁ x₂) *
          noiseOp ρ (fun y₂ => g (Sum.elim (x₁ + P) y₂)) x₂ := by
        refine expect_congr rfl fun x₁ _ => ?_
        rw [bernoulliAverage_expect_comm]
        refine expect_congr rfl fun x₂ _ => ?_
        rw [noiseOp, ← bernoulliAverage_const_mul]
    _ ≤ 𝔼 x₁, bernoulliAverage ((1 - ρ) / 2) fun P => F x₁ * G (x₁ + P) :=
        expect_le_expect fun x₁ _ => bernoulliAverage_mono hr hr' fun P => hκ _ _
    _ = 𝔼 x₁, F x₁ * noiseOp ρ G x₁ := by
        simp only [noiseOp, bernoulliAverage_const_mul]
    _ ≤ lpNorm p F * lpNorm q G := hι F G
    _ = lpNorm p f * lpNorm q g := by
        rw [lpNorm_sumElim p f, lpNorm_sumElim q g]

/-- **The Two-Function Hypercontractivity Induction Theorem**: if the two-function inequality
`𝔼_x f x · T_ρ g x ≤ ‖f‖_p ‖g‖_q` holds for all functions of a single bit, then it holds for all
functions on every cube. Here `𝔼_x f x · T_ρ g x` is the expectation of `f x g y` over a
`ρ`-correlated pair `(x, y)` [O'Donnell, Section 9.4][ODonnell2014]. -/
theorem expect_mul_noiseOp_le_of_unit {p q ρ : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) (hρ : 0 ≤ ρ)
    (hρ' : ρ ≤ 1)
    (h : ∀ f g : (Unit → Bool) → ℝ, 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g)
    (f g : (ι → Bool) → ℝ) : 𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
  have hfin (n : ℕ) (f g : (Fin n → Bool) → ℝ) :
      𝔼 x, f x * noiseOp ρ g x ≤ lpNorm p f * lpNorm q g := by
    induction n with
    | zero => exact expect_mul_noiseOp_le_of_isEmpty hp hq f g
    | succ n ih =>
      exact expect_mul_noiseOp_le_of_equiv
        ((Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv)
        (expect_mul_noiseOp_le_sum (by linarith) hρ' ih h) f g
  exact expect_mul_noiseOp_le_of_equiv (Fintype.equivFin ι).symm (hfin _) f g

end Cslib.BitString
