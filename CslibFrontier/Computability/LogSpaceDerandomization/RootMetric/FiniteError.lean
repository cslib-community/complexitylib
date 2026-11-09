/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.ConditionalWalk
import CslibFrontier.Foundations.Analysis.RootError
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Finite atom payments and conditional Jensen for row errors

A bounded nonnegative pair of tables admits an explicit root-to-ordinary error payment
at each retained atom. This conservative payment retains the full environment cardinality.
The integrated envelope and conditional Jensen estimates avoid extracting atoms.
The actual child reserve uses these integrated estimates; the atom lemmas remain independent
finite-domain tools for clients that explicitly need entrywise control.
These original finite inequalities use Samuel Schlesinger's integrated row normalization.
-/
public section
open Finset
open scoped BigOperators
noncomputable section

namespace Cslib
attribute [local instance] Classical.propDecidable
variable {Ω V : Type*} [Fintype Ω] [Fintype V]

/-- A finite-domain rooted moment controls a retained entry, with the entire finite
atom cost explicit. This conservative bound pays `card Ω`; it asserts no uniform bound
independent of the environment size. Both tables must be bounded normalized outputs. -/
theorem bounded_sub_fourth_le_rootDistPow_atom
    {N u B : ℝ} (hN : 0 < N) (hu : 0 < u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A A' : Ω → V → V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 B)
    (hA' : ∀ σ x y, A' σ x y ∈ Set.Icc 0 B)
    (σ : Ω) (x y : V) (hx : X σ x) (hy : Y σ y) :
    |A σ x y - A' σ x y| ^ 4 ≤
      (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * (N * u * Fintype.card Ω) *
        rootDistPow 4 N u X Y A A' := by
  let e := fun τ a b => |A τ a b ^ (4⁻¹ : ℝ) - A' τ a b ^ (4⁻¹ : ℝ)| ^ 4
  have hpoint := abs_sub_le_mul_abs_rpow_inv_sub (s := 4) (by decide)
    (hA σ x y).1 (hA' σ x y).1 (hA σ x y).2 (hA' σ x y).2
  norm_num only [Nat.cast_ofNat] at hpoint
  have hscalar := pow_le_pow_left₀ (abs_nonneg _) hpoint 4
  rw [mul_pow] at hscalar
  have hterm : e σ x y ≤ ∑ τ, ∑ a ∈ ({a | X τ a} : Finset V),
      ∑ b ∈ ({b | Y τ b} : Finset V), e τ a b := by
    apply (single_le_sum (fun b _ => by dsimp only [e]; positivity)
      (show y ∈ ({b | Y σ b} : Finset V) by simpa using hy)).trans
    apply (single_le_sum (fun a _ => sum_nonneg fun b _ => by dsimp only [e]; positivity)
      (show x ∈ ({a | X σ a} : Finset V) by simpa using hx)).trans
    exact single_le_sum (f := fun τ => ∑ a ∈ ({a | X τ a} : Finset V),
      ∑ b ∈ ({b | Y τ b} : Finset V), e τ a b)
      (fun τ _ => sum_nonneg fun a _ => sum_nonneg fun b _ => by dsimp only [e]; positivity)
      (mem_univ σ)
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by
    have : Nonempty Ω := ⟨σ⟩
    exact_mod_cast Fintype.card_ne_zero
  have heq : (N * u * Fintype.card Ω) * rootDistPow 4 N u X Y A A' =
      ∑ τ, ∑ a ∈ ({a | X τ a} : Finset V), ∑ b ∈ ({b | Y τ b} : Finset V), e τ a b := by
    simp only [rootDistPow, rowNormPow, expect_eq_sum_div_card, card_univ, e]
    field_simp
    norm_num
  apply hscalar.trans
  rw [mul_assoc, heq]
  norm_num only [e, one_div] at hterm ⊢
  exact mul_le_mul_of_nonneg_left hterm (by positivity)

/-- An explicit sufficient rooted accuracy allocation on the child's own source/usage
domain. Values off usage must agree; values off source are never constrained. -/
theorem bounded_sub_fourth_le_of_root_budget
    {N u B q : ℝ} (hN : 0 < N) (hu : 0 < u) (hq : 0 ≤ q)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A A' : Ω → V → V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 B)
    (hA' : ∀ σ x y, A' σ x y ∈ Set.Icc 0 B)
    (hoff : ∀ σ x y, ¬ Y σ y → A σ x y = A' σ x y)
    (hbudget : rootDistPow 4 N u X Y A A' ≤
      q / (1 + (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * (N * u * Fintype.card Ω)))
    (σ : Ω) (x y : V) (hx : X σ x) : |A σ x y - A' σ x y| ^ 4 ≤ q := by
  by_cases hy : Y σ y
  · have hb := bounded_sub_fourth_le_rootDistPow_atom hN hu X Y A A' hA hA' σ x y hx hy
    let c := (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * (N * u * Fintype.card Ω)
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    apply hb.trans
    change c * rootDistPow 4 N u X Y A A' ≤ q
    apply (mul_le_mul_of_nonneg_left hbudget hc).trans
    change c * (q / (1 + c)) ≤ q
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  · simp only [hoff σ x y hy, sub_self, abs_zero, zero_pow (by decide : 4 ≠ 0)]
    exact hq

/-- An environment-dependent envelope integrates without extracting any atom. Repeating
it across retained source/terminal pairs costs only the square of the vertex width. -/
theorem rowNormPow_fourth_le_expect_envelope {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (F : Ω → V → V → ℝ) (q : Ω → ℝ) (hq : ∀ σ, 0 ≤ q σ)
    (hF : ∀ σ x y, X σ x → Y σ y → |F σ x y| ^ 4 ≤ q σ) :
    rowNormPow 4 N u X Y F ≤ (Fintype.card V : ℝ) ^ 2 / (N * u) * 𝔼 σ, q σ := by
  unfold rowNormPow
  have hsum (σ : Ω) :
      (∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), |F σ x y| ^ 4) ≤
        (Fintype.card V : ℝ) ^ 2 * q σ := by
    calc
      _ ≤ ∑ x ∈ ({x | X σ x} : Finset V), ∑ y ∈ ({y | Y σ y} : Finset V), q σ :=
        sum_le_sum fun x hx => sum_le_sum fun y hy =>
          hF σ x y (mem_filter.mp hx).2 (mem_filter.mp hy).2
      _ ≤ (Fintype.card V : ℝ) ^ 2 * q σ := by
        simp only [sum_const, nsmul_eq_mul]
        have hx : (#({x | X σ x} : Finset V) : ℝ) ≤ Fintype.card V :=
          by exact_mod_cast card_le_card (filter_subset _ _)
        have hy : (#({y | Y σ y} : Finset V) : ℝ) ≤ Fintype.card V :=
          by exact_mod_cast card_le_card (filter_subset _ _)
        have hm := mul_le_mul_of_nonneg_right
          (mul_le_mul hx hy (by positivity) (by positivity)) (hq σ)
        nlinarith only [hm]
  calc
    _ ≤ (N * u)⁻¹ * 𝔼 σ, (Fintype.card V : ℝ) ^ 2 * q σ :=
      mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => hsum σ) (inv_nonneg.mpr hNu)
    _ = _ := by rw [← mul_expect]; ring

/-- Conditional Jensen on the same full environment, with no independence requirement.
The fourth moment of the deterministic slice mean is at most the original row moment. -/
theorem rowNormPow_sliceMean_fourth_le {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (F : Ω → V → V → ℝ) :
    rowNormPow 4 N u X Y (fun _ => rowSliceMean X Y F) ≤ rowNormPow 4 N u X Y F := by
  apply (rowNormPow_le_of_conditional_expect_le hNu F (fun _ => rowSliceMean X Y F) 1 ?_).trans_eq
    (one_mul _)
  intro x y
  let S := ({σ | X σ x ∧ Y σ y} : Finset Ω)
  have h1 := sq_expect_le_expect_sq S (fun σ => F σ x y)
  have h2 := sq_expect_le_expect_sq S (fun σ => F σ x y ^ 2)
  have h3 := (pow_le_pow_left₀ (sq_nonneg _) h1 2).trans h2
  have h4 : |𝔼 σ ∈ S, F σ x y| ^ 4 ≤ 𝔼 σ ∈ S, |F σ x y| ^ 4 := by
    simpa only [(by decide : Even (4 : ℕ)).pow_abs, ← pow_mul, Nat.reduceMul] using h3
  change (𝔼 σ ∈ S, |𝔼 τ ∈ S, F τ x y| ^ 4) ≤ 1 * 𝔼 σ ∈ S, |F σ x y| ^ 4
  rcases S.eq_empty_or_nonempty with hs | hs
  · simp only [hs, expect_empty, mul_zero, le_refl]
  · rw [expect_const hs, one_mul]
    exact h4

set_option backward.isDefEq.respectTransparency false in
/-- Bounded root error pays bias after conditional averaging on the identical slice.
No pointwise error, independence, or environment-cardinality factor is needed. -/
theorem rowNormPow_sliceMean_sub_le_rootDistPow {N u B : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (A A' : Ω → V → V → ℝ)
    (hA : ∀ σ x y, A σ x y ∈ Set.Icc 0 B)
    (hA' : ∀ σ x y, A' σ x y ∈ Set.Icc 0 B) :
    rowNormPow 4 N u X Y (fun _ x y => rowSliceMean X Y A x y -
      rowSliceMean X Y A' x y) ≤
      (4 * B ^ ((3 : ℝ) / 4)) ^ 4 * rootDistPow 4 N u X Y A A' := by
  have he : (fun _ x y => rowSliceMean X Y A x y - rowSliceMean X Y A' x y) =
      (fun (_ : Ω) => rowSliceMean X Y (fun σ x y => A σ x y - A' σ x y)) := by
    funext σ x y
    simp only [rowSliceMean, expect_sub_distrib]
  rw [he]
  apply (rowNormPow_sliceMean_fourth_le hNu X Y _).trans
  have hb := rowNormPow_sub_le_rootDistPow (s := 4) (N := N) (u := u) (X := X) (Y := Y)
      (C := B) (H := A) (H' := A') (by decide : 4 ≠ 0) hNu
      (fun σ x y _ _ => hA σ x y) (fun σ x y _ _ => hA' σ x y)
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hb
  exact hb

end Cslib
