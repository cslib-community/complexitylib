/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.FineProductMean
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for fine-bin product means

The broad terminal slice contains two of four seeds; the fine slice contains one.
The actual rates equal those densities. The true path `0 → 1 → 2` has weight one, while the
two estimated factors depend on the same Boolean seed and never coexist. Their product is zero.

The broad conditional mean error is `1/2`, with integrated fourth power `1/96`.
The fine-domain ordinary error is `1/12`. The comparison is sharp:
`(b/a)^4 (πa/πb) = (1/2)^4 * 2 = 1/8 = (b/a)^3`.
Omitting the inverse terminal-density factor would give a false bound in this example.
-/

namespace ComplexityTests.FineProductMean

open Finset Cslib
open scoped BigOperators

private abbrev source (_ : Bool) (_ : Fin 3) : Prop := True
private abbrev broad (τ : Fin 4) (_ : Fin 3) : Prop := τ.val < 2
private abbrev fine (τ : Fin 4) (_ : Fin 3) : Prop := τ = 0
private abbrev middle (_ : Bool × Fin 4) (_ : Fin 3) : Prop := True
private abbrev X (σ : Bool × Fin 4) (x : Fin 3) : Prop := source σ.1 x
private abbrev Ya (σ : Bool × Fin 4) (y : Fin 3) : Prop := broad σ.2 y
private abbrev Yb (σ : Bool × Fin 4) (y : Fin 3) : Prop := fine σ.2 y

private def F (_ : Bool × Fin 4) (x z : Fin 3) : ℝ := if x = 0 ∧ z = 1 then 1 else 0
private def F' (σ : Bool × Fin 4) (x z : Fin 3) : ℝ :=
  if σ.1 = true ∧ x = 0 ∧ z = 1 then 1 else 0
private def B (σ : Bool × Fin 4) (z y : Fin 3) : ℝ :=
  if fine σ.2 y ∧ z = 1 ∧ y = 2 then 1 else 0
private def B' (σ : Bool × Fin 4) (z y : Fin 3) : ℝ :=
  if σ.1 = false ∧ fine σ.2 y ∧ z = 1 ∧ y = 2 then 1 else 0

private noncomputable def E (σ : Bool × Fin 4) (x y : Fin 3) : ℝ :=
  (∑ z, F σ x z * B σ z y) - ∑ z, F' σ x z * B' σ z y

private theorem broad_set (y : Fin 3) : ({τ | broad τ y} : Finset (Fin 4)) = {0, 1} := by
  change ({τ : Fin 4 | τ.val < 2} : Finset (Fin 4)) = {0, 1}
  decide

private theorem fine_set (y : Fin 3) : ({τ | fine τ y} : Finset (Fin 4)) = {0} := by
  change ({τ : Fin 4 | τ = 0} : Finset (Fin 4)) = {0}
  decide

private theorem broad_density (y : Fin 3) : (dens {τ | broad τ y} : ℝ) = 1 / 2 := by
  rw [broad_set, dens_eq_card_div_card]
  norm_num

private theorem fine_density (y : Fin 3) : (dens {τ | fine τ y} : ℝ) = 1 / 4 := by
  rw [fine_set, dens_eq_card_div_card]
  norm_num

private theorem fine_sub (τ : Fin 4) (y : Fin 3) (hτ : fine τ y) : broad τ y := by
  rcases hτ with rfl
  norm_num [broad]

private theorem estimated_product_zero (σ : Bool × Fin 4) (x y : Fin 3) :
    ∑ z, F' σ x z * B' σ z y = 0 := by
  rcases σ with ⟨γ, τ⟩
  cases γ <;> simp [F', B']

private theorem E_eq (σ : Bool × Fin 4) (x y : Fin 3) :
    E σ x y = if fine σ.2 y ∧ x = 0 ∧ y = 2 then 1 else 0 := by
  rw [E, estimated_product_zero, sub_zero]
  by_cases hx : x = 0 <;> by_cases hy : y = 2 <;> by_cases ht : fine σ.2 y <;>
    simp [F, B, hx, hy, ht]

private theorem E_support (σ : Bool × Fin 4) (x y : Fin 3) (hy : ¬ fine σ.2 y) :
    E σ x y = 0 := by simp [E_eq, hy]

private theorem mean_eq (x y : Fin 3) :
    conditionalTableMean X Ya E x y = if x = 0 ∧ y = 2 then 1 / 2 else 0 := by
  have hset : ({σ | X σ x ∧ Ya σ y} : Finset (Bool × Fin 4)) = univ ×ˢ {0, 1} := by
    ext ⟨γ, τ⟩
    fin_cases τ <;> simp [X, Ya, source, broad]
  rw [conditionalTableMean, hset, expect_product]
  by_cases hx : x = 0 <;> by_cases hy : y = 2 <;>
    norm_num [E_eq, fine, hx, hy, expect_eq_sum_div_card, Fintype.sum_bool]

private noncomputable def meanError : ℝ :=
  rowNormPow 4 3 1 X Ya (fun _ x y => conditionalTableMean X Ya E x y)

example : conditionalTableMean X Ya E 0 2 =
    conditionalTableMean X Ya (fun σ x y => ∑ z, F σ x z * B σ z y) 0 2 -
      conditionalTableMean X Ya (fun σ x y => ∑ z, F' σ x z * B' σ z y) 0 2 := by
  delta E
  simpa only [one_mul] using conditionalTableMean_mul_sub X Ya 1
    (fun σ x y => ∑ z, F σ x z * B σ z y) (fun σ x y => ∑ z, F' σ x z * B' σ z y) 0 2

private theorem meanError_eq : meanError = 1 / 96 := by
  norm_num [meanError, rowNormPow, mean_eq, X, Ya, source, broad, expect_eq_sum_div_card,
    sum_filter, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, Fin.sum_univ_three]

private theorem fineError_eq : rowNormPow 4 3 1 X Yb E = 1 / 12 := by
  norm_num [rowNormPow, E_eq, X, Yb, source, fine, expect_eq_sum_div_card, sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_four, Fin.sum_univ_three]

-- Changing the conditioning is necessary before taking the fourth power.
example : meanError ≤ (1 / 8) * rowNormPow 4 3 1 X Yb E := by
  have h := rowNormPow_fineMean_le source broad fine (s := 4) (N := 3) (u := 1)
    (c := 1 / 2) (πa := 1 / 2) (πb := 1 / 4) (by decide) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) broad_density fine_density fine_sub E E_support
  norm_num at h
  exact h

-- The inverse-density factor is sharp here; deleting it makes the asserted estimate false.
example : meanError = (1 / 8) * rowNormPow 4 3 1 X Yb E ∧
    ¬ meanError ≤ (1 / 16) * rowNormPow 4 3 1 X Yb E := by
  rw [meanError_eq, fineError_eq]
  norm_num

example : ((1 / 4 : ℝ) / (1 / 2)) ^ 4 *
      ((dens {τ | broad τ 0} : ℝ) / dens {τ | fine τ 0}) =
    ((1 / 4 : ℝ) / (1 / 2)) ^ (4 - 1 : ℕ) := by
  rw [broad_density, fine_density]
  norm_num

private theorem cap (T : Finset (Fin 3)) (a : Fin 3) {v : Fin 3 → ℝ}
    (hv : ∀ z, z ≠ a → v z = 0) : #{z ∈ T | v z ≠ 0} ≤ 1 := by
  refine card_le_one.2 fun z hz z' hz' => ?_
  have hza : z = a := by
    by_contra h
    exact (mem_filter.mp hz).2 (hv z h)
  have hz'a : z' = a := by
    by_contra h
    exact (mem_filter.mp hz').2 (hv z' h)
  exact hza.trans hz'a.symm

-- The full fine-product theorem consumes all four factors, both left row caps and actual
-- marginal densities. No product bound, mean identity or estimator error is postulated.
example : meanError ≤ 524288 * (rootDistPow 4 3 1 X middle F F' +
    rootDistPow 4 3 1 middle Yb B B') := by
  have h := rowNormPow_fineProductMean_le source broad fine middle
    (s := 4) (N := 3) (u := 1) (a := 1 / 2) (b := 1 / 4) (f := 1)
    (πa := 1 / 2) (πb := 1 / 4) (πf := 1) (Ca := 1) (cb := 1)
    (CF := 1) (CB := 1) (Kf := 1) (Kr := 1) (Kc := 1)
    (F := F) (F' := F') (B := B) (B' := B')
    (by decide) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) broad_density fine_density fine_sub
    (by norm_num) (by norm_num)
    (fun _ _ _ => by unfold F; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold F'; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B'; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold F; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold F'; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B; split_ifs <;> norm_num)
    (fun _ _ _ => by unfold B'; split_ifs <;> norm_num)
    (fun _ _ _ => cap _ 1 fun z hz => by simp [F, hz])
    (fun _ _ _ => cap _ 1 fun z hz => by simp [F', hz])
    (fun _ _ _ => cap _ 2 fun y hy => by simp [B, hy])
    (fun _ _ _ => cap _ 0 fun x hx => by simp [F', hx])
    (fun _ _ _ h => by simp [B, h]) (fun _ _ _ h => by simp [B', h])
  dsimp only [meanError, X, Ya, Yb, source, broad, E, middle] at h ⊢
  norm_num [← mul_assoc] at h ⊢
  exact h

-- Positive terminal densities do not require the source slice to be nonempty.
example (x y : Fin 3) : conditionalTableMean (fun (_ : Bool × Fin 4) _ => False) Ya E x y = 0 := by
  simp [conditionalTableMean]

end ComplexityTests.FineProductMean
