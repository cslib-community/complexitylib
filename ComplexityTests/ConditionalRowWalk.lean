/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (actual retained-pair walk regressions)

public import Complexity.Probability.PairwiseIndependentHash.RowFourthMoment
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Tactic.FinCases

/-!
# Nonconstant conditional walks on unequal and empty slices

The four actual slices have sizes two, three, zero and one. A lazy involution exchanges the two
nonzero seeds inside every slice. The positive integrated centered input moment is `17/24`;
actual two-step averaging reduces it to `3/8`. No output-moment hypothesis is supplied.
-/

public section

namespace ComplexityTests.ConditionalRowWalk

open Cslib Cslib.RotationMap Cslib.Probability Finset
open scoped BigOperators

/-- The second source occurs only at seed zero. -/
abbrev source (σ : Fin 3) (x : Bool) : Prop := x = false ∨ σ = 0
/-- The first target excludes seed zero. -/
abbrev target (σ : Fin 3) (y : Bool) : Prop := y = true ∨ σ ≠ 0

private theorem keep_swap (σ : Fin 3) (x y : Bool) :
    (source (Equiv.swap 1 2 σ) x ∧ target (Equiv.swap 1 2 σ) y) ↔
      source σ x ∧ target σ y := by
  fin_cases σ <;> cases x <;> cases y <;> norm_num [source, target, Equiv.swap_apply_def]

/-- Restrict the same actual seed exchange to each retained pair. -/
@[expose] def swapSlice (x y : Bool) (σ : RetainedPairSlice source target x y) :
    RetainedPairSlice source target x y :=
  ⟨Equiv.swap 1 2 σ.val, by
    have h : source σ.val x ∧ target σ.val y := by
      simpa only [mem_filter, mem_univ, true_and] using σ.property
    simpa using (keep_swap σ.val x y).mpr h⟩

/-- Restricting the seed swap preserves its involution property on every slice. -/
theorem swapSlice_involutive (x y : Bool) : Function.Involutive (swapSlice x y) := by
  intro σ
  apply Subtype.ext
  exact Equiv.swap_apply_self 1 2 σ.val

/-- A genuine one-step lazy seed average, instantiated separately on all four actual slices. -/
@[expose] noncomputable def graph (x y : Bool) :
    RotationMap (RetainedPairSlice source target x y) (Unit ⊕ Unit) :=
  (ofInvolutive (swapSlice x y) (swapSlice_involutive x y)).lazy

/-- A nonconstant sample on the original environment. -/
@[expose] def sample (σ : Fin 3) (_x _y : Bool) : ℝ := σ.val + 1

private theorem walk_formula (x y : Bool) (f : RetainedPairSlice source target x y → ℝ)
    (σ : RetainedPairSlice source target x y) :
    (graph x y).walk f σ = (f σ + f (swapSlice x y σ)) / 2 := by
  rw [graph, walk_lazy_apply]
  simp only [walk_apply, neighbor_ofInvolutive, Fintype.expect_unique]

private theorem walk_two (x y : Bool) (f : RetainedPairSlice source target x y → ℝ)
    (σ : RetainedPairSlice source target x y) :
    ((graph x y).walk ^ 2) f σ = (f σ + f (swapSlice x y σ)) / 2 := by
  rw [pow_two, mul_apply_eq_comp, walk_formula, walk_formula, walk_formula,
    swapSlice_involutive]
  ring

private theorem average_eq (σ : Fin 3) (x y : Bool) :
    conditionalWalk source target graph (fun _ _ => 1) sample σ x y =
      if σ ∈ ({σ | source σ x ∧ target σ y} : Finset (Fin 3)) then
        ((σ.val + 1 : ℝ) + ((Equiv.swap 1 2 σ).val + 1)) / 2 else 0 := by
  unfold conditionalWalk
  split_ifs
  · rw [show 2 * (1 : ℕ) = 2 from rfl, walk_two]
    rfl
  · rfl

/-- At least one actual pair slice is empty. -/
theorem empty_slice : ({σ | source σ true ∧ target σ false} : Finset (Fin 3)) = ∅ := by
  ext σ
  simp [source, target]

/-- The unequal nonempty slice sizes are visible in the actual retention events. -/
theorem unequal_slice_sizes :
    #({σ | source σ false ∧ target σ false} : Finset (Fin 3)) = 2 ∧
    #({σ | source σ false ∧ target σ true} : Finset (Fin 3)) = 3 := by decide

/-- The pair-centered input has a positive, nonconstant integrated fourth moment. -/
theorem centered_input_moment : rowNormPow 4 1 1 source target
    (fun σ x y => sample σ x y - rowSliceMean source target sample x y) = 17 / 24 := by
  have hz : ({x : Fin 3 | x = 0} : Finset (Fin 3)) = {0} := by decide
  have hn : ({x : Fin 3 | x ≠ 0} : Finset (Fin 3)) = {1, 2} := by decide
  norm_num [rowNormPow, rowSliceMean, expect_eq_sum_div_card, Fin.sum_univ_succ,
    Fintype.sum_bool, sum_filter, filter_insert, filter_singleton, source, target, sample, hz, hn]

/-- The actual positive-length graph average has the smaller, still positive moment `3/8`. -/
theorem averaged_moment : rowNormPow 4 1 1 source target
    (fun σ x y => conditionalWalk source target graph (fun _ _ => 1) sample σ x y -
      rowSliceMean source target sample x y) = 3 / 8 := by
  simp_rw [average_eq]
  have hz : ({x : Fin 3 | x = 0} : Finset (Fin 3)) = {0} := by decide
  have hn : ({x : Fin 3 | x ≠ 0} : Finset (Fin 3)) = {1, 2} := by decide
  norm_num [rowNormPow, rowSliceMean, expect_eq_sum_div_card, Fin.sum_univ_succ,
    Fintype.sum_bool, sum_filter, filter_insert, filter_singleton, source, target, sample,
    Equiv.swap_apply_def, hz, hn]

/-- The new integrated theorem obtains its output estimate from the actual slice graphs. -/
theorem graph_supplied_bound : rowNormPow 4 1 1 source target
    (fun σ x y => conditionalWalk source target graph (fun _ _ => 1) sample σ x y -
      rowSliceMean source target sample x y) ≤
      2 * rowNormPow 4 1 1 source target
        (fun σ x y => sample σ x y - rowSliceMean source target sample x y) := by
  simpa only [one_pow, mul_one] using rowNormPow_conditionalWalk_le source target
    (lam := 1) (by norm_num) graph (fun x y => (graph x y).spectralExpansion_le_one) 1 sample

/-- Empty/unequal slices introduce no extra factor, and the example is a strict contraction. -/
example : rowNormPow 4 1 1 source target
    (fun σ x y => conditionalWalk source target graph (fun _ _ => 1) sample σ x y -
      rowSliceMean source target sample x y) <
      rowNormPow 4 1 1 source target
        (fun σ x y => sample σ x y - rowSliceMean source target sample x y) := by
  rw [averaged_moment, centered_input_moment]
  norm_num

/-- A concrete component environment with no retained channels and three free bits. -/
abbrev ComponentEnv :=
  (∀ _j : Fin 0, RetentionSlice 2 3 1 1 (0 : ZMod 2)) × (Fin 3 → ZMod 2)

/-- In this model every coordinate of the actual full slice is part of the component state. -/
@[expose] def componentModel (x z : Unit) :
    RetainedPairSlice (fun (_ : ComponentEnv) (_ : Unit) => True) (fun _ _ => True) x z ≃
      ComponentEnv where
  toFun := Subtype.val
  invFun σ := ⟨σ, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Transport the actual component walk to the actual retained-pair subtype. -/
@[expose] noncomputable def componentGraph (x z : Unit) :=
  ((ofPerms (componentMove 3 2 (fun _ : Fin 0 => 2) (fun _ => 1))).lazy.reindex
    (componentEquiv 2 (fun _ => by decide) (fun _ => 0)).symm).reindex (componentModel x z).symm

/-- A sample depending on an actual free coordinate, rather than a constant placeholder. -/
@[expose] def componentInput (σ : ComponentEnv) (_x _z : Unit) : ℝ :=
  if σ.2 0 = 0 then 1 else 0

/-- The component specialization has a nonconstant, fully represented actual-slice instance. -/
theorem concrete_component_bound :
    rowNormPow 4 1 1 (fun (_ : ComponentEnv) (_ : Unit) => True) (fun _ _ => True)
      (fun σ x z =>
        conditionalWalk (fun _ _ => True) (fun _ _ => True) componentGraph
          (fun _ _ => 1) componentInput σ x z -
        rowSliceMean (fun _ _ => True) (fun _ _ => True) componentInput x z) ≤
      32 * (1 - 1 / 12607488) ^ 2 * rowNormPow 4 1 1
        (fun (_ : ComponentEnv) (_ : Unit) => True) (fun _ _ => True) componentInput := by
  have h := rowNormPow_conditionalWalk_component_le
    (P := fun _ : Fin 0 => 2) (L := fun _ => 1) (M := 2)
    (fun (_ : ComponentEnv) (_ : Unit) => True) (fun _ _ => True)
    (by decide : 3 ≤ 3) (fun _ => by decide) (fun _ _ _ => 0) componentGraph
    (fun x z _ => componentModel x z) (fun _ _ _ => rfl) (N := 1) (u := 1)
    (by norm_num) 1 componentInput
  norm_num only [Nat.cast_zero, zero_add, Nat.cast_ofNat, one_pow, mul_one, Nat.reduceMul] at h ⊢
  exact h

/-- The concrete input genuinely distinguishes two full component environments. -/
example : componentInput (fun j => Fin.elim0 j, fun _ => 0) () () ≠
    componentInput (fun j => Fin.elim0 j, fun _ => 1) () () := by
  norm_num [componentInput]

/-- Zero normalization is allowed without changing the actual walk family. -/
example : rowNormPow 4 0 1 source target (fun σ x y =>
    conditionalWalk source target graph (fun _ _ => 1) sample σ x y -
      rowSliceMean source target sample x y) = 0 := by
  simp [rowNormPow]

end ComplexityTests.ConditionalRowWalk
