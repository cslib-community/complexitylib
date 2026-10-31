/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.TrueSampleMeans
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the true sampled means

The source and intermediate channels each retain on one of two seeds. The broad terminal slice
has two of four seeds; its usage slice has only one. Both correction factors are therefore two.
The correction edge `0 → 1` has weight `1/2`, and the dense edge `1 → 0` has weight `1/3`.
The product sample is `2/3` on one of its four conditioning draws and zero on the others, giving
the prescribed positive product `1/6`.
-/

namespace ComplexityTests.TrueSampleMeans

open Finset Matrix
open scoped BigOperators

private abbrev X (s : Bool) (_ : Fin 2) : Prop := s = true
private abbrev Z (t : Bool) (_ : Fin 2) : Prop := t = true
private abbrev Y (_ : Fin 4) (_ : Fin 2) : Prop := True
private abbrev Ya (t : Fin 4) (_ : Fin 2) : Prop := t.val < 2
private abbrev Yt (t : Fin 4) (_ : Fin 2) : Prop := t = 0

private noncomputable def left (x z : Fin 2) : ℝ := if x = 0 ∧ z = 1 then 1 / 2 else 0
private noncomputable def right (z y : Fin 2) : ℝ := if z = 1 ∧ y = 0 then 1 / 3 else 0

private theorem source_slice (x : Fin 2) : ({s | X s x} : Finset Bool) = {true} := by
  change ({s | s = true} : Finset Bool) = {true}
  decide

private theorem middle_slice (z : Fin 2) : ({t | Z t z} : Finset Bool) = {true} := by
  change ({t | t = true} : Finset Bool) = {true}
  decide

private theorem broad_slice (y : Fin 2) : ({t | Ya t y} : Finset (Fin 4)) = {0, 1} := by
  change ({t : Fin 4 | t.val < 2} : Finset (Fin 4)) = {0, 1}
  decide

private theorem usage_slice (y : Fin 2) : ({t | Yt t y} : Finset (Fin 4)) = {0} := by
  change ({t | t = 0} : Finset (Fin 4)) = {0}
  decide

private theorem middle_density (z : Fin 2) : (dens {t | Z t z} : ℝ) = 1 / 2 := by
  rw [middle_slice, dens_eq_card_div_card]
  norm_num

private theorem broad_density (y : Fin 2) : (dens {t | Ya t y} : ℝ) = 1 / 2 := by
  rw [broad_slice, dens_eq_card_div_card]
  norm_num

private theorem usage_density (y : Fin 2) : (dens {t | Yt t y} : ℝ) = 1 / 4 := by
  rw [usage_slice, dens_eq_card_div_card]
  norm_num

private theorem usage_subset (y : Fin 2) (t : Fin 4) (ht : Yt t y) : Ya t y := by
  rcases ht with rfl
  norm_num [Ya]

private theorem column_support (z : Fin 2) : #{w : Fin 2 | 0 < left w z} ≤ 1 := by
  refine card_le_one.2 fun u hu v hv => ?_
  have hu0 : u = 0 := by
    by_contra h
    simp [left, h] at hu
  have hv0 : v = 0 := by
    by_contra h
    simp [left, h] at hv
  exact hu0.trans hv0.symm

private noncomputable def correction (d : Bool × Bool) (x z : Fin 2) : ℝ :=
  correctionAtom (fun _ _ => 0) (fun _ => 1) 8 8 1 left X Z Z id (fun _ => 1)
    (fun _ => 1) (fun _ => 1) d x z

private noncomputable def dense (t : Fin 4) (z y : Fin 2) : ℝ :=
  denseAtom Y Yt id (fun _ => 1) (fun _ => 1) 4 1 right t z y

private theorem correction_eq (d : Bool × Bool) (x z : Fin 2) :
    correction d x z = if d.2 = true then left x z else 0 := by
  have hn : correctionNormalizer (fun _ _ => 0) (fun _ => 1) 8 8 1 left X Z Z
      (fun _ => 1) (fun _ => 1) x z = 1 := by
    simp [correctionNormalizer, correctionPrep, rowGate, incomingGate, X, Z, filter_eq']
  norm_num [correction, correctionAtom, rowGate, incomingGate, Z, hn]

private theorem dense_eq (t : Fin 4) (z y : Fin 2) :
    dense t z y = if t = 0 then right z y else 0 := by
  norm_num [dense, denseAtom, atomNormalizer, atomPrep, rowGate, Yt, filter_eq']

private noncomputable def sample (d : (Bool × Bool) × Fin 4) : ℝ :=
  4 * ∑ z, correction d.1 0 z * dense d.2 z 0

-- Both scalar corrections are nontrivial, and the integrand is genuinely nonzero.
example : (dens {t | Ya t 0} : ℝ) / dens {t | Yt t 0} = 2 ∧
    (1 : ℝ) / dens {t | Z t 0} = 2 := by
  rw [broad_density, usage_density, middle_density]
  norm_num

example : sample ((true, true), 0) = 2 / 3 := by
  norm_num [sample, correction_eq, dense_eq, left, right, Fin.sum_univ_two]

example : sample ((true, false), 0) = 0 ∧ sample ((true, true), 1) = 0 := by
  norm_num [sample, correction_eq, dense_eq, left, right, Fin.sum_univ_two]

-- The direct term changes from the two-draw broad slice to the singleton usage slice.
private theorem direct_mean :
    𝔼 t ∈ ({t | Ya t 0} : Finset (Fin 4)), 2 * dense t 1 0 = 1 / 3 := by
  have h := expect_denseAtom_change_usage (Y := Y) (Ya := Ya) (Yt := Yt) (k := id)
    (h := fun _ => 1) (ρ := fun _ => 1) (K := 4) (b := 1) (G := right) (x := 1) (y := 0)
    (usage_subset 0) ⟨0, by decide⟩ (fun _ _ => rfl) (fun _ => zero_le_one) (fun _ => le_rfl)
    (η := 1) one_pos (fun _ _ => rfl) one_pos
    (fun w => by fin_cases w <;> norm_num [right]) (M := 1) (by norm_num [right, Fin.sum_univ_two])
    (c := 1) zero_le_one (by norm_num) (fun w _ => by simp [Y, Yt])
  rw [broad_density, usage_density] at h
  norm_num [dense, right] at h ⊢
  exact h

-- Adding the independent source conditioning leaves the direct mean unchanged.
example : 𝔼 d ∈ ({s | X s 1} : Finset Bool) ×ˢ ({t | Ya t 0} : Finset (Fin 4)),
    2 * dense d.2 1 0 = 1 / 3 := by
  rw [expect_product]
  simp only [direct_mean, source_slice, expect_singleton]

-- The product theorem is applied with every gate, pair-count and density hypothesis discharged.
-- In particular the coefficient `f / πf = 2` is justified by the actual middle-channel density.
example : 𝔼 d ∈ (({s | X s 0} : Finset Bool) ×ˢ (univ : Finset Bool)) ×ˢ
      ({t | Ya t 0} : Finset (Fin 4)), sample d = 1 / 6 := by
  have h := expect_correctionAtom_mul_denseAtom
    (I := fun _ _ => 0) (τ := fun _ => 1) (Q := id) (hF := fun _ => 1) (ρF := fun _ => 1)
    (k := id) (hB := fun _ => 1) (ρB := fun _ => 1) (KF := 8) (Kc := 8) (KB := 4)
    (f := 1) (b := 1) (πf := 1 / 2) (G := left) (H := right) (g₀ := fun _ => 1)
    (X := X) (Z := Z) (Zt := Z) (Y := Y) (Ya := Ya) (Yt := Yt) (x := 0) (y := 0)
    (hSx := ⟨true, by decide⟩) (hZπ := middle_density) (hπf := by norm_num)
    (hYt := usage_subset 0) (hSy := ⟨0, by decide⟩)
    (hQh := fun _ _ => rfl) (hρF0 := fun _ => zero_le_one) (hρF1 := fun _ => le_rfl)
    (ηF := 1) (hηF := one_pos) (hρFη := fun _ _ => rfl)
    (hτ0 := fun _ => zero_le_one) (hτ1 := fun _ => le_rfl) (τ₀ := 0) (hτ₀ := le_rfl)
    (hττ := fun _ _ => rfl) (e := 0) (hI := fun _ _ _ => rfl)
    (hf := one_pos) (hG0 := fun w => by fin_cases w <;> norm_num [left])
    (MF := 1) (hGM := by norm_num [left, Fin.sum_univ_two]) (cF := 1) (hcF := zero_le_one)
    (hKF := by norm_num) (hpairZ := fun z w _ => by simp [Z])
    (p := 1) (hp := zero_le_one) (hpairX := fun w _ => by simp [X])
    (R := 1) (hR := fun z _ => by simpa using column_support z)
    (hKc := by norm_num) (hkh := fun _ _ => rfl) (hρB0 := fun _ => zero_le_one)
    (hρB1 := fun _ => le_rfl) (ηB := 1) (hηB := one_pos) (hρBη := fun _ _ => rfl)
    (hb := one_pos) (hH0 := fun z w => by fin_cases z <;> fin_cases w <;> norm_num [right])
    (MB := 1) (hHM := fun z => by fin_cases z <;> norm_num [right, Fin.sum_univ_two])
    (cB := 1) (hcB := zero_le_one) (hKB := by norm_num) (hpairY := fun w _ => by simp [Y, Yt])
  rw [broad_density, usage_density] at h
  norm_num [sample, correction, dense, left, right, Fin.sum_univ_two] at h ⊢
  exact h

end ComplexityTests.TrueSampleMeans
