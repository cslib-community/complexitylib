/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.DetectedHierarchy
import Mathlib.Tactic.FinCases

/-!
# Tests for the hierarchy constants and the iterated hierarchy
-/

namespace ComplexityTests.DetectedHierarchy

open Finset Matrix Cslib.Probability

/-! ### Constants -/

-- Stage parameters exist for the density divisor `q = 2` and any channel constants with
-- `c_π > 0`.
example : Nonempty (HierarchyParams 2 1 2 2 0) := HierarchyParams.nonempty (by norm_num) one_pos

/-- A channel with one seed that retains every vertex. -/
private abbrev all {V : Type*} : Unit → V → Prop := fun _ _ => True

/-- Channels that retain everything satisfy the interface at a rate `f ≤ 1` whenever
`C_π f ≥ 1` and `C_pair f ≥ 1`, with `c_π = 1` and `C_var = 0`. -/
private theorem retentionChannels_all {V : Type*} {f Cπ Cpair : ℝ} (hf1 : f ≤ 1)
    (hCπ : 1 ≤ Cπ * f) (hCp : 1 ≤ Cpair * f) :
    RetentionChannels (all (V := V)) all f 1 1 Cπ Cpair 0 where
  dens_X _ := by simp [all]
  dens_Y _ := by simp [all]
  lower := by simpa using hf1
  upper := hCπ
  pair _ _ _ := by simpa [all] using hCp
  tail A _ := by
    have : ({s | 2 * (#{x ∈ A | all s x} : ℝ) < #A * 1} : Finset Unit) = ∅ := by
      ext s
      simp only [all, filter_true, mul_one, mem_filter, mem_univ, true_and, notMem_empty,
        iff_false, not_lt]
      linarith [(Nat.cast_nonneg (α := ℝ) #A)]
    rw [this]
    simp

/-! ### The walk on `Fin n` -/

/-- The walk on `Fin n` that moves from `i` to `i + 1` with probability `1 / 2`. -/
private noncomputable def walk (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j => if i.val + 1 = j.val then 1 / 2 else 0

private theorem walk_upper (n : ℕ) : (walk n).IsStrictUpperTriangular := by
  intro i j h
  simp only [walk, of_apply, ite_eq_right_iff]
  intro hij
  exact absurd (Fin.lt_def.mpr (by omega)) h

private theorem walk_nonneg (n : ℕ) (i j : Fin n) : 0 ≤ walk n i j := by
  simp only [walk, of_apply]; split_ifs <;> norm_num

private theorem walk_row (n : ℕ) : walk n *ᵥ 1 ≤ 1 := by
  intro i
  simp only [walk, mulVec, dotProduct, of_apply, Pi.one_apply, mul_one]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
  have hcard : #({j | i.val + 1 = j.val} : Finset (Fin n)) ≤ 1 :=
    card_le_one.mpr fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact Fin.ext (by omega)
  have : (#({j | i.val + 1 = j.val} : Finset (Fin n)) : ℝ) ≤ 1 := by exact_mod_cast hcard
  linarith

/-! ### Stage vertices `Fin (3 (m + 1) ^ l)` with lexicographic copies -/

-- After one stage at rate `f₀ = 1` with full-retention channels, the walk on `Fin 3` becomes a
-- strictly upper triangular, nonnegative, substochastic matrix on `Fin (3 (m + 1))` with
-- entries at most `q⁻¹ = 1 / 2`, for every choice of the stage parameters.
example (P : HierarchyParams 2 1 1 1 0) :
    let H := hierarchy P (V := fun l => Fin (3 * (P.m + 1) ^ l)) (radixCopyEquiv 3 P.m)
      (fun _ => all) (fun _ => all) (walk (3 * (P.m + 1) ^ 0)) 1
    H.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ H x y) ∧ H *ᵥ 1 ≤ 1 ∧
      ∀ x y, H x y ≤ (2 : ℝ)⁻¹ ^ 1 :=
  hierarchy_invariant (P := P) (q := 2) (V := fun l => Fin (3 * (P.m + 1) ^ l))
    (e := radixCopyEquiv 3 P.m) (X := fun _ => all) (Y := fun _ => all)
    (S := walk (3 * (P.m + 1) ^ 0))
    (π := fun _ => 1) (fun l _ _ h => radixCopyEquiv_lt 3 P.m l h) (by norm_num) one_pos
    (walk_upper _) (walk_nonneg _) (walk_row _) 1 fun l hl => by
      obtain rfl : l = 0 := by omega
      exact retentionChannels_all (f := (2 : ℝ)⁻¹ ^ 0) (Cπ := 1) (Cpair := 1) (by norm_num)
        (by norm_num) (by norm_num)

end ComplexityTests.DetectedHierarchy
